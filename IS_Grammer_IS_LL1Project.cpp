#include <iostream>
#include <bits/stdc++.h>
using namespace std;
vector <string> rules;
vector<char> Terminlas;
vector<char> nonterminals;
vector<int> nullablerule;
vector<char> nullableNonterminal;
set<char>symbols;
set<char>::iterator it;
vector<string> begin_D_with;
vector <string> beginWith;
vector<string> firstOf;
vector<string> first_Of_rigtht_Side;
vector<string> folwed_D_by;
vector<string> DirectEndOf;
vector<string> EndOf;
vector<string> Folowedby;
vector<string> ExtendFolowedby;
vector<string> folowsetis;
vector <string>selectionset;


/*****************************Start of seperate() Function*****************************************/
void seperate()
{
    int len=rules.size();
    for(int i=0; i<len; i++)
    {
        for(int j=0; j<rules[i].length(); j++)
        {
            if(rules[i][j]!='$'&&rules[i][j]!='=')
            {
                symbols.insert(rules[i][j]); //create set of symbols to prevent duplicates (Store unique symbols)
                // we will use symbols set to find reflexive in Step 3 (Line 176 )
            }
        }
    }
}
/*****************************End of seperate() Function*****************************************/
void seperate_terminals()
{
    // seperate terminals and non terminals
    for(it=symbols.begin(); it!=symbols.end(); it++)
    {
        if(isupper(*it))
            nonterminals.push_back(*it); // Store all nonterminals in a vector
        else
            Terminlas.push_back(*it);  // store all Terminals in a vector
    }
}
/*****************************End of seperate_terminals() Function*****************************************/

void FindNullableAndnonterminals()
{
    //find the nullabe rules  and the nullable nontermials
    int len=rules.size();
    for(int i=0; i<len; i++)
    {
        if(rules[i][2]=='$') // if there are epslion
        {
            char nont=rules[i][0];
            nullableNonterminal.push_back(nont);//assign the non terminal to be nullable nonterminal
            nullablerule.push_back(i);// insert the index of the rule that contain epslion in the nullablerule vector
        }

    }

}
/*****************************End of FindNullableAndnonterminals() Function**********************************/

bool is_null_nonterminal(char a) //check if the symbol is nullable non terminla or not.
{
    int value=0;
    for(int i=0; i<nullableNonterminal.size(); i++)
    {
        if(nullableNonterminal[i]==a)
            ++value;

    }
    if(value)//if the crachter been found  then it is nullble non terminal
        return 1;
    else
        return 0;

}
void extended_Nullable_rule()
/* if the  rule are in the form AB and all symbols of A and B is nullable nonterminals so
it will be nullalle rule and its non ternminal will be a nullable non terminal
*/
{

    for(int i=0; i<rules.size(); i++)
    {
        int counter=0;
        for(int j=2; j<rules[i].length(); j++) //check all the symbols of the rhs if nullable nonterminal or not
        {
            if(is_null_nonterminal(rules[i][j]))
                ++counter;
        }
        if(counter==(rules[i].length())-2) // for example : Rule is S=AB , check if A and B is nullable nonterminals so S is
            // also nullable nonterminal and Rule is nullable Rule
        {
            nullablerule.push_back(i);
            nullableNonterminal.push_back(rules[i][0]);
        }

    }
}
/*****************************End of extended_Nullable_rule() Function**********************************/


/****************************step 1 find nullable rules and nullable non terminals*********************/
void stepOne()
{
    FindNullableAndnonterminals();// find the nullable Rules and nullable nonterminals that already inserted in the Grammer
    extended_Nullable_rule();// extend New nullable Rules

    cout<<"***********STEP(1)************\n";
    cout <<"Nullable Rules are Rules : ";
    for(int i=0; i<nullablerule.size(); i++) cout<<nullablerule[i]+1<<" ";
    cout<<"\n"<<nullablerule.size()<<"\n";
    cout <<"Nullable nonterminals are : ";
    for(int i=0; i<nullableNonterminal.size(); i++) cout<<nullableNonterminal[i]<<" ";
    cout<<"\n";
}

/******************************************step 2 Begin Directly With ***************************************************/

void steptwo()
{
    int len= rules.size();
    for(int i=0; i<len; i++)
    {
        string s="";
        s+=rules[i][0];
        s+=" BDW ";
        for(int j=2; j<rules[i].length(); j++)
        {

            if(rules[i][j]!='$')
                if(is_null_nonterminal(rules[i][j])) // if the current nullable  we will continue
                    // and insert the following symbol until reaching not nullable symbol
                {

                    begin_D_with.push_back(s+rules[i][j]);
                    continue;
                }
                else
                {
                    // if not we will excute current and break
                    begin_D_with.push_back(s+rules[i][j]);
                    break;
                }
        }

    }
    cout<<"***********STEP(2)************\n";
    for(int i=0; i<begin_D_with.size(); i++)  cout<<begin_D_with[i]<<"\n";
}
/******************************step 3  compute  begin with  reflexive  transitive ************/
void step3()
{
    vector<string> from_BDW;
    vector<string> withitself;
    vector<string> transitive;
    /*********************from BDW  ***********************/
    int bdwlen=begin_D_with.size();
    for(int i=0; i<bdwlen; i++)
    {
        string s="";
        s+=begin_D_with[i][0];
        s+=" BW ";
        s+=begin_D_with[i][begin_D_with[i].length()-1];
        from_BDW.push_back(s);  //  from_BDW Vector contains BW Relations

    }
    /**************reflexive*********************/
    for(it=symbols.begin(); it!=symbols.end(); it++)
    {
        string s="";
        s+=*it;
        s+=" BW ";
        s+=*it;
        withitself.push_back(s);  // withitself Vector contains reflexive Relations
    }
    /*************transitive********************/
    int fromlen=from_BDW.size();
    for(int i=0; i<fromlen; i++)
    {
        string temp=from_BDW[i];
        char first1=temp[0];
        char last1=temp[temp.length()-1];
        for(int j=0; j<fromlen; j++)
        {
            if(i!=j)  // 2 different rules
            {
                char first2=from_BDW[j][0];
                char last2=from_BDW[j][from_BDW[j].length()-1];
                if(last1==first2)
                {
                    string s="";
                    s+=first1;
                    s+=" BW ";
                    s+=last2;
                    transitive.push_back(s); // transitive Vector contains Transitive Relations

                }
            }
        }
    }
    /************************Push all vectors in beginWith Vector **************************/
    int len1=from_BDW.size();
    int len2=withitself.size();
    int len3=transitive.size();
    for(int i=0; i<len1; i++)
    {
        beginWith.push_back(from_BDW[i]);
    }
    for(int i=0; i<len2; i++)
    {
        beginWith.push_back(withitself[i]);
    }
    for(int i=0; i<len3; i++)
    {
        beginWith.push_back(transitive[i]);
    }

    cout<<"***********STEP(3)************\n";
    cout<<"(From BDW)\n";
    for(int i=0; i<len1; i++) cout<<from_BDW[i]<<"\n";
    cout<<"\n(reflexive)\n";
    for(int i=0; i<len2; i++) cout<<withitself[i]<<"\n";
    cout<<"\n(transitive)\n";
    for(int i=0; i<len3; i++) cout<<transitive[i]<<"\n";
    cout<<"\n";
}
/**********************************************strp 4 : first(x) *********************************************/
void step4()
{
    //get all the terminlas from begin with for each rule

    int len=beginWith.size();
    for( int i=0; i<len; i++)
    {
        if(islower(beginWith[i][(beginWith[i].length())-1]))//if it terminal
        {
            char x=beginWith[i][(beginWith[i].length())-1];
            string s="";
            s+=beginWith[i][0];
            s+=" it's first is  ";
            s+=x;
            firstOf.push_back(s);

        }

    }
    cout<<"***********STEP(4)************\n";
    for(int i=0; i<firstOf.size(); i++) cout<<firstOf[i]<<"\n";
    cout<<"\n";
}


// we use this method in Step 5 to get the first of any nonterminal

vector <char> getthefirstof(char a)  //get the first of nonterminal and send them as vector
{
    vector <char> vect;
    for(int i=0; i<firstOf.size(); i++)
    {
        if(firstOf[i][0]==a)
        {
            char x=firstOf[i][(firstOf[i].length())-1];
            vect.push_back(x);

        }
    }
    return vect;    // contains the first set of a specific nonterminal

}

/******************************Step5 : compute the first of rigth side for each rule *******************/
void  step5()
{
    set<string> fiset;
    set<string> ::iterator ir;

    int lenrukes=rules.size();
    for(int i=0; i<lenrukes; i++) //Iterate each rule and check
    {
        int rigthsidelen=rules[i].length()-2;
        string RHS=rules[i].substr(2,rigthsidelen);
        for(int j=2; j<rules[i].length(); j++) // go through the rigth hand side
        {
            string s="";
            if(islower(rules[i][j]))// if the right is terminal so get it and break ;
            {
                string s="";
                s+=rules[i][j];
                s+=" is first of ";
                s+=RHS;
                fiset.insert(s);
                break;

            }


            else //if  nullable  nonterminal
            {
                char current=rules[i][j];
                if(is_null_nonterminal(current))  // if the current is nullable non terminal
                {
                    vector<char> vect=getthefirstof(current); // get the first of it and continue till the first terminal
                    // or not nullable non termoinal
                    for(int i=0; i<vect.size(); i++)
                    {
                        string s="";
                        s+=vect[i];
                        s+=" is first of ";
                        s+=RHS;
                        fiset.insert(s);

                    }


                }
                else  /// if the current is ternminal or not nullable nonterminal
                {
                    vector<char> vect=getthefirstof(current);// get the first of it and break beacuse we now we find terminal sympol or not nullable
                    for(int i=0; i<vect.size(); i++)
                    {
                        string s="";
                        s+=vect[i];
                        s+=" is first of ";
                        s+=RHS;
                        fiset.insert(s);
                        break;

                    }


                }
            }

        }



    }
// swap from the set to the vector with removing duplicates
    for(ir=fiset.begin(); ir!=fiset.end(); ir++)
        first_Of_rigtht_Side.push_back(*ir);


    cout<<"***********STEP(5)************\n";
    for(int i=0; i<first_Of_rigtht_Side.size(); i++)  cout<<first_Of_rigtht_Side[i]<<"\n";
    cout<<"\n";

}

/******************************************step 6 is folowed dirctly by :**************************************************/
void step6()
{
    int tlen=nonterminals.size();
    for(int i=0; i<tlen; i++) // for each non terminal go through and get the next not nullable symbol
    {
        for(int j=0; j<rules.size(); j++)
        {
            // go throuth the  rules and find it.
            int val=rules[j].find(nonterminals[i]);
            if(val!=-1&&val>=2) //if found on the rigth side
            {
                for(int k=val+1; k<rules[j].length(); j++)
                {
                    if(!is_null_nonterminal(rules[j][k])) // if  the current is not  nullable get it and break
                    {
                        string s="";
                        s+=nonterminals[i];
                        s+=" FDB ";
                        s+=rules[j][k];
                        folwed_D_by.push_back(s);
                        break;
                    }
                }

            }
        }


    }

    cout<<"***********STEP(6)************\n";
    for(int i=0; i<folwed_D_by.size(); i++) cout<<folwed_D_by[i]<<"\n";
    cout<<"\n";
}
/******************************* step 7 compute relation is direct end of *********************/

void step7()
{
    int rullen=rules.size();
    for(int i=0; i<rullen; i++)
    {
        for(int j=rules[i].length()-1; j>=2; j--) // loop through rules in reverse
        {
            if(!is_null_nonterminal(rules[i][j])&&rules[i][j]!='$') // if not nullable nonterminal get the DEO and break
            {
                string s="";
                s+=rules[i][j];
                s+=" DEO ";
                s+=rules[i][0];
                DirectEndOf.push_back(s);
                break;
            }
            else  // if nullable get the DEO and continue till the condition break
            {
                if(rules[i][j]!='$')
                {
                    string s="";
                    s+=rules[i][j];
                    s+=" DEO ";
                    s+=rules[i][0];
                    DirectEndOf.push_back(s);
                }

            }
        }
    }

    cout<<"***********STEP(7)************\n";
    for(int i=0; i<DirectEndOf.size(); i++) cout<<DirectEndOf[i]<<"\n";
    cout<<"\n";
}
/***********************Step 8 : compute relation is End of **************************************/
void step8()  // compute the reflexive transitive of the rules
{
    vector<string> fromDEo;
    vector<string> withitself;
    vector<string> transitive;

    /**************** 	from end of 	* **********************/

    for(int i=0; i<DirectEndOf.size(); i++)
    {

        string s="";
        s+=DirectEndOf[i][0];
        s+=" EO ";
        s+=DirectEndOf[i][DirectEndOf[i].length()-1];
        fromDEo.push_back(s);

    }
    /************************reflexive *****************************/
    for(it=symbols.begin(); it!=symbols.end(); it++)
    {
        string s="";
        s+=*it;
        s+=" EO ";
        s+=*it;
        withitself.push_back(s);
    }
    /**********************************transitive ********************************/
    int len=fromDEo.size();
    for(int i=0; i<len; i++)
    {
        char first1=fromDEo[i][0];
        char last1=fromDEo[i][fromDEo[i].length()-1];
        for(int j=0; j<len; j++)
        {
            if(i!=j)
            {
                char first2=fromDEo[j][0];
                char last2=fromDEo[j][fromDEo[j].length()-1];
                if(last1==first2)
                {
                    string s="";
                    s+=first1;
                    s+=" EO ";
                    s+=last2;
                    transitive.push_back(s);

                }


            }

        }
    }

    /************gethering ***************/
    set<string> se;
    set<string> ::iterator ir;

    int len1=fromDEo.size();
    int len2=withitself.size();
    int len3=transitive.size();
    for(int i=0; i<len1; i++)
    {
        se.insert(fromDEo[i]);
    }
    for(int i=0; i<len2; i++)
    {
        se.insert(withitself[i]);
    }
    for(int i=0; i<len3; i++)
    {
        se.insert(transitive[i]);
    }
    for(ir=se.begin(); ir!=se.end(); ir++)
    {
        EndOf.push_back(*ir);
    }

    cout<<"***********STEP(8)************\n";

    for(int i=0; i<EndOf.size(); i++) cout<<EndOf[i]<<"\n";
    cout<<"\n";
}
/************************Step 9: compute relation is followed by  **************************************/
/**
 *  W EO X          X FDB Y         Y BW Z             ( SO : W FB Z )
**/
void  step9()
{
    int lenEO=EndOf.size();
    int lenFDB=folwed_D_by.size();
    int lenBW=beginWith.size();
    for(int i=0; i<lenEO; i++)
    {
        char first1=EndOf[i][0];
        char last1=EndOf[i][EndOf[i].length()-1];
        for(int j=0; j<lenFDB; j++)
        {
            char first2=folwed_D_by[j][0];
            char last2=folwed_D_by[j][folwed_D_by[j].length()-1];
            for(int k=0; k<lenBW; k++)
            {
                char first3=beginWith[k][0];
                char last3=beginWith[k][beginWith[k].length()-1];
                if((last1==first2)&&(last2==first3))
                {
                    string s="";
                    s+=first1;
                    s+=" FB ";
                    s+=last3;
                    Folowedby.push_back(s);
                }


            }
        }
    }

    cout<<"***********STEP(9)************\n";

    for(int i=0; i<Folowedby.size(); i++) cout<<Folowedby[i]<<"\n";
    cout<<"\n";
}
/***********************Step 10 :  extend the followed by to include end mark  **************************************/

void step10()
{
    /**
    A FB ← if A EO S where A represents any nonterminal and S represents the starting nonterminal.

    **/
    int leneo=EndOf.size();
    for(int i=0; i<leneo; i++)
    {
        if(isupper(EndOf[i][0]))
        {
            if(EndOf[i][EndOf[i].length()-1]==rules[0][0])
            {
                string s="";
                s+= EndOf[i][0];
                s+=" FB ";
                s+="__";
                ExtendFolowedby.push_back(s);
            }

        }
    }

    cout<<"***********STEP(10)************\n";

    for(int i=0; i<ExtendFolowedby.size(); i++) cout<<ExtendFolowedby[i]<<"\n";
    cout<<"\n";

}
/*****************************************step 11 compute the follow set: *******************************************/
void step11()
{
    char nullable;
    int len=Folowedby.size();
    int nulllen=nullableNonterminal.size();// get the follow set for each nullable nonterminal
    for(int i=0; i<nulllen; i++)
    {
        nullable=nullableNonterminal[i]; // get character by character
        vector <char> vect;

        for(int j=0; j<len; j++)
        {
            if(Folowedby[j][0]==nullable && islower(Folowedby[j][Folowedby[j].length()-1])) // check if lhs ==nullable && rhs is a terminal char
            {
                vect.push_back(Folowedby[j][Folowedby[j].length()-1]);

            }
        }
        string s="";
        s+=nullable;
        s+=" 'S  FOLLOW IS {";
        for(int i=0; i<vect.size(); i++)
        {
            s+=vect[i];
            if(i)
                s+=",";

        }
        s+="}";
        folowsetis.push_back(s);
    }

    cout<<"***********STEP(11)************\n";

    for(int i=0; i<folowsetis.size(); i++) cout<<folowsetis[i]<<"\n";
    cout<<"\n";


}
/**********************************************************************************************/

bool isnulllaberule(int  k)  // check if the rule nullable rule.
{
    for(int i=0; i<nullablerule.size(); i++)
    {
        if(k==nullablerule[i])
            return 1;
    }
    return 0;
}
/****************************************step 12 : get the Selection set for each rule **********************************************/


void step12()
{
    int rulelen=rules.size();
    for(int i=0; i<rulelen; i++)
    {
        if(!isnulllaberule(i))
        {
            //cout<<i<<endl;
            vector<char>vect;
            string s=rules[i].substr(2,rules[i].length()-2);
            //cout<<s<<endl;
            for(int j=0; j<first_Of_rigtht_Side.size(); j++)
            {
                int x=first_Of_rigtht_Side[j].find(s);
                if(x!=-1)
                {
                    string temp=first_Of_rigtht_Side[j].substr(14,first_Of_rigtht_Side[j].length()-14);
                    if(temp==s)
                    {
                        vect.push_back(first_Of_rigtht_Side[j][0]);
                    }
                }
            }
            sort(vect.begin(),vect.end());
            string y="SELECTION SET OF  ";
            y+=rules[i][0];
            y+=" {";
            for(int k=0; k<vect.size(); k++)
            {
                int z=vect.size();
                if(z>1&&k!=z-1)
                {
                    y+=vect[k];
                    y+=",";
                }
                else
                {
                    y+=vect[k];
                }

            }
            y+="}";
            selectionset.push_back(y);
        }
        /*************if nullable rule **********/
        else
        {
            vector <char> vect2;
            string s=rules[i].substr(2,rules[i].length()-2);
            /************************get the folow set of the  non terminal ********************/
            for(int y=0; y<folowsetis.size(); y++)
            {
                if(folowsetis[y][0]==rules[i][0])
                {
                    int len=folowsetis[y].length();
                    for(int w=0; w<len; w++)
                    {
                        if(islower(folowsetis[y][w]))
                            vect2.push_back(folowsetis[y][w]);
                    }
                }
            }
            /********************************get the first of the rigth side **********************/
            for(int j=0; j<first_Of_rigtht_Side.size(); j++)
            {
                int x=first_Of_rigtht_Side[j].find(s);
                if(x!=-1)
                {
                    string temp=first_Of_rigtht_Side[j].substr(14,first_Of_rigtht_Side[j].length()-14);
                    if(temp==s)
                    {
                        vect2.push_back(first_Of_rigtht_Side[j][0]);
                    }
                }



            }
            sort(vect2.begin(),vect2.end());
            string y="SELECTION SET OF  ";
            y+=rules[i][0];
            y+=" {";
            for(int k=0; k<vect2.size(); k++)
            {
                int z=vect2.size();
                if(z>1&&k!=z-1)
                {
                    y+=vect2[k];
                    y+=",";
                }
                else
                {
                    y+=vect2[k];
                }

            }
            y+="}";
            selectionset.push_back(y);


        }
    }

    cout<<"***********STEP(12)************\n";

    for(int i=0; i<selectionset.size(); i++) cout<<selectionset[i]<<"\n";
    cout<<"\n";

}
/***************************************check if the rule ll1***********************************/
bool iSLL1()
{
    int count=0;
    for(int i=0; i<selectionset.size(); i++)
    {
        for(int j=0; j<selectionset.size(); j++)
        {
            if(selectionset[i]==selectionset[j]&&i!=j)
            {
                ++count;
            }
        }
    }
    if(count)
        return false;
    else
    {
        return true;
    }
}






/****************************************************************************************************/


int main()
{
    int n;
    cout<<" Enter the number of rules  "<<endl;
    cin>>n;
    cin.clear();
    cin.ignore();
    string s;
    for(int i=0; i<n; i++)
    {
        getline(cin,s);
        rules.push_back(s);
    }

    seperate();
    seperate_terminals();
    stepOne();
    steptwo();
    step3();
    step4();
    step5();
    int nullsize=nullablerule.size();
    if(nullsize>0)
    {


        step6();
        step7();
        step8();
        step9();
        step10();
        step11();
        step12();

        if(iSLL1() )
        {
            cout<<"The rules you entered is LL1 Grammer "<<endl;
        }
        else
        {
            cout<<"The rules you entered is Not  LL1 Grammer "<<endl;
        }
    }
    else
    {


        step12();

        if(iSLL1() )
        {
            cout<<"The rules you entered is LL1 Grammer "<<endl;
        }
        else
        {
            cout<<"The rules you entered is  Not LL1 Grammer "<<endl;
        }





    }





    return 0;
}