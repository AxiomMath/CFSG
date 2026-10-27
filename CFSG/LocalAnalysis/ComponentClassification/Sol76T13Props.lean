module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76Thm13Props

public section

namespace CFSG.ComponentClassification.Sol76T13

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.ComponentClassification.Sol76

@[expose] def simpleAmbient : Thm13Ambient := fun G _ _ => SimpleAmbient G

theorem solomonThm13Simple_of_props
    (h33 : Lemma33InputFor simpleAmbient) (hres : Lemma313ResidueInputFor simpleAmbient)
    (h32 : Lemma32InputFor simpleAmbient) (h315a : Lemma315aInputFor simpleAmbient)
    (h315c : Lemma315cInputFor simpleAmbient) (hbal : Lemma316BalancedInputFor simpleAmbient)
    (hprod : Lemma316ProductInputFor simpleAmbient) : SolomonThm13Simple :=
  solomonThm13Simple_of_noChoice fun _ _ _ hG _ hN =>
    false_of_isSolomonChoice_of_props h33 hres h32 h315a h315c hbal hprod hG hN

theorem lemma32InputFor_simple_of_simple (h : SolomonThm13Simple) :
    Lemma32InputFor simpleAmbient :=
  fun _ _ _ hG _ hN => (not_isSolomonChoice_of_simple h hG hN).elim

theorem lemma33InputFor_simple_of_simple (h : SolomonThm13Simple) :
    Lemma33InputFor simpleAmbient :=
  fun _ _ _ hG _ hN => (not_isSolomonChoice_of_simple h hG hN).elim

theorem lemma313ResidueInputFor_simple_of_simple (h : SolomonThm13Simple) :
    Lemma313ResidueInputFor simpleAmbient :=
  fun _ _ _ hG _ hN => (not_isSolomonChoice_of_simple h hG hN).elim

theorem lemma315aInputFor_simple_of_simple (h : SolomonThm13Simple) :
    Lemma315aInputFor simpleAmbient :=
  fun _ _ _ hG _ hN => (not_isSolomonChoice_of_simple h hG hN).elim

theorem lemma315cInputFor_simple_of_simple (h : SolomonThm13Simple) :
    Lemma315cInputFor simpleAmbient :=
  fun _ _ _ hG _ hN => (not_isSolomonChoice_of_simple h hG hN).elim

theorem lemma316BalancedInputFor_simple_of_simple (h : SolomonThm13Simple) :
    Lemma316BalancedInputFor simpleAmbient :=
  fun _ _ _ hG _ hN => (not_isSolomonChoice_of_simple h hG hN).elim

theorem lemma316ProductInputFor_simple_of_simple (h : SolomonThm13Simple) :
    Lemma316ProductInputFor simpleAmbient :=
  fun _ _ _ hG _ hN => (not_isSolomonChoice_of_simple h hG hN).elim

end CFSG.ComponentClassification.Sol76T13
