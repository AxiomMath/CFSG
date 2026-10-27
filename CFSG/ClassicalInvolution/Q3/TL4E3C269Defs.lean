module

public import CFSG.ClassicalInvolution.Q3.TL4Conn264A
public import CFSG.ClassicalInvolution.Q3.TL4Conn26E4A
public import CFSG.ClassicalInvolution.Q3.TL4E3Plus
public import CFSG.ClassicalInvolution.Q3.TL4ModelFacts

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

section Cit3


@[expose] def TightE3Z2Sec163 (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (J : Subgroup Y)
    (u : Y), E3Frame n R S t J u → ∀ (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u)
    (Sb : Sylow 2 ↥(secR R u)), TightEx (SecQ R u) (secR R u) Sb (E3.secT htu ht) →
      TightEdgeless (secR R u) → (∀ W ∈ WSet (E3.secΩ R u), MuIsoZ2 (E3.secΩ R u) W) →
        ¬ TightInO2 (E3.secT htu ht) → Concl163 (secR R u) (E3.secT htu ht)

@[expose] def TightE3C269S (n : ℕ) : Prop :=
  TightLambdaCommR 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (J : Subgroup Y)
    (u : Y), E3Frame n R S t J u → ∀ (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u)
    (Sb : Sylow 2 ↥(secR R u)), TightEx (SecQ R u) (secR R u) Sb (E3.secT htu ht) →
      TightEdgeless (secR R u) → (∀ W ∈ WSet (E3.secΩ R u), MuIsoZ2 (E3.secΩ R u) W) →
        ¬ TightInO2 (E3.secT htu ht) → Concl163 (secR R u) (E3.secT htu ht) →
      ∀ (Rd : Subgroup Y) (Sd : Sylow 2 Rd) (S' : Sylow 2 Y) (R' T W : Subgroup Y),
        tightCore Rd = J → TightStd8R 3 n Rd Sd u (tightCore R) S' R' T W t →
          MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W →
            ¬ C264One (CoreAssembly.conjClass (tightCore Rd)) u t

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
