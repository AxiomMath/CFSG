module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph
open scoped commutatorElement

section Cit3


@[expose] def TightE3C268Ex (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (J : Subgroup Y)
    (u : Y), E3Frame n R S t J u → ∀ (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u),
      TightEdgeless (secR R u) → (∀ W ∈ WSet (E3.secΩ R u), MuIsoZ2 (E3.secΩ R u) W) →
        ¬ TightInO2 (E3.secT htu ht) → Concl163 (secR R u) (E3.secT htu ht) →
      ∀ (Rd : Subgroup Y) (Sd : Sylow 2 Rd) (S' : Sylow 2 Y) (R' T W : Subgroup Y),
        tightCore Rd = J → TightStd8R 3 n Rd Sd u (tightCore R) S' R' T W t →
          MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W →
            C264One (CoreAssembly.conjClass (tightCore Rd)) u t →
        ∀ x ∈ nbrGen (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J,
          ¬ ∀ y ∈ E3.orbGen (CoreAssembly.conjClass (tightCore R)) (tightCore R) J,
            ⁅x * (u * t) * x⁻¹, y⁆ ∈
              oddCoreOf (E3.orbGen (CoreAssembly.conjClass (tightCore R)) (tightCore R) J)

@[expose] def TightE3C269Gen (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (J : Subgroup Y)
    (u : Y), E3Frame n R S t J u → ∀ (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u)
    (Sb : Sylow 2 ↥(secR R u)), TightEx (SecQ R u) (secR R u) Sb (E3.secT htu ht) →
      TightEdgeless (secR R u) → (∀ W ∈ WSet (E3.secΩ R u), MuIsoZ2 (E3.secΩ R u) W) →
        ¬ TightInO2 (E3.secT htu ht) →
          omegaNbr (CoreAssembly.conjClass (tightCore R)) J ⊆
            orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J (tightCore R) →
      ∀ (Rd : Subgroup Y) (Sd : Sylow 2 Rd) (S' : Sylow 2 Y) (R' T W : Subgroup Y),
        tightCore Rd = J → TightStd8R 3 n Rd Sd u (tightCore R) S' R' T W t →
          MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W →
        ∀ x ∈ nbrGen (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J,
          x * t * x⁻¹ ≠ t → x * t * x⁻¹ * t = t * (x * t * x⁻¹) →
            nbrGen (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J ≤
              nbrGen (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J ⊓
                  Subgroup.centralizer ({t} : Set Y) ⊔ Subgroup.zpowers x ⊔
                oddCoreOf (nbrGen (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J)

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
