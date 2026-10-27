module

public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113Native

public section

namespace CFSG.QuasithinUnique.Bridge

open CFSG.Quasithin CFSG.Open
open scoped commutatorElement

@[expose] def AsB113DetList (𝒦 : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (G A L : Subgroup (MulAut V)), 𝒦 ↥G → pCoreOf 2 G = ⊥ →
      IsFFStarOffender G A → CFSG.Open.IsComponentOf L G → ⁅L, A⁆ = L →
        IsLieAltType ↥L ∧ SQTKCharTwoOrAltNative (↥L ⧸ Subgroup.center ↥L)

@[expose] def AsLieAltSylowCentralizerList : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (L T : Subgroup Ω), CFSG.IsQuasisimple ↥L →
    Odd (Nat.card ↥(Subgroup.center ↥L)) → IsLieAltType ↥L →
    SQTKCharTwoOrAltNative (↥L ⧸ Subgroup.center ↥L) → CFSG.QuasithinUnique.IsSylowTwoOf T L →
    ∀ x : Ω, x ∈ Subgroup.normalizer (L : Set Ω) → x ∈ Subgroup.centralizer (T : Set Ω) →
      Odd (orderOf x) → x ∈ Subgroup.centralizer (L : Set Ω)

@[expose] def AsLieAltOvergroupsList : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (L T X K : Subgroup Ω), CFSG.IsQuasisimple ↥L →
    Odd (Nat.card ↥(Subgroup.center ↥L)) → IsLieAltType ↥L →
    SQTKCharTwoOrAltNative (↥L ⧸ Subgroup.center ↥L) → CFSG.QuasithinUnique.IsSylowTwoOf T L →
    T ≤ X → X ≤ L → X ≠ L → K ≤ X → CFSG.Open.IsSubnormal K X →
    (CFSG.IsQuasisimple ↥K ∨ Nat.card ↥K = 3) → ¬ K ≤ Subgroup.centralizer (L : Set Ω) →
    ∃ m, IsAlt m ↥L ∧ ((∃ n, n ≤ m ∧ IsAlt n ↥K) ∨ (IsPSL 3 2 1 ↥K ∧ m = 7))

structure AsB113InputsList (𝒦 : ∀ (X : Type) [Group X], Prop) : Prop where
  timmesfeld : AsB15Part4
  determination : AsB113DetList 𝒦
  sylowCentralizer : AsLieAltSylowCentralizerList
  overgroups : AsLieAltOvergroupsList

end CFSG.QuasithinUnique.Bridge
