module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeAut
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeGen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeFacts

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.Blueprint CFSG.QuasithinUnique.Setup.Family

@[expose] def HeTwoRankProp : Prop :=
  ∀ B : Subgroup (MulAut (NativeSporadic.Carrier .He)), (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
    (∀ x ∈ B, x * x = 1) → Nat.card B ≤ 2 ^ 6

@[expose] def HeThreeConjProp : Prop :=
  ∀ ψ : MulAut (NativeSporadic.Carrier .He), ψ * ψ = 1 → ψ ≠ 1 →
    ∃ cs : List (MulAut (NativeSporadic.Carrier .He)), cs.length = 3 ∧
      (∀ c ∈ cs, c ∈ (MulAut.conj : NativeSporadic.Carrier .He →*
        MulAut (NativeSporadic.Carrier .He)).range) ∧
      ∀ s : NativeSporadic.Carrier .He, MulAut.conj s ∈ Subgroup.closure (conjSet cs {ψ})

theorem heTwoRankProp
    : HeTwoRankProp := he_rank

theorem heThreeConjProp
    : HeThreeConjProp := he_gen

theorem heFaithfulDimProp
    :
    ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v * v = 1) →
      ∀ σ : NativeSporadic.Carrier .He →* MulAut V, Function.Injective σ → 2 ^ 21 ≤ Nat.card V :=
  fun V _ _ hV σ hσ => he_dim V hV σ hσ

theorem he_nontrivial : Nontrivial (NativeSporadic.Carrier .He) := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have h1 : Nat.card (NativeSporadic.Carrier .He) = 1 := by
    have : Unique (NativeSporadic.Carrier .He) := uniqueOfSubsingleton 1
    exact Nat.card_unique
  have h2 : Nat.card (NativeSporadic.Carrier .He) = 4030387200 := CFSG.Sporadic.He.card_He
  omega

theorem heExclusionProp_of
    (hb : HeTwoRankProp) (hc : HeThreeConjProp)
    : HeExclusionProp := by
  have hd := heFaithfulDimProp
  intro W _ _ hW L E hperf hirr hE hEne hEel hoff ⟨e⟩
  have : Nontrivial (NativeSporadic.Carrier .He) := he_nontrivial
  have h := weight_lt_of_three_conj hW hperf hirr hE hEne hEel e (r := 6) (k := 3) (ρ := 21)
    (by norm_num) (fun E _ _ _ π hπ hC hodd => he_cover E π hπ hC hodd) hb hc hd
  omega

theorem heExclusionProp
    : HeExclusionProp :=
  heExclusionProp_of heTwoRankProp heThreeConjProp

theorem sporadicExclusion_He
    : SporadicExclusion .He :=
  sporadicExclusion_of_He heExclusionProp

end CFSG.QuasithinUnique.Setup.X1
