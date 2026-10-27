module

public import CFSG.Open.GriessG2FourRootInvolutions
public import CFSG.LieType.Steinberg.CentralExt.G2FourRootLifts

public section

namespace CFSG.LieType.Steinberg.CentralExt.G2Four

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Open Subgroup CFSG.LieType.Chevalley.G2FieldFour

theorem g2RootNormSq_le_six : ∀ δ ∈ rootFinset .G2, g2RootNormSq δ ≤ 6 := by
  decide +kernel

theorem two_le_g2RootNormSq : ∀ δ ∈ rootFinset .G2, 2 ≤ g2RootNormSq δ := by
  decide +kernel

theorem g2RootNormSq_longRoots : ∀ γ ∈ longRoots, g2RootNormSq γ = 6 := by
  decide +kernel

theorem g2RootNormSq_shortRoots : ∀ γ ∈ shortRoots, g2RootNormSq γ = 2 := by
  decide +kernel

theorem rootA_mem_longRoots : rootA ∈ longRoots := by decide +kernel

theorem rootR_mem_shortRoots : rootR ∈ shortRoots := by decide +kernel

theorem isRoot_of_mem_union {γ : Fin Tag.G2.rank → ℤ}
    (hγ : γ ∈ longRoots ∪ shortRoots) : IsRoot .G2 γ := by
  rw [longRoots_union_shortRoots] at hγ
  exact mem_rootFinset.1 hγ

theorem isG2LongRoot_iff {γ : Fin Tag.G2.rank → ℤ} :
    IsG2LongRoot γ ↔ γ ∈ longRoots := by
  constructor
  · rintro ⟨hγ, hmax⟩
    rcases mem_longRoots_or_mem_shortRoots hγ with h | h
    · exact h
    · have h1 := hmax rootA (isRoot_of_mem_union (Finset.mem_union_left _ rootA_mem_longRoots))
      rw [g2RootNormSq_longRoots _ rootA_mem_longRoots, g2RootNormSq_shortRoots _ h] at h1
      norm_num at h1
  · intro hγ
    refine ⟨isRoot_of_mem_union (Finset.mem_union_left _ hγ), fun δ hδ => ?_⟩
    rw [g2RootNormSq_longRoots _ hγ]
    exact g2RootNormSq_le_six δ (mem_rootFinset.2 hδ)

theorem isG2ShortRoot_iff {γ : Fin Tag.G2.rank → ℤ} :
    IsG2ShortRoot γ ↔ γ ∈ shortRoots := by
  constructor
  · rintro ⟨hγ, hmin⟩
    rcases mem_longRoots_or_mem_shortRoots hγ with h | h
    · have h1 := hmin rootR (isRoot_of_mem_union (Finset.mem_union_right _ rootR_mem_shortRoots))
      rw [g2RootNormSq_shortRoots _ rootR_mem_shortRoots, g2RootNormSq_longRoots _ h] at h1
      norm_num at h1
    · exact h
  · intro hγ
    refine ⟨isRoot_of_mem_union (Finset.mem_union_right _ hγ), fun δ hδ => ?_⟩
    rw [g2RootNormSq_shortRoots _ hγ]
    exact two_le_g2RootNormSq δ (mem_rootFinset.2 hδ)

theorem g2_four_root_lifts
    (L : Type) [Group L] (hL : CFSG.Open.IsQuasisimple L) (hZ : Nat.card (center L) = 2)
    (_hmodel : CFSG.Blueprint.LieModel (L ⧸ center L) .G2 0 2 2) :
    (∀ x : L, IsG2FourLongRootInvolution (x : L ⧸ center L) → orderOf x = 2) ∧
      (∀ x : L, IsG2FourShortRootInvolution (x : L ⧸ center L) → orderOf x = 4) := by
  constructor
  · rintro x ⟨K, _, _, hK, e, γ, s, h, hγ, hs, hx⟩
    exact orderOf_eq_two_of_isConj_long_of_adjointQuotient hZ hK e (isG2LongRoot_iff.1 hγ) hs hx
  · rintro x ⟨K, _, _, hK, e, γ, s, h, hγ, hs, hx⟩
    have : Finite (adjointGroup .G2 K) := Subtype.finite
    have : Finite (center L) := Nat.finite_of_card_ne_zero (by rw [hZ]; norm_num)
    have : Finite (L ⧸ center L) := Finite.of_equiv _ e.symm.toEquiv
    have : Finite L := Finite.of_subgroup_quotient (center L)
    have : Group.IsPerfect L := ⟨hL.1⟩
    exact orderOf_eq_four_of_isConj_short_of_adjointQuotient hZ hK e (isG2ShortRoot_iff.1 hγ) hs
      hx

end CFSG.LieType.Steinberg.CentralExt.G2Four
