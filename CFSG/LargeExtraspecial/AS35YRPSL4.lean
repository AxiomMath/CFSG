module

public import CFSG.LargeExtraspecial.AS35YRSet
public import CFSG.LargeExtraspecial.AS35YLMLin

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.Blueprint AS35YR

namespace S14

theorem asc512PSL4WidthThreeStmt : Asc512PSL4WidthThreeStmt := by
  intro G _ _ S hS hst hnd hL _ hw
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  have hc := Setting.center_LbarAsc_eq_bot_YL hS hst hnd
  have hLcard : Nat.card S.LbarAsc = 20160 := by
    have h1 := (CFSG.Timmesfeld.card_statedClassicalModel_two
      (CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hL)).1 rfl
    rw [← Nat.card_congr (AS35YL.quotEquiv_YL S.LbarAsc hc).toEquiv, h1]
    decide
  have hdim : finrank (ZMod 2) S.Qt = 2 * (2 + 1) := by rw [S.finrank_Qt_eq_two_mul_width, hw]
  have hdvd : 20160 ∣ Nat.card S.O := hLcard ▸ Subgroup.card_subgroup_dvd_card S.LbarAsc
  have h2 : (Nat.card (ZMod 2) : ℤ) = 2 := by rw [Nat.card_zmod]; rfl
  have hOcard : Nat.card S.O = 40320 := by
    by_cases hp : CFSG.GroupTheory.WeirSylow.IsPlusType S.q
    · have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type S.q_nondegenerate hdim
        (ε := 1) (Or.inl ⟨rfl, hp⟩)
      rw [h2] at h
      generalize Nat.card S.O = N at h hdvd ⊢
      norm_num [Finset.prod_Icc_succ_top] at h
      omega
    · have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type S.q_nondegenerate hdim
        (ε := -1) (Or.inr ⟨rfl, hp⟩)
      rw [h2] at h
      generalize Nat.card S.O = N at h hdvd ⊢
      norm_num [Finset.prod_Icc_succ_top] at h
      omega
  have hidx : Nat.card S.LbarAsc * 2 = Nat.card S.O := by rw [hLcard, hOcard]
  have : Nontrivial (S.LbarAsc ⧸ center S.LbarAsc) := AS35YL.nontrivial_of_inspNondeg_YL hnd
  obtain ⟨t₀, ht₀⟩ := Setting.DbarAsc_nonempty_YL (S := S)
  obtain ⟨t, ht, htM, rfl⟩ := ht₀
  obtain ⟨g, rfl⟩ := isConj_iff.mp (S.isConj_of_mem_ESet ht.1)
  obtain ⟨F, hFℓ, hFt⟩ := Setting.exists_frame_YR hS ht htM
  have hrad := Setting.radHyp_YR hS hidx ht htM F hFℓ hFt
  have : Finite (S.Qt ≃ₗ[ZMod 2] S.Qt) := finite_linearEquiv_YR
  have hcard : Nat.card (S.PbarL_YR g) = 8 := by
    rw [Setting.card_PbarL_YR hS ht htM, hw]
    norm_num
  exact hrad.false_of_card_eq_eight hcard

end S14

end CFSG.LargeExtraspecial
