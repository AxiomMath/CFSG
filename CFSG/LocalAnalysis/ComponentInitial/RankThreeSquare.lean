module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.InvolutionCoverage
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open CFSG.ProperTwoGeneratedCore

variable {H : Type*} [Group H] [Finite H]

theorem square_involution_sylow_maximal_transfer (S : Sylow 2 H) (U : Subgroup H)
    (hUS : U ≤ (S : Subgroup H)) (hindex : U.relIndex (S : Subgroup H) = 2) {t x : H}
    (ht : orderOf t = 2) (hx : x ^ 2 = t) : ∃ g : H, g⁻¹ * t * g ∈ U := by
  by_contra hnone
  have hmiss : ∀ g : H, g⁻¹ * t * g ∉ U := by simpa only [not_exists] using hnone
  have hodd : Odd (S : Subgroup H).index := Nat.odd_iff.mpr (by have := S.not_dvd_index; omega)
  have hpositive : 1 ≤ (S : Subgroup H).index :=
    Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  have hUindex : U.index = 2 * (S : Subgroup H).index := by
    simpa only [hindex] using (Subgroup.relIndex_mul_index hUS).symm
  obtain ⟨sign, hsign, -⟩ :=
    coset_involution_sign_obstruction U _ hodd hpositive hUindex t ht hmiss
  rw [← hx, map_pow, Int.units_sq] at hsign
  exact absurd hsign (by decide)

theorem rank_three_square_involution_coverage (hrank : 3 ≤ CFSG.Open.twoRank H) {t : H}
    (ht : orderOf t = 2) (hsq : ∃ x : H, x ^ 2 = t) :
    ∃ E : Subgroup H, CFSG.Open.IsElemAbelian 2 E ∧ Nat.card E = 8 ∧ t ∈ E := by
  classical
  obtain ⟨x, hx⟩ := hsq
  let S : Sylow 2 H := default
  let P := (S : Subgroup H)
  have hPrank : 3 ≤ CFSG.Open.twoRank P := by
    rw [CFSG.Open.twoRank, ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup,
      (CFSG.SectionRank.pRank_sylow S).1]
    exact hrank
  obtain ⟨A, hA, hAcard⟩ := exists_elementary_eight_of_rank_three hPrank
  obtain ⟨V, hVnormal, hV, hVcard⟩ := high_two_rank_normal_four P S.isPGroup' hPrank
  have : V.Normal := hVnormal
  let C := Subgroup.centralizer (V : Set P)
  obtain ⟨-, -, hindex⟩ := normal_four_centralizer_index S.isPGroup' V hV hVcard
  change C.index ≤ 2 at hindex
  let D := C.map P.subtype
  have hDP : D ≤ P := Subgroup.map_subtype_le _
  have hrelative : D.relIndex P = C.index := by
    change ((C.map P.subtype).comap P.subtype).index = C.index
    rw [Subgroup.comap_map_eq_self_of_injective P.subtype_injective]
  have hconjugate : ∃ g : H, g⁻¹ * t * g ∈ D := by
    by_cases hCtop : C = ⊤
    · have hD : D = P := by
        change C.map P.subtype = P
        rw [hCtop, Subgroup.map_top, Subgroup.range_subtype]
      obtain ⟨g, -, hgt⟩ := involution_conjugate_into_sylow S (⊤ : Subgroup H) le_top
        t (by trivial) ht
      exact ⟨g, hD.symm ▸ hgt⟩
    · have hCindex : C.index = 2 := by
        have hpositive : 0 < C.index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
        have hnotOne : C.index ≠ 1 := fun h => hCtop (Subgroup.index_eq_one.mp h)
        omega
      exact square_involution_sylow_maximal_transfer S D hDP (hrelative.trans hCindex) ht hx
  obtain ⟨g, y, hyC, hy⟩ := hconjugate
  change (y : H) = g⁻¹ * t * g at hy
  have hyOrder : orderOf y = 2 := by
    rw [← Subgroup.orderOf_coe, hy]
    simpa only [MulAut.conj_apply, inv_inv, ht] using (MulAut.conj g⁻¹).orderOf_eq t
  obtain ⟨E, -, hE, hEcard, hyE⟩ := normal_four_centralizer_involution_coverage
    S.isPGroup' V hV hVcard A hA hAcard y hyOrder hyC
  obtain ⟨F, -, hF, hFcard, hyF⟩ := elementary_eight_coverage_lift P y ⟨E, hE, hEcard, hyE⟩
  exact elementary_eight_coverage_conjugate t g F hF hFcard (hy ▸ hyF)

theorem rank_three_square_involution_coverage_pRank (hrank : 3 ≤ CFSG.pRank 2 H) {t : H}
    (ht : orderOf t = 2) (hsq : ∃ x : H, x ^ 2 = t) :
    ∃ E : Subgroup H, CFSG.IsElementaryAbelian 2 E ∧ Nat.card E = 8 ∧ t ∈ E := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at hrank
  obtain ⟨E, hE, hcard, htE⟩ := rank_three_square_involution_coverage hrank ht hsq
  exact ⟨E, (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 E).2 hE, hcard, htE⟩

end CFSG.LocalAnalysis.ComponentInitial
