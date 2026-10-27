module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4Fusion
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.PrimePowLog
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.AutModelPlane

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
open scoped commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem primePowOK_eleven_319440 : PrimePowOK 11 319440 := by
  refine primePow_mod_ne_one_of_check_log (by norm_num) (L := {2, 3, 5, 11})
    (by norm_num [Nat.primeFactors]) ?_
  decide +kernel

theorem centralizer_singleton_congr_zpowers {G : Type*} [Group G] {a b : G}
    (h : Subgroup.zpowers a = Subgroup.zpowers b) :
    Subgroup.centralizer ({a} : Set G) = Subgroup.centralizer ({b} : Set G) := by
  have h1 : ∀ {a b : G}, b ∈ Subgroup.zpowers a →
      Subgroup.centralizer ({a} : Set G) ≤ Subgroup.centralizer ({b} : Set G) := by
    intro a b hb g hg
    rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (Commute.zpow_right (show Commute g a from hg) n).eq
  exact le_antisymm (h1 (h ▸ Subgroup.mem_zpowers b)) (h1 (h ▸ Subgroup.mem_zpowers a))

theorem orderOf_conj_eq_of {G : Type*} [Group G] (k x : G) : orderOf (k * x * k⁻¹) = orderOf x := by
  simpa [MulAut.conj_apply] using (MulAut.conj k).orderOf_eq x

section Cen


theorem j4_card_centralizer_dvd {y : J} (hy : orderOf y = 11) :
    Nat.card (Subgroup.centralizer ({y} : Set J)) ∣ 11 ^ 3 * 240 := by
  obtain ⟨h, hh⟩ := exists_conj_mem_of_orderOf Q11 card_Q11 not_dvd_card_J hy
  set y' : J := h⁻¹ * y * h with hy'
  have hconj : h * y' * h⁻¹ = y := by rw [hy']; group
  have hcard : Nat.card (Subgroup.centralizer ({y} : Set J)) =
      Nat.card (Subgroup.centralizer ({y'} : Set J)) := by
    have := card_inf_centralizer_conj (⊤ : Subgroup J) (Subgroup.mem_top h) y'
    rw [hconj] at this
    simpa using this
  have hy'o : orderOf y' = 11 := by
    have := orderOf_conj_eq_of h⁻¹ y
    rw [inv_inv] at this
    rw [hy', this, hy]
  rw [hcard]
  by_cases hz : y' ∈ Subgroup.zpowers qz
  · have hy1 : y' ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hy'o
      exact absurd hy'o (by norm_num)
    have hzp := @zpowers_eq_of_mem_of_ne_one J (Subgroup.toGroup J) _ _ _ orderOf_qz hz hy1
    rw [centralizer_singleton_congr_zpowers hzp, ← card_normalizer_Q11]
    exact Subgroup.card_dvd_of_le centralizer_qz_le_normalizer_J4
  · obtain ⟨h1, h2⟩ := card_centralizer_noncentral_le hh hz
    obtain ⟨m, hm⟩ := h1
    rw [hm] at h2 ⊢
    have hm2 : m ≤ 2 := by omega
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · rw [h0] at hm
        exact absurd hm Nat.card_pos.ne'
      · exact h0
    interval_cases m <;> norm_num

theorem j4_rankOK_cen {y : J} (hy : orderOf y = 11) :
    RankOK 11 (Subgroup.centralizer ({y} : Set J)) :=
  rankOK_of_primePowOK (primePowOK_eleven_319440.of_dvd (j4_card_centralizer_dvd hy))

end Cen

end CFSG.HardMathSupport.Dickson.I271
