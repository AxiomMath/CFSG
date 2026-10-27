module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec2Defs
public import CFSG.HardMathSupport.Solomon.Coordinator.T112MOrder
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree
public import CFSG.Quasithin.Background.GoldschmidtListedSolv
public import CFSG.ClassicalInvolution.PerfectCase.Basic
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThreeSU

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem map_center_mulEquiv {K K' : Type*} [Group K] [Group K'] (e : K ≃* K') :
    (Subgroup.center K).map e.toMonoidHom = Subgroup.center K' := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff] at hy
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g, rfl⟩ := e.surjective g
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hy g]
  · intro hx
    refine ⟨e.symm x, ?_, by simp⟩
    rw [Subgroup.mem_center_iff] at hx
    show e.symm x ∈ Subgroup.center K
    rw [Subgroup.mem_center_iff]
    intro g
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hx (e g)

theorem card_quotient_center_mul {K : Type*} [Group K] [Finite K] :
    Nat.card (K ⧸ Subgroup.center K) * Nat.card (Subgroup.center K) = Nat.card K :=
  (Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center K)).symm

theorem card_statedSU_three_of_card {F : Type} [Field F] [Finite F] {q : ℕ}
    (hK : Nat.card F = q ^ 2) :
    Nat.card ↥(StatedSU 3 q F) = q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) :=
  CFSG.SectionRank.OddCover.card_statedSU_three_of_card_eq_sq hK

theorem exc_facts_SL {K : Type} [Group K] [Finite K] {F : Type} [Field F] [Finite F]
    (hq9 : Nat.card F % 9 = 4 ∨ Nat.card F % 9 = 7) (e : K ≃* ↥(StatedSL 3 F)) :
    20160 ≤ Nat.card (K ⧸ Subgroup.center K) ∧
      (Nat.card (K ⧸ Subgroup.center K)).factorization 3 = 2 ∧
      (Nat.card (K ⧸ Subgroup.center K) = 20160 →
        ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
          Nonempty ((K ⧸ Subgroup.center K) ≃* projectiveSL 3 F)) := by
  set q := Nat.card F with hqdef
  have hq4 : 4 ≤ q := by omega
  have hZ : Nat.card (Subgroup.center K) = 3 := by
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact CFSG.Quasithin.Vol2.Ch11.SecA.C10KG.card_center_statedSL_three (by omega)
  have hN : Nat.card K = q ^ 3 * (q ^ 3 - 1) * (q ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv, CFSG.SectionRank.OddCover.card_statedSL_three,
      Nat.mul_right_comm]
  have hL := card_quotient_center_mul (K := K)
  rw [hZ, hN] at hL
  set L := Nat.card (K ⧸ Subgroup.center K) with hLdef
  have h64 : 64 ≤ q ^ 3 := by
    calc 64 = 4 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq4 3
  have h63 : 63 ≤ q ^ 3 - 1 := by omega
  have h15 : 15 ≤ q ^ 2 - 1 := by
    have : 16 ≤ q ^ 2 := by
      calc 16 = 4 ^ 2 := by norm_num
        _ ≤ q ^ 2 := Nat.pow_le_pow_left hq4 2
    omega
  have hbound : 64 * 63 * 15 ≤ q ^ 3 * (q ^ 3 - 1) * (q ^ 2 - 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul h64 h63) h15
  refine ⟨by omega, ?_, fun hL20 => ?_⟩
  · have h3 := t112m_factorization_SL hq9
    have hL0 : L ≠ 0 := by
      intro h0
      rw [h0] at hL
      omega
    have := Nat.factorization_mul hL0 (show (3 : ℕ) ≠ 0 by norm_num)
    rw [hL] at this
    have h4 := congrArg (fun f : ℕ →₀ ℕ => f 3) this
    simp only [Finsupp.add_apply] at h4
    have h33 : (3 : ℕ).factorization 3 = 1 := Nat.Prime.factorization_self Nat.prime_three
    omega
  · have hq4' : q = 4 := by
      by_contra hne
      have hq5 : 5 ≤ q := by omega
      have h125 : 125 ≤ q ^ 3 := by
        calc 125 = 5 ^ 3 := by norm_num
          _ ≤ q ^ 3 := Nat.pow_le_pow_left hq5 3
      have h124 : 124 ≤ q ^ 3 - 1 := by omega
      have h24 : 24 ≤ q ^ 2 - 1 := by
        have : 25 ≤ q ^ 2 := by
          calc 25 = 5 ^ 2 := by norm_num
            _ ≤ q ^ 2 := Nat.pow_le_pow_left hq5 2
        omega
      have := Nat.mul_le_mul (Nat.mul_le_mul h125 h124) h24
      omega
    refine ⟨F, inferInstance, inferInstance, hq4', ?_⟩
    let e' : K ≃* Matrix.SpecialLinearGroup (Fin 3) F :=
      e.trans (specialLinearGroupEquivStatedSL 3 F).symm
    exact ⟨(QuotientGroup.congr (Subgroup.center K)
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F)) e'
      (map_center_mulEquiv e')).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3
        F)⟩

theorem exc_facts_SU {K : Type} [Group K] [Finite K] (hq : CFSG.Open.IsQuasisimple K)
    {F : Type} [Field F] [Finite F] {q : ℕ} (hFq : Nat.card F = q ^ 2)
    (hq9 : q % 9 = 2 ∨ q % 9 = 5) (e : K ≃* ↥(StatedSU 3 q F)) :
    20160 ≤ Nat.card (K ⧸ Subgroup.center K) ∧
      (Nat.card (K ⧸ Subgroup.center K)).factorization 3 = 2 ∧
      Nat.card (K ⧸ Subgroup.center K) ≠ 20160 := by
  have hq2 : q ≠ 2 := by
    rintro rfl
    have hs : Group.IsSolvable ↥(StatedSU 3 (2 ^ 1) F) :=
      CFSG.Quasithin.isSolvable_statedSU_one (by simpa using hFq)
    exact CFSG.ClassicalInvolution.not_isSolvable_of_open_isQuasisimple hq
      (Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective)
  have hq5 : 5 ≤ q := by omega
  have hZ : Nat.card (Subgroup.center K) = 3 := by
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact CFSG.Quasithin.Vol2.Ch11.SecA.C10KG.card_center_statedSU_three hFq (by omega)
  have hN : Nat.card K = q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) := by
    rw [Nat.card_congr e.toEquiv, card_statedSU_three_of_card hFq]
  have hL := card_quotient_center_mul (K := K)
  rw [hZ, hN] at hL
  set L := Nat.card (K ⧸ Subgroup.center K) with hLdef
  have h125 : 125 ≤ q ^ 3 := by
    calc 125 = 5 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq5 3
  have h24 : 24 ≤ q ^ 2 - 1 := by
    have : 25 ≤ q ^ 2 := by
      calc 25 = 5 ^ 2 := by norm_num
        _ ≤ q ^ 2 := Nat.pow_le_pow_left hq5 2
    omega
  have hbound : 125 * 24 * 126 ≤ q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul h125 h24) (by omega)
  refine ⟨by omega, ?_, by omega⟩
  have h3 := t112m_factorization_SU hq9
  have hL0 : L ≠ 0 := by
    intro h0
    rw [h0] at hL
    omega
  have := Nat.factorization_mul hL0 (show (3 : ℕ) ≠ 0 by norm_num)
  rw [hL] at this
  have h4 := congrArg (fun f : ℕ →₀ ℕ => f 3) this
  simp only [Finsupp.add_apply] at h4
  have h33 : (3 : ℕ).factorization 3 = 1 := Nat.Prime.factorization_self Nat.prime_three
  omega

theorem exc_facts {K : Type} [Group K] [Finite K] (hq : CFSG.Open.IsQuasisimple K)
    (h : IsSLThreeExc K ∨ IsSUThreeExc K) :
    20160 ≤ Nat.card (K ⧸ Subgroup.center K) ∧
      (Nat.card (K ⧸ Subgroup.center K)).factorization 3 = 2 ∧
      (Nat.card (K ⧸ Subgroup.center K) = 20160 →
        ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
          Nonempty ((K ⧸ Subgroup.center K) ≃* projectiveSL 3 F)) := by
  rcases h with ⟨F, hF, hfin, hq9, ⟨e⟩⟩ | ⟨F, hF, hfin, q, hFq, hq9, ⟨e⟩⟩
  · exact exc_facts_SL hq9 e
  · obtain ⟨h1, h2, h3⟩ := exc_facts_SU hq hFq hq9 e
    exact ⟨h1, h2, fun h4 => (h3 h4).elim⟩

end CFSG.HardMathSupport.Solomon.Coordinator
