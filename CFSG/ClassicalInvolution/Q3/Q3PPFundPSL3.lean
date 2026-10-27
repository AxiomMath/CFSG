module

public import CFSG.ClassicalInvolution.Q3.Q3PPFundAbs
public import CFSG.ClassicalInvolution.Q3.Q3PPFundGam
public import CFSG.ClassicalInvolution.Q3.Q3TSetup
public import CFSG.LocalAnalysis.ComponentInitial.LinearModelOuterTwoPart

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3PP

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3NM
  CFSG.ClassicalInvolution.Balance
open scoped MatrixGroups

theorem natCard_gf3 : Nat.card (GaloisField 3 1) = 3 := by
  rw [GaloisField.card 3 1 (by norm_num)]
  norm_num

section SL3

variable {F : Type} [Field F]

theorem orderOf_rootInv₃ (h2 : (2 : F) ≠ 0) : orderOf (rootInv₃ F) = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact rootInv₃_mul_self) (rootInv₃_ne_one h2)

theorem eq_one_or_conj_of_fixes_conjSub [Finite F] (hF : Nat.card F = 3) (hout : OutOne SL(3, F))
    {ρ : MulAut SL(3, F)} (hρ2 : ρ * ρ = 1) {g₀ : SL(3, F)}
    (hρR : ∀ r ∈ conjSub g₀ (rootSL2₃ F), ρ r = r) :
    ρ = 1 ∨ ∃ s : SL(3, F), s * s = 1 ∧ s ≠ 1 ∧ ρ = MulAut.conj s := by
  have hZ := center_sl3_eq_bot hF
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_natCard (by rw [hF]; decide)
  obtain ⟨c, hc⟩ : ∃ c : MulAut SL(3, F), c = MulAut.conj g₀ := ⟨_, rfl⟩
  have hcr : ∀ x, c x = g₀ * x * g₀⁻¹ := fun x => by rw [hc]; rfl
  obtain ⟨ρ', hρ'⟩ : ∃ ρ' : MulAut SL(3, F), ρ' = c⁻¹ * ρ * c := ⟨_, rfl⟩
  have hρ'R : ∀ r ∈ rootSL2₃ F, ρ' r = r := by
    intro r hr
    have h1 : ρ (c r) = c r := by rw [hcr]; exact hρR _ (conj_mem_conjSub hr)
    rw [hρ']
    show c⁻¹ (ρ (c r)) = r
    rw [h1]
    exact MulAut.inv_apply_self _ c r
  have hρ'2 : ρ' * ρ' = 1 := by
    calc ρ' * ρ' = c⁻¹ * (ρ * ρ) * c := by rw [hρ']; group
      _ = 1 := by rw [hρ2]; group
  have hk := eq_one_or_conj_of_invol hZ hout (R := rootSL2₃ F) (t := rootInv₃ F)
    rootInv₃_mul_self (rootInv₃_ne_one h2)
    (fun g hg hg2 => eq_one_or_rootInv_of_commutes hg hg2) (gam' F)
    (fun r hr => gam'_apply_of_mem_rootSL2 hr) gam'_sq
    (fun g hg => gam'_eq_inv_of_commutes hg) ρ' hρ'2 hρ'R
  have hρ : ρ = c * ρ' * c⁻¹ := by rw [hρ']; group
  rcases hk with h | h
  · left
    rw [hρ, h, mul_one, mul_inv_cancel]
  · right
    refine ⟨g₀ * rootInv₃ F * g₀⁻¹, ?_, ?_, ?_⟩
    · calc g₀ * rootInv₃ F * g₀⁻¹ * (g₀ * rootInv₃ F * g₀⁻¹)
          = g₀ * (rootInv₃ F * rootInv₃ F) * g₀⁻¹ := by group
        _ = 1 := by rw [rootInv₃_mul_self]; group
    · intro h1
      apply rootInv₃_ne_one h2
      calc rootInv₃ F = g₀⁻¹ * (g₀ * rootInv₃ F * g₀⁻¹) * g₀ := by group
        _ = 1 := by rw [h1]; group
    · rw [hρ, h, hc, map_mul, map_mul, map_inv]

end SL3

theorem outOne_sl3_gf3 : OutOne SL(3, GaloisField 3 1) := by
  have hF : Nat.card (GaloisField 3 1) = 3 := natCard_gf3
  have hZ := center_sl3_eq_bot hF
  have hinj : Function.Injective
      (QuotientGroup.mk' (Subgroup.center SL(3, GaloisField 3 1))) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hZ]
  let e : SL(3, GaloisField 3 1) ≃* (SL(3, GaloisField 3 1) ⧸
      Subgroup.center SL(3, GaloisField 3 1)) :=
    MulEquiv.ofBijective (QuotientGroup.mk' _) ⟨hinj, QuotientGroup.mk'_surjective _⟩
  have hadm : StatedLieAdmissible .PSL 3 3 1 :=
    ⟨Nat.prime_three, le_rfl, by norm_num, by decide, by decide⟩
  have hT : StatedClassicalModel SL(3, GaloisField 3 1) .PSL 3 3 1 :=
    ⟨hadm, GaloisField 3 1, inferInstance, inferInstance, by rw [hF, pow_one],
      ⟨e.trans (projectiveSpecialLinearGroupEquivStatedProj 3 (GaloisField 3 1))⟩⟩
  have hout := (CFSG.LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound
    SL(3, GaloisField 3 1) 3 3 1 hT).2.2.2.2 (by norm_num)
  refine OutOne.of_card_dvd_two (hout.trans ?_)
  norm_num

theorem oddCoreIn_fixed_eq_bot_of_model {t : StatedLieTag} {n : ℕ} (hFT : IsFundTag t)
    (hadm : StatedLieAdmissible t n 3 1) {ρ : MulAut (modelUniv t n 3 1 Nat.prime_three).K}
    (hρ : ρ = 1 ∨ ∃ s : (modelUniv t n 3 1 Nat.prime_three).K, orderOf s = 2 ∧
      ρ = MulAut.conj s)
    (hinv : ∃ x : (modelUniv t n 3 1 Nat.prime_three).K, orderOf x = 2) :
    oddCoreIn (fixedSubgroup ρ) = ⊥ := by
  have hfin : Finite (modelUniv t n 3 1 Nat.prime_three).K :=
    ModelFacts.finite_modelUniv (by norm_num) Nat.prime_three hFT hadm
  have hKq := (ModelFacts.modelClauseZero t n 3 1 Nat.prime_three hFT hadm).1
  rcases hρ with rfl | ⟨s, hs, rfl⟩
  · rw [fixedSubgroup_one_eq_top]
    exact oddCoreIn_top_eq_bot_of_isQuasisimple hKq
      (modelFiniteCenterTwoGroup3 t n Nat.prime_three hFT hadm).2 hinv
  · rw [fixedSubgroup_conj_eq]
    exact modelOddCentralizerFree3_proved t n Nat.prime_three hFT hadm _ (MonoidHom.id _)
      Function.surjective_id (by simp) s hs

theorem fixedOddFreeFund_psl3 : FixedOddFreeFund (CompData.model .PSL 3) := by
  have hF : Nat.card (GaloisField 3 1) = 3 := natCard_gf3
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_of_odd_natCard (by rw [hF]; decide)
  have hadm : StatedLieAdmissible .PSL 3 3 1 :=
    ⟨Nat.prime_three, le_rfl, by norm_num, by decide, by decide⟩
  have hZ : Subgroup.center (CompData.model .PSL 3).G = ⊥ := center_sl3_eq_bot hF
  refine fixedOddFreeFund_of_center_eq_bot hZ ?_
  intro ρ hρ2 ⟨R, hR, hρR⟩
  have hRl : R ∈ longRootSet (K := GaloisField 3 1) (by norm_num : 2 ≤ 3) :=
    RouteD.fundamentalSubgroups_psl_subset (m := 2) (F := GaloisField 3 1) (by norm_num) hR
  obtain ⟨g₀, rfl⟩ := (mem_longRootSet_iff (K := GaloisField 3 1) (n := 3) (by norm_num)).mp hRl
  rcases eq_one_or_conj_of_fixes_conjSub hF outOne_sl3_gf3 hρ2 (g₀ := g₀) hρR with
    h | ⟨s, hs2, hs1, hs⟩
  · exact oddCoreIn_fixed_eq_bot_of_model (t := .PSL) (n := 3) trivial hadm (Or.inl h)
      ⟨rootInv₃ (GaloisField 3 1), orderOf_rootInv₃ h2⟩
  · have hs' : orderOf s = 2 := orderOf_eq_prime (by rw [pow_two]; exact hs2) hs1
    exact oddCoreIn_fixed_eq_bot_of_model (t := .PSL) (n := 3) trivial hadm
      (Or.inr ⟨s, hs', hs⟩) ⟨rootInv₃ (GaloisField 3 1), orderOf_rootInv₃ h2⟩

end CFSG.ClassicalInvolution.Q3.Q3PP
