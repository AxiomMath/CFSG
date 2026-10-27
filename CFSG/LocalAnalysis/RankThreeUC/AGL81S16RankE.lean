module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16RankD

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.ClassicalGroups.Unitary Matrix
open CFSG.LieType.Universal.Unitary (SUid)

section Export

variable {F : Type} [Field F] [Finite F] {σ : F ≃+* F}

theorem exists_ne_zero_herm_eq_zero {W : Submodule F (Fin 4 → F)}
    (hW : Module.finrank F ↥W = 2) (x : Fin 4 → F) :
    ∃ w ∈ W, w ≠ 0 ∧ herm σ w x = 0 := by
  let ψ : ↥W →+ F :=
    AddMonoidHom.mk' (fun w => herm σ (w : Fin 4 → F) x) (fun a b => herm_add_left σ _ _ _)
  have hmul := AddSubgroup.card_ker_mul_card_range ψ
  have hW' : Nat.card ↥W = Nat.card F ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := F) (V := ↥W), hW]
  have hr : Nat.card ψ.range ≤ Nat.card F :=
    Nat.card_le_card_of_injective (fun y : ψ.range => (y : F)) Subtype.val_injective
  have hF : 1 < Nat.card F := Finite.one_lt_card
  have hk : 1 < Nat.card ψ.ker := by
    by_contra hle
    push_neg at hle
    have h1 : Nat.card ψ.ker * Nat.card ψ.range ≤ Nat.card F := by
      calc Nat.card ψ.ker * Nat.card ψ.range ≤ 1 * Nat.card F := Nat.mul_le_mul hle hr
        _ = Nat.card F := one_mul _
    rw [hmul, hW'] at h1
    nlinarith
  haveI : Nontrivial ↥ψ.ker := Finite.one_lt_card_iff_nontrivial.mp hk
  obtain ⟨w, hw0⟩ := exists_ne (0 : ↥ψ.ker)
  refine ⟨(w.1 : Fin 4 → F), w.1.2, fun h => hw0 ?_, w.2⟩
  exact Subtype.ext (Subtype.ext h)

theorem generation_model (hσ : IsUnitaryInvolution σ) (h2 : (2 : F) = 0) {E : Subgroup (SUid σ 4)}
    (hE2 : ∀ a ∈ E, a * a = 1) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = (2 ^ n) ^ 2) (hcard : Nat.card ↥E = 2 ^ (4 * n)) (x : Fin 4 → F) :
    ∃ a ∈ E, a ≠ 1 ∧ a • x = x := by
  obtain ⟨hu, heq, hEP⟩ := eq_PW_of_card_eq hσ h2 hE2 hEc hn hF hcard
  obtain ⟨w, hwW, hw0, hwx⟩ := exists_ne_zero_herm_eq_zero (σ := σ) hu x
  have hti : ∀ w' ∈ commSp E, herm σ w w' = 0 := by
    intro w' hw'
    have hh : w ∈ horth σ (commSp E) := by
      rw [← fixSp_eq_horth hσ hE2, ← heq]; exact hwW
    rw [herm_conj σ hσ.invol w' w, mem_horth.mp hh w' hw', map_zero]
  have hww : herm σ w w = 0 := hti w hwW
  have hc : (1 : F) + σ 1 = 0 := by rw [map_one, one_add_one_eq_two, h2]
  refine ⟨tv hσ.invol hww hc, ?_, ?_, ?_⟩
  · have hmem : tv hσ.invol hww hc ∈ PW (commSp E) := by
      refine mem_PW.mpr ⟨fun v => ?_, fun w' hw' => ?_⟩
      · rw [tv_smul, add_sub_cancel_left]
        exact (commSp E).smul_mem _ hwW
      · rw [tv_smul, hti w' hw', mul_zero, zero_smul, add_zero]
    rwa [← hEP] at hmem
  · intro h1
    obtain ⟨y, hy⟩ := exists_herm_ne_zero σ hw0
    have := congrArg (fun g : SUid σ 4 => g • y) h1
    simp only [tv_smul, one_smul, one_mul] at this
    have h3 : (herm σ w y) • w = 0 := by
      have := add_eq_left.mp this
      exact this
    rcases smul_eq_zero.mp h3 with h | h
    · exact hy h
    · exact hw0 h
  · rw [tv_smul, hwx, mul_zero, zero_smul, add_zero]

theorem ts_plane_model (hσ : IsUnitaryInvolution σ) (h2 : (2 : F) = 0) {E : Subgroup (SUid σ 4)}
    (hE2 : ∀ a ∈ E, a * a = 1) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = (2 ^ n) ^ 2) (hcard : 2 ^ (2 * n) ≤ Nat.card ↥E)
    (hts : ∀ u ∈ commSp E, herm σ u u = 0) :
    commSp E = fixSp E ∧ Nat.card ↥(commSp E) = 2 ^ (4 * n) := by
  have hu2 := two_le_finrank_commSp_of_card_ge hσ hE2 hEc hn hF hcard
  have hsum := finrank_commSp_add_finrank_fixSp hσ hE2
  have hle : commSp E ≤ fixSp E := by
    rw [fixSp_eq_horth hσ hE2]
    intro u hu
    refine mem_horth.mpr fun u' hu' => ?_
    exact herm_eq_zero_of_forall_isotropic hσ (S := commSp E) hts hu' hu
  have hfr := Submodule.finrank_mono hle
  have hu : Module.finrank F ↥(commSp E) = 2 := by omega
  refine ⟨Submodule.eq_of_le_of_finrank_eq hle (by omega), ?_⟩
  rw [Module.natCard_eq_pow_finrank (K := F) (V := ↥(commSp E)), hu, hF]
  ring

end Export

end CFSG.LocalAnalysis.RankThreeUC
