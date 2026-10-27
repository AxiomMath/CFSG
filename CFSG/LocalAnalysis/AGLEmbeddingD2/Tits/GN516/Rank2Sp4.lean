module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.QuasisimpleTwoNonab
public import CFSG.LieType.Universal.Symplectic
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFourSylow

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFour

variable (F : Type) [Field F] [Finite F] [CharP F 2]

theorem sp4_nonab_two : ∃ Q : Subgroup (StatedSp 2 F),
    IsPGroup 2 Q ∧ ∃ a ∈ Q, ∃ b ∈ Q, a * b ≠ b * a := by
  have := Fintype.ofFinite F
  obtain ⟨k, hp, hk⟩ := FiniteField.card F 2
  refine ⟨unipotent 2 F, ?_, lam (1 : F), lam_mem_unipotent 1,
    tau (C := sym2 (0 : F) 0 1) (sym2_transpose 0 0 1), tau_mem_unipotent _, ?_⟩
  · refine IsPGroup.of_card (n := k * 2 ^ 2) ?_
    rw [card_unipotent, Nat.card_eq_fintype_card, hk, pow_mul]
  · intro h
    have h1 : lam (1 : F) * tau (C := sym2 (0 : F) 0 1) (sym2_transpose 0 0 1) * (lam (1 : F))⁻¹ =
        tau (C := sym2 (0 : F) 0 1) (sym2_transpose 0 0 1) := by
      rw [h, mul_assoc, mul_inv_cancel, mul_one]
    rw [lam_mul_tau_mul_inv] at h1
    have h2 := tau_injective _ _ h1
    have := congrFun (congrFun h2 0) 0
    simp [unitri, sym2, Matrix.mul_apply, Fin.sum_univ_two] at this


theorem sp4_center_eq_bot : Subgroup.center (StatedSp 2 F) = ⊥ := by
  rw [CFSG.LieType.Universal.Symplectic.center_eq]
  exact CFSG.Timmesfeld.ClassicalOrders.statedScalars_subgroupOf_statedSp_eq_bot 2

theorem sp4_card_quot : Nat.card (StatedSp 2 F ⧸ Subgroup.center (StatedSp 2 F)) =
    Nat.card F ^ 4 * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 4 - 1)) := by
  rw [Nat.card_congr (CFSG.LieType.Universal.Symplectic.centerQuotientEquiv 2 F).toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSp_of_charTwo,
    show Finset.Icc 1 2 = {1, 2} by rfl, Finset.prod_pair (by norm_num)]
  norm_num

theorem isQuasisimpleTwoNonab_sp4 (hq : 4 ≤ Nat.card F) :
    IsQuasisimpleTwoNonab (StatedSp 2 F) := by
  obtain ⟨hperf, hsimple, -⟩ := CFSG.LieType.Universal.Symplectic.isQuasisimple 2 F (by norm_num)
    (Or.inl (Or.inr hq))
  refine ⟨hperf.commutator_eq_top, hsimple, ?_, ?_, sp4_nonab_two F⟩
  · rw [sp4_card_quot]
    have h1 : 1 ≤ Nat.card F ^ 2 - 1 := by
      have : 16 ≤ Nat.card F ^ 2 := by nlinarith
      omega
    have h2 : 1 ≤ Nat.card F ^ 4 - 1 := by
      have : 256 ≤ Nat.card F ^ 4 := by nlinarith [Nat.pow_le_pow_left hq 4]
      omega
    have h3 : 256 ≤ Nat.card F ^ 4 := by
      calc 256 = 4 ^ 4 := by norm_num
        _ ≤ Nat.card F ^ 4 := Nat.pow_le_pow_left hq 4
    have h4 : Nat.card F ^ 4 * (1 * 1) ≤
        Nat.card F ^ 4 * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 4 - 1)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul h1 h2)
    simp only [mul_one] at h4
    omega
  · intro z hz
    rw [sp4_center_eq_bot, Subgroup.mem_bot] at hz
    rw [hz, orderOf_one]
    exact odd_one

end CFSG.AGLEmbeddingD2.Tits.GN516
