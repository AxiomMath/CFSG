module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L129JF4

@[expose] public section

namespace CFSG.OddStandard.SmallF3.Omega

open Matrix

abbrev Sec12SL : Type := SpecialLinearGroup (Fin 2) Sec12F4

theorem sec12F4_card_sl : Nat.card Sec12SL = 60 := by
  have h1 : Nat.card Sec12SL = Nat.card {M : Sec12M // M.det = 1} := Nat.card_congr (Equiv.refl _)
  rw [h1, Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact sec12_sl_fin

theorem sec12F4_conj (A : Sec12SL) :
    ∃ g : Sec12SL, ∃ R ∈ sec12Reps, (g : Sec12M) * (A : Sec12M) = R * (g : Sec12M) := by
  obtain ⟨g, hg, R, hR, h⟩ := sec12_conj_fin (A : Sec12M) A.2
  exact ⟨⟨g, hg⟩, R, hR, h⟩

theorem sec12SL_cancel_left (g : Sec12SL) {X Y : Sec12M} (h : (g : Sec12M) * X = (g : Sec12M) * Y) :
    X = Y := by
  have hg : ((g⁻¹ : Sec12SL) : Sec12M) * (g : Sec12M) = 1 := by
    rw [← SpecialLinearGroup.coe_mul, inv_mul_cancel, SpecialLinearGroup.coe_one]
  calc X = (((g⁻¹ : Sec12SL) : Sec12M) * (g : Sec12M)) * X := by rw [hg, one_mul]
    _ = ((g⁻¹ : Sec12SL) : Sec12M) * ((g : Sec12M) * X) := by rw [Matrix.mul_assoc]
    _ = ((g⁻¹ : Sec12SL) : Sec12M) * ((g : Sec12M) * Y) := by rw [h]
    _ = (((g⁻¹ : Sec12SL) : Sec12M) * (g : Sec12M)) * Y := by rw [Matrix.mul_assoc]
    _ = Y := by rw [hg, one_mul]

theorem sec12SL_cancel_right (k : Sec12SL) {X Y : Sec12M}
    (h : X * (k : Sec12M)ᵀ = Y * (k : Sec12M)ᵀ) : X = Y := by
  have hk : (k : Sec12M)ᵀ * ((k⁻¹ : Sec12SL) : Sec12M)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← SpecialLinearGroup.coe_mul, inv_mul_cancel,
      SpecialLinearGroup.coe_one, Matrix.transpose_one]
  calc X = X * ((k : Sec12M)ᵀ * ((k⁻¹ : Sec12SL) : Sec12M)ᵀ) := by rw [hk, mul_one]
    _ = (X * (k : Sec12M)ᵀ) * ((k⁻¹ : Sec12SL) : Sec12M)ᵀ := by rw [Matrix.mul_assoc]
    _ = (Y * (k : Sec12M)ᵀ) * ((k⁻¹ : Sec12SL) : Sec12M)ᵀ := by rw [h]
    _ = Y * ((k : Sec12M)ᵀ * ((k⁻¹ : Sec12SL) : Sec12M)ᵀ) := by rw [Matrix.mul_assoc]
    _ = Y := by rw [hk, mul_one]

theorem sec12SL_eq_one_of_conj (g A : Sec12SL)
    (h : (g : Sec12M) * (A : Sec12M) = 1 * (g : Sec12M)) : A = 1 := by
  apply Subtype.ext
  apply sec12SL_cancel_left g
  rw [h, one_mul, SpecialLinearGroup.coe_one, mul_one]

private theorem sec12F4_fix_inj (A B g k : Sec12SL) {R R' : Sec12M}
    (hg : (g : Sec12M) * (A : Sec12M) = R * (g : Sec12M))
    (hk : (k : Sec12M) * (B : Sec12M) = R' * (k : Sec12M)) :
    ∃ f : {M : Sec12M // (A : Sec12M) * M * (B : Sec12M)ᵀ = M} →
        {M : Sec12M // R * M * R'ᵀ = M}, Function.Injective f := by
  have key : ∀ M : Sec12M, R * ((g : Sec12M) * M * (k : Sec12M)ᵀ) * R'ᵀ =
      (g : Sec12M) * ((A : Sec12M) * M * (B : Sec12M)ᵀ) * (k : Sec12M)ᵀ := by
    intro M
    calc R * ((g : Sec12M) * M * (k : Sec12M)ᵀ) * R'ᵀ
        = (R * (g : Sec12M)) * M * ((k : Sec12M)ᵀ * R'ᵀ) := by simp only [Matrix.mul_assoc]
      _ = ((g : Sec12M) * (A : Sec12M)) * M * (R' * (k : Sec12M))ᵀ := by
          rw [← hg, Matrix.transpose_mul]
      _ = ((g : Sec12M) * (A : Sec12M)) * M * ((k : Sec12M) * (B : Sec12M))ᵀ := by rw [hk]
      _ = (g : Sec12M) * ((A : Sec12M) * M * (B : Sec12M)ᵀ) * (k : Sec12M)ᵀ := by
          rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
  refine ⟨fun M => ⟨(g : Sec12M) * M.1 * (k : Sec12M)ᵀ, ?_⟩, ?_⟩
  · rw [key, M.2]
  · intro M M' h
    apply Subtype.ext
    have h1 := congrArg Subtype.val h
    simp only at h1
    exact sec12SL_cancel_left g (sec12SL_cancel_right k h1)

theorem sec12F4_fix_le (A B : Sec12SL) (h : A ≠ 1 ∨ B ≠ 1) :
    Nat.card {M : Sec12M // (A : Sec12M) * M * (B : Sec12M)ᵀ = M} ≤ 16 := by
  obtain ⟨g, R, hR, hg⟩ := sec12F4_conj A
  obtain ⟨k, R', hR', hk⟩ := sec12F4_conj B
  have hne : R ≠ 1 ∨ R' ≠ 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    subst h1
    subst h2
    rcases h with h | h
    · exact h (sec12SL_eq_one_of_conj g A hg)
    · exact h (sec12SL_eq_one_of_conj k B hk)
  obtain ⟨f, hf⟩ := sec12F4_fix_inj A B g k hg hk
  calc Nat.card {M : Sec12M // (A : Sec12M) * M * (B : Sec12M)ᵀ = M}
      ≤ Nat.card {M : Sec12M // R * M * R'ᵀ = M} := Nat.card_le_card_of_injective f hf
    _ = (Finset.univ.filter (fun M : Sec12M => R * M * R'ᵀ = M)).card := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    _ ≤ 16 := sec12_fix_fin R hR R' hR' hne

private theorem sec12F4_fix2_inj (A B g k : Sec12SL) {R R' : Sec12M}
    (hg : (g : Sec12M) * (A : Sec12M) = R * (g : Sec12M))
    (hk : (k : Sec12M) * (B : Sec12M) = R' * (k : Sec12M)) :
    ∃ f : {M : Sec12M // (A : Sec12M) * M = M ∧ M * (B : Sec12M)ᵀ = M} →
        {M : Sec12M // R * M = M ∧ M * R'ᵀ = M}, Function.Injective f := by
  have key1 : ∀ M : Sec12M, R * ((g : Sec12M) * M * (k : Sec12M)ᵀ) =
      (g : Sec12M) * ((A : Sec12M) * M) * (k : Sec12M)ᵀ := by
    intro M
    calc R * ((g : Sec12M) * M * (k : Sec12M)ᵀ) = (R * (g : Sec12M)) * M * (k : Sec12M)ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = ((g : Sec12M) * (A : Sec12M)) * M * (k : Sec12M)ᵀ := by rw [← hg]
      _ = (g : Sec12M) * ((A : Sec12M) * M) * (k : Sec12M)ᵀ := by simp only [Matrix.mul_assoc]
  have key2 : ∀ M : Sec12M, ((g : Sec12M) * M * (k : Sec12M)ᵀ) * R'ᵀ =
      (g : Sec12M) * (M * (B : Sec12M)ᵀ) * (k : Sec12M)ᵀ := by
    intro M
    calc ((g : Sec12M) * M * (k : Sec12M)ᵀ) * R'ᵀ
        = (g : Sec12M) * M * ((k : Sec12M)ᵀ * R'ᵀ) := by simp only [Matrix.mul_assoc]
      _ = (g : Sec12M) * M * (R' * (k : Sec12M))ᵀ := by rw [Matrix.transpose_mul]
      _ = (g : Sec12M) * M * ((k : Sec12M) * (B : Sec12M))ᵀ := by rw [hk]
      _ = (g : Sec12M) * (M * (B : Sec12M)ᵀ) * (k : Sec12M)ᵀ := by
          rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
  refine ⟨fun M => ⟨(g : Sec12M) * M.1 * (k : Sec12M)ᵀ, ?_, ?_⟩, ?_⟩
  · rw [key1, M.2.1]
  · rw [key2, M.2.2]
  · intro M M' h
    apply Subtype.ext
    have h1 := congrArg Subtype.val h
    simp only at h1
    exact sec12SL_cancel_left g (sec12SL_cancel_right k h1)

theorem sec12F4_fix2_le (A B : Sec12SL) (hA : A ≠ 1) (hB : B ≠ 1) :
    Nat.card {M : Sec12M // (A : Sec12M) * M = M ∧ M * (B : Sec12M)ᵀ = M} ≤ 4 := by
  obtain ⟨g, R, hR, hg⟩ := sec12F4_conj A
  obtain ⟨k, R', hR', hk⟩ := sec12F4_conj B
  have hne : R ≠ 1 := by
    rintro rfl
    exact hA (sec12SL_eq_one_of_conj g A hg)
  have hne' : R' ≠ 1 := by
    rintro rfl
    exact hB (sec12SL_eq_one_of_conj k B hk)
  obtain ⟨f, hf⟩ := sec12F4_fix2_inj A B g k hg hk
  calc Nat.card {M : Sec12M // (A : Sec12M) * M = M ∧ M * (B : Sec12M)ᵀ = M}
      ≤ Nat.card {M : Sec12M // R * M = M ∧ M * R'ᵀ = M} := Nat.card_le_card_of_injective f hf
    _ = (Finset.univ.filter (fun M : Sec12M => R * M = M ∧ M * R'ᵀ = M)).card := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    _ ≤ 4 := sec12_fix2_fin R hR R' hR' hne hne'

theorem sec12F4_cent_card (A : Sec12SL) (hA : A * A = 1) :
    Nat.card (Subgroup.centralizer ({A} : Set Sec12SL)) = 60 ∨
      Nat.card (Subgroup.centralizer ({A} : Set Sec12SL)) = 4 := by
  have hAA : (A : Sec12M) * (A : Sec12M) = 1 := by
    rw [← SpecialLinearGroup.coe_mul, hA, SpecialLinearGroup.coe_one]
  let e : ↥(Subgroup.centralizer ({A} : Set Sec12SL)) ≃
      {B : Sec12M // B.det = 1 ∧ B * (A : Sec12M) = (A : Sec12M) * B} :=
    { toFun := fun B => ⟨(B.1 : Sec12M), B.1.2, by
        have h := Subgroup.mem_centralizer_singleton_iff.mp B.2
        exact congrArg Subtype.val h⟩
      invFun := fun B => ⟨⟨B.1, B.2.1⟩, by
        refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
        exact Subtype.ext B.2.2⟩
      left_inv := fun B => rfl
      right_inv := fun B => rfl }
  have hcard : Nat.card (Subgroup.centralizer ({A} : Set Sec12SL)) =
      (Finset.univ.filter
        (fun B : Sec12M => B.det = 1 ∧ B * (A : Sec12M) = (A : Sec12M) * B)).card := by
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hcard]
  exact sec12_cent_fin (A : Sec12M) A.2 hAA

theorem sec12U_det : (!![1, 1; 0, 1] : Sec12M).det = 1 := by
  rw [Matrix.det_fin_two_of]
  simp

theorem sec12Lo_det : (!![1, 0; 1, 1] : Sec12M).det = 1 := by
  rw [Matrix.det_fin_two_of]
  simp

def sec12U : Sec12SL := ⟨!![1, 1; 0, 1], sec12U_det⟩

def sec12Lo : Sec12SL := ⟨!![1, 0; 1, 1], sec12Lo_det⟩

theorem sec12F4_gen_fin : ∀ M : Sec12M, (sec12U : Sec12M) * M = M → (sec12Lo : Sec12M) * M = M →
    M = 0 := by
  decide +kernel

end CFSG.OddStandard.SmallF3.Omega
