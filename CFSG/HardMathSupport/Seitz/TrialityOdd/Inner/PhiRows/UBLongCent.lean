module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.CentralizerK
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4HexCent

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex
  CFSG.Timmesfeld.RankTwo CFSG.LieType.Universal CFSG.ClassicalInvolution.G2D4Models
  CFSG.ClassicalInvolution.ModelFacts CFSG.LieType.CurtisTits
open scoped MatrixGroups commutatorElement

section UBLongCent


variable {K : Type} [Field K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem d4X_zero_add' (a b : K) :
    d4X hσ 0 (a + b) = d4X hσ 0 a * d4X hσ 0 b := d4X_add hσ 0 a b

include hσ in
theorem slShort_HSL_conj_d4X_zero (t : Kˣ) (c : K) :
    slShort σ hσ (HSL t) * d4X hσ 0 c * (slShort σ hσ (HSL t))⁻¹ =
      d4X hσ 0 ((t : K) ^ 2 * c) := by
  rw [d4X_zero_eq hσ, d4X_zero_eq hσ, ← map_inv, ← map_mul, ← map_mul]
  have e : HSL t = diagSL t := rfl
  rw [e, diagSL_conj_sl2Upper]

include hσ in
theorem slShort_HSL_fix_d4X_zero (t : Kˣ) (ht2 : (t : K) ^ 2 ≠ 1) (c : K)
    (h : slShort σ hσ (HSL t) * d4X hσ 0 c * (slShort σ hσ (HSL t))⁻¹ = d4X hσ 0 c) :
    d4X hσ 0 c = 1 := by
  rw [slShort_HSL_conj_d4X_zero hσ] at h
  have hc : ((t : K) ^ 2 - 1) * c = 0 := by
    have h1 : d4X hσ 0 ((t : K) ^ 2 * c - c) = 1 := by
      have e := d4X_zero_add' hσ ((t : K) ^ 2 * c - c) c
      rw [sub_add_cancel] at e
      rw [e] at h
      exact mul_right_cancel (h.trans (one_mul _).symm)
    have h2 : d4X hσ 0 ((t : K) ^ 2 * c - c) = d4X hσ 0 (0 : K) := by
      rw [h1]
      exact (d4X_zero_zero hσ).symm
    have h3 : (t : K) ^ 2 * c - c = 0 := d4X_injective hσ 0 h2
    linear_combination h3
  have hc0 : c = 0 := by
    rcases mul_eq_zero.1 hc with h0 | h0
    · exact absurd (sub_eq_zero.1 h0) ht2
    · exact h0
  rw [hc0]
  exact d4X_zero_zero hσ

section Transfer

variable {X : Type*} [Group X]

theorem fix_free_transfer {z w : X} (hw : w * z * w⁻¹ = z ∨ w * z * w⁻¹ = z⁻¹)
    {S S' : Subgroup X} (hmap : ∀ x ∈ S, w * x * w⁻¹ ∈ S')
    (hS' : ∀ y ∈ S', z * y * z⁻¹ = y → y = 1) :
    ∀ x ∈ S, z * x * z⁻¹ = x → x = 1 := by
  intro x hx hzx
  have hy : w * x * w⁻¹ ∈ S' := hmap x hx
  have e : w * (z * x * z⁻¹) * w⁻¹ = (w * z * w⁻¹) * (w * x * w⁻¹) * (w * z * w⁻¹)⁻¹ := by group
  rw [hzx] at e
  have hzy : z * (w * x * w⁻¹) * z⁻¹ = w * x * w⁻¹ := by
    rcases hw with h | h
    · rw [h] at e
      exact e.symm
    · rw [h] at e
      have e2 : z⁻¹ * (w * x * w⁻¹) * z = w * x * w⁻¹ := by
        simpa using e.symm
      calc z * (w * x * w⁻¹) * z⁻¹ = z * (z⁻¹ * (w * x * w⁻¹) * z) * z⁻¹ := by rw [e2]
        _ = w * x * w⁻¹ := by group
  have h1 : w * x * w⁻¹ = 1 := hS' _ hy hzy
  have : x = w⁻¹ * (w * x * w⁻¹) * w := by group
  rw [this, h1]
  group

end Transfer

include hσ in
theorem slShort_HSL_commute_nHat_zero (t : Kˣ) (ht : (t : K) * σ t * σ (σ t) = 1) :
    Commute (slShort σ hσ (HSL t)) (nHat σ (ng 0)) := by
  obtain ⟨C, hC⟩ := rankOne_long_le_range_slLong σ hσ (nHat_mem_rankOne σ (ng 0))
  rw [← hC]
  exact slShort_HSL_commute_slLong hσ t ht C

theorem conj_mem_of_conjBy {X : Type*} [Group X] {m : X} {A B : Subgroup X}
    (h : CFSG.GH74.BNPair.conjBy m⁻¹ A = B) {x : X} (hx : x ∈ A) : m * x * m⁻¹ ∈ B := by
  rw [← h]
  refine ⟨x, hx, ?_⟩
  simp [MulAut.conj_apply]

include hσ in
theorem longCent_slShort_HSL
    (t : Kˣ) (ht : (t : K) * σ t * σ (σ t) = 1)
    (ht2 : (t : K) ^ 2 ≠ 1) :
    LongCent (d4RGD2 σ hσ) (slShort σ hσ (HSL t)) := by
  have R := d4RGD2 σ hσ
  set z := slShort σ hσ (HSL t) with hz
  have hr1 : nHat σ (ng 1) * z * (nHat σ (ng 1))⁻¹ = z⁻¹ := by
    have h := slShort_HSL_mul_nHat_one hσ t
    rw [← hz] at h
    have e : nHat σ (ng 1) * z⁻¹ * (nHat σ (ng 1))⁻¹ = z := by
      rw [← h]; group
    calc nHat σ (ng 1) * z * (nHat σ (ng 1))⁻¹
        = (nHat σ (ng 1) * z⁻¹ * (nHat σ (ng 1))⁻¹)⁻¹ := by group
      _ = z⁻¹ := by rw [e]
  have hr2 : nHat σ (ng 0) * z * (nHat σ (ng 0))⁻¹ = z := by
    have h := (slShort_HSL_commute_nHat_zero hσ t ht).eq
    rw [← hz] at h
    rw [← h]; group
  obtain ⟨a11, a12, a1⟩ := R.act₁
  obtain ⟨a21, a22, a2⟩ := R.act₂
  have F1 : ∀ x ∈ hexGroup (twistedX σ) 1, z * x * z⁻¹ = x → x = 1 := by
    intro x hx hzx
    obtain ⟨c, rfl⟩ := (mem_hexGroup_iff' hσ 0 (by norm_num)).1 hx
    exact slShort_HSL_fix_d4X_zero hσ t ht2 c hzx
  have Fm1 : ∀ x ∈ hexGroup (twistedX σ) (-1), z * x * z⁻¹ = x → x = 1 :=
    fix_free_transfer (w := nHat σ (ng 1)) (Or.inr hr1) (S' := hexGroup (twistedX σ) 1)
      (fun x hx => conj_mem_of_conjBy a12 hx) F1
  have F5 : ∀ x ∈ hexGroup (twistedX σ) 5, z * x * z⁻¹ = x → x = 1 := by
    have h := (a2 5 (by norm_num) (by norm_num)).1
    have e : ((6 : ℕ) : ℤ) - 5 = 1 := by norm_num
    rw [e] at h
    exact fix_free_transfer (w := nHat σ (ng 0)) (Or.inl hr2) (S' := hexGroup (twistedX σ) 1)
      (fun x hx => conj_mem_of_conjBy h hx) F1
  have Fm5 : ∀ x ∈ hexGroup (twistedX σ) (-5), z * x * z⁻¹ = x → x = 1 := by
    have h := (a2 5 (by norm_num) (by norm_num)).2
    have e : -(((6 : ℕ) : ℤ) - 5) = -1 := by norm_num
    rw [e] at h
    exact fix_free_transfer (w := nHat σ (ng 0)) (Or.inl hr2) (S' := hexGroup (twistedX σ) (-1))
      (fun x hx => conj_mem_of_conjBy h hx) Fm1
  have F3 : ∀ x ∈ hexGroup (twistedX σ) 3, z * x * z⁻¹ = x → x = 1 := by
    have h := (a1 3 (by norm_num) (by norm_num)).1
    have e : ((6 : ℕ) : ℤ) + 2 - 3 = 5 := by norm_num
    rw [e] at h
    exact fix_free_transfer (w := nHat σ (ng 1)) (Or.inr hr1) (S' := hexGroup (twistedX σ) 5)
      (fun x hx => conj_mem_of_conjBy h hx) F5
  have Fm3 : ∀ x ∈ hexGroup (twistedX σ) (-3), z * x * z⁻¹ = x → x = 1 := by
    have h := (a1 3 (by norm_num) (by norm_num)).2
    have e : -(((6 : ℕ) : ℤ) + 2 - 3) = -5 := by norm_num
    rw [e] at h
    exact fix_free_transfer (w := nHat σ (ng 1)) (Or.inr hr1) (S' := hexGroup (twistedX σ) (-5))
      (fun x hx => conj_mem_of_conjBy h hx) Fm5
  refine ⟨Subgroup.mem_iSup_of_mem (ng 1) (slShort_HSL_mem_hHat hσ t), ?_, ?_⟩
  · intro k hk hk2 x hx
    have hx' : x ∈ longSub 6 (hexGroup (twistedX σ)) := root_le_longSub hk hk2 hx
    have := longSub_le_centralizer_slShort_HSL hσ t ht hx'
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    have hxz : z * x = x * z := this.symm
    rw [hxz]
    group
  · intro k hk hk2 x hx hzx
    obtain ⟨h0, h6⟩ := hk
    have hcase : k = 1 ∨ k = 3 ∨ k = 5 ∨ k = -1 ∨ k = -3 ∨ k = -5 := by omega
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl
    · exact F1 x hx hzx
    · exact F3 x hx hzx
    · exact F5 x hx hzx
    · exact Fm1 x hx hzx
    · exact Fm3 x hx hzx
    · exact Fm5 x hx hzx

end UBLongCent

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
