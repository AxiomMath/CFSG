module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4Basic
public import CFSG.GH74.Generic.BProg.B2.GenLocDiagU
public import CFSG.GH74.Generic.S1.UniGraph

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Matrix
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

namespace GenLocU4Basic

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem inv_coe_of_isUnitaryU {q : ℕ} {A : GL (Fin 4) K}
    (hA : IsUnitaryU q (A : Matrix (Fin 4) (Fin 4) K)) :
    ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      ((A : Matrix (Fin 4) (Fin 4) K).map (· ^ q))ᵀ :=
  Units.inv_eq_of_mul_eq_one_left hA

omit [Finite K] in
theorem map_smul_pow {q : ℕ} (c : K) (M : Matrix (Fin 4) (Fin 4) K) :
    (c • M).map (· ^ q) = c ^ q • M.map (· ^ q) := by
  ext i j
  simp [mul_pow]

omit [Finite K] in
theorem bar_eq_pow {p f : ℕ} (h : UnitaryFieldData p f K) :
    (⇑h.bar : K → K) = fun c => c ^ (p ^ f) := funext fun c => h.bar_apply c

omit [Finite K] in
theorem transpose_eq_of_graph {p f : ℕ} (h : UnitaryFieldData p f K) {A : GL (Fin 4) K}
    (hA : IsUnitaryU (p ^ f) (A : Matrix (Fin 4) (Fin 4) K)) {c : K}
    (hc : (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)) = c • 1) :
    (A : Matrix (Fin 4) (Fin 4) K)ᵀ = A ∨ (A : Matrix (Fin 4) (Fin 4) K)ᵀ = -(A : Matrix (Fin 4) (Fin 4) K) := by
  set B : Matrix (Fin 4) (Fin 4) K := (A : Matrix (Fin 4) (Fin 4) K) with hB
  set Bb : Matrix (Fin 4) (Fin 4) K := B.map (· ^ (p ^ f)) with hBb
  have hbb : Bb.map (· ^ (p ^ f)) = B := by
    rw [hBb, ← bar_eq_pow h]
    ext i j
    simp [h.bar_bar]
  have hc0 : c ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hc
    rw [h0, zero_smul, Matrix.det_zero, Matrix.det_mul] at this
    have hd : B.det ≠ 0 := (Matrix.isUnits_det_units A).ne_zero
    have hd2 : Bb.det ≠ 0 := by
      have := congrArg Matrix.det hA
      rw [Matrix.det_mul, Matrix.det_one] at this
      intro h1
      rw [Matrix.det_transpose] at this
      rw [h1, zero_mul] at this
      exact zero_ne_one this
    exact mul_ne_zero hd hd2 this
  have hinv : ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = Bbᵀ := inv_coe_of_isUnitaryU hA
  have h1 : Bbᵀ = c⁻¹ • Bb := by
    rw [← hinv]
    have h2 : ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * B = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
        = ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (B * (c⁻¹ • Bb)) := by
          rw [Matrix.mul_smul, hc, smul_smul, inv_mul_cancel₀ hc0, one_smul, Matrix.mul_one]
      _ = c⁻¹ • Bb := by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  have h3 : Bᵀ = (c⁻¹) ^ (p ^ f) • B := by
    have := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M.map (· ^ (p ^ f))) h1
    simp only [Matrix.transpose_map] at this
    rw [map_smul_pow, hbb] at this
    exact this
  set ε : K := (c⁻¹) ^ (p ^ f) with hε
  have hB0 : B ≠ 0 := by
    intro h0
    have hA' : Bbᵀ * B = 1 := hA
    rw [h0, Matrix.mul_zero] at hA'
    exact zero_ne_one hA'
  obtain ⟨i, j, hij⟩ : ∃ i j, B i j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hB0 (Matrix.ext fun i j => hcon i j)
  have h4 : B = (ε * ε) • B := by
    have h5 := congrArg Matrix.transpose h3
    rw [Matrix.transpose_transpose, Matrix.transpose_smul, h3, smul_smul] at h5
    exact h5
  have h6 : ε * ε = 1 := by
    have := congrFun (congrFun h4 i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    have h7 : (ε * ε - 1) * B i j = 0 := by linear_combination -this
    rcases mul_eq_zero.mp h7 with h8 | h8
    · exact sub_eq_zero.mp h8
    · exact absurd h8 hij
  rcases mul_self_eq_one_iff.mp h6 with h9 | h9
  · left
    rw [h3, h9, one_smul]
  · right
    rw [h3, h9, neg_smul, one_smul]

omit [Finite K] in
theorem isUnitaryU_one {q : ℕ} (hq : q ≠ 0) : IsUnitaryU q (1 : Matrix (Fin 4) (Fin 4) K) := by
  unfold IsUnitaryU
  rw [Matrix.map_one (fun x : K => x ^ q) (zero_pow hq) (one_pow q), Matrix.transpose_one, Matrix.mul_one]

theorem inner_or_graph {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2)
    (φ : MulAut ↥(StatedSU 4 (p ^ f) K)) (hφ : φ * φ = 1) :
    IsInnerDiagU4 φ ∨ ∃ A : GL (Fin 4) K, IsGraphU4 A φ ∧
      ((A : Matrix (Fin 4) (Fin 4) K)ᵀ = A ∨ (A : Matrix (Fin 4) (Fin 4) K)ᵀ = -(A : Matrix (Fin 4) (Fin 4) K)) := by
  have h : UnitaryFieldData p f K := GenLocDiagU.unitaryFieldData_of_card hp hK
  by_cases hφ1 : φ = 1
  · left
    refine ⟨1, isUnitaryU_one (pow_ne_zero f hp.ne_zero), fun g => ?_⟩
    rw [hφ1]
    simp
  · obtain ⟨A, σ, hσ, hA, hφA, -, hbar⟩ := Generic.S1.Uni.aut_form_uni h hp2 φ hφ hφ1
    have hAu : IsUnitaryU (p ^ f) (A : Matrix (Fin 4) (Fin 4) K) := by
      unfold IsUnitaryU
      rw [← bar_eq_pow h]
      exact hA
    rcases hσ with rfl | hσb
    · left
      refine ⟨A, hAu, fun g => ?_⟩
      have := congrArg (fun u : GL (Fin 4) K => (u : Matrix (Fin 4) (Fin 4) K)) (hφA g)
      simp only [Units.val_mul, coe_glAut] at this
      rw [this]
      simp
    · right
      have hσp : (⇑σ : K → K) = fun c => c ^ (p ^ f) := by
        rw [← bar_eq_pow h]
        exact funext hσb
      obtain ⟨c, hc0, hc⟩ := hbar hσb
      refine ⟨A, ⟨hAu, fun g => ?_⟩, transpose_eq_of_graph h hAu (by rw [← bar_eq_pow h]; exact hc)⟩
      have := congrArg (fun u : GL (Fin 4) K => (u : Matrix (Fin 4) (Fin 4) K)) (hφA g)
      simp only [Units.val_mul, coe_glAut, hσp] at this
      exact this

omit [Finite K] in
theorem proportional_of_conj_eq {p f : ℕ} (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) {u v : GL (Fin 4) K}
    (huv : ∀ g : GL (Fin 4) K, g ∈ StatedSU 4 (p ^ f) K → u * g * u⁻¹ = v * g * v⁻¹) :
    ∃ l : K, l ≠ 0 ∧ (u : Matrix (Fin 4) (Fin 4) K) = l • (v : Matrix (Fin 4) (Fin 4) K) := by
  obtain ⟨l, hl⟩ := Generic.S1.Uni.commutant_scalar h hp2
    (S := ((v⁻¹ * u : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) (fun m hm => by
      have h1 : v⁻¹ * u * m = m * (v⁻¹ * u) := by
        calc v⁻¹ * u * m = v⁻¹ * (u * m * u⁻¹) * u := by group
          _ = v⁻¹ * (v * m * v⁻¹) * u := by rw [huv m hm]
          _ = m * (v⁻¹ * u) := by group
      have h2 := congrArg (fun w : GL (Fin 4) K => (w : Matrix (Fin 4) (Fin 4) K)) h1
      simpa only [Units.val_mul] using h2)
  have hu : (u : Matrix (Fin 4) (Fin 4) K) = l • (v : Matrix (Fin 4) (Fin 4) K) := by
    have h2 : (u : Matrix (Fin 4) (Fin 4) K) =
        (v : Matrix (Fin 4) (Fin 4) K) * ((v⁻¹ * u : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
      rw [← Units.val_mul, mul_inv_cancel_left]
    rw [h2, hl, Matrix.mul_smul, Matrix.mul_one]
  refine ⟨l, fun h0 => ?_, hu⟩
  have h3 := u.mul_inv
  rw [hu, h0, zero_smul, zero_mul] at h3
  exact zero_ne_one h3

theorem comm_or_anticomm_U4_of_card {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2)
    {A : Type} [Group A] (α : A →* MulAut ↥(StatedSU 4 (p ^ f) K)) (ρ : A → GL (Fin 4) K)
    (hρ : ∀ (a : A) (g : ↥(StatedSU 4 (p ^ f) K)),
      (((α a g : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        (ρ a : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          ((ρ a)⁻¹ : GL (Fin 4) K))
    (hsq : ∀ a, α a * α a = 1) (a b : A) (hab : α a * α b = α b * α a) :
    ρ a * ρ b = ρ b * ρ a ∨
      (ρ a : Matrix (Fin 4) (Fin 4) K) * (ρ b : Matrix (Fin 4) (Fin 4) K) =
        -((ρ b : Matrix (Fin 4) (Fin 4) K) * (ρ a : Matrix (Fin 4) (Fin 4) K)) := by
  have h : UnitaryFieldData p f K := GenLocDiagU.unitaryFieldData_of_card hp hK
  have hρ' : ∀ (a : A) (g : ↥(StatedSU 4 (p ^ f) K)),
      ((α a g : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K) = ρ a * (g : GL (Fin 4) K) * (ρ a)⁻¹ :=
    fun a g => Units.ext (by rw [hρ a g, Units.val_mul, Units.val_mul])
  obtain ⟨l, hl0, hl⟩ := proportional_of_conj_eq h hp2 (u := ρ a * ρ b) (v := ρ b * ρ a) (fun g hg => by
    have h1 := congrArg (fun φ : MulAut ↥(StatedSU 4 (p ^ f) K) =>
      ((φ ⟨g, hg⟩ : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K)) hab
    simp only [MulAut.mul_apply, hρ'] at h1
    calc ρ a * ρ b * g * (ρ a * ρ b)⁻¹ = ρ a * (ρ b * g * (ρ b)⁻¹) * (ρ a)⁻¹ := by group
      _ = ρ b * (ρ a * g * (ρ a)⁻¹) * (ρ b)⁻¹ := h1
      _ = ρ b * ρ a * g * (ρ b * ρ a)⁻¹ := by group)
  rw [Units.val_mul, Units.val_mul] at hl
  obtain ⟨ca, hca0, hca⟩ := proportional_of_conj_eq h hp2 (u := ρ a * ρ a) (v := 1) (fun g hg => by
    have h1 := congrArg (fun φ : MulAut ↥(StatedSU 4 (p ^ f) K) =>
      ((φ ⟨g, hg⟩ : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K)) (hsq a)
    simp only [MulAut.mul_apply, hρ', MulAut.one_apply] at h1
    calc ρ a * ρ a * g * (ρ a * ρ a)⁻¹ = ρ a * (ρ a * g * (ρ a)⁻¹) * (ρ a)⁻¹ := by group
      _ = g := h1
      _ = 1 * g * 1⁻¹ := by group)
  rw [Units.val_mul, Units.val_one] at hca
  set X : Matrix (Fin 4) (Fin 4) K := (ρ a : Matrix (Fin 4) (Fin 4) K) with hX
  set Y : Matrix (Fin 4) (Fin 4) K := (ρ b : Matrix (Fin 4) (Fin 4) K) with hY
  have h1 : X * (X * Y) = ca • Y := by
    rw [← Matrix.mul_assoc, hca, Matrix.smul_mul, Matrix.one_mul]
  have h2 : X * (X * Y) = (l * l * ca) • Y := by
    calc X * (X * Y) = X * (l • (Y * X)) := by rw [hl]
      _ = l • ((X * Y) * X) := by rw [Matrix.mul_smul, Matrix.mul_assoc]
      _ = l • ((l • (Y * X)) * X) := by rw [hl]
      _ = (l * l) • (Y * (X * X)) := by rw [Matrix.smul_mul, smul_smul, Matrix.mul_assoc]
      _ = (l * l * ca) • Y := by rw [hca, Matrix.mul_smul, Matrix.mul_one, smul_smul]
  have hY0 : Y ≠ 0 := by
    intro h0
    have h3 := (ρ b).mul_inv
    rw [← hY, h0, zero_mul] at h3
    exact zero_ne_one h3
  obtain ⟨i, j, hij⟩ : ∃ i j, Y i j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hY0 (Matrix.ext fun i j => hcon i j)
  have h4 : l * l = 1 := by
    have h5 := congrFun (congrFun (h1.symm.trans h2) i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at h5
    have h6 : ca * (l * l - 1) * Y i j = 0 := by linear_combination -h5
    rcases mul_eq_zero.mp h6 with h7 | h7
    · rcases mul_eq_zero.mp h7 with h8 | h8
      · exact absurd h8 hca0
      · exact sub_eq_zero.mp h8
    · exact absurd h7 hij
  rcases mul_self_eq_one_iff.mp h4 with h9 | h9
  · left
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, ← hX, ← hY, hl, h9, one_smul]
  · right
    rw [hl, h9, neg_smul, one_smul]

end GenLocU4Basic

end CFSG.GH74.Generic.BProg.B2
