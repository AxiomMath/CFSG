module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongKGL34Gen
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongKGL34Norm

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open Matrix


theorem exists_fixed_sqrt {F : Type*} [Field F] [Finite F] [CharP F 2] (φ : F ≃+* F) {a : F}
    (ha : φ a = a) : ∃ b : F, φ b = b ∧ b * b = a := by
  obtain ⟨b, hb⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) a
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hsq : φ b * φ b = b * b := by
    rw [← map_mul, ← hb, ha]
  have hzero : (φ b - b) * (φ b - b) = 0 := by
    linear_combination hsq + (b * b - φ b * b) * h2
  exact ⟨b, sub_eq_zero.mp (mul_self_eq_zero.mp hzero), hb.symm⟩

theorem kgl34_col_mul {n : ℕ} {F : Type*} [Field F] [DecidableEq (Fin n)] (i0 : Fin n)
    (e z : Fin n → F) (Y Z : Matrix (Fin n) (Fin n) F)
    (hY : ∀ j k, Y j k = if k = i0 then e j else if j = k then 1 else 0)
    (hZ : ∀ j k, Z j k = if k = i0 then z j else if j = k then 1 else 0)
    (hz : z i0 * e i0 = 1) (hz' : ∀ j, j ≠ i0 → z j = -(e j * z i0)) :
    Y * Z = 1 := by
  ext j k
  simp only [Matrix.mul_apply, Matrix.one_apply]
  by_cases hk : k = i0
  · rw [hk]
    by_cases hj : j = i0
    · rw [hj, if_pos rfl, Finset.sum_eq_single i0]
      · simpa [hY, hZ, mul_comm] using hz
      · intro b _ hb
        simp [hY, hZ, hb, Ne.symm hb]
      · intro h
        exact absurd (Finset.mem_univ i0) h
    · have hterm : ∀ m, Y j m * Z m i0
          = (if j = m then z m else 0) + (if m = i0 then e j * z m else 0) := by
        intro m
        by_cases hm : m = i0
        · rw [hm]
          simp [hY, hZ, hj]
        · by_cases hjm : j = m
          · simp [hY, hZ, hm, hjm]
          · simp [hY, hZ, hm, hjm]
      simp only [hterm, Finset.sum_add_distrib]
      rw [Finset.sum_ite_eq, Finset.sum_ite_eq', if_pos (Finset.mem_univ j),
        if_pos (Finset.mem_univ i0), if_neg hj]
      linear_combination hz' j hj
  · have hcol : ∀ m, Y j m * Z m k = if m = k then Y j m else 0 := by
      intro m
      rw [hZ, if_neg hk]
      by_cases hmk : m = k <;> simp [hmk]
    simp only [hcol]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ k), hY, if_neg hk]

theorem exists_isotropic_column {n : ℕ} (hn : 2 ≤ n) {F : Type*} [Field F] [Finite F] [CharP F 2]
    (φ : F ≃+* F) (D : Matrix (Fin n) (Fin n) F) (hDφ : ∀ i j, φ (D i j) = D i j)
    (hDs : ∀ i j, D i j = D j i) :
    ∃ (Y : GL (Fin n) F) (p : Fin n),
      (∀ i j, φ ((Y : Matrix (Fin n) (Fin n) F) i j) = (Y : Matrix (Fin n) (Fin n) F) i j) ∧
      ((Y : Matrix (Fin n) (Fin n) F)ᵀ * D * (Y : Matrix (Fin n) (Fin n) F)) p p = 0 := by
  obtain ⟨i0, i1, hi⟩ : ∃ i0 i1 : Fin n, i0 ≠ i1 :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩
  by_cases hD : D i1 i1 = 0
  · refine ⟨1, i1, ?_, ?_⟩
    · intro j k
      simp only [Units.val_one, Matrix.one_apply]
      split_ifs <;> simp
    · simpa using hD
  · have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    obtain ⟨s₁, hs₁φ, hs₁⟩ := exists_fixed_sqrt φ (hDφ i1 i1)
    obtain ⟨s₀, hs₀φ, hs₀⟩ := exists_fixed_sqrt φ (hDφ i0 i0)
    have hs₁ne : s₁ ≠ 0 := by
      intro h
      apply hD
      rw [← hs₁, h, zero_mul]
    obtain ⟨e, he0, he1, heo⟩ : ∃ e : Fin n → F, e i0 = s₁ ∧ e i1 = s₀ ∧
        ∀ j, j ≠ i0 → j ≠ i1 → e j = 0 :=
      ⟨fun j => if j = i0 then s₁ else if j = i1 then s₀ else 0, by simp,
        by simp [Ne.symm hi], fun j h0 h1 => by simp [h0, h1]⟩
    obtain ⟨z, hz0, hz1, hzo⟩ : ∃ z : Fin n → F, z i0 = s₁⁻¹ ∧ z i1 = -(s₀ * s₁⁻¹) ∧
        ∀ j, j ≠ i0 → j ≠ i1 → z j = 0 :=
      ⟨fun j => if j = i0 then s₁⁻¹ else if j = i1 then -(s₀ * s₁⁻¹) else 0, by simp,
        by simp [Ne.symm hi], fun j h0 h1 => by simp [h0, h1]⟩
    have hz : z i0 * e i0 = 1 := by
      rw [hz0, he0, inv_mul_cancel₀ hs₁ne]
    have hz' : ∀ j, j ≠ i0 → z j = -(e j * z i0) := by
      intro j hj0
      by_cases hj1 : j = i1
      · rw [hj1, hz1, he1, hz0]
      · rw [hzo j hj0 hj1, heo j hj0 hj1, zero_mul, neg_zero]
    have hz2' : ∀ j, j ≠ i0 → e j = -(z j * e i0) := fun j hj => by
      linear_combination (-(e j)) * hz + e i0 * hz' j hj
    obtain ⟨Y, hY⟩ : ∃ Y : Matrix (Fin n) (Fin n) F,
        ∀ j k, Y j k = if k = i0 then e j else if j = k then 1 else 0 :=
      ⟨Matrix.of fun j k => if k = i0 then e j else if j = k then 1 else 0, fun _ _ => rfl⟩
    obtain ⟨Z, hZ⟩ : ∃ Z : Matrix (Fin n) (Fin n) F,
        ∀ j k, Z j k = if k = i0 then z j else if j = k then 1 else 0 :=
      ⟨Matrix.of fun j k => if k = i0 then z j else if j = k then 1 else 0, fun _ _ => rfl⟩
    have hYZ : Y * Z = 1 := kgl34_col_mul i0 e z Y Z hY hZ hz hz'
    have hZY : Z * Y = 1 := kgl34_col_mul i0 z e Z Y hZ hY (by rw [mul_comm]; exact hz) hz2'
    have hefix : ∀ j, φ (e j) = e j := by
      intro j
      by_cases h0 : j = i0
      · rw [h0, he0]
        exact hs₁φ
      by_cases h1 : j = i1
      · rw [h1, he1]
        exact hs₀φ
      rw [heo j h0 h1, map_zero]
    refine ⟨⟨Y, Z, hYZ, hZY⟩, i0, ?_, ?_⟩
    · intro j k
      show φ (Y j k) = Y j k
      rw [hY]
      split_ifs <;> first | exact hefix j | simp
    · show (Yᵀ * D * Y) i0 i0 = 0
      have hYcol : ∀ j, Y j i0 = e j := fun j => by rw [hY, if_pos rfl]
      simp only [Matrix.mul_apply, Matrix.transpose_apply, hYcol]
      have hA : ∀ k, ∑ j, e j * D j k = e i0 * D i0 k + e i1 * D i1 k := fun k =>
        Fintype.sum_eq_add i0 i1 hi (fun j hj => by simp [heo j hj.1 hj.2])
      have hB : ∑ k, (∑ j, e j * D j k) * e k
          = (∑ j, e j * D j i0) * e i0 + (∑ j, e j * D j i1) * e i1 :=
        Fintype.sum_eq_add i0 i1 hi (fun k hk => by simp [heo k hk.1 hk.2])
      rw [hB, hA i0, hA i1, he0, he1]
      linear_combination (D i0 i0) * hs₁ + (D i1 i1) * hs₀ + (s₀ * s₁) * hDs i1 i0
        + (s₀ * s₁ * D i0 i1 + D i0 i0 * D i1 i1) * h2

section Rational

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem closure_eq_top_of_rational_symmetric {n : ℕ} (hn : 3 ≤ n) {F : Type*} [Field F] [Finite F]
    [CharP F 2] (φ : F ≃+* F) (C : GL (Fin n) F)
    (hCφ : ∀ i j, φ ((C : Matrix (Fin n) (Fin n) F) i j) = (C : Matrix (Fin n) (Fin n) F) i j)
    (hC : ∀ i j, (C : Matrix (Fin n) (Fin n) F) i j = (C : Matrix (Fin n) (Fin n) F) j i) :
    Subgroup.closure ({x : projectiveSL n F | fieldAut n F φ x = x} ∪
      {x : projectiveSL n F | (conjAut n F C * dualAut n F) x = x}) = ⊤ := by
  set M : Matrix (Fin n) (Fin n) F := (C : Matrix (Fin n) (Fin n) F) with hM
  set Dm : Matrix (Fin n) (Fin n) F := ((C⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
    with hDm
  have hMDm : M * Dm = 1 := Units.mul_inv C
  have hDmM : Dm * M = 1 := Units.inv_mul C
  have hMT : Mᵀ = M := by
    ext i j
    exact hC j i
  have hmapC : GeneralLinearGroup.map (φ : F →+* F) C = C := by
    apply Units.ext
    ext i j
    simpa using hCφ i j
  have hDφ : ∀ i j, φ (Dm i j) = Dm i j := by
    intro i j
    have h1 : GeneralLinearGroup.map (φ : F →+* F) C⁻¹ = C⁻¹ := by rw [map_inv, hmapC]
    have h2 := congrArg (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F) i j) h1
    exact (GeneralLinearGroup.map_apply (φ : F →+* F) i j C⁻¹).symm.trans h2
  have hDmT : Dmᵀ = Dm := by
    have h1 : Dmᵀ * M = 1 := by
      have := congrArg Matrix.transpose hMDm
      rwa [Matrix.transpose_mul, hMT, Matrix.transpose_one] at this
    calc Dmᵀ = Dmᵀ * (M * Dm) := by rw [hMDm, Matrix.mul_one]
      _ = (Dmᵀ * M) * Dm := by rw [Matrix.mul_assoc]
      _ = Dm := by rw [h1, Matrix.one_mul]
  have hDs : ∀ i j, Dm i j = Dm j i := by
    intro i j
    have := congrFun (congrFun hDmT i) j
    simpa using this.symm
  obtain ⟨Y, p, hYφ, hYp⟩ := exists_isotropic_column (by omega : 2 ≤ n) φ Dm hDφ hDs
  obtain ⟨C', hC'⟩ : ∃ C' : GL (Fin n) F, C' = Y⁻¹ * C * GeneralLinearGroup.inverseTranspose Y :=
    ⟨_, rfl⟩
  have hC'mat : (C' : Matrix (Fin n) (Fin n) F) =
      ((Y⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * M *
        ((Y⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ := by
    rw [hC', Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_inverseTranspose]
  have hC'sym : ∀ i j, (C' : Matrix (Fin n) (Fin n) F) i j = (C' : Matrix (Fin n) (Fin n) F) j i := by
    intro i j
    have hT : (C' : Matrix (Fin n) (Fin n) F)ᵀ = (C' : Matrix (Fin n) (Fin n) F) := by
      rw [hC'mat, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hMT,
        Matrix.mul_assoc]
    have := congrFun (congrFun hT i) j
    simpa using this.symm
  have hC'inv : ((C'⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      (Y : Matrix (Fin n) (Fin n) F)ᵀ * Dm * (Y : Matrix (Fin n) (Fin n) F) := by
    have h1 : C'⁻¹ = GeneralLinearGroup.inverseTranspose Y⁻¹ * C⁻¹ * Y := by
      rw [hC', _root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, map_inv]
      group
    rw [h1, Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_inverseTranspose, inv_inv]
  have hC'p : ((C'⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) p p = 0 := by
    rw [hC'inv]
    exact hYp
  have hgen := closure_eq_top_of_isotropic_coord hn φ C' hC'sym p hC'p
  have hYmap : GeneralLinearGroup.map (φ : F →+* F) Y = Y := by
    apply Units.ext
    ext i j
    simpa using hYφ i j
  have hcf : conjAut n F Y * fieldAut n F φ * (conjAut n F Y)⁻¹ = fieldAut n F φ := by
    have h1 : fieldAut n F φ * conjAut n F Y = conjAut n F Y * fieldAut n F φ := by
      rw [fieldAut_mul_conjAut, hYmap]
    calc conjAut n F Y * fieldAut n F φ * (conjAut n F Y)⁻¹
        = (fieldAut n F φ * conjAut n F Y) * (conjAut n F Y)⁻¹ := by rw [h1]
      _ = fieldAut n F φ := by group
  have hcg : conjAut n F Y * (conjAut n F C' * dualAut n F) * (conjAut n F Y)⁻¹ =
      conjAut n F C * dualAut n F := by
    calc conjAut n F Y * (conjAut n F C' * dualAut n F) * (conjAut n F Y)⁻¹
        = conjAut n F Y * conjAut n F C' * (dualAut n F * conjAut n F Y⁻¹) := by
          rw [map_inv]; group
      _ = conjAut n F Y * conjAut n F C' *
            (conjAut n F (GeneralLinearGroup.inverseTranspose Y⁻¹) * dualAut n F) := by
          rw [dualAut_mul_conjAut]
      _ = conjAut n F (Y * C' * GeneralLinearGroup.inverseTranspose Y⁻¹) * dualAut n F := by
          rw [map_mul, map_mul]; group
      _ = conjAut n F C * dualAut n F := by
          rw [hC', map_inv]
          congr 2
          group
  have hconj := closure_fixedPoints_conj (conjAut n F Y) (fieldAut n F φ)
    (conjAut n F C' * dualAut n F)
  rw [hcf, hcg, hgen] at hconj
  rw [hconj, Subgroup.map_top]
  exact MonoidHom.range_eq_top.mpr (conjAut n F Y).surjective

end Rational

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
