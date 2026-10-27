module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2UniResD

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HDescUniRes

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitaryFrame
open CFSG.RankThree.PartOne.CTP
open Matrix

section U6Ring

private theorem u6cRing_comm_inv {R : Type*} [Ring R] {Y Y' P : R} (hY : P * Y = Y * P)
    (hYY' : Y * Y' = 1) (hY'Y : Y' * Y = 1) : P * Y' = Y' * P := by
  calc P * Y' = (Y' * Y) * P * Y' := by rw [hY'Y, one_mul]
    _ = Y' * (Y * P) * Y' := by simp only [mul_assoc]
    _ = Y' * (P * Y) * Y' := by rw [hY]
    _ = Y' * P * (Y * Y') := by simp only [mul_assoc]
    _ = Y' * P := by rw [hYY', mul_one]

private theorem u6cRing_conj_shape {R : Type*} [Ring R] {Y Y' M P : R} (hY : P * Y = Y * P)
    (hY' : P * Y' = Y' * P) (hYY' : Y * Y' = 1) (hM : M - 1 = P * (M - 1) * P) :
    Y * M * Y' - 1 = P * (Y * M * Y' - 1) * P := by
  have e1 : Y * M * Y' - 1 = Y * (M - 1) * Y' := by
    rw [mul_sub, sub_mul, mul_one, hYY']
  calc Y * M * Y' - 1 = Y * (M - 1) * Y' := e1
    _ = Y * (P * (M - 1) * P) * Y' := by rw [← hM]
    _ = (Y * P) * (M - 1) * (P * Y') := by simp only [mul_assoc]
    _ = (P * Y) * (M - 1) * (Y' * P) := by rw [← hY, hY']
    _ = P * (Y * (M - 1) * Y') * P := by simp only [mul_assoc]
    _ = P * (Y * M * Y' - 1) * P := by rw [e1]

private theorem u6cGrp {G : Type*} [Group G] {x y z : G} (hz : x * z = z * x)
    (h : (x * y * x⁻¹)⁻¹ * y = z) : y * x = x * y * z := by
  have e1 : y = x * y * x⁻¹ * z := inv_mul_eq_iff_eq_mul.1 h
  calc y * x = (x * y * x⁻¹ * z) * x := by rw [← e1]
    _ = x * y * (x⁻¹ * (z * x)) := by simp only [mul_assoc]
    _ = x * y * (x⁻¹ * (x * z)) := by rw [hz]
    _ = x * y * z := by rw [inv_mul_cancel_left]

end U6Ring

section U6Block

variable {K : Type} [Field K]

local notation "σ₆" => (finSumFinEquiv : Fin 4 ⊕ Fin 2 ≃ Fin 6)

private noncomputable def u6cBlk (B : Matrix (Fin 4) (Fin 4) K) : Matrix (Fin 6) (Fin 6) K :=
  Matrix.reindex σ₆ σ₆ (Matrix.fromBlocks B 0 0 1)

private theorem u6cBlk_apply (B : Matrix (Fin 4) (Fin 4) K) (a b : Fin 4 ⊕ Fin 2) :
    u6cBlk B (σ₆ a) (σ₆ b) =
      (Matrix.fromBlocks B 0 0 1 : Matrix (Fin 4 ⊕ Fin 2) (Fin 4 ⊕ Fin 2) K) a b := by
  simp [u6cBlk]

private theorem u6cBlk_castAdd (B : Matrix (Fin 4) (Fin 4) K) (a b : Fin 4) :
    u6cBlk B (Fin.castAdd 2 a) (Fin.castAdd 2 b) = B a b := by
  have h1 := u6cBlk_apply B (Sum.inl a) (Sum.inl b)
  rw [finSumFinEquiv_apply_left, finSumFinEquiv_apply_left, Matrix.fromBlocks_apply₁₁] at h1
  exact h1

private theorem u6cBlk_one : u6cBlk (1 : Matrix (Fin 4) (Fin 4) K) = 1 := by
  simp only [u6cBlk, Matrix.reindex_apply, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

private theorem u6cBlk_mul (B B' : Matrix (Fin 4) (Fin 4) K) :
    u6cBlk (B * B') = u6cBlk B * u6cBlk B' := by
  have hmul : (Matrix.fromBlocks B 0 0 1 : Matrix (Fin 4 ⊕ Fin 2) (Fin 4 ⊕ Fin 2) K) *
      Matrix.fromBlocks B' 0 0 1 = Matrix.fromBlocks (B * B') 0 0 1 := by
    rw [Matrix.fromBlocks_multiply]
    simp
  simp only [u6cBlk, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, hmul]

private theorem u6cBlk_det (B : Matrix (Fin 4) (Fin 4) K) : (u6cBlk B).det = B.det := by
  rw [u6cBlk, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

private theorem u6cBlk_map (f : K →+* K) (B : Matrix (Fin 4) (Fin 4) K) :
    (u6cBlk B).map f = u6cBlk (B.map f) := by
  have e : (Matrix.fromBlocks B 0 0 1 : Matrix (Fin 4 ⊕ Fin 2) (Fin 4 ⊕ Fin 2) K).map f =
      Matrix.fromBlocks (B.map f) 0 0 1 := by
    rw [Matrix.fromBlocks_map]
    simp
  simp only [u6cBlk, Matrix.reindex_apply]
  rw [← e]
  rfl

private theorem u6cBlk_transpose (B : Matrix (Fin 4) (Fin 4) K) :
    (u6cBlk B)ᵀ = u6cBlk Bᵀ := by
  simp only [u6cBlk, Matrix.reindex_apply, Matrix.transpose_submatrix,
    Matrix.fromBlocks_transpose, Matrix.transpose_zero, Matrix.transpose_one]

private theorem u6cBlk_injective :
    Function.Injective (u6cBlk : Matrix (Fin 4) (Fin 4) K → Matrix (Fin 6) (Fin 6) K) := by
  intro B B' hBB
  have h1 : (Matrix.fromBlocks B 0 0 1 : Matrix (Fin 4 ⊕ Fin 2) (Fin 4 ⊕ Fin 2) K) =
      Matrix.fromBlocks B' 0 0 1 := (Matrix.reindex σ₆ σ₆).injective hBB
  exact (Matrix.fromBlocks_inj.1 h1).1

private theorem u6cBlk_apply_of_le (B : Matrix (Fin 4) (Fin 4) K) {i j : Fin 6}
    (hij : 4 ≤ (i : ℕ) ∨ 4 ≤ (j : ℕ)) : u6cBlk B i j = if i = j then 1 else 0 := by
  obtain ⟨a, rfl⟩ := (σ₆).surjective i
  obtain ⟨b, rfl⟩ := (σ₆).surjective j
  rw [u6cBlk_apply]
  rcases a with a | a <;> rcases b with b | b
  · exfalso
    have ha := a.isLt
    have hb := b.isLt
    simp only [finSumFinEquiv_apply_left, Fin.val_castAdd] at hij
    omega
  · have hne : σ₆ (Sum.inl a) ≠ σ₆ (Sum.inr b) := fun hab => Sum.inl_ne_inr ((σ₆).injective hab)
    rw [if_neg hne]
    simp
  · have hne : σ₆ (Sum.inr a) ≠ σ₆ (Sum.inl b) := fun hab => Sum.inr_ne_inl ((σ₆).injective hab)
    rw [if_neg hne]
    simp
  · by_cases hab : a = b
    · subst hab
      simp
    · have hne : σ₆ (Sum.inr a) ≠ σ₆ (Sum.inr b) :=
        fun hh => hab (Sum.inr_injective ((σ₆).injective hh))
      rw [if_neg hne]
      simp [Matrix.one_apply, hab]

private theorem u6cExists {M : Matrix (Fin 6) (Fin 6) K}
    (hM : ∀ i j : Fin 6, (4 ≤ (i : ℕ) ∨ 4 ≤ (j : ℕ)) → M i j = if i = j then 1 else 0) :
    ∃ B : Matrix (Fin 4) (Fin 4) K, M = u6cBlk B := by
  refine ⟨Matrix.of fun a b => M (Fin.castAdd 2 a) (Fin.castAdd 2 b), ?_⟩
  ext i j
  by_cases hij : 4 ≤ (i : ℕ) ∨ 4 ≤ (j : ℕ)
  · rw [hM i j hij, u6cBlk_apply_of_le _ hij]
  · push Not at hij
    obtain ⟨a, rfl⟩ : ∃ a : Fin 4, Fin.castAdd 2 a = i := ⟨⟨i, hij.1⟩, Fin.ext rfl⟩
    obtain ⟨b, rfl⟩ : ∃ b : Fin 4, Fin.castAdd 2 b = j := ⟨⟨j, hij.2⟩, Fin.ext rfl⟩
    rw [u6cBlk_castAdd]
    rfl

private noncomputable def u6cHom : Matrix (Fin 4) (Fin 4) K →* Matrix (Fin 6) (Fin 6) K where
  toFun := u6cBlk
  map_one' := u6cBlk_one
  map_mul' := u6cBlk_mul

private noncomputable def u6cGL : GL (Fin 4) K →* GL (Fin 6) K := Units.map u6cHom

private theorem coe_u6cGL (g : GL (Fin 4) K) :
    ((u6cGL g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      u6cBlk (g : Matrix (Fin 4) (Fin 4) K) :=
  rfl

private theorem u6cGL_mem {ℓ f : ℕ} (h : UnitaryFieldData ℓ f K) {g : GL (Fin 4) K}
    (hg : g ∈ gramSU h (idGram K 4)) : u6cGL g ∈ gramSU h (idGram K 6) := by
  obtain ⟨hu, hdet⟩ := mem_gramSU.1 hg
  have hI4 : idGram K 4 = (1 : Matrix (Fin 4) (Fin 4) K) := Units.val_one
  have hI6 : idGram K 6 = (1 : Matrix (Fin 6) (Fin 6) K) := Units.val_one
  rw [hI4, Matrix.mul_one] at hu
  refine mem_gramSU.2 ⟨?_, ?_⟩
  · rw [hI6, Matrix.mul_one, coe_u6cGL, u6cBlk_map, u6cBlk_transpose, ← u6cBlk_mul, hu,
      u6cBlk_one]
  · rw [coe_u6cGL, u6cBlk_det, hdet]

private abbrev U6Shape (M : Matrix (Fin 6) (Fin 6) K) : Prop :=
  ∀ i j : Fin 6, (4 ≤ (i : ℕ) ∨ 4 ≤ (j : ℕ)) → M i j = if i = j then 1 else 0

private theorem u6cShape_blk (B : Matrix (Fin 4) (Fin 4) K) : U6Shape (u6cBlk B) :=
  fun _ _ hij => u6cBlk_apply_of_le B hij

private def u6cP (K : Type) [Field K] : Fin 6 → K := fun i => if (i : ℕ) < 4 then 1 else 0

private theorem u6cShape_iff {M : Matrix (Fin 6) (Fin 6) K} :
    U6Shape M ↔ M - 1 = diagonal (u6cP K) * (M - 1) * diagonal (u6cP K) := by
  have hP : ∀ i j : Fin 6, (diagonal (u6cP K) * (M - 1) * diagonal (u6cP K)) i j =
      u6cP K i * (M - 1) i j * u6cP K j := by
    intro i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  constructor
  · intro hM
    ext i j
    rw [hP]
    by_cases hij : 4 ≤ (i : ℕ) ∨ 4 ≤ (j : ℕ)
    · have h0 : (M - 1) i j = 0 := by
        rw [Matrix.sub_apply, hM i j hij, Matrix.one_apply, sub_self]
      rw [h0, mul_zero, zero_mul]
    · push Not at hij
      simp [u6cP, hij.1, hij.2]
  · intro hM i j hij
    have h1 := congrFun (congrFun hM i) j
    rw [hP] at h1
    have h0 : u6cP K i = 0 ∨ u6cP K j = 0 := by
      rcases hij with hi | hj
      · left
        unfold u6cP
        rw [if_neg (by omega)]
      · right
        unfold u6cP
        rw [if_neg (by omega)]
    have h2 : (M - 1) i j = 0 := by
      rcases h0 with h0 | h0
      · rw [h1, h0]
        ring
      · rw [h1, h0]
        ring
    rw [Matrix.sub_apply, Matrix.one_apply, sub_eq_zero] at h2
    exact h2

private def u6cD (ω : K) : Fin 6 → K := fun i => if (i : ℕ) < 4 then 1 else ω

private theorem u6cD_apply_lt (ω : K) {i : Fin 6} (hi : (i : ℕ) < 4) : u6cD ω i = 1 := by
  unfold u6cD
  exact if_pos hi

private theorem u6cD_apply_ge (ω : K) {i : Fin 6} (hi : 4 ≤ (i : ℕ)) : u6cD ω i = ω := by
  unfold u6cD
  exact if_neg (by omega)

private theorem u6cD_eq (ω : K) : u6cD ω = ![1, 1, 1, 1, ω, ω] := by
  funext i
  fin_cases i <;> first | rfl | simp [u6cD]

private theorem u6cComm_pm {ω : K} (hω1 : (1 : K) ≠ ω) {Y : Matrix (Fin 6) (Fin 6) K}
    (hY : diagonal (u6cD ω) * Y = Y * diagonal (u6cD ω)) :
    diagonal (u6cP K) * Y = Y * diagonal (u6cP K) := by
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hi : (i : ℕ) < 4 <;> by_cases hj : (j : ℕ) < 4
  · simp [u6cP, hi, hj]
  · have hne : u6cD ω i ≠ u6cD ω j := by
      rw [u6cD_apply_lt ω hi, u6cD_apply_ge ω (not_lt.1 hj)]
      exact hω1
    rw [apply_eq_zero_of_diagonal_comm hY hne]
    simp
  · have hne : u6cD ω i ≠ u6cD ω j := by
      rw [u6cD_apply_ge ω (not_lt.1 hi), u6cD_apply_lt ω hj]
      exact hω1.symm
    rw [apply_eq_zero_of_diagonal_comm hY hne]
    simp
  · simp [u6cP, hi, hj]

private noncomputable def u6cBlkP {ℓ f : ℕ} (h : UnitaryFieldData ℓ f K) :
    gramSU h (idGram K 4) →* primeFormP h (idGram K 6) :=
  (QuotientGroup.mk' _).comp
    ((u6cGL.comp (gramSU h (idGram K 4)).subtype).codRestrict (gramSU h (idGram K 6))
      (fun g => u6cGL_mem h g.2))

private theorem u6cBlkP_apply {ℓ f : ℕ} (h : UnitaryFieldData ℓ f K)
    (g : gramSU h (idGram K 4)) :
    u6cBlkP h g = ((⟨u6cGL (g : GL (Fin 4) K), u6cGL_mem h g.2⟩ : gramSU h (idGram K 6)) :
      primeFormP h (idGram K 6)) :=
  rfl

private theorem u6cBlkP_injective {ℓ f : ℕ} (h : UnitaryFieldData ℓ f K) :
    Function.Injective (u6cBlkP h) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  rw [u6cBlkP_apply] at hg
  obtain ⟨c, -, -, hc⟩ := mem_normOneScalars.1 ((QuotientGroup.eq_one_iff _).1 hg)
  have hc' : u6cGL (g : GL (Fin 4) K) = GeneralLinearGroup.scalar (Fin 6) c := hc
  have h55 : (c : K) = 1 := by
    have h1 := congrArg (fun A : GL (Fin 6) K => (A : Matrix (Fin 6) (Fin 6) K) 5 5) hc'
    simp only [coe_u6cGL, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq] at h1
    rw [u6cBlk_apply_of_le (i := 5) (j := 5) _ (Or.inl (by decide)), if_pos rfl] at h1
    exact h1.symm
  have hc1 : c = 1 := Units.ext h55
  rw [hc1, map_one] at hc'
  have hg1 : u6cBlk ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = u6cBlk 1 := by
    rw [u6cBlk_one]
    have h2 := congrArg Units.val hc'
    rwa [coe_u6cGL, Units.val_one] at h2
  have hg2 := u6cBlk_injective hg1
  exact Subtype.ext (Units.ext hg2)

private theorem u6cExists_gl {ℓ f : ℕ} (h : UnitaryFieldData ℓ f K) {Z : GL (Fin 6) K}
    (hZ : Z ∈ gramSU h (idGram K 6)) (hs : U6Shape (Z : Matrix (Fin 6) (Fin 6) K)) :
    ∃ g : GL (Fin 4) K, g ∈ gramSU h (idGram K 4) ∧ u6cGL g = Z := by
  obtain ⟨B, hB⟩ := u6cExists hs
  obtain ⟨hu, hdet⟩ := mem_gramSU.1 hZ
  have hI4 : idGram K 4 = (1 : Matrix (Fin 4) (Fin 4) K) := Units.val_one
  have hI6 : idGram K 6 = (1 : Matrix (Fin 6) (Fin 6) K) := Units.val_one
  have hdetB : B.det = 1 := by rw [← u6cBlk_det, ← hB, hdet]
  have hunit : IsUnit B :=
    (Matrix.isUnit_iff_isUnit_det B).2 (by rw [hdetB]; exact isUnit_one)
  refine ⟨hunit.unit, ?_, Units.ext (by rw [coe_u6cGL, IsUnit.unit_spec, ← hB])⟩
  refine mem_gramSU.2 ⟨?_, by rw [IsUnit.unit_spec, hdetB]⟩
  rw [hI4, Matrix.mul_one, IsUnit.unit_spec]
  rw [hI6, Matrix.mul_one, hB] at hu
  apply u6cBlk_injective
  rw [u6cBlk_mul, ← u6cBlk_transpose, ← u6cBlk_map, u6cBlk_one]
  exact hu

private theorem u6cConj {ω : K} (hω1 : (1 : K) ≠ ω) {ℓ f : ℕ} (h : UnitaryFieldData ℓ f K)
    {X₀ : primeFormUnitary h (idGram K 6)}
    (hX₀ : ((X₀ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = diagonal (u6cD ω))
    {u : GL (Fin 6) K} (hu : u ∈ gramSU h (idGram K 6))
    (hcomm : u * (X₀ : GL (Fin 6) K) = (X₀ : GL (Fin 6) K) * u)
    {g : GL (Fin 4) K} (hg : g ∈ gramSU h (idGram K 4)) :
    ∃ g'' : GL (Fin 4) K, g'' ∈ gramSU h (idGram K 4) ∧ u6cGL g'' = u * u6cGL g * u⁻¹ := by
  have hY : diagonal (u6cD ω) * (u : Matrix (Fin 6) (Fin 6) K) =
      (u : Matrix (Fin 6) (Fin 6) K) * diagonal (u6cD ω) := by
    have h1 := congrArg (fun g : GL (Fin 6) K => (g : Matrix (Fin 6) (Fin 6) K)) hcomm
    simp only [Units.val_mul, hX₀] at h1
    exact h1.symm
  have hpY := u6cComm_pm hω1 hY
  have hYY' : (u : Matrix (Fin 6) (Fin 6) K) *
      ((u⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hY'Y : ((u⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
      (u : Matrix (Fin 6) (Fin 6) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hpY' := u6cRing_comm_inv hpY hYY' hY'Y
  have hZmem : u * u6cGL g * u⁻¹ ∈ gramSU h (idGram K 6) :=
    mul_mem (mul_mem hu (u6cGL_mem h hg)) (inv_mem hu)
  have hshape : U6Shape ((u * u6cGL g * u⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by
    rw [Units.val_mul, Units.val_mul, coe_u6cGL]
    exact (u6cShape_iff).2 (u6cRing_conj_shape hpY hpY' hYY'
      ((u6cShape_iff).1 (u6cShape_blk ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))))
  exact u6cExists_gl h hZmem hshape

end U6Block

section U6Field

variable {K : Type} [Field K]

private theorem u6cPow3 (h : UnitaryFieldData 2 1 K) {c : K} (hc : c ≠ 0) : c ^ 3 = 1 := by
  have := h.finite
  have := Fintype.ofFinite K
  have hcard : Fintype.card K = 4 := by
    rw [← Nat.card_eq_fintype_card, h.card]
    norm_num
  have := FiniteField.pow_card_sub_one_eq_one c hc
  rwa [hcard] at this

private theorem u6cNorm (h : UnitaryFieldData 2 1 K) {c : K} (hc : c ≠ 0) : h.norm c = 1 := by
  rw [UnitaryFieldData.norm, h.bar_apply, pow_one, ← pow_succ', u6cPow3 h hc]

private theorem u6cOne_ne [CharP K 2] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) : (1 : K) ≠ ω := by
  intro h1
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  rw [← h1] at hω
  have h10 : (1 : K) = 0 := by linear_combination hω - h2
  exact one_ne_zero h10

private theorem u6cZeta [CharP K 2] {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    {Y : Matrix (Fin 6) (Fin 6) K} (hdet : Y.det ≠ 0) {c : K}
    (hY : ∀ i j, Y i j * u6cD ω j = u6cD ω i * Y i j * c) : c = 1 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hrow : ∀ i, ∃ j, Y i j ≠ 0 := by
    intro i
    by_contra hcon
    push Not at hcon
    exact hdet (Matrix.det_eq_zero_of_row_eq_zero i hcon)
  have hD : ∀ j, u6cD ω j = 1 ∨ u6cD ω j = ω := by
    intro j
    by_cases hj : (j : ℕ) < 4
    · exact Or.inl (u6cD_apply_lt ω hj)
    · exact Or.inr (u6cD_apply_ge ω (not_lt.1 hj))
  have hD0 : u6cD ω 0 = 1 := u6cD_apply_lt ω (i := 0) (by decide)
  have hD4 : u6cD ω 4 = ω := u6cD_apply_ge ω (i := 4) (by decide)
  obtain ⟨j₀, hj₀⟩ := hrow 0
  obtain ⟨j₁, hj₁⟩ := hrow 4
  have e0 : u6cD ω j₀ = c := by
    have h3 := hY 0 j₀
    rw [hD0, one_mul] at h3
    exact mul_left_cancel₀ hj₀ h3
  have e1 : u6cD ω j₁ = ω * c := by
    have h3 := hY 4 j₁
    rw [hD4] at h3
    have h4 : Y 4 j₁ * u6cD ω j₁ = Y 4 j₁ * (ω * c) := by
      rw [h3]
      ring
    exact mul_left_cancel₀ hj₁ h4
  rcases hD j₀ with h0 | h0
  · rw [← e0, h0]
  · exfalso
    have hc : c = ω := by rw [← e0, h0]
    rw [hc] at e1
    rcases hD j₁ with h1 | h1
    · rw [h1] at e1
      have hsq : ω ^ 2 = 1 := by
        rw [sq]
        exact e1.symm
      have hω0 : ω = 0 := by linear_combination hω - hsq - h2
      rw [hω0] at hω
      simp at hω
    · rw [h1] at e1
      have hsq : ω ^ 2 = ω := by
        rw [sq]
        exact e1.symm
      have h10 : (1 : K) = 0 := by linear_combination hω - hsq - ω * h2
      exact one_ne_zero h10

end U6Field

section U6Group

variable {K : Type} [Field K]

private theorem u6cComm [CharP K 2] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) {ℓ f : ℕ}
    (h : UnitaryFieldData ℓ f K) {X₀ : primeFormUnitary h (idGram K 6)}
    (hX₀ : ((X₀ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = diagonal (u6cD ω))
    {Y₁ : gramSU h (idGram K 6)}
    (hy : (Y₁ : primeFormP h (idGram K 6)) ∈
      fixSubgroup (primeFormConjHom h (idGram K 6) X₀)) :
    (Y₁ : GL (Fin 6) K) * (X₀ : GL (Fin 6) K) = (X₀ : GL (Fin 6) K) * (Y₁ : GL (Fin 6) K) := by
  rw [mem_fixSubgroup, primeFormConjHom_mk] at hy
  obtain ⟨c, -, -, hc⟩ := mem_normOneScalars.1 (QuotientGroup.eq.1 hy)
  have hc' : ((X₀ : GL (Fin 6) K) * (Y₁ : GL (Fin 6) K) * (X₀ : GL (Fin 6) K)⁻¹)⁻¹ *
      (Y₁ : GL (Fin 6) K) = GeneralLinearGroup.scalar (Fin 6) c := hc
  have e2 := u6cGrp (commute_scalar c (X₀ : GL (Fin 6) K)).eq hc'
  have e3 : ∀ i j, ((Y₁ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i j * u6cD ω j =
      u6cD ω i * ((Y₁ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i j * (c : K) := by
    intro i j
    have h1 := congrArg (fun g : GL (Fin 6) K => (g : Matrix (Fin 6) (Fin 6) K) i j) e2
    simpa only [Units.val_mul, hX₀, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.mul_diagonal, Matrix.diagonal_mul] using h1
  have hdet : ((Y₁ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det ≠ 0 := by
    rw [(mem_gramSU.1 Y₁.2).2]
    exact one_ne_zero
  have hc1 : c = 1 := Units.ext (u6cZeta hω hdet e3)
  rw [hc1, map_one, mul_one] at e2
  exact e2

private theorem u6cThree [CharP K 2] (h : UnitaryFieldData 2 1 K) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) : 3 ∣ Nat.card (gramSU h (idGram K 4)) := by
  have hω0 : ω ≠ 0 := by
    rintro rfl
    simp at hω
  have hω1 : (1 : K) ≠ ω := u6cOne_ne hω
  have h3 : ω * ω * ω = 1 := by
    have := u6cPow3 h hω0
    linear_combination this
  let dv : Fin 4 → Kˣ := ![Units.mk0 ω hω0, Units.mk0 ω hω0, Units.mk0 ω hω0, 1]
  have hnorm : ∀ i, h.norm ((dv i : Kˣ) : K) = 1 := fun i => u6cNorm h (dv i).ne_zero
  have hprod : ∏ i, ((dv i : Kˣ) : K) = 1 := by
    rw [Fin.prod_univ_four]
    show ω * ω * ω * 1 = 1
    rw [mul_one]
    exact h3
  let d : gramSU h (idGram K 4) :=
    ⟨CFSG.RankThree.Classical.unitaryDiagGL dv,
      CFSG.RankThree.Classical.unitaryDiagGL_mem_gramSU h hnorm hprod⟩
  have hd3 : d ^ 3 = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, Subgroup.coe_one, Units.val_one]
    show (diagonal fun i => ((dv i : Kˣ) : K)) ^ 3 = 1
    rw [Matrix.diagonal_pow, ← Matrix.diagonal_one]
    congr 1
    funext i
    show ((dv i : Kˣ) : K) ^ 3 = 1
    exact u6cPow3 h (dv i).ne_zero
  have hd1 : d ≠ 1 := by
    intro h1
    have h1' := congrArg
      (fun A : gramSU h (idGram K 4) => ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 0) h1
    have h2 : ω = 1 := h1'
    exact hω1 h2.symm
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [← orderOf_eq_prime hd3 hd1]
  exact orderOf_dvd_natCard d

end U6Group

section CoreSix

variable {K : Type} [Field K] [CharP K 2] [Finite K]

theorem mk_mem_fixSubgroup_of_block (h : UnitaryFieldData 2 1 K)
    {X : primeFormUnitary h (idGram K 6)} {e : Fin 6 → K}
    (hX : ((X : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = diagonal e)
    (he : ∀ i : Fin 6, (i : ℕ) < 4 → e i = 1) (g : gramSU h (idGram K 6))
    (hg : ∀ i j : Fin 6, (4 ≤ (i : ℕ) ∨ 4 ≤ (j : ℕ)) →
      ((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i j = if i = j then 1 else 0) :
    (g : primeFormP h (idGram K 6)) ∈ fixSubgroup (primeFormConjHom h (idGram K 6) X) := by
  have hXg : (X : GL (Fin 6) K) * (g : GL (Fin 6) K) = (g : GL (Fin 6) K) * (X : GL (Fin 6) K) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hX]
    ext i j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hij : 4 ≤ (i : ℕ) ∨ 4 ≤ (j : ℕ)
    · rw [hg i j hij]
      split_ifs with hij'
      · rw [hij', mul_one, one_mul]
      · rw [mul_zero, zero_mul]
    · push Not at hij
      rw [he i hij.1, he j hij.2, one_mul, mul_one]
  rw [mem_fixSubgroup, primeFormConjHom_mk]
  congr 1
  apply Subtype.ext
  show (X : GL (Fin 6) K) * (g : GL (Fin 6) K) * (X : GL (Fin 6) K)⁻¹ = (g : GL (Fin 6) K)
  rw [hXg, mul_inv_cancel_right]

theorem glaPLayer_ne_bot_six (h : UnitaryFieldData 2 1 K) {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    {X₀ : primeFormUnitary h (idGram K 6)}
    (hX₀ : ((X₀ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = diagonal ![1, 1, 1, 1, ω, ω])
    {Y : Subgroup (primeFormP h (idGram K 6))}
    (hYX : Y ≤ fixSubgroup (primeFormConjHom h (idGram K 6) X₀))
    (hJY : ∀ g : gramSU h (idGram K 6),
      (∀ i j : Fin 6, (4 ≤ (i : ℕ) ∨ 4 ≤ (j : ℕ)) →
        ((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i j = if i = j then 1 else 0) →
      (g : primeFormP h (idGram K 6)) ∈ Y) :
    GLAPLayer 3 Y ≠ ⊥ := by
  rw [← u6cD_eq] at hX₀
  set N4 := normOneScalars h (gramSU h (idGram K 4)) 4 with hN4
  have hinj4 : Function.Injective (QuotientGroup.mk' N4) := primeFormP_mk_injective_four h
  obtain ⟨φ, hφdef⟩ : ∃ φ : gramSU h (idGram K 4) →* primeFormP h (idGram K 6),
      φ = u6cBlkP h := ⟨_, rfl⟩
  have hφ : ∀ g : gramSU h (idGram K 4), φ g =
      ((⟨u6cGL (g : GL (Fin 4) K), u6cGL_mem h g.2⟩ : gramSU h (idGram K 6)) :
        primeFormP h (idGram K 6)) := fun g => by rw [hφdef]; rfl
  have hφinj : Function.Injective φ := by
    rw [hφdef]
    exact u6cBlkP_injective h
  have hJY' : φ.range ≤ Y := by
    rintro _ ⟨g, rfl⟩
    rw [hφ]
    refine hJY _ fun i j hij => ?_
    show u6cBlk ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i j = _
    exact u6cBlk_apply_of_le _ hij
  have hJn : (φ.range.subgroupOf Y).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hJY']
    rintro _ y ⟨g, rfl⟩ hy
    obtain ⟨Y₁, rfl⟩ := QuotientGroup.mk_surjective y
    have hcomm := u6cComm hω h hX₀ (hYX hy)
    obtain ⟨g'', hg'', hZ⟩ := u6cConj (u6cOne_ne hω) h hX₀ Y₁.2 hcomm g.2
    refine ⟨⟨g'', hg''⟩, ?_⟩
    rw [hφ, hφ, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext hZ
  haveI : IsSimpleGroup (primeFormP h (idGram K 4)) :=
    CFSG.RankThree.Classical.isSimpleGroup_primeFormP_one h (n := 4) (by norm_num) (by norm_num)
  let eP : gramSU h (idGram K 4) ≃* primeFormP h (idGram K 4) :=
    MulEquiv.ofBijective (QuotientGroup.mk' N4) ⟨hinj4, QuotientGroup.mk'_surjective N4⟩
  let eJ : gramSU h (idGram K 4) ≃* φ.range := MonoidHom.ofInjective hφinj
  haveI : IsSimpleGroup φ.range := (eP.symm.trans eJ).symm.isSimpleGroup
  have hnc : ∃ a b : φ.range, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    refine CFSG.RankThree.Classical.not_commute_primeFormP_one h (n := 4) (by norm_num)
      (by norm_num) fun x y => ?_
    apply (eP.symm.trans eJ).injective
    rw [map_mul, map_mul]
    exact hcon _ _
  have h3J : 3 ∣ Nat.card φ.range := by
    rw [← Nat.card_congr eJ.toEquiv]
    exact u6cThree h hω
  have hle := le_glaPLayer_of_normal_simple Nat.prime_three hJY' hJn hnc h3J
  intro hbot
  rw [hbot] at hle
  obtain ⟨a, b, hab⟩ := hnc
  apply hab
  have ha : a = 1 := Subtype.ext (Subgroup.mem_bot.1 (hle a.2))
  have hb : b = 1 := Subtype.ext (Subgroup.mem_bot.1 (hle b.2))
  rw [ha, hb]

end CoreSix

end CFSG.LocalAnalysis.GLTheoremA.HDescUniRes

end
