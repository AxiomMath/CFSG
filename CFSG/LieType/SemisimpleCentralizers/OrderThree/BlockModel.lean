module

public import CFSG.LieType.SemisimpleCentralizers.OrderThree.Defs
public import CFSG.ClassicalGroups.UnitaryFlag.HyperbolicData

public section

namespace CFSG.LieType.SemisimpleCentralizers.OrderThree

open Matrix CFSG.Open CFSG.Open.StatedAPI CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag
open scoped commutatorElement

variable {p f : ℕ} {K : Type} [Field K] {a k : ℕ} {α β γ : K} {n : ℕ}

@[expose] def blockMat (X : Matrix (Fin a) (Fin a) K) (Y : Matrix (Fin k) (Fin k) K)
    (Z : Matrix (Fin a) (Fin a) K) : Matrix (HypIndex a k) (HypIndex a k) K :=
  fromBlocks X 0 0 (fromBlocks Y 0 0 Z)

theorem blockMat_mul (X X' : Matrix (Fin a) (Fin a) K) (Y Y' : Matrix (Fin k) (Fin k) K)
    (Z Z' : Matrix (Fin a) (Fin a) K) :
    blockMat X Y Z * blockMat X' Y' Z' = blockMat (X * X') (Y * Y') (Z * Z') := by
  simp [blockMat, fromBlocks_multiply]

theorem blockMat_one :
    blockMat (1 : Matrix (Fin a) (Fin a) K) (1 : Matrix (Fin k) (Fin k) K)
      (1 : Matrix (Fin a) (Fin a) K) = 1 := by
  simp only [blockMat, fromBlocks_one]

theorem blockMat_inj {X X' : Matrix (Fin a) (Fin a) K} {Y Y' : Matrix (Fin k) (Fin k) K}
    {Z Z' : Matrix (Fin a) (Fin a) K} :
    blockMat X Y Z = blockMat X' Y' Z' ↔ X = X' ∧ Y = Y' ∧ Z = Z' := by
  simp [blockMat, fromBlocks_inj, and_assoc]

theorem blockMat_det (X : Matrix (Fin a) (Fin a) K) (Y : Matrix (Fin k) (Fin k) K)
    (Z : Matrix (Fin a) (Fin a) K) : (blockMat X Y Z).det = X.det * Y.det * Z.det := by
  rw [blockMat, det_fromBlocks_zero₂₁, det_fromBlocks_zero₂₁, mul_assoc]

theorem blockMat_conjTranspose (h : UnitaryFieldData p f K) (X : Matrix (Fin a) (Fin a) K)
    (Y : Matrix (Fin k) (Fin k) K) (Z : Matrix (Fin a) (Fin a) K) :
    ((blockMat X Y Z).map h.bar)ᵀ =
      blockMat ((X.map h.bar)ᵀ) ((Y.map h.bar)ᵀ) ((Z.map h.bar)ᵀ) := by
  ext i j
  rcases i with i | (i | i) <;> rcases j with j | (j | j) <;> simp [blockMat]

theorem blockMat_diagonal_const (α β γ : K) :
    blockMat (diagonal (fun _ : Fin a => α)) (diagonal (fun _ : Fin k => β))
      (diagonal (fun _ : Fin a => γ)) = hypDiag a k α β γ := by
  simp only [blockMat, hypDiag, fromBlocks_diagonal]

theorem blockMat_smul_one (α β γ : K) :
    blockMat (α • (1 : Matrix (Fin a) (Fin a) K)) (β • (1 : Matrix (Fin k) (Fin k) K))
      (γ • (1 : Matrix (Fin a) (Fin a) K)) = hypDiag a k α β γ := by
  rw [smul_one_eq_diagonal, smul_one_eq_diagonal, smul_one_eq_diagonal, blockMat_diagonal_const]

@[expose] noncomputable def blockDiag (X : GL (Fin a) K) (Y : GL (Fin k) K) (Z : GL (Fin a) K) :
    GL (HypIndex a k) K :=
  ⟨blockMat (X : Matrix (Fin a) (Fin a) K) (Y : Matrix (Fin k) (Fin k) K)
      (Z : Matrix (Fin a) (Fin a) K),
    blockMat ((X⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)
      ((Y⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K)
      ((Z⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K),
    by simp only [blockMat_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, blockMat_one],
    by simp only [blockMat_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, blockMat_one]⟩

@[simp] theorem coe_blockDiag (X : GL (Fin a) K) (Y : GL (Fin k) K) (Z : GL (Fin a) K) :
    ((blockDiag X Y Z : GL (HypIndex a k) K) : Matrix (HypIndex a k) (HypIndex a k) K) =
      blockMat (X : Matrix (Fin a) (Fin a) K) (Y : Matrix (Fin k) (Fin k) K)
        (Z : Matrix (Fin a) (Fin a) K) := rfl

@[simp] theorem blockDiag_mul (X X' : GL (Fin a) K) (Y Y' : GL (Fin k) K) (Z Z' : GL (Fin a) K) :
    blockDiag X Y Z * blockDiag X' Y' Z' = blockDiag (X * X') (Y * Y') (Z * Z') := by
  apply Units.ext
  simp only [Units.val_mul, coe_blockDiag, blockMat_mul]

@[simp] theorem blockDiag_one :
    blockDiag (1 : GL (Fin a) K) (1 : GL (Fin k) K) (1 : GL (Fin a) K) = 1 := by
  apply Units.ext
  simp only [coe_blockDiag, blockMat_one, Units.val_one]

@[simp] theorem blockDiag_inv (X : GL (Fin a) K) (Y : GL (Fin k) K) (Z : GL (Fin a) K) :
    (blockDiag X Y Z)⁻¹ = blockDiag X⁻¹ Y⁻¹ Z⁻¹ := by
  exact inv_eq_of_mul_eq_one_right (by rw [blockDiag_mul]; simp)

theorem blockDiag_inj {X X' : GL (Fin a) K} {Y Y' : GL (Fin k) K} {Z Z' : GL (Fin a) K} :
    blockDiag X Y Z = blockDiag X' Y' Z' ↔ X = X' ∧ Y = Y' ∧ Z = Z' := by
  constructor
  · intro h
    have h' :=
      congrArg (fun u : GL (HypIndex a k) K => (u : Matrix (HypIndex a k) (HypIndex a k) K)) h
    rw [coe_blockDiag, coe_blockDiag, blockMat_inj] at h'
    exact ⟨Units.ext h'.1, Units.ext h'.2.1, Units.ext h'.2.2⟩
  · rintro ⟨rfl, rfl, rfl⟩; rfl

@[expose] noncomputable def starInv (h : UnitaryFieldData p f K) (X : GL (Fin a) K) :
    GL (Fin a) K :=
  ⟨(((X⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K).map h.bar)ᵀ,
    (((X : GL (Fin a) K) : Matrix (Fin a) (Fin a) K).map h.bar)ᵀ,
    by
      rw [← Matrix.transpose_mul, ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]
      simp,
    by
      rw [← Matrix.transpose_mul, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
      simp⟩

@[simp] theorem coe_starInv (h : UnitaryFieldData p f K) (X : GL (Fin a) K) :
    ((starInv h X : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) =
      (((X⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K).map h.bar)ᵀ := rfl

theorem starInv_mul (h : UnitaryFieldData p f K) (X Y : GL (Fin a) K) :
    starInv h (X * Y) = starInv h X * starInv h Y := by
  apply Units.ext
  simp only [coe_starInv, _root_.mul_inv_rev, Units.val_mul, Matrix.map_mul, Matrix.transpose_mul]

@[simp] theorem starInv_one (h : UnitaryFieldData p f K) :
    starInv h (1 : GL (Fin a) K) = 1 := by
  apply Units.ext
  simp [coe_starInv]

theorem starInv_inv (h : UnitaryFieldData p f K) (X : GL (Fin a) K) :
    starInv h X⁻¹ = (starInv h X)⁻¹ := by
  exact eq_inv_of_mul_eq_one_right (by rw [← starInv_mul, mul_inv_cancel, starInv_one])

theorem starInv_commutator (h : UnitaryFieldData p f K) (X X' : GL (Fin a) K) :
    starInv h X * starInv h X' * (starInv h X)⁻¹ * (starInv h X')⁻¹ =
      starInv h (X * X' * X⁻¹ * X'⁻¹) := by
  rw [starInv_mul, starInv_mul, starInv_mul, starInv_inv, starInv_inv]

@[expose] def hypDiagEntries (a k : ℕ) (α β γ : K) : HypIndex a k → K :=
  Sum.elim (fun _ => α) (Sum.elim (fun _ => β) (fun _ => γ))

theorem hypDiag_eq_diagonal (α β γ : K) :
    hypDiag a k α β γ = diagonal (hypDiagEntries a k α β γ) := rfl

@[simp] theorem hypDiagEntries_inl (i : Fin a) : hypDiagEntries a k α β γ (Sum.inl i) = α := rfl

@[simp] theorem hypDiagEntries_inr_inl (j : Fin k) :
    hypDiagEntries a k α β γ (Sum.inr (Sum.inl j)) = β := rfl

@[simp] theorem hypDiagEntries_inr_inr (i : Fin a) :
    hypDiagEntries a k α β γ (Sum.inr (Sum.inr i)) = γ := rfl

theorem commute_hypDiag_apply {g : Matrix (HypIndex a k) (HypIndex a k) K}
    (hg : Commute g (hypDiag a k α β γ)) (i j : HypIndex a k) :
    g i j * hypDiagEntries a k α β γ j = hypDiagEntries a k α β γ i * g i j := by
  have h := congrFun (congrFun hg.eq i) j
  simpa only [hypDiag_eq_diagonal, mul_diagonal, diagonal_mul] using h

theorem commute_hypDiag_apply_eq_zero {g : Matrix (HypIndex a k) (HypIndex a k) K}
    (hg : Commute g (hypDiag a k α β γ)) {i j : HypIndex a k}
    (hij : hypDiagEntries a k α β γ i ≠ hypDiagEntries a k α β γ j) : g i j = 0 := by
  have h := commute_hypDiag_apply hg i j
  have h' : g i j * (hypDiagEntries a k α β γ j - hypDiagEntries a k α β γ i) = 0 := by
    rw [mul_sub, h]; ring
  rcases mul_eq_zero.mp h' with h0 | h0
  · exact h0
  · exact absurd (sub_eq_zero.mp h0).symm hij

theorem eq_blockMat_of_commute_hypDiag (hαβ : α ≠ β) (hβγ : β ≠ γ) (hαγ : α ≠ γ)
    {g : Matrix (HypIndex a k) (HypIndex a k) K} (hg : Commute g (hypDiag a k α β γ)) :
    g = blockMat g.toBlocks₁₁ (g.toBlocks₂₂).toBlocks₁₁ (g.toBlocks₂₂).toBlocks₂₂ := by
  have h := fromBlocks_toBlocks g
  have h12 : g.toBlocks₁₂ = 0 := by
    ext i j
    rcases j with l | l
    · exact commute_hypDiag_apply_eq_zero hg (by simpa using hαβ)
    · exact commute_hypDiag_apply_eq_zero hg (by simpa using hαγ)
  have h21 : g.toBlocks₂₁ = 0 := by
    ext i j
    rcases i with l | l
    · exact commute_hypDiag_apply_eq_zero hg (by simpa using (Ne.symm hαβ))
    · exact commute_hypDiag_apply_eq_zero hg (by simpa using (Ne.symm hαγ))
  have hE12 : (g.toBlocks₂₂).toBlocks₁₂ = 0 := by
    ext i j
    exact commute_hypDiag_apply_eq_zero hg (by simpa using hβγ)
  have hE21 : (g.toBlocks₂₂).toBlocks₂₁ = 0 := by
    ext i j
    exact commute_hypDiag_apply_eq_zero hg (by simpa using (Ne.symm hβγ))
  rw [h12, h21] at h
  conv_lhs => rw [← h]
  rw [blockMat, fromBlocks_inj]
  exact ⟨rfl, rfl, rfl, (fromBlocks_toBlocks (g.toBlocks₂₂)).symm.trans (by rw [hE12, hE21])⟩

theorem blockMat_star_mul_hypGram (h : UnitaryFieldData p f K)
    (X : Matrix (Fin a) (Fin a) K) (Y : Matrix (Fin k) (Fin k) K)
    (Z : Matrix (Fin a) (Fin a) K) :
    blockMat ((X.map h.bar)ᵀ) ((Y.map h.bar)ᵀ) ((Z.map h.bar)ᵀ) * hypGram a k K =
      fromBlocks 0 (fromCols 0 ((X.map h.bar)ᵀ)) (fromRows 0 ((Z.map h.bar)ᵀ))
        (fromBlocks ((Y.map h.bar)ᵀ) 0 0 0) := by
  simp [blockMat, hypGram, fromBlocks_multiply, mul_fromCols, fromBlocks_mul_fromRows]

theorem blockMat_star_mul_hypGram_mul (h : UnitaryFieldData p f K)
    (X : Matrix (Fin a) (Fin a) K) (Y : Matrix (Fin k) (Fin k) K)
    (Z : Matrix (Fin a) (Fin a) K) :
    fromBlocks 0 (fromCols 0 ((X.map h.bar)ᵀ)) (fromRows 0 ((Z.map h.bar)ᵀ))
        (fromBlocks ((Y.map h.bar)ᵀ) 0 0 0) * blockMat X Y Z =
      fromBlocks 0 (fromCols 0 ((X.map h.bar)ᵀ * Z))
        (fromRows 0 ((Z.map h.bar)ᵀ * X))
        (fromBlocks ((Y.map h.bar)ᵀ * Y) 0 0 0) := by
  simp [blockMat, fromBlocks_multiply, fromCols_mul_fromBlocks, fromRows_mul]

theorem blockMat_conjTranspose_mul_hypGram_mul (h : UnitaryFieldData p f K)
    (X : Matrix (Fin a) (Fin a) K) (Y : Matrix (Fin k) (Fin k) K)
    (Z : Matrix (Fin a) (Fin a) K) :
    ((blockMat X Y Z).map h.bar)ᵀ * hypGram a k K * blockMat X Y Z =
      fromBlocks 0 (fromCols 0 ((X.map h.bar)ᵀ * Z))
        (fromRows 0 ((Z.map h.bar)ᵀ * X))
        (fromBlocks ((Y.map h.bar)ᵀ * Y) 0 0 0) := by
  rw [blockMat_conjTranspose, blockMat_star_mul_hypGram, blockMat_star_mul_hypGram_mul]

theorem blockDiag_mem_hypSU_iff {h : UnitaryFieldData p f K}
    (X : GL (Fin a) K) (Y : GL (Fin k) K) (Z : GL (Fin a) K) :
    blockDiag X Y Z ∈ hypSU h a k ↔
      ((X : Matrix (Fin a) (Fin a) K).map h.bar)ᵀ * (Z : Matrix (Fin a) (Fin a) K) = 1 ∧
      ((Y : Matrix (Fin k) (Fin k) K).map h.bar)ᵀ * (Y : Matrix (Fin k) (Fin k) K) = 1 ∧
      ((Z : Matrix (Fin a) (Fin a) K).map h.bar)ᵀ * (X : Matrix (Fin a) (Fin a) K) = 1 ∧
      (X : Matrix (Fin a) (Fin a) K).det * (Y : Matrix (Fin k) (Fin k) K).det *
        (Z : Matrix (Fin a) (Fin a) K).det = 1 := by
  rw [mem_hypSU]
  constructor
  · rintro ⟨hiso, hdet⟩
    rw [coe_blockDiag, blockMat_conjTranspose_mul_hypGram_mul, hypGram] at hiso
    have hb := fromBlocks_inj.mp hiso
    refine ⟨(fromCols_inj.eq_iff.mp hb.2.1).2, (fromBlocks_inj.mp hb.2.2.2).1,
      (fromRows_inj.eq_iff.mp hb.2.2.1).2, ?_⟩
    rw [coe_blockDiag, blockMat_det] at hdet
    exact hdet
  · rintro ⟨hXZ, hYY, hZX, hdet⟩
    refine ⟨?_, ?_⟩
    · rw [coe_blockDiag, blockMat_conjTranspose_mul_hypGram_mul, hXZ, hYY, hZX, hypGram]
    · rw [coe_blockDiag, blockMat_det, hdet]

theorem blockDiag_one_mem_hypSU (h : UnitaryFieldData p f K) {Y : GL (Fin k) K}
    (hY : Y ∈ unitarySU p f K k) : blockDiag 1 Y 1 ∈ hypSU h a k := by
  rw [blockDiag_mem_hypSU_iff]
  obtain ⟨hdet, huni⟩ := (mem_unitarySU_iff h).mp hY
  exact ⟨by simp, huni, by simp, by simp [hdet]⟩

theorem starInv_map_transpose (h : UnitaryFieldData p f K) (X : GL (Fin a) K) :
    (((starInv h X : GL (Fin a) K) : Matrix (Fin a) (Fin a) K).map h.bar)ᵀ =
      ((X⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) := by
  simp only [coe_starInv, Matrix.transpose_map, Matrix.transpose_transpose]
  ext i j
  simp [h.bar_bar]

theorem blockDiag_starInv_mem_hypSU (h : UnitaryFieldData p f K) {X : GL (Fin a) K}
    (hX : X ∈ StatedSL a K) : blockDiag X 1 (starInv h X) ∈ hypSU h a k := by
  rw [blockDiag_mem_hypSU_iff]
  have hdetX : (X : Matrix (Fin a) (Fin a) K).det = 1 := mem_statedSL_iff.mp hX
  have hXinv : ((X⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K).det =
      ((X : Matrix (Fin a) (Fin a) K).det)⁻¹ := by
    have h := congrArg Matrix.det (show ((X⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) *
        (X : Matrix (Fin a) (Fin a) K) = 1 from by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one])
    rw [Matrix.det_mul, Matrix.det_one] at h
    exact eq_inv_of_mul_eq_one_left h
  have hdetS : ((starInv h X : GL (Fin a) K) : Matrix (Fin a) (Fin a) K).det = 1 := by
    rw [coe_starInv, Matrix.det_transpose]
    have h1 : (((X⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K).map h.bar).det =
        h.bar (((X⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K).det) := by
      simpa using (RingHom.map_det h.bar
        ((X⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)).symm
    rw [h1, hXinv, map_inv₀, hdetX, map_one, inv_one]
  refine ⟨?_, by simp, ?_, ?_⟩
  · rw [coe_starInv, ← Matrix.transpose_mul, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel,
      Units.val_one]
    simp
  · rw [starInv_map_transpose, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  · rw [hdetX, hdetS]
    simp

def hypUnitary (h : UnitaryFieldData p f K) (n : ℕ) : Subgroup (GL (Fin n) K) where
  carrier := {U | ((U : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * (U : Matrix (Fin n) (Fin n) K) = 1}
  mul_mem' {U V} hU hV := by
    have hU' : ((U : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * (U : Matrix (Fin n) (Fin n) K) = 1 :=
      hU
    have hV' : ((V : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * (V : Matrix (Fin n) (Fin n) K) = 1 :=
      hV
    change ((↑(U * V) : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
      (↑(U * V) : Matrix (Fin n) (Fin n) K) = 1
    rw [Units.val_mul, Matrix.map_mul, Matrix.transpose_mul]
    simp only [mul_assoc]
    nth_rewrite 2 [← mul_assoc]
    rw [hU', Matrix.one_mul]
    exact hV'
  one_mem' := by simp
  inv_mem' {U} hU := by
    have hU' : ((U : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * (U : Matrix (Fin n) (Fin n) K) = 1 :=
      hU
    have hU'' : (U : Matrix (Fin n) (Fin n) K) * ((U : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ = 1 :=
      mul_eq_one_comm.mp hU'
    have hUinv : (U : Matrix (Fin n) (Fin n) K)⁻¹ =
        ((U : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ := Matrix.inv_eq_right_inv hU''
    have hmap :
        ((U : Matrix (Fin n) (Fin n) K).map h.bar).map h.bar = (U : Matrix (Fin n) (Fin n) K) := by
      ext i j
      simp [h.bar_bar]
    change ((↑U⁻¹ : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * (↑U⁻¹ : Matrix (Fin n) (Fin n) K) = 1
    rw [GeneralLinearGroup.coe_inv, hUinv, Matrix.transpose_map, hmap, Matrix.transpose_transpose]
    exact hU''

theorem mem_hypUnitary {h : UnitaryFieldData p f K} {n : ℕ} {U : GL (Fin n) K} :
    U ∈ hypUnitary h n ↔ ((U : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
      (U : Matrix (Fin n) (Fin n) K) = 1 := Iff.rfl

theorem det_commutator_eq_one (A B : GL (Fin n) K) :
    ((⁅A, B⁆ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 := by
  have h : GeneralLinearGroup.det ⁅A, B⁆ = 1 := by
    rw [commutatorElement_def]
    simp only [map_mul, map_inv]
    simp [mul_comm, mul_left_comm, mul_assoc]
  rw [← GeneralLinearGroup.val_det_apply, h, Units.val_one]

theorem commutator_mem_unitarySU (h : UnitaryFieldData p f K) {n : ℕ} {U V : GL (Fin n) K}
    (hU : U ∈ hypUnitary h n) (hV : V ∈ hypUnitary h n) :
    ⁅U, V⁆ ∈ unitarySU p f K n := by
  have hmem : ⁅U, V⁆ ∈ hypUnitary h n := by
    rw [commutatorElement_def]
    exact (hypUnitary h n).mul_mem
      ((hypUnitary h n).mul_mem ((hypUnitary h n).mul_mem hU hV) ((hypUnitary h n).inv_mem hU))
      ((hypUnitary h n).inv_mem hV)
  rw [mem_unitarySU_iff h]
  exact ⟨det_commutator_eq_one U V, mem_hypUnitary.mp hmem⟩

@[expose] noncomputable def phi1Hom (h : UnitaryFieldData p f K) (a k : ℕ) :
    unitarySU p f K k →* hypSU h a k where
  toFun Y := ⟨blockDiag 1 (Y : GL (Fin k) K) 1, blockDiag_one_mem_hypSU h Y.2⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    simp [coe_blockDiag]
  map_mul' Y Y' := by
    apply Subtype.ext
    apply Units.ext
    simp [coe_blockDiag, blockDiag_mul]

@[expose] noncomputable def phi2Hom (h : UnitaryFieldData p f K) (a k : ℕ) :
    StatedSL a K →* hypSU h a k where
  toFun X := ⟨blockDiag (X : GL (Fin a) K) 1 (starInv h (X : GL (Fin a) K)),
    blockDiag_starInv_mem_hypSU h X.2⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    simp [coe_blockDiag]
  map_mul' X X' := by
    apply Subtype.ext
    apply Units.ext
    simp [coe_blockDiag, starInv_mul, blockDiag_mul]

@[simp] theorem coe_phi1Hom (h : UnitaryFieldData p f K) (Y : unitarySU p f K k) :
    ((phi1Hom h a k Y : hypSU h a k) : GL (HypIndex a k) K) =
      blockDiag 1 (Y : GL (Fin k) K) 1 := rfl

@[simp] theorem coe_phi2Hom (h : UnitaryFieldData p f K) (X : StatedSL a K) :
    ((phi2Hom h a k X : hypSU h a k) : GL (HypIndex a k) K) =
      blockDiag (X : GL (Fin a) K) 1 (starInv h (X : GL (Fin a) K)) := rfl

theorem phi1Hom_injective (h : UnitaryFieldData p f K) : Function.Injective (phi1Hom h a k) := by
  intro Y Y' hYY'
  have h' := congrArg (fun x : hypSU h a k => ((x : GL (HypIndex a k) K) :
    Matrix (HypIndex a k) (HypIndex a k) K)) hYY'
  rw [coe_phi1Hom, coe_phi1Hom, coe_blockDiag, coe_blockDiag, blockMat_inj] at h'
  exact Subtype.ext (Units.ext h'.2.1)

theorem phi2Hom_injective (h : UnitaryFieldData p f K) : Function.Injective (phi2Hom h a k) := by
  intro X X' hXX'
  have h' := congrArg (fun x : hypSU h a k => ((x : GL (HypIndex a k) K) :
    Matrix (HypIndex a k) (HypIndex a k) K)) hXX'
  rw [coe_phi2Hom, coe_phi2Hom, coe_blockDiag, coe_blockDiag, blockMat_inj] at h'
  exact Subtype.ext (Units.ext h'.1)

theorem blockDiag_one_commute_hypDiag (Y : GL (Fin k) K) :
    Commute ((blockDiag 1 Y 1 : GL (HypIndex a k) K) : Matrix (HypIndex a k) (HypIndex a k) K)
      (hypDiag a k α β γ) := by
  rw [commute_iff_eq, coe_blockDiag, ← blockMat_smul_one, blockMat_mul, blockMat_mul, blockMat_inj]
  refine ⟨by simp, ?_, by simp⟩
  rw [mul_smul_comm, smul_mul_assoc, mul_one, one_mul]

theorem blockDiag_starInv_commute_hypDiag (h : UnitaryFieldData p f K) (X : GL (Fin a) K) :
    Commute ((blockDiag X 1 (starInv h X) : GL (HypIndex a k) K) :
      Matrix (HypIndex a k) (HypIndex a k) K) (hypDiag a k α β γ) := by
  rw [commute_iff_eq, coe_blockDiag, ← blockMat_smul_one, blockMat_mul, blockMat_mul, blockMat_inj]
  refine ⟨by simp, by simp, ?_⟩
  rw [mul_smul_comm, smul_mul_assoc, mul_one, one_mul]

theorem exists_blockDiag_of_mem_hypSU_of_commute {h : UnitaryFieldData p f K}
    (hαβ : α ≠ β) (hβγ : β ≠ γ) (hαγ : α ≠ γ)
    {g : hypSU h a k}
    (hg : Commute ((g : GL (HypIndex a k) K) : Matrix (HypIndex a k) (HypIndex a k) K)
      (hypDiag a k α β γ)) :
    ∃ X : GL (Fin a) K, ∃ Y : GL (Fin k) K, ∃ Z : GL (Fin a) K,
      (g : GL (HypIndex a k) K) = blockDiag X Y Z ∧
      ((Y : Matrix (Fin k) (Fin k) K).map h.bar)ᵀ * (Y : Matrix (Fin k) (Fin k) K) = 1 ∧
      Z = starInv h X := by
  set M : Matrix (HypIndex a k) (HypIndex a k) K :=
    ((g : GL (HypIndex a k) K) : Matrix (HypIndex a k) (HypIndex a k) K) with hM
  have hgM : Commute M (hypDiag a k α β γ) := by rw [hM]; exact hg
  have hblock : M = blockMat M.toBlocks₁₁ (M.toBlocks₂₂).toBlocks₁₁ (M.toBlocks₂₂).toBlocks₂₂ :=
    eq_blockMat_of_commute_hypDiag hαβ hβγ hαγ hgM
  set X0 : Matrix (Fin a) (Fin a) K := M.toBlocks₁₁ with hX0
  set Y0 : Matrix (Fin k) (Fin k) K := (M.toBlocks₂₂).toBlocks₁₁ with hY0
  set Z0 : Matrix (Fin a) (Fin a) K := (M.toBlocks₂₂).toBlocks₂₂ with hZ0
  have hblock' : M = blockMat X0 Y0 Z0 := by rw [hblock, hX0, hY0, hZ0]
  have hiso : (M.map h.bar)ᵀ * hypGram a k K * M = hypGram a k K := by
    rw [hM]; exact (mem_hypSU.mp g.2).1
  rw [hblock', blockMat_conjTranspose_mul_hypGram_mul, hypGram] at hiso
  have hb := fromBlocks_inj.mp hiso
  have hXZ : (X0.map h.bar)ᵀ * Z0 = 1 := (fromCols_inj.eq_iff.mp hb.2.1).2
  have hZX : (Z0.map h.bar)ᵀ * X0 = 1 := (fromRows_inj.eq_iff.mp hb.2.2.1).2
  have hYY : (Y0.map h.bar)ᵀ * Y0 = 1 := (fromBlocks_inj.mp hb.2.2.2).1
  have hg_inv : Commute (((g : GL (HypIndex a k) K) : Matrix (HypIndex a k) (HypIndex a k) K)⁻¹)
      (hypDiag a k α β γ) := by
    have h := hg.units_inv_left
    rwa [GeneralLinearGroup.coe_inv] at h
  have hblock_inv : ((g : GL (HypIndex a k) K)⁻¹ : Matrix (HypIndex a k) (HypIndex a k) K) =
      blockMat (((g : GL (HypIndex a k) K)⁻¹ : Matrix (HypIndex a k) (HypIndex a k) K).toBlocks₁₁)
        ((((g : GL (HypIndex a k) K)⁻¹ :
          Matrix (HypIndex a k) (HypIndex a k) K).toBlocks₂₂).toBlocks₁₁)
        ((((g : GL (HypIndex a k) K)⁻¹ :
          Matrix (HypIndex a k) (HypIndex a k) K).toBlocks₂₂).toBlocks₂₂) :=
    eq_blockMat_of_commute_hypDiag hαβ hβγ hαγ hg_inv
  set W1 : Matrix (Fin a) (Fin a) K :=
    ((g : GL (HypIndex a k) K)⁻¹ : Matrix (HypIndex a k) (HypIndex a k) K).toBlocks₁₁ with hW1
  set W2 : Matrix (Fin k) (Fin k) K :=
    (((g : GL (HypIndex a k) K)⁻¹ :
      Matrix (HypIndex a k) (HypIndex a k) K).toBlocks₂₂).toBlocks₁₁ with hW2
  set W3 : Matrix (Fin a) (Fin a) K :=
    (((g : GL (HypIndex a k) K)⁻¹ :
      Matrix (HypIndex a k) (HypIndex a k) K).toBlocks₂₂).toBlocks₂₂ with hW3
  have hblock_inv' : ((g : GL (HypIndex a k) K)⁻¹ : Matrix (HypIndex a k) (HypIndex a k) K) =
      blockMat W1 W2 W3 := by rw [hblock_inv, hW1, hW2, hW3]
  have hgg : blockMat X0 Y0 Z0 * blockMat W1 W2 W3 = 1 := by
    rw [← hblock', ← hblock_inv', hM, ← GeneralLinearGroup.coe_inv, ← Units.val_mul,
      mul_inv_cancel, Units.val_one]
  have hg'g : blockMat W1 W2 W3 * blockMat X0 Y0 Z0 = 1 := by
    rw [← hblock_inv', ← hblock', hM, ← GeneralLinearGroup.coe_inv, ← Units.val_mul,
      inv_mul_cancel, Units.val_one]
  rw [blockMat_mul, ← blockMat_one, blockMat_inj] at hgg hg'g
  let Xgl : GL (Fin a) K := ⟨X0, W1, hgg.1, hg'g.1⟩
  let Ygl : GL (Fin k) K := ⟨Y0, W2, hgg.2.1, hg'g.2.1⟩
  let Zgl : GL (Fin a) K := ⟨Z0, W3, hgg.2.2, hg'g.2.2⟩
  refine ⟨Xgl, Ygl, Zgl, ?_, hYY, ?_⟩
  · apply Units.ext
    rw [← hM, hblock']
    rfl
  · apply Units.ext
    have hXZ' : ((X0.map h.bar)ᵀ) * Z0 = 1 := hXZ
    have hXgl : (Xgl : Matrix (Fin a) (Fin a) K) = X0 := rfl
    have hprod : ((X0.map h.bar)ᵀ) *
        (((Xgl⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K).map h.bar)ᵀ = 1 := by
      rw [← hXgl, ← Matrix.transpose_mul, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel,
        Units.val_one]
      simp
    change Z0 = (((Xgl⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K).map h.bar)ᵀ
    rw [← Matrix.inv_eq_right_inv hXZ', Matrix.inv_eq_right_inv hprod]

theorem commutator_blockDiag (h : UnitaryFieldData p f K) {X X' Z Z' : GL (Fin a) K}
    {Y Y' : GL (Fin k) K} (hZ : Z = starInv h X) (hZ' : Z' = starInv h X') :
    ⁅blockDiag X Y Z, blockDiag X' Y' Z'⁆ =
      blockDiag ⁅X, X'⁆ ⁅Y, Y'⁆ (starInv h ⁅X, X'⁆) := by
  rw [commutatorElement_def, commutatorElement_def, blockDiag_inv, blockDiag_inv, blockDiag_mul,
    blockDiag_mul, blockDiag_mul, blockDiag_inj]
  refine ⟨rfl, rfl, ?_⟩
  rw [hZ, hZ']
  exact starInv_commutator h X X'

theorem commutator_hypSU_eq (h : UnitaryFieldData p f K) {x y : hypSU h a k}
    {X X' Z Z' : GL (Fin a) K} {Y Y' : GL (Fin k) K}
    (hx : (x : GL (HypIndex a k) K) = blockDiag X Y Z)
    (hy : (y : GL (HypIndex a k) K) = blockDiag X' Y' Z')
    (hZ : Z = starInv h X) (hZ' : Z' = starInv h X') :
    ((⁅x, y⁆ : hypSU h a k) : GL (HypIndex a k) K) =
      blockDiag ⁅X, X'⁆ ⁅Y, Y'⁆ (starInv h ⁅X, X'⁆) := by
  rw [commutatorElement_def]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hx, hy]
  exact commutator_blockDiag h hZ hZ'

theorem exists_hypSU_blocks {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) (a k : ℕ)
    {α β γ : K} (hαβ : α ≠ β) (hβγ : β ≠ γ) (hαγ : α ≠ γ) :
    ∃ M₁ M₂ : Subgroup ↥(hypSU h a k),
      (∀ x ∈ M₁, Commute ((x : GL (HypIndex a k) K) : Matrix (HypIndex a k) (HypIndex a k) K)
        (hypDiag a k α β γ)) ∧
      (∀ x ∈ M₂, Commute ((x : GL (HypIndex a k) K) : Matrix (HypIndex a k) (HypIndex a k) K)
        (hypDiag a k α β γ)) ∧
      (∀ x ∈ M₁, ∀ y ∈ M₂, Commute x y) ∧
      (∀ x y : ↥(hypSU h a k),
        Commute ((x : GL (HypIndex a k) K) : Matrix (HypIndex a k) (HypIndex a k) K)
          (hypDiag a k α β γ) →
        Commute ((y : GL (HypIndex a k) K) : Matrix (HypIndex a k) (HypIndex a k) K)
          (hypDiag a k α β γ) →
        ⁅x, y⁆ ∈ M₁ ⊔ M₂) ∧
      Nonempty (M₁ ≃* StatedSU k (p ^ f) K) ∧ Nonempty (M₂ ≃* StatedSL a K) := by
  refine ⟨(phi1Hom h a k).range, (phi2Hom h a k).range, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro x ⟨Y, rfl⟩
    exact blockDiag_one_commute_hypDiag (K := K) (a := a) (k := k) (α := α) (β := β) (γ := γ)
      (Y : GL (Fin k) K)
  · rintro x ⟨X, rfl⟩
    exact blockDiag_starInv_commute_hypDiag (K := K) (a := a) (k := k) (α := α) (β := β) (γ := γ)
      h (X : GL (Fin a) K)
  · rintro x ⟨Y, rfl⟩ y ⟨X, rfl⟩
    show Commute (phi1Hom h a k Y) (phi2Hom h a k X)
    rw [commute_iff_eq]
    apply Subtype.ext
    change blockDiag 1 (Y : GL (Fin k) K) 1 * blockDiag (X : GL (Fin a) K) 1
        (starInv h (X : GL (Fin a) K)) =
      blockDiag (X : GL (Fin a) K) 1 (starInv h (X : GL (Fin a) K)) *
        blockDiag 1 (Y : GL (Fin k) K) 1
    rw [blockDiag_mul, blockDiag_mul]
    simp
  · intro x y hx hy
    obtain ⟨X, Y, Z, hx_eq, hY, hZ⟩ :=
      exists_blockDiag_of_mem_hypSU_of_commute hαβ hβγ hαγ hx
    obtain ⟨X', Y', Z', hy_eq, hY', hZ'⟩ :=
      exists_blockDiag_of_mem_hypSU_of_commute hαβ hβγ hαγ hy
    have hmemY : (Y : GL (Fin k) K) ∈ hypUnitary h k := hY
    have hmemY' : (Y' : GL (Fin k) K) ∈ hypUnitary h k := hY'
    have hB : ⁅Y, Y'⁆ ∈ unitarySU p f K k := commutator_mem_unitarySU h hmemY hmemY'
    have hA : ⁅X, X'⁆ ∈ StatedSL a K := by
      rw [mem_statedSL_iff]
      exact det_commutator_eq_one X X'
    have hcomm_eq : ⁅x, y⁆ = phi2Hom h a k ⟨⁅X, X'⁆, hA⟩ * phi1Hom h a k ⟨⁅Y, Y'⁆, hB⟩ := by
      apply Subtype.ext
      rw [commutator_hypSU_eq h hx_eq hy_eq hZ hZ']
      simp [coe_blockDiag, blockDiag_mul]
    rw [hcomm_eq]
    have hmem2 : phi2Hom h a k ⟨⁅X, X'⁆, hA⟩ ∈ (phi2Hom h a k).range :=
      MonoidHom.mem_range.mpr ⟨⟨⁅X, X'⁆, hA⟩, rfl⟩
    have hmem1 : phi1Hom h a k ⟨⁅Y, Y'⁆, hB⟩ ∈ (phi1Hom h a k).range :=
      MonoidHom.mem_range.mpr ⟨⟨⁅Y, Y'⁆, hB⟩, rfl⟩
    have hmem := Subgroup.mul_mem_sup hmem2 hmem1
    rwa [sup_comm] at hmem
  · exact ⟨(MonoidHom.ofInjective (phi1Hom_injective (a := a) (k := k) h)).symm⟩
  · exact ⟨(MonoidHom.ofInjective (phi2Hom_injective (a := a) (k := k) h)).symm⟩

end CFSG.LieType.SemisimpleCentralizers.OrderThree
