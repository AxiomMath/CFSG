module

public import CFSG.LieType.Steinberg.CentralExt.SUThree
public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.ClassicalInvolution.Phan

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg

section BlockMat

variable {F : Type*} [Field F] {m k i : ℕ}

@[expose] def blockSel (F : Type*) [Field F] (m k i : ℕ) : Matrix (Fin m) (Fin k) F :=
  Matrix.of fun a j => if a.val = i + j.val then 1 else 0

theorem blockSel_apply (a : Fin m) (j : Fin k) :
    blockSel F m k i a j = if a.val = i + j.val then 1 else 0 :=
  rfl

theorem blockSel_transpose_mul_self (h : i + k ≤ m) :
    (blockSel F m k i)ᵀ * blockSel F m k i = 1 := by
  ext j j'
  rw [mul_apply, one_apply]
  have hj : i + j.val < m := by have := j.isLt; omega
  rw [Finset.sum_eq_single (⟨i + j.val, hj⟩ : Fin m)]
  · simp only [transpose_apply, blockSel_apply, ite_true, one_mul]
    by_cases hjj : j = j'
    · subst hjj
      simp
    · have : ¬ (i + j.val = i + j'.val) := fun h' => hjj (Fin.ext (by omega))
      simp [hjj, Fin.val_inj]
  · intro a _ ha
    simp only [transpose_apply, blockSel_apply]
    have : ¬ a.val = i + j.val := fun h' => ha (Fin.ext (by simpa using h'))
    simp [this]
  · simp

@[expose] def blockMat (m i : ℕ) {k : ℕ} (A : Matrix (Fin k) (Fin k) F) :
    Matrix (Fin m) (Fin m) F :=
  1 + blockSel F m k i * (A - 1) * (blockSel F m k i)ᵀ

theorem blockMat_mul (h : i + k ≤ m) (A B : Matrix (Fin k) (Fin k) F) :
    blockMat m i (A * B) = blockMat m i A * blockMat m i B := by
  have hL := blockSel_transpose_mul_self (F := F) h
  unfold blockMat
  set L : Matrix (Fin m) (Fin k) F := blockSel F m k i
  have e1 : A * B - 1 = (A - 1) + (B - 1) + (A - 1) * (B - 1) := by noncomm_ring
  have e2 : (L * (A - 1) * Lᵀ) * (L * (B - 1) * Lᵀ) = L * ((A - 1) * (B - 1)) * Lᵀ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Lᵀ L (((B - 1) * Lᵀ)), hL, Matrix.one_mul]
  have hG : L * (A * B - 1) * Lᵀ =
      L * (A - 1) * Lᵀ + L * (B - 1) * Lᵀ + L * ((A - 1) * (B - 1)) * Lᵀ := by
    rw [e1, Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul]
  have key : ∀ E E' G : Matrix (Fin m) (Fin m) F, G = E + E' + E * E' →
      1 + G = (1 + E) * (1 + E') := by
    intro E E' G hG
    rw [hG]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one]
    abel
  exact key _ _ _ (by rw [hG, e2])

theorem blockMat_one : blockMat m i (1 : Matrix (Fin k) (Fin k) F) = 1 := by
  simp [blockMat]

theorem det_blockMat (h : i + k ≤ m) (A : Matrix (Fin k) (Fin k) F) :
    (blockMat m i A).det = A.det := by
  have hL := blockSel_transpose_mul_self (F := F) h
  unfold blockMat
  set L : Matrix (Fin m) (Fin k) F := blockSel F m k i
  rw [Matrix.mul_assoc, Matrix.det_one_add_mul_comm, Matrix.mul_assoc (A - 1) Lᵀ L, hL,
    Matrix.mul_one]
  simp

theorem conjTr_blockMat (σ : F ≃+* F) (A : Matrix (Fin k) (Fin k) F) :
    conjTr σ (blockMat m i A) = blockMat m i (conjTr σ A) := by
  have hL : (blockSel F m k i).map σ = blockSel F m k i := by
    ext a j
    simp only [Matrix.map_apply, blockSel_apply]
    split_ifs <;> simp
  have hLt : ((blockSel F m k i)ᵀ).map σ = (blockSel F m k i)ᵀ := by
    rw [Matrix.transpose_map, hL]
  have hN : (A - 1).map σ = A.map σ - 1 := by
    rw [Matrix.map_sub _ (map_sub σ), Matrix.map_one _ (map_zero σ) (map_one σ)]
  unfold blockMat conjTr
  rw [Matrix.map_add _ (map_add σ), Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.map_mul,
    Matrix.map_mul,
    hL, hLt, hN, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_mul,
    Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_sub,
    Matrix.transpose_one, Matrix.mul_assoc]

@[expose] def blockMatHom (m i : ℕ) (h : i + k ≤ m) :
    Matrix (Fin k) (Fin k) F →* Matrix (Fin m) (Fin m) F where
  toFun := blockMat m i
  map_one' := blockMat_one
  map_mul' := blockMat_mul h

@[expose] def blockGL (m i : ℕ) (h : i + k ≤ m) : GL (Fin k) F →* GL (Fin m) F :=
  Units.map (blockMatHom m i h)

theorem coe_blockGL (h : i + k ≤ m) (g : GL (Fin k) F) :
    ((blockGL m i h g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
      blockMat m i (g : Matrix (Fin k) (Fin k) F) :=
  rfl

theorem blockGL_mem_SUid (σ : F ≃+* F) (h : i + k ≤ m) {g : GL (Fin k) F} (hg : g ∈ SUid σ k) :
    blockGL m i h g ∈ SUid σ m := by
  obtain ⟨hdet, hiso⟩ := hg
  refine ⟨by rw [coe_blockGL, det_blockMat h, hdet], ?_⟩
  rw [coe_blockGL, conjTr_blockMat, ← blockMat_mul h, hiso, blockMat_one]

end BlockMat

section Defs

variable (K : Type) [Field K] [Finite K] (p f : ℕ) [Fact p.Prime] [CharP K p]

abbrev Su (d : ℕ) : Type := ↥(SUid (unitaryInvolution K p f) d)

@[expose] noncomputable def blockEmb (m k i : ℕ) (h : i + k ≤ m) : Su K p f k →* Su K p f m :=
  ((blockGL (F := K) m i h).comp (SUid (unitaryInvolution K p f) k).subtype).codRestrict _
    fun g => blockGL_mem_SUid _ h g.2

variable {K p f}

theorem coe_blockEmb {m k i : ℕ} (h : i + k ≤ m) (g : Su K p f k) :
    ((blockEmb K p f m k i h g : Su K p f m) : GL (Fin m) K) =
      blockGL m i h (g : GL (Fin k) K) :=
  rfl

theorem coe_coe_blockEmb {m k i : ℕ} (h : i + k ≤ m) (g : Su K p f k) :
    (((blockEmb K p f m k i h g : Su K p f m) : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) =
      blockMat m i (((g : Su K p f k) : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) :=
  rfl

variable (K p f)

@[expose] noncomputable def blockEmb2 (n : ℕ) (i : Fin n) : Su K p f 2 →* Su K p f (n + 1) :=
  blockEmb K p f (n + 1) 2 i (by omega)

@[expose] noncomputable def blockEmb3 (n : ℕ) (i : Fin n) (h : (i : ℕ) + 1 < n) :
    Su K p f 3 →* Su K p f (n + 1) :=
  blockEmb K p f (n + 1) 3 i (by omega)

@[expose] noncomputable def B12 : Subgroup (Su K p f 3) :=
  (embSUid (unitaryInvolution K p f) 2).range

@[expose] noncomputable def B23 : Subgroup (Su K p f 3) :=
  (embSUid (unitaryInvolution K p f) 0).range

@[expose] def UnitaryBlockStandardPair {X : Type} [Group X] (W U V : Subgroup X) : Prop :=
  ∃ (θ : Su K p f 3 →* X) (c : Su K p f 3), θ.range = W ∧ θ.ker ≤ Subgroup.center (Su K p f 3) ∧
    ((((B12 K p f).map (MulAut.conj c⁻¹).toMonoidHom).map θ = U ∧
      ((B23 K p f).map (MulAut.conj c⁻¹).toMonoidHom).map θ = V) ∨
     (((B12 K p f).map (MulAut.conj c⁻¹).toMonoidHom).map θ = V ∧
      ((B23 K p f).map (MulAut.conj c⁻¹).toMonoidHom).map θ = U))

structure WeakPhanA {X : Type} [Group X] (n : ℕ) (U : Fin n → Subgroup X)
    (W : Fin n → Fin n → Subgroup X) : Prop where
  iso : ∀ i, Nonempty (Su K p f 2 ≃* U i)
  join : ∀ i j, i < j → W i j = U i ⊔ U j
  comm : ∀ i j : Fin n, (i : ℕ) + 1 < j → ∀ x ∈ U i, ∀ y ∈ U j, x * y = y * x
  pair : ∀ i j : Fin n, (j : ℕ) = i + 1 → UnitaryBlockStandardPair K p f (W i j) (U i) (U j)
  gen : ⨆ i, U i = ⊤

@[expose] def AdjacentTripleFour {X : Type} [Group X] {n : ℕ} (W : Fin n → Fin n → Subgroup X) :
    Prop :=
  ∀ i j k : Fin n, (j : ℕ) = i + 1 → (k : ℕ) = j + 1 →
    ∃ θ : Su K p f 4 →* X, θ.range = W i j ⊔ W j k ∧ θ.ker ≤ Subgroup.center (Su K p f 4)

structure PhanFamily (Y : Type) [Group Y] (n : ℕ) where
  ι : Fin n → (Su K p f 2 →* Y)
  θ : Fin n → (Su K p f 3 →* Y)
  left : ∀ i : Fin n, (i : ℕ) + 1 < n →
    (θ i).comp (embSUid (unitaryInvolution K p f) 2) = ι i
  right : ∀ (i : Fin n) (h : (i : ℕ) + 1 < n),
    (θ i).comp (embSUid (unitaryInvolution K p f) 0) = ι ⟨i + 1, h⟩
  comm : ∀ i j : Fin n, (i : ℕ) + 1 < j → ∀ a b, ι i a * ι j b = ι j b * ι i a

@[expose] def PhanUniversalAt (n : ℕ) : Prop :=
  ∀ {Y : Type} [Group Y] (F : PhanFamily K p f Y n), ∃ ψ : Su K p f (n + 1) →* Y,
    (∀ i : Fin n, ψ.comp (blockEmb2 K p f n i) = F.ι i) ∧
    (∀ (i : Fin n) (h : (i : ℕ) + 1 < n), ψ.comp (blockEmb3 K p f n i h) = F.θ i)

end Defs

@[expose] def PhanUniversal : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (p f : ℕ) [Fact p.Prime] [CharP K p],
    Nat.card K = (p ^ f) ^ 2 → 5 ≤ p ^ f → ∀ {n : ℕ}, 3 ≤ n → PhanUniversalAt K p f n

@[expose] def WeakPhanUnitaryRecognitionOdd : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (p f : ℕ) [Fact p.Prime] [CharP K p],
    Nat.card K = (p ^ f) ^ 2 → p ≠ 2 → ∀ {n : ℕ}, 3 ≤ n →
    ∀ {X : Type} [Group X] {U : Fin n → Subgroup X} {W : Fin n → Fin n → Subgroup X},
      WeakPhanA K p f n U W →
      (5 ≤ p ^ f ∨ (p ^ f = 3 ∧ 4 ≤ n ∧ AdjacentTripleFour K p f W)) →
      ∃ θ : Su K p f (n + 1) →* X, Function.Surjective θ ∧
        θ.ker ≤ Subgroup.center (Su K p f (n + 1))

end CFSG.ClassicalInvolution.Phan
