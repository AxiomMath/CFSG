module

public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryHermitian
public import Mathlib.Data.Matrix.ColumnRowPartitioned

public section

namespace CFSG.ClassicalGroups.UnitaryFlag

open Matrix CFSG.LocalAnalysis.ComponentInitial

abbrev HypIndex (r ε : ℕ) : Type := Fin r ⊕ Fin ε ⊕ Fin r

variable {r ε : ℕ}

@[expose] def hypPartner : HypIndex r ε → HypIndex r ε
  | .inl i => .inr (.inr i)
  | .inr (.inl k) => .inr (.inl k)
  | .inr (.inr i) => .inl i

@[simp] theorem hypPartner_inl (i : Fin r) :
    hypPartner (.inl i : HypIndex r ε) = .inr (.inr i) := rfl

@[simp] theorem hypPartner_inr_inl (k : Fin ε) :
    hypPartner (.inr (.inl k) : HypIndex r ε) = .inr (.inl k) := rfl

@[simp] theorem hypPartner_inr_inr (i : Fin r) :
    hypPartner (.inr (.inr i) : HypIndex r ε) = .inl i := rfl

@[simp] theorem hypPartner_hypPartner (a : HypIndex r ε) : hypPartner (hypPartner a) = a := by
  rcases a with i | k | i <;> rfl

theorem hypPartner_involutive : Function.Involutive (hypPartner (r := r) (ε := ε)) :=
  hypPartner_hypPartner

theorem hypPartner_injective : Function.Injective (hypPartner (r := r) (ε := ε)) :=
  hypPartner_involutive.injective

theorem hypPartner_eq_iff {a b : HypIndex r ε} : hypPartner a = b ↔ a = hypPartner b :=
  ⟨fun h => by rw [← h, hypPartner_hypPartner], fun h => by rw [h, hypPartner_hypPartner]⟩

variable (r ε) (K : Type*) [Field K]

@[expose] def hypGram : Matrix (HypIndex r ε) (HypIndex r ε) K :=
  fromBlocks 0 (fromCols 0 1) (fromRows 0 1) (fromBlocks 1 0 0 0)

variable {r ε K}

theorem hypGram_apply (a b : HypIndex r ε) :
    hypGram r ε K a b = if b = hypPartner a then 1 else 0 := by
  rcases a with i | k | i <;> rcases b with j | l | j <;>
    simp [hypGram, one_apply, eq_comm]

@[simp] theorem hypGram_inl_inl (i j : Fin r) : hypGram r ε K (.inl i) (.inl j) = 0 := by
  simp [hypGram]

@[simp] theorem hypGram_inl_inr_inl (i : Fin r) (l : Fin ε) :
    hypGram r ε K (.inl i) (.inr (.inl l)) = 0 := by
  simp [hypGram]

@[simp] theorem hypGram_inl_inr_inr (i j : Fin r) :
    hypGram r ε K (.inl i) (.inr (.inr j)) = if i = j then 1 else 0 := by
  simp [hypGram, one_apply]

@[simp] theorem hypGram_inr_inl_inl (k : Fin ε) (j : Fin r) :
    hypGram r ε K (.inr (.inl k)) (.inl j) = 0 := by
  simp [hypGram]

@[simp] theorem hypGram_inr_inl_inr_inl (k l : Fin ε) :
    hypGram r ε K (.inr (.inl k)) (.inr (.inl l)) = if k = l then 1 else 0 := by
  simp [hypGram, one_apply]

@[simp] theorem hypGram_inr_inl_inr_inr (k : Fin ε) (j : Fin r) :
    hypGram r ε K (.inr (.inl k)) (.inr (.inr j)) = 0 := by
  simp [hypGram]

@[simp] theorem hypGram_inr_inr_inl (i j : Fin r) :
    hypGram r ε K (.inr (.inr i)) (.inl j) = if i = j then 1 else 0 := by
  simp [hypGram, one_apply]

@[simp] theorem hypGram_inr_inr_inr_inl (i : Fin r) (l : Fin ε) :
    hypGram r ε K (.inr (.inr i)) (.inr (.inl l)) = 0 := by
  simp [hypGram]

@[simp] theorem hypGram_inr_inr_inr_inr (i j : Fin r) :
    hypGram r ε K (.inr (.inr i)) (.inr (.inr j)) = 0 := by
  simp [hypGram]

theorem hypGram_mulVec (y : HypIndex r ε → K) (a : HypIndex r ε) :
    (hypGram r ε K *ᵥ y) a = y (hypPartner a) := by
  simp [mulVec, dotProduct, hypGram_apply]

theorem hypGram_mul_apply (M : Matrix (HypIndex r ε) (HypIndex r ε) K) (a b : HypIndex r ε) :
    (hypGram r ε K * M) a b = M (hypPartner a) b := by
  simp [mul_apply, hypGram_apply]

theorem mul_hypGram_apply (M : Matrix (HypIndex r ε) (HypIndex r ε) K) (a b : HypIndex r ε) :
    (M * hypGram r ε K) a b = M a (hypPartner b) := by
  simp only [mul_apply, hypGram_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (hypPartner b)]
  · simp
  · intro c _ hc
    rw [ite_eq_right_iff]
    rintro rfl
    exact absurd (hypPartner_hypPartner c).symm hc
  · simp

theorem hypGram_mul_self : hypGram r ε K * hypGram r ε K = 1 := by
  ext a b
  rw [hypGram_mul_apply, hypGram_apply, hypPartner_hypPartner, one_apply]
  by_cases hab : a = b <;> simp [hab, eq_comm]

theorem hypGram_transpose : (hypGram r ε K)ᵀ = hypGram r ε K := by
  ext a b
  simp only [transpose_apply, hypGram_apply]
  by_cases hab : a = hypPartner b
  · rw [ite_eq_left hab, ite_eq_left (hypPartner_eq_iff.mpr hab).symm]
  · rw [ite_eq_right hab, ite_eq_right fun h' => hab (hypPartner_eq_iff.mp h'.symm)]

theorem hypGram_map {L : Type*} [Field L] (σ : K →+* L) :
    (hypGram r ε K).map σ = hypGram r ε L := by
  ext a b
  simp only [map_apply, hypGram_apply]
  split_ifs <;> simp

theorem det_hypGram_ne_zero : (hypGram r ε K).det ≠ 0 := by
  intro h
  have := congrArg det (hypGram_mul_self (r := r) (ε := ε) (K := K))
  rw [det_mul, h, zero_mul, det_one] at this
  exact zero_ne_one this

variable {p f : ℕ} {ι : Type*} [Fintype ι]

@[expose] noncomputable def gramForm (h : UnitaryFieldData p f K) (G : Matrix ι ι K) :
    (ι → K) →ₛₗ[h.bar] (ι → K) →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ h.bar (RingHom.id K) (fun x y => (fun a => h.bar (x a)) ⬝ᵥ (G *ᵥ y))
    (fun x x' y => by simp only [Pi.add_apply, map_add]; exact add_dotProduct _ _ _)
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul, map_mul]
      exact smul_dotProduct (h.bar c) (fun a => h.bar (x a)) _)
    (fun x y y' => by simp only [mulVec_add, dotProduct_add])
    (fun c x y => by simp only [mulVec_smul, dotProduct_smul, RingHom.id_apply])

theorem gramForm_apply (h : UnitaryFieldData p f K) (G : Matrix ι ι K) (x y : ι → K) :
    gramForm h G x y = (fun a => h.bar (x a)) ⬝ᵥ (G *ᵥ y) :=
  rfl

theorem gramForm_mulVec {κ : Type*} [Fintype κ] (h : UnitaryFieldData p f K)
    (G : Matrix κ κ K) (M : Matrix κ ι K) (x y : ι → K) :
    gramForm h G (M *ᵥ x) (M *ᵥ y) = gramForm h ((M.map h.bar)ᵀ * G * M) x y := by
  rw [gramForm_apply, gramForm_apply]
  have hx : (fun a => h.bar ((M *ᵥ x) a)) = M.map h.bar *ᵥ fun a => h.bar (x a) := by
    funext a
    simp [mulVec, dotProduct, map_sum]
  rw [hx, ← vecMul_transpose (M.map h.bar), ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec,
    Matrix.mul_assoc]

theorem gramForm_single [DecidableEq ι] (h : UnitaryFieldData p f K) (G : Matrix ι ι K)
    (a b : ι) : gramForm h G (Pi.single a 1) (Pi.single b 1) = G a b := by
  rw [gramForm_apply]
  have : (fun c => h.bar ((Pi.single a (1 : K) : ι → K) c)) = Pi.single a 1 := by
    funext c
    by_cases hc : c = a
    · subst hc
      simp
    · simp [hc]
  rw [this, single_dotProduct, one_mul, mulVec_single_one, col_apply]

theorem gramForm_injective [DecidableEq ι] (h : UnitaryFieldData p f K) {G G' : Matrix ι ι K}
    (hGG' : ∀ x y, gramForm h G x y = gramForm h G' x y) : G = G' := by
  ext a b
  rw [← gramForm_single h G, ← gramForm_single h G', hGG']

theorem gramForm_isometry_iff [DecidableEq ι] (h : UnitaryFieldData p f K) (G M : Matrix ι ι K) :
    (∀ x y, gramForm h G (M *ᵥ x) (M *ᵥ y) = gramForm h G x y) ↔ (M.map h.bar)ᵀ * G * M = G := by
  constructor
  · intro hM
    exact gramForm_injective h fun x y => by rw [← gramForm_mulVec, hM]
  · intro hM x y
    rw [gramForm_mulVec, hM]

theorem gramForm_isSymm (h : UnitaryFieldData p f K) {G : Matrix ι ι K}
    (hG : (G.map h.bar)ᵀ = G) : (gramForm h G).IsSymm := by
  refine ⟨fun x y => ?_⟩
  simp only [gramForm_apply, dotProduct, mulVec, map_sum, map_mul, UnitaryFieldData.bar_bar,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have hab : h.bar (G b a) = G a b := by
    have := congrFun (congrFun hG a) b
    simpa using this
  rw [hab]
  ring

theorem gramForm_separatingLeft [DecidableEq ι] (h : UnitaryFieldData p f K) {G : Matrix ι ι K}
    (hG : G.det ≠ 0) : (gramForm h G).SeparatingLeft := by
  intro x hx
  have hv : (fun a => h.bar (x a)) ᵥ* G = 0 := by
    funext b
    have := hx (Pi.single b 1)
    rw [gramForm_apply, mulVec_single_one] at this
    simpa [vecMul, dotProduct, mul_comm] using this
  have hv' : (fun a => h.bar (x a)) = 0 :=
    eq_zero_of_vecMul_eq_zero hG hv
  funext a
  have := congrFun hv' a
  simpa [UnitaryFieldData.bar_eq_zero_iff] using this

theorem conjTranspose_mul_mul (h : UnitaryFieldData p f K) (G A B : Matrix ι ι K) :
    ((A * B).map h.bar)ᵀ * G * (A * B) = (B.map h.bar)ᵀ * (((A.map h.bar)ᵀ * G * A)) * B := by
  rw [Matrix.map_mul, transpose_mul]
  simp only [Matrix.mul_assoc]

variable [DecidableEq ι]

@[expose] def gramSU (h : UnitaryFieldData p f K) (G : Matrix ι ι K) : Subgroup (GL ι K) where
  carrier := {g | ((g : Matrix ι ι K).map h.bar)ᵀ * G * g = G ∧ (g : Matrix ι ι K).det = 1}
  mul_mem' {g g'} hg hg' := by
    refine ⟨?_, by rw [Units.val_mul, det_mul, hg.2, hg'.2, one_mul]⟩
    rw [Units.val_mul, conjTranspose_mul_mul, hg.1, hg'.1]
  one_mem' := ⟨by simp, by simp⟩
  inv_mem' {g} hg := by
    have hgg : (g : Matrix ι ι K) * ((g⁻¹ : GL ι K) : Matrix ι ι K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    refine ⟨?_, ?_⟩
    · have := conjTranspose_mul_mul h G (g : Matrix ι ι K) ((g⁻¹ : GL ι K) : Matrix ι ι K)
      rw [hg.1, hgg] at this
      simpa using this.symm
    · have := congrArg det hgg
      rwa [det_mul, hg.2, one_mul, det_one] at this

theorem mem_gramSU {h : UnitaryFieldData p f K} {G : Matrix ι ι K} {g : GL ι K} :
    g ∈ gramSU h G ↔ ((g : Matrix ι ι K).map h.bar)ᵀ * G * g = G ∧ (g : Matrix ι ι K).det = 1 :=
  Iff.rfl

theorem mem_gramSU_iff_isometry {h : UnitaryFieldData p f K} {G : Matrix ι ι K} {g : GL ι K} :
    g ∈ gramSU h G ↔ (∀ x y, gramForm h G ((g : Matrix ι ι K) *ᵥ x) ((g : Matrix ι ι K) *ᵥ y) =
      gramForm h G x y) ∧ (g : Matrix ι ι K).det = 1 := by
  rw [mem_gramSU, gramForm_isometry_iff]

theorem toLin_mem_sesqSpecialUnitaryGroup_iff (h : UnitaryFieldData p f K) (G : Matrix ι ι K)
    (g : GL ι K) :
    Matrix.GeneralLinearGroup.toLin g ∈ sesqSpecialUnitaryGroup (gramForm h G) ↔
      g ∈ gramSU h G := by
  rw [mem_sesqSpecialUnitaryGroup, mem_sesqUnitaryGroup, mem_gramSU_iff_isometry,
    Matrix.GeneralLinearGroup.coe_toLin, ← Matrix.toLin'_apply', LinearMap.det_toLin']
  simp only [Matrix.toLin'_apply]

theorem card_gramSU (h : UnitaryFieldData p f K) (G : Matrix ι ι K) :
    Nat.card (gramSU h G) = Nat.card (sesqSpecialUnitaryGroup (gramForm h G)) := by
  refine Nat.card_congr ((Matrix.GeneralLinearGroup.toLin.toEquiv.subtypeEquiv fun g => ?_))
  exact (toLin_mem_sesqSpecialUnitaryGroup_iff h G g).symm

noncomputable abbrev hypForm (h : UnitaryFieldData p f K) (r ε : ℕ) :
    (HypIndex r ε → K) →ₛₗ[h.bar] (HypIndex r ε → K) →ₗ[K] K :=
  gramForm h (hypGram r ε K)

theorem hypForm_apply (h : UnitaryFieldData p f K) (x y : HypIndex r ε → K) :
    hypForm h r ε x y = ∑ a, h.bar (x a) * y (hypPartner a) := by
  simp [gramForm_apply, dotProduct, hypGram_mulVec]

theorem hypGram_conjTranspose (h : UnitaryFieldData p f K) :
    ((hypGram r ε K).map h.bar)ᵀ = hypGram r ε K := by
  rw [hypGram_map, hypGram_transpose]

theorem hypForm_isSymm (h : UnitaryFieldData p f K) : (hypForm h r ε).IsSymm :=
  gramForm_isSymm h (hypGram_conjTranspose h)

theorem hypForm_separatingLeft (h : UnitaryFieldData p f K) : (hypForm h r ε).SeparatingLeft :=
  gramForm_separatingLeft h det_hypGram_ne_zero

end CFSG.ClassicalGroups.UnitaryFlag
