module

public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Matrix Subgroup

@[expose] def kperm : Fin 4 → Equiv.Perm (Fin 4) :=
  ![1, Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.swap 0 2 * Equiv.swap 1 3,
    Equiv.swap 0 3 * Equiv.swap 1 2]

theorem kperm_mul : ∀ g h : Fin 4, ∃ k : Fin 4, kperm g * kperm h = kperm k := by decide

theorem kperm_sq : ∀ g : Fin 4, kperm g * kperm g = 1 := by decide

theorem kperm_zero_apply : ∀ g : Fin 4, kperm g 0 = g := by decide

theorem kperm_sign : ∀ g : Fin 4, Equiv.Perm.sign (kperm g) = 1 := by decide

theorem kperm_eq_zero_iff : ∀ j k : Fin 4, (0 : Fin 4) = kperm j k ↔ j = k := by decide

theorem kperm_inv (j : Fin 4) : (kperm j)⁻¹ = kperm j := inv_eq_of_mul_eq_one_right (kperm_sq j)

theorem kperm_zero : kperm 0 = 1 := rfl

section Mono

variable {K : Type} [Field K]

@[expose] def mono (σ : Equiv.Perm (Fin 4)) (ε : Fin 4 → K) : Matrix (Fin 4) (Fin 4) K :=
  Matrix.of fun i j => if i = σ j then ε j else 0

theorem mono_mul (σ τ : Equiv.Perm (Fin 4)) (ε δ : Fin 4 → K) :
    mono σ ε * mono τ δ = mono (σ * τ) (fun k => ε (τ k) * δ k) := by
  ext i k
  simp only [mono, Matrix.mul_apply, Matrix.of_apply, Equiv.Perm.mul_apply]
  rw [Finset.sum_eq_single (τ k)]
  · by_cases h : i = σ (τ k) <;> simp [h]
  · intro j _ hj
    simp [hj]
  · simp

theorem mono_one_eq : mono (1 : Equiv.Perm (Fin 4)) (fun _ => (1 : K)) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [mono, Matrix.one_apply, h]

theorem mono_mulVec (σ : Equiv.Perm (Fin 4)) (ε w : Fin 4 → K) (i : Fin 4) :
    (mono σ ε *ᵥ w) i = ε (σ⁻¹ i) * w (σ⁻¹ i) := by
  simp only [Matrix.mulVec, dotProduct, mono, Matrix.of_apply]
  rw [Finset.sum_eq_single (σ⁻¹ i)]
  · simp
  · intro j _ hj
    have : ¬ i = σ j := fun h => hj (by rw [h]; simp)
    simp [this]
  · simp

theorem mono_kperm_zero_mulVec (ε w : Fin 4 → K) (i : Fin 4) :
    (mono (kperm 0) ε *ᵥ w) i = ε i * w i := by
  rw [mono_mulVec, kperm_zero, inv_one]
  rfl

theorem mono_one_perm_eq (σ : Equiv.Perm (Fin 4)) :
    mono σ (fun _ => (1 : K)) = (σ⁻¹).permMatrix K := by
  ext i j
  simp only [mono, Matrix.of_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
  have key : i = σ j ↔ σ⁻¹ i = j := by
    constructor
    · intro h
      rw [h]
      simp
    · intro h
      rw [← h]
      simp
  by_cases h : i = σ j
  · simp only [eq_true h, eq_true (key.1 h), ↓reduceIte]
  · simp only [eq_false h, eq_false (fun h' => h (key.2 h')), ↓reduceIte]

theorem mono_eq_mul_diagonal (σ : Equiv.Perm (Fin 4)) (ε : Fin 4 → K) :
    mono σ ε = mono σ (fun _ => 1) * Matrix.diagonal ε := by
  ext i j
  simp [mono, Matrix.mul_diagonal]

theorem det_mono_kperm (g : Fin 4) (ε : Fin 4 → K) : (mono (kperm g) ε).det = ∏ i, ε i := by
  rw [mono_eq_mul_diagonal, Matrix.det_mul, mono_one_perm_eq, Matrix.det_permutation,
    Matrix.det_diagonal, Equiv.Perm.sign_inv, kperm_sign]
  simp

@[expose] def IsSgn (A : Matrix (Fin 4) (Fin 4) K) : Prop :=
  ∃ (g : Fin 4) (ε : Fin 4 → K), (∀ i, ε i = 1 ∨ ε i = -1) ∧ A = mono (kperm g) ε

theorem pm_mul {a b : K} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    a * b = 1 ∨ a * b = -1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp

theorem pm_mul_self {a : K} (ha : a = 1 ∨ a = -1) : a * a = 1 := by
  rcases ha with rfl | rfl <;> simp

theorem IsSgn.mul {A B : Matrix (Fin 4) (Fin 4) K} (hA : IsSgn A) (hB : IsSgn B) :
    IsSgn (A * B) := by
  obtain ⟨g, ε, hε, rfl⟩ := hA
  obtain ⟨h, δ, hδ, rfl⟩ := hB
  obtain ⟨k, hk⟩ := kperm_mul g h
  exact ⟨k, fun i => ε (kperm h i) * δ i, fun i => pm_mul (hε _) (hδ _), by rw [mono_mul, hk]⟩

theorem isSgn_one : IsSgn (1 : Matrix (Fin 4) (Fin 4) K) :=
  ⟨0, fun _ => 1, fun _ => Or.inl rfl, by rw [← mono_one_eq]; rfl⟩

theorem IsSgn.inv {A : GL (Fin 4) K} (hA : IsSgn (A : Matrix (Fin 4) (Fin 4) K)) :
    IsSgn ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
  obtain ⟨g, ε, hε, hAe⟩ := hA
  refine ⟨g, fun k => ε (kperm g k), fun i => hε _, ?_⟩
  rw [Matrix.GeneralLinearGroup.coe_inv]
  apply Matrix.inv_eq_left_inv
  rw [hAe, mono_mul, kperm_sq, ← mono_one_eq]
  congr 1
  funext k
  have hk : kperm g (kperm g k) = k := by
    have := congrArg (fun σ : Equiv.Perm (Fin 4) => σ k) (kperm_sq g)
    simpa using this
  simp only [hk]
  exact pm_mul_self (hε k)

variable (K) in
@[expose] def sgnGroup : Subgroup (GL (Fin 4) K) where
  carrier := {A | IsSgn (A : Matrix (Fin 4) (Fin 4) K)}
  mul_mem' := fun {A B} hA hB => by
    have := IsSgn.mul hA hB
    simpa using this
  one_mem' := by simpa using isSgn_one
  inv_mem' := fun {A} hA => IsSgn.inv hA

theorem sgn_pow_four {A : GL (Fin 4) K} (hA : A ∈ sgnGroup K) : A ^ 4 = 1 := by
  obtain ⟨g, ε, hε, hAe⟩ := hA
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one, hAe]
  have hk : ∀ k, kperm g (kperm g k) = k := fun k => by
    have := congrArg (fun σ : Equiv.Perm (Fin 4) => σ k) (kperm_sq g)
    simpa using this
  have h2 : mono (kperm g) ε * mono (kperm g) ε =
      mono 1 (fun k => ε (kperm g k) * ε k) := by
    rw [mono_mul, kperm_sq]
  have h4 : mono (1 : Equiv.Perm (Fin 4)) (fun k => ε (kperm g k) * ε k) *
      mono 1 (fun k => ε (kperm g k) * ε k) = 1 := by
    rw [mono_mul, mul_one, ← mono_one_eq]
    congr 1
    funext k
    exact pm_mul_self (pm_mul (hε _) (hε _))
  have e4 : ∀ M : Matrix (Fin 4) (Fin 4) K, M ^ 4 = (M * M) * (M * M) := fun M => by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [e4, h2, h4]

theorem isPGroup_sgnGroup : IsPGroup 2 ↥(sgnGroup K) := fun A =>
  ⟨2, Subtype.ext (by simpa using sgn_pow_four A.2)⟩

@[expose] def monoGL (g : Fin 4) (ε : Fin 4 → K) (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    GL (Fin 4) K where
  val := mono (kperm g) ε
  inv := mono (kperm g) (fun k => ε (kperm g k))
  val_inv := by
    have hk : ∀ k, kperm g (kperm g k) = k := fun k => by
      have := congrArg (fun σ : Equiv.Perm (Fin 4) => σ k) (kperm_sq g)
      simpa using this
    rw [mono_mul, kperm_sq, ← mono_one_eq]
    congr 1
    funext k
    exact pm_mul_self (hε _)
  inv_val := by
    have hk : ∀ k, kperm g (kperm g k) = k := fun k => by
      have := congrArg (fun σ : Equiv.Perm (Fin 4) => σ k) (kperm_sq g)
      simpa using this
    rw [mono_mul, kperm_sq, ← mono_one_eq]
    congr 1
    funext k
    simp only [hk]
    exact pm_mul_self (hε k)

theorem coe_monoGL (g : Fin 4) (ε : Fin 4 → K) (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    ((monoGL g ε hε : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = mono (kperm g) ε := rfl

theorem monoGL_mem_sgnGroup (g : Fin 4) (ε : Fin 4 → K) (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    monoGL g ε hε ∈ sgnGroup K := ⟨g, ε, hε, rfl⟩

theorem eq_bot_or_top_of_sgn_invariant (h2 : (2 : K) ≠ 0) (W : Submodule K (Fin 4 → K))
    (hW : ∀ (g : Fin 4) (ε : Fin 4 → K), (∀ i, ε i = 1 ∨ ε i = -1) →
      ε 0 * ε 1 * ε 2 * ε 3 = 1 → ∀ w ∈ W, mono (kperm g) ε *ᵥ w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra h
    exact hw0 (funext fun j => by_contra fun hj => h ⟨j, hj⟩)
  have hperm : ∀ j : Fin 4, ∀ v ∈ W, mono (kperm j) (fun _ => (1 : K)) *ᵥ v ∈ W := fun j v hv =>
    hW j (fun _ => 1) (fun _ => Or.inl rfl) (by simp) v hv
  have hw'W : mono (kperm i) (fun _ => (1 : K)) *ᵥ w ∈ W := hperm i w hwW
  have hw'0 : (mono (kperm i) (fun _ => (1 : K)) *ᵥ w) 0 = w i := by
    rw [mono_mulVec, kperm_inv, kperm_zero_apply, one_mul]
  set w' := mono (kperm i) (fun _ => (1 : K)) *ᵥ w with hw'
  let da : Fin 4 → K := ![1, 1, -1, -1]
  let db : Fin 4 → K := ![1, -1, 1, -1]
  have hdaW : ∀ v ∈ W, mono (kperm 0) da *ᵥ v ∈ W := fun v hv =>
    hW 0 da (by intro j; fin_cases j <;> simp [da]) (by simp [da]) v hv
  have hdbW : ∀ v ∈ W, mono (kperm 0) db *ᵥ v ∈ W := fun v hv =>
    hW 0 db (by intro j; fin_cases j <;> simp [db]) (by simp [db]) v hv
  have hw1 : w' + mono (kperm 0) da *ᵥ w' ∈ W := W.add_mem hw'W (hdaW _ hw'W)
  have hw2 : (w' + mono (kperm 0) da *ᵥ w') + mono (kperm 0) db *ᵥ (w' + mono (kperm 0) da *ᵥ w')
      ∈ W := W.add_mem hw1 (hdbW _ hw1)
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h2
  have hw0' : w' 0 ≠ 0 := by rw [hw'0]; exact hi
  have hvec : (w' + mono (kperm 0) da *ᵥ w') +
      mono (kperm 0) db *ᵥ (w' + mono (kperm 0) da *ᵥ w') =
        (4 * w' 0) • (fun k : Fin 4 => if (0 : Fin 4) = k then (1 : K) else 0) := by
    funext k
    simp only [Pi.add_apply, mono_kperm_zero_mulVec, Pi.smul_apply, smul_eq_mul]
    fin_cases k <;> simp [da, db]
    ring
  have he0 : (fun k : Fin 4 => if (0 : Fin 4) = k then (1 : K) else 0) ∈ W := by
    have := W.smul_mem (4 * w' 0)⁻¹ hw2
    rw [hvec, smul_smul, inv_mul_cancel₀ (mul_ne_zero h4 hw0'), one_smul] at this
    exact this
  have he : ∀ j : Fin 4, (fun k : Fin 4 => if j = k then (1 : K) else 0) ∈ W := by
    intro j
    have := hperm j _ he0
    convert this using 1
    funext k
    rw [mono_mulVec, kperm_inv]
    simp only [one_mul]
    by_cases hjk : j = k
    · have : (0 : Fin 4) = kperm j k := (kperm_eq_zero_iff j k).2 hjk
      simp [hjk, this]
    · have : ¬ (0 : Fin 4) = kperm j k := fun h => hjk ((kperm_eq_zero_iff j k).1 h)
      simp [hjk, this]
  rw [Submodule.eq_top_iff']
  intro v
  rw [pi_eq_sum_univ v]
  exact W.sum_mem fun j _ => W.smul_mem _ (he j)

end Mono

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
