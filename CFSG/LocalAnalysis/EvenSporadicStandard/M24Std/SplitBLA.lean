module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.ZMod.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.Tactic.ContinuousFunctionalCalculus

public section

namespace CFSG.EvenSporadicStandard.M24Std.SplitB

open Matrix

abbrev F2 : Type := ZMod 2

abbrev Mat4 : Type := Matrix (Fin 4) (Fin 4) F2

@[expose] def wordMat {m : ℕ} (A : Fin m → Mat4) : List (Fin m) → Mat4
  | [] => 1
  | k :: r => wordMat A r * A k

theorem wordMat_append {m : ℕ} (A : Fin m → Mat4) (l₁ l₂ : List (Fin m)) :
    wordMat A (l₁ ++ l₂) = wordMat A l₂ * wordMat A l₁ := by
  induction l₁ with
  | nil => simp [wordMat]
  | cons k r ih => simp only [List.cons_append, wordMat, ih, Matrix.mul_assoc]

@[expose] def wordCoc {m : ℕ} (A : Fin m → Mat4) (lam : Fin m → Fin 4 → F2) :
    List (Fin m) → Fin 4 → F2
  | [] => 0
  | k :: r => wordCoc A lam r + wordMat A r *ᵥ lam k

@[expose] def wordBlk {m : ℕ} (A : Fin m → Mat4) (k' : Fin m) : List (Fin m) → Mat4
  | [] => 0
  | k :: r => wordBlk A k' r + if k' = k then wordMat A r else 0

theorem wordCoc_eq {m : ℕ} (A : Fin m → Mat4) (lam : Fin m → Fin 4 → F2) (r : List (Fin m)) :
    wordCoc A lam r = ∑ k', wordBlk A k' r *ᵥ lam k' := by
  induction r with
  | nil => simp [wordCoc, wordBlk]
  | cons k r ih =>
    simp only [wordCoc, wordBlk, ih, Matrix.add_mulVec, Finset.sum_add_distrib]
    congr 1
    have : ∀ k' : Fin m, (if k' = k then wordMat A r else 0) *ᵥ lam k' =
        if k' = k then wordMat A r *ᵥ lam k else 0 := by
      intro k'
      split_ifs with h
      · subst h; rfl
      · simp
    simp [this]

theorem exists_mu_of_dual {m : ℕ} {ρ : Type*} [Fintype ρ] (A : Fin m → Mat4)
    (words : ρ → List (Fin m)) (Psi : Fin m → Mat4) (Cm : Fin m → ρ → Mat4)
    (hdual : ∀ k k' : Fin m, (if k = k' then (1 : Mat4) else 0) =
      (1 + A k) * Psi k' + ∑ r, Cm k r * wordBlk A k' (words r))
    (lam : Fin m → Fin 4 → F2) (hlam : ∀ r, wordCoc A lam (words r) = 0) :
    ∃ μ : Fin 4 → F2, ∀ k, lam k = (1 + A k) *ᵥ μ := by
  refine ⟨∑ k', Psi k' *ᵥ lam k', fun k => ?_⟩
  have h1 : lam k = ∑ k', (if k = k' then (1 : Mat4) else 0) *ᵥ lam k' := by
    have : ∀ k' : Fin m, (if k = k' then (1 : Mat4) else 0) *ᵥ lam k' =
        if k = k' then lam k' else 0 := by
      intro k'
      split_ifs <;> simp
    rw [Finset.sum_congr rfl (fun k' _ => this k'), Finset.sum_ite_eq]
    simp
  have h2 : ∑ k', (if k = k' then (1 : Mat4) else 0) *ᵥ lam k' =
      (1 + A k) *ᵥ (∑ k', Psi k' *ᵥ lam k') +
        ∑ r, Cm k r *ᵥ (wordCoc A lam (words r)) := by
    simp only [hdual, Matrix.add_mulVec, Finset.sum_add_distrib, Matrix.mulVec_sum,
      Matrix.mulVec_mulVec, Matrix.sum_mulVec, wordCoc_eq]
    congr 1
    exact Finset.sum_comm
  rw [h1, h2]
  simp [hlam]

theorem F2_cases (a : F2) : a = 0 ∨ a = 1 := by
  revert a; decide

theorem F2_add_self (a : F2) : a + a = 0 := by
  revert a; decide

section LA

variable {V : Type*} [AddCommGroup V] [Module F2 V]

theorem exists_invariant_functional {m : ℕ} {ρ : Type*} [Fintype ρ]
    (yb : Fin 4 → V) (zb : V) (pb : V →ₗ[F2] (Fin 4 → F2))
    (hpy : ∀ i, pb (yb i) = Pi.single i 1) (hpz : pb zb = 0)
    (hker : ∀ v, pb v = 0 → ∃ a : F2, v = a • zb) (hz : zb ≠ 0)
    (T : Fin m → V →ₗ[F2] V) (A : Fin m → Mat4)
    (hTz : ∀ k, T k zb = zb) (hTp : ∀ k v, pb (T k v) = pb v ᵥ* A k)
    (words : ρ → List (Fin m)) (hwords : ∀ r, ((words r).map T).prod = 1)
    (Psi : Fin m → Mat4) (Cm : Fin m → ρ → Mat4)
    (hdual : ∀ k k' : Fin m, (if k = k' then (1 : Mat4) else 0) =
      (1 + A k) * Psi k' + ∑ r, Cm k r * wordBlk A k' (words r)) :
    ∃ f : V →ₗ[F2] F2, f zb = 1 ∧ ∀ k v, f (T k v) = f v := by
  classical
  let Ξ : (Fin 4 → F2) × F2 →ₗ[F2] V :=
    (Fintype.linearCombination F2 yb).coprod (LinearMap.toSpanSingleton F2 V zb)
  have hΞ : ∀ c a, Ξ (c, a) = ∑ i, c i • yb i + a • zb := by
    intro c a
    simp [Ξ, Fintype.linearCombination_apply]
  have hpΞ : ∀ c a, pb (Ξ (c, a)) = c := by
    intro c a
    simp only [hΞ, map_add, map_sum, map_smul, hpz, smul_zero, add_zero, hpy]
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hinj : Function.Injective Ξ := by
    refine (injective_iff_map_eq_zero Ξ).2 ?_
    rintro ⟨c, a⟩ h
    have hc : c = 0 := by rw [← hpΞ c a, h, map_zero]
    subst hc
    have ha : a • zb = 0 := by simpa [hΞ] using h
    rcases F2_cases a with rfl | rfl
    · rfl
    · exact absurd (by simpa using ha) hz
  have hsurj : Function.Surjective Ξ := by
    intro v
    obtain ⟨a, ha⟩ := hker (v - Ξ (pb v, 0)) (by rw [map_sub, hpΞ]; exact sub_self _)
    refine ⟨(pb v, a), ?_⟩
    rw [hΞ] at ha ⊢
    simp only [zero_smul, add_zero] at ha
    rw [← ha]; abel
  let E := LinearEquiv.ofBijective Ξ ⟨hinj, hsurj⟩
  have hE : ∀ p, E p = Ξ p := fun p => rfl
  let lam : Fin m → Fin 4 → F2 := fun k i => (E.symm (T k (yb i))).2
  have hTy : ∀ k i, T k (yb i) = Ξ (A k i, lam k i) := by
    intro k i
    have h1 : T k (yb i) = Ξ (E.symm (T k (yb i))) := by
      rw [← hE, LinearEquiv.apply_symm_apply]
    have h2 : (E.symm (T k (yb i))).1 = A k i := by
      have := hpΞ (E.symm (T k (yb i))).1 (E.symm (T k (yb i))).2
      rw [← hE, Prod.mk.eta, LinearEquiv.apply_symm_apply, hTp, hpy] at this
      rw [← this]
      simp
      rfl
    rw [h1]
    congr 1
    exact Prod.ext h2 rfl
  have hkey : ∀ k c a, T k (Ξ (c, a)) = Ξ (c ᵥ* A k, a + c ⬝ᵥ lam k) := by
    intro k c a
    have hp : (c ᵥ* A k, a + c ⬝ᵥ lam k) = ∑ i, c i • (A k i, lam k i) + (0, a) := by
      refine Prod.ext ?_ ?_
      · simp [Prod.fst_sum, vecMul_eq_sum]
      · simp [Prod.snd_sum, dotProduct, add_comm]
    rw [hp, map_add, map_sum, hΞ, map_add, map_sum, map_smul, hTz]
    simp only [map_smul, hTy]
    rw [hΞ 0 a]
    simp
  have hword : ∀ (r : List (Fin m)) c a,
      (r.map T).prod (Ξ (c, a)) = Ξ (c ᵥ* wordMat A r, a + c ⬝ᵥ wordCoc A lam r) := by
    intro r
    induction r with
    | nil => intro c a; simp [wordMat, wordCoc]
    | cons k r ih =>
      intro c a
      rw [List.map_cons, List.prod_cons, Module.End.mul_apply, ih, hkey]
      simp only [wordMat, wordCoc, Matrix.vecMul_vecMul, dotProduct_add, dotProduct_mulVec,
        add_assoc]
  have hlam : ∀ r, wordCoc A lam (words r) = 0 := by
    intro r
    funext i
    have h := hword (words r) (Pi.single i 1) 0
    rw [hwords r, Module.End.one_apply] at h
    have h' := hinj h
    have := congrArg Prod.snd h'
    simpa using this.symm
  obtain ⟨μ, hμ⟩ := exists_mu_of_dual A words Psi Cm hdual lam hlam
  let f : V →ₗ[F2] F2 :=
    { toFun := fun v => (E.symm v).2 + μ ⬝ᵥ (E.symm v).1
      map_add' := by
        intro v w
        simp only [map_add, Prod.snd_add, Prod.fst_add, dotProduct_add]
        abel
      map_smul' := by
        intro a v
        simp [dotProduct_smul, mul_add] }
  have hf : ∀ c a, f (Ξ (c, a)) = a + μ ⬝ᵥ c := by
    intro c a
    show (E.symm (Ξ (c, a))).2 + μ ⬝ᵥ (E.symm (Ξ (c, a))).1 = _
    rw [← hE, LinearEquiv.symm_apply_apply]
  refine ⟨f, ?_, ?_⟩
  · have : zb = Ξ (0, 1) := by rw [hΞ]; simp
    rw [this, hf]; simp
  · intro k v
    obtain ⟨⟨c, a⟩, rfl⟩ := hsurj v
    rw [hkey, hf, hf, hμ k, Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add,
      dotProduct_comm μ (c ᵥ* A k), ← dotProduct_mulVec, dotProduct_comm μ c]
    have h2 := F2_add_self (c ⬝ᵥ A k *ᵥ μ)
    linear_combination h2

end LA

end CFSG.EvenSporadicStandard.M24Std.SplitB
