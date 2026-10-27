module

public import CFSG.HardMathSupport.Foote.ModuleExclusions.Hilbert90

public section

namespace CFSG.GH74.GLS.IVK.H90

variable {F : Type*} [Field F]

@[expose] def Ai (σ : F ≃+* F) (A : Matrix (Fin 2) (Fin 2) F) : ℕ → Matrix (Fin 2) (Fin 2) F
  | 0 => 1
  | n + 1 => A * (Ai σ A n).map σ

@[expose] def sv (σ : F ≃+* F) (i : ℕ) (w : Fin 2 → F) : Fin 2 → F := fun j => (σ ^ i) (w j)

@[expose] def tr (σ : F ≃+* F) (A : Matrix (Fin 2) (Fin 2) F) (r : ℕ) (w : Fin 2 → F) : Fin 2 → F :=
  ∑ i ∈ Finset.range r, (Ai σ A i).mulVec (sv σ i w)

@[expose] def σv (σ : F ≃+* F) : (Fin 2 → F) →+ (Fin 2 → F) :=
  AddMonoidHom.mk' (fun u j => σ (u j)) (by intro a b; ext j; simp)

theorem Ai_eq (σ : F ≃+* F) (A : Matrix (Fin 2) (Fin 2) F) (n : ℕ) :
    Ai σ A n = HardMathSupport.Foote.ModuleExclusions.Ai σ A n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change A * (Ai σ A n).map σ = A * (HardMathSupport.Foote.ModuleExclusions.Ai σ A n).map σ
    rw [ih]

theorem tr_eq (σ : F ≃+* F) (A : Matrix (Fin 2) (Fin 2) F) (r : ℕ) (w : Fin 2 → F) :
    tr σ A r w = HardMathSupport.Foote.ModuleExclusions.tr σ A r w := by
  simp only [tr, HardMathSupport.Foote.ModuleExclusions.tr, Ai_eq]
  rfl

theorem σv_apply (σ : F ≃+* F) (u : Fin 2 → F) (j : Fin 2) : σv σ u j = σ (u j) := rfl

theorem sv_zero (σ : F ≃+* F) (w : Fin 2 → F) : sv σ 0 w = w := by
  ext j; simp [sv]

theorem sv_succ (σ : F ≃+* F) (i : ℕ) (w : Fin 2 → F) :
    sv σ (i + 1) w = σv σ (sv σ i w) := by
  ext j
  simp only [sv, pow_succ', σv_apply]
  rfl

theorem sv_smul (σ : F ≃+* F) (i : ℕ) (a : F) (w : Fin 2 → F) :
    sv σ i (a • w) = (σ ^ i) a • sv σ i w := by
  ext j; simp [sv]

theorem σv_mulVec (σ : F ≃+* F) (M : Matrix (Fin 2) (Fin 2) F) (u : Fin 2 → F) :
    σv σ (M.mulVec u) = (M.map σ).mulVec (σv σ u) := by
  ext j
  exact RingHom.map_mulVec σ.toRingHom M u j

theorem mulVec_tr_fixed (σ : F ≃+* F) (A : Matrix (Fin 2) (Fin 2) F) (r : ℕ)
    (hσ : σ ^ r = 1) (hA : Ai σ A r = 1) (w : Fin 2 → F) :
    A.mulVec (σv σ (tr σ A r w)) = tr σ A r w := by
  rw [tr_eq]
  exact HardMathSupport.Foote.ModuleExclusions.mulVec_tr_fixed σ A r hσ (by rwa [← Ai_eq]) w

theorem tr_smul (σ : F ≃+* F) (A : Matrix (Fin 2) (Fin 2) F) (r : ℕ) (a : F) (w : Fin 2 → F) :
    tr σ A r (a • w) = ∑ i ∈ Finset.range r, (σ ^ i) a • (Ai σ A i).mulVec (sv σ i w) := by
  simp only [tr, sv_smul, Matrix.mulVec_smul]

theorem sigma_pow_linearIndependent (σ : F ≃+* F) (r : ℕ) (hr : orderOf σ = r) :
    LinearIndependent F (fun i : Fin r => ((fun u : Fˣ => (σ ^ (i : ℕ)) (u : F)) : Fˣ → F)) :=
  HardMathSupport.Foote.ModuleExclusions.sigma_pow_linearIndependent σ r hr

theorem span_tr (σ : F ≃+* F) (A : Matrix (Fin 2) (Fin 2) F) (r : ℕ) (hr : orderOf σ = r)
    (hr0 : 0 < r) : Submodule.span F (Set.range (tr σ A r)) = ⊤ := by
  have h : tr σ A r = HardMathSupport.Foote.ModuleExclusions.tr σ A r := funext (tr_eq σ A r)
  rw [h]
  exact HardMathSupport.Foote.ModuleExclusions.span_tr σ A r hr hr0

theorem speiser (σ : F ≃+* F) (A : Matrix (Fin 2) (Fin 2) F) (r : ℕ) (hr : orderOf σ = r)
    (hr0 : 0 < r) (hA : Ai σ A r = 1) :
    ∃ B : Matrix (Fin 2) (Fin 2) F, B.det ≠ 0 ∧ A * B.map σ = B :=
  HardMathSupport.Foote.ModuleExclusions.speiser σ A r hr hr0 (by rwa [← Ai_eq])

theorem pow_succ_apply (σ : F ≃+* F) (n : ℕ) (x : F) : (σ ^ (n + 1)) x = σ ((σ ^ n) x) :=
  HardMathSupport.Foote.ModuleExclusions.pow_succ_apply σ n x

theorem Ai_succ_right (σ : F ≃+* F) (A : Matrix (Fin 2) (Fin 2) F) (n : ℕ) :
    Ai σ A (n + 1) = Ai σ A n * A.map (σ ^ n) := by
  rw [Ai_eq, Ai_eq]
  exact HardMathSupport.Foote.ModuleExclusions.Ai_succ_right σ A n

theorem Ai_smul (σ : F ≃+* F) (A : Matrix (Fin 2) (Fin 2) F) (l : F) (n : ℕ) :
    Ai σ (l • A) n = (∏ i ∈ Finset.range n, (σ ^ i) l) • Ai σ A n := by
  rw [Ai_eq, Ai_eq]
  exact HardMathSupport.Foote.ModuleExclusions.Ai_smul σ A l n

theorem det_Ai_ne_zero (σ : F ≃+* F) (A : Matrix (Fin 2) (Fin 2) F) (hA : A.det ≠ 0) (n : ℕ) :
    (Ai σ A n).det ≠ 0 := by
  rw [Ai_eq]
  exact HardMathSupport.Foote.ModuleExclusions.det_Ai_ne_zero σ A hA n

theorem prod_pow_eq_norm [Finite F] (σ : F ≃+* F) (x : F) :
    ∏ i ∈ Finset.range (orderOf σ), (σ ^ i) x =
      algebraMap (FixedPoints.subfield (Subgroup.zpowers σ) F) F
        (Algebra.norm (FixedPoints.subfield (Subgroup.zpowers σ) F) x) :=
  HardMathSupport.Foote.ModuleExclusions.prod_pow_eq_norm σ x

theorem mem_fixedPoints_subfield_of_apply_eq (σ : F ≃+* F) (x : F) (h : σ x = x) :
    x ∈ FixedPoints.subfield (Subgroup.zpowers σ) F :=
  HardMathSupport.Foote.ModuleExclusions.mem_fixedPoints_subfield_of_apply_eq σ x h

theorem exists_prod_pow_eq [Finite F] (σ : F ≃+* F) (c : F) (hc : σ c = c) (hc0 : c ≠ 0) :
    ∃ l : F, l ≠ 0 ∧ ∏ i ∈ Finset.range (orderOf σ), (σ ^ i) l = c :=
  HardMathSupport.Foote.ModuleExclusions.exists_prod_pow_eq σ c hc hc0

theorem hilbert90_matrix [Finite F] (σ : F ≃+* F) (A : Matrix (Fin 2) (Fin 2) F) (hA : A.det ≠ 0)
    (c : F) (hc : Ai σ A (orderOf σ) = c • (1 : Matrix (Fin 2) (Fin 2) F)) :
    ∃ (l : F) (B : Matrix (Fin 2) (Fin 2) F), l ≠ 0 ∧ B.det ≠ 0 ∧ (l • A) * B.map σ = B :=
  HardMathSupport.Foote.ModuleExclusions.hilbert90_matrix σ A hA c (by rwa [← Ai_eq])

end CFSG.GH74.GLS.IVK.H90
