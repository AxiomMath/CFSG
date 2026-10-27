module

public import CFSG.LocalAnalysis.SectionRank.ClassicalEven.Basic

public section

namespace CFSG.SectionRank.ClassicalEven

namespace OrthRot

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix
open scoped commutatorElement

variable {ι : Type} {K : Type} [Field K]

@[expose] def IsPolar (Q : (ι → K) → K) (a : ι → K) (f : (ι → K) →ₗ[K] K) (q : K) : Prop :=
  ∀ v t, Q (v + t • a) = Q v + t * f v + t ^ 2 * q

namespace IsPolar

variable {Q : (ι → K) → K} {a b : ι → K} {f g : (ι → K) →ₗ[K] K} {q r : K}

theorem add (ha : IsPolar Q a f q) (hb : IsPolar Q b g r) {s : K} (hs : q + r + g a = s) :
    IsPolar Q (a + b) (f + g) s := fun v t => by
  rw [smul_add, ← add_assoc, hb, ha, map_add, map_smul, smul_eq_mul, LinearMap.add_apply, ← hs]
  ring

theorem symm (ha : IsPolar Q a f q) (hb : IsPolar Q b g r) : f b = g a := by
  have h := hb a 1
  have h' := ha b 1
  have ha0 := ha 0 1
  have hb0 := hb 0 1
  rw [one_smul, add_comm b a] at h'
  simp only [one_smul, zero_add, map_zero, mul_zero, add_zero, one_pow, one_mul] at h h' ha0 hb0
  linear_combination h - h' - hb0 + ha0

theorem self (ha : IsPolar Q a f q) : f a = 2 * q := by
  have h1 := ha a 1
  have h2 := ha 0 2
  have h0 := ha 0 1
  rw [one_smul, ← two_smul K a] at h1
  simp only [one_smul, zero_add, map_zero, mul_zero, add_zero, one_pow, one_mul] at h1 h2 h0
  linear_combination h2 - h1 - h0

theorem self_eq_zero [CharP K 2] (ha : IsPolar Q a f q) : f a = 0 := by
  rw [ha.self, CharTwo.two_eq_zero, zero_mul]

end IsPolar

@[expose] def tv (a : ι → K) (f : (ι → K) →ₗ[K] K) : (ι → K) →ₗ[K] (ι → K) :=
  LinearMap.id + f.smulRight a

theorem tv_apply (a : ι → K) (f : (ι → K) →ₗ[K] K) (v : ι → K) : tv a f v = v + f v • a := rfl

theorem tv_comm {a b : ι → K} {f g : (ι → K) →ₗ[K] K} (hfb : f b = 0) (hga : g a = 0)
    (v : ι → K) : tv a f (tv b g v) = tv b g (tv a f v) := by
  simp only [tv_apply, map_add, map_smul, hfb, hga, zero_smul, add_zero]
  abel

section CharTwo

variable [CharP K 2]

theorem self_add_self (v : ι → K) : v + v = 0 := by
  rw [← two_smul K v, CharTwo.two_eq_zero, zero_smul]

theorem tv_tv {a : ι → K} {f : (ι → K) →ₗ[K] K} (h : f a = 0) (v : ι → K) :
    tv a f (tv a f v) = v := by
  rw [tv_apply, tv_apply, map_add, map_smul, h, smul_eq_mul, mul_zero, add_zero, add_assoc,
    ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero]

theorem Q_tv {Q : (ι → K) → K} {a : ι → K} {f : (ι → K) →ₗ[K] K} (ha : IsPolar Q a f 1)
    (v : ι → K) : Q (tv a f v) = Q v := by
  rw [tv_apply, ha, mul_one, ← sq, add_assoc, CharTwo.add_self_eq_zero, add_zero]

end CharTwo

theorem mul_eq_commutator {G : Type*} [Group G] {s t : G} (hs : s * s = 1) (ht : t * t = 1)
    (h3 : (s * t) ^ 3 = 1) : s * t = ⁅t, s⁆ := by
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  rw [pow_three'] at h3
  rw [commutatorElement_def]
  calc s * t = s⁻¹ * t⁻¹ := by rw [hs', ht']
    _ = t * (s * t * (s * t) * (s * t)) * t⁻¹ * s⁻¹ * t⁻¹ := by rw [h3]; group
    _ = t * s * t * s := by group
    _ = t * s * t⁻¹ * s⁻¹ := by rw [hs', ht']

structure Plane (Q : (ι → K) → K) where
  a : ι → K
  b : ι → K
  f : (ι → K) →ₗ[K] K
  g : (ι → K) →ₗ[K] K
  isPolar_a : IsPolar Q a f 1
  isPolar_b : IsPolar Q b g 1
  f_b : f b = 1

namespace Plane

variable {Q : (ι → K) → K}

structure Orth (P P' : Plane Q) : Prop where
  f_a : P.f P'.a = 0
  f_b : P.f P'.b = 0
  g_a : P.g P'.a = 0
  g_b : P.g P'.b = 0

theorem g_a (P : Plane Q) : P.g P.a = 1 := (P.isPolar_a.symm P.isPolar_b).symm.trans P.f_b

section CharTwo

variable [CharP K 2] (P : Plane Q)

theorem f_a : P.f P.a = 0 := P.isPolar_a.self_eq_zero

theorem g_b : P.g P.b = 0 := P.isPolar_b.self_eq_zero

theorem b_ne_smul_a (u : K) : P.b ≠ u • P.a := fun h => by
  have h1 := P.f_b
  rw [h, map_smul, P.f_a, smul_zero] at h1
  exact zero_ne_one h1

end CharTwo

end Plane

section Matrices

variable [Fintype ι] [DecidableEq ι]

theorem gl_ext {x y : GL ι K} (h : ∀ v, (x : Matrix ι ι K) *ᵥ v = (y : Matrix ι ι K) *ᵥ v) :
    x = y :=
  Units.ext (Matrix.toLin'.injective (LinearMap.ext fun v => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, h]))

theorem mul_mulVec (x y : GL ι K) (v : ι → K) :
    ((x * y : GL ι K) : Matrix ι ι K) *ᵥ v = (x : Matrix ι ι K) *ᵥ ((y : Matrix ι ι K) *ᵥ v) := by
  rw [Units.val_mul, mulVec_mulVec]

theorem pow_mulVec_of_fix {x : GL ι K} {v : ι → K} (h : (x : Matrix ι ι K) *ᵥ v = v) (k : ℕ) :
    ((x ^ k : GL ι K) : Matrix ι ι K) *ᵥ v = v := by
  induction k with
  | zero => rw [pow_zero, Units.val_one, one_mulVec]
  | succ k ih => rw [pow_succ, mul_mulVec, h, ih]

theorem exists_smul_of_mem_scalars {c : GL ι K} (hc : c ∈ StatedScalars ι K) :
    ∃ u : K, ∀ v, (c : Matrix ι ι K) *ᵥ v = u • v := by
  obtain ⟨u, rfl⟩ := hc
  exact ⟨u, fun v => by
    ext i
    simp [GeneralLinearGroup.coe_scalar, scalar_apply, mulVec_diagonal]⟩

variable [CharP K 2]

theorem toMatrix'_tv_mul_self {a : ι → K} {f : (ι → K) →ₗ[K] K} (h : f a = 0) :
    LinearMap.toMatrix' (tv a f) * LinearMap.toMatrix' (tv a f) = 1 := by
  rw [← LinearMap.toMatrix'_comp, show (tv a f).comp (tv a f) = LinearMap.id from
    LinearMap.ext (tv_tv h), LinearMap.toMatrix'_id]

noncomputable def tvGL (a : ι → K) (f : (ι → K) →ₗ[K] K) (h : f a = 0) : GL ι K :=
  ⟨LinearMap.toMatrix' (tv a f), LinearMap.toMatrix' (tv a f), toMatrix'_tv_mul_self h,
    toMatrix'_tv_mul_self h⟩

theorem tvGL_mulVec {a : ι → K} {f : (ι → K) →ₗ[K] K} (h : f a = 0) (v : ι → K) :
    (tvGL a f h : Matrix ι ι K) *ᵥ v = tv a f v :=
  LinearMap.toMatrix'_mulVec _ v

theorem tvGL_mul_self {a : ι → K} {f : (ι → K) →ₗ[K] K} (h : f a = 0) :
    tvGL a f h * tvGL a f h = 1 :=
  Units.ext (toMatrix'_tv_mul_self h)

theorem tvGL_commute {a b : ι → K} {f g : (ι → K) →ₗ[K] K} (ha : f a = 0) (hb : g b = 0)
    (hfb : f b = 0) (hga : g a = 0) : Commute (tvGL a f ha) (tvGL b g hb) :=
  gl_ext fun v => by simp only [mul_mulVec, tvGL_mulVec, tv_comm hfb hga]

theorem tvGL_mem {Q : (ι → K) → K} {a : ι → K} {f : (ι → K) →ₗ[K] K} (ha : IsPolar Q a f 1)
    (h : f a = 0) :
    tvGL a f h ∈ Subgroup.closure {A : GL ι K | ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v} :=
  Subgroup.subset_closure fun v => by rw [tvGL_mulVec, Q_tv ha]

namespace Plane

variable {Q : (ι → K) → K} (P : Plane Q)

noncomputable def rot : GL ι K := tvGL P.a P.f P.f_a * tvGL P.b P.g P.g_b

theorem rot_mulVec (v : ι → K) :
    (P.rot : Matrix ι ι K) *ᵥ v = v + (P.f v + P.g v) • P.a + P.g v • P.b := by
  simp only [rot, mul_mulVec, tvGL_mulVec, tv_apply]
  rw [map_add, map_smul, P.f_b, smul_eq_mul, mul_one]
  abel

theorem rot_pow_three : P.rot ^ 3 = 1 := gl_ext fun v => by
  rw [pow_three, mul_mulVec, mul_mulVec, Units.val_one, one_mulVec]
  simp only [rot_mulVec, map_add, map_smul, P.f_a, P.f_b, P.g_a, P.g_b, smul_eq_mul, mul_zero,
    mul_one, add_zero]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  grind

theorem rot_mem : P.rot ∈ StatedOmega Q := by
  rw [rot, mul_eq_commutator (tvGL_mul_self _) (tvGL_mul_self _) P.rot_pow_three]
  exact Subgroup.commutator_mem_commutator (tvGL_mem P.isPolar_b _) (tvGL_mem P.isPolar_a _)

theorem rot_a : (P.rot : Matrix ι ι K) *ᵥ P.a = P.b := by
  rw [rot_mulVec, P.f_a, P.g_a, zero_add, one_smul, one_smul, self_add_self, zero_add]

theorem rot_fix {v : ι → K} (hf : P.f v = 0) (hg : P.g v = 0) :
    (P.rot : Matrix ι ι K) *ᵥ v = v := by
  rw [rot_mulVec, hf, hg, add_zero, zero_smul, zero_smul, add_zero, add_zero]

theorem rot_commute {P P' : Plane Q} (h : P.Orth P') : Commute P.rot P'.rot :=
  Commute.mul_left
    (Commute.mul_right (tvGL_commute _ _ h.f_a ((P'.isPolar_a.symm P.isPolar_a).trans h.f_a))
      (tvGL_commute _ _ h.f_b ((P'.isPolar_b.symm P.isPolar_a).trans h.f_b)))
    (Commute.mul_right (tvGL_commute _ _ h.g_a ((P'.isPolar_a.symm P.isPolar_b).trans h.g_a))
      (tvGL_commute _ _ h.g_b ((P'.isPolar_b.symm P.isPolar_b).trans h.g_b)))

theorem three_le_pRank_three [Finite K] {P₀ P₁ P₂ : Plane Q} (h₀₁ : P₀.Orth P₁)
    (h₀₂ : P₀.Orth P₂) (h₁₂ : P₁.Orth P₂) :
    3 ≤ pRank 3 (⊤ : Subgroup (StatedProj (StatedOmega Q))) := by
  refine three_le_pRank_statedProj P₀.rot_mem P₁.rot_mem P₂.rot_mem P₀.rot_pow_three
    P₁.rot_pow_three P₂.rot_pow_three (rot_commute h₀₁) (rot_commute h₀₂) (rot_commute h₁₂)
    (fun hc => ?_) (fun m c hc h => ?_) (fun m k c hc h => ?_)
  · obtain ⟨u, hu⟩ := exists_smul_of_mem_scalars hc
    exact P₀.b_ne_smul_a u (P₀.rot_a.symm.trans (hu P₀.a))
  · obtain ⟨u, hu⟩ := exists_smul_of_mem_scalars hc
    refine P₁.b_ne_smul_a u ?_
    rw [← P₁.rot_a, ← h, mul_mulVec, hu, mulVec_smul,
      pow_mulVec_of_fix (P₀.rot_fix h₀₁.f_a h₀₁.g_a)]
  · obtain ⟨u, hu⟩ := exists_smul_of_mem_scalars hc
    refine P₂.b_ne_smul_a u ?_
    rw [← P₂.rot_a, ← h]
    simp only [mul_mulVec, hu, mulVec_smul, pow_mulVec_of_fix (P₁.rot_fix h₁₂.f_a h₁₂.g_a),
      pow_mulVec_of_fix (P₀.rot_fix h₀₂.f_a h₀₂.g_a)]

end Plane

end Matrices

section Frames

variable [DecidableEq ι]

structure Frame (Q : (ι → K) → K) where
  X : Fin 3 → ι
  Y : Fin 3 → ι
  w : ι → K
  β : (ι → K) →ₗ[K] K
  injX : Function.Injective X
  injY : Function.Injective Y
  X_ne_Y : ∀ i j, X i ≠ Y j
  w_X : ∀ i, w (X i) = 0
  w_Y : ∀ i, w (Y i) = 0
  isPolar_X : ∀ i, IsPolar Q (Pi.single (X i) 1) (LinearMap.proj (Y i)) 0
  isPolar_Y : ∀ i, IsPolar Q (Pi.single (Y i) 1) (LinearMap.proj (X i)) 0
  isPolar_w : IsPolar Q w β 1

namespace Frame

variable {Q : (ι → K) → K} (F : Frame Q)

theorem Y_ne_X (i j : Fin 3) : F.Y j ≠ F.X i := (F.X_ne_Y i j).symm

theorem polar_X {u : ι → K} {φ : (ι → K) →ₗ[K] K} {q : K} (hu : IsPolar Q u φ q) (j : Fin 3) :
    φ (Pi.single (F.X j) 1) = u (F.Y j) :=
  ((F.isPolar_X j).symm hu).symm

theorem polar_Y {u : ι → K} {φ : (ι → K) →ₗ[K] K} {q : K} (hu : IsPolar Q u φ q) (j : Fin 3) :
    φ (Pi.single (F.Y j) 1) = u (F.X j) :=
  ((F.isPolar_Y j).symm hu).symm

def hyp (i : Fin 3) : ι → K := Pi.single (F.X i) 1 + Pi.single (F.Y i) 1

def hypF (i : Fin 3) : (ι → K) →ₗ[K] K :=
  (LinearMap.proj (F.Y i) : (ι → K) →ₗ[K] K) + LinearMap.proj (F.X i)

theorem isPolar_hyp (i : Fin 3) : IsPolar Q (F.hyp i) (F.hypF i) 1 :=
  (F.isPolar_X i).add (F.isPolar_Y i) (by simp)

def plane (i : Fin 3) (u : ι → K) (φ : (ι → K) →ₗ[K] K) (hu : IsPolar Q u φ 1)
    (huX : u (F.X i) = 0) (huY : u (F.Y i) = 0) : Plane Q where
  a := F.hyp i
  b := Pi.single (F.X i) 1 + u
  f := F.hypF i
  g := (LinearMap.proj (F.Y i) : (ι → K) →ₗ[K] K) + φ
  isPolar_a := F.isPolar_hyp i
  isPolar_b := (F.isPolar_X i).add hu (by rw [F.polar_X hu, huY, zero_add, add_zero])
  f_b := by simp [hypF, huX, huY, F.Y_ne_X]

theorem plane_orth {i j : Fin 3} (hij : i ≠ j) {u u' : ι → K} {φ φ' : (ι → K) →ₗ[K] K}
    {hu : IsPolar Q u φ 1} {huX : u (F.X i) = 0} {huY : u (F.Y i) = 0}
    {hu' : IsPolar Q u' φ' 1} {huX' : u' (F.X j) = 0} {huY' : u' (F.Y j) = 0}
    (h₁ : u' (F.Y i) + u' (F.X i) = 0) (h₂ : u (F.Y j) + u (F.X j) = 0)
    (h₃ : u' (F.Y i) + u (F.Y j) + φ u' = 0) :
    (F.plane i u φ hu huX huY).Orth (F.plane j u' φ' hu' huX' huY') where
  f_a := by simp [plane, hyp, hypF, F.injX.eq_iff, F.injY.eq_iff, F.Y_ne_X, hij]
  f_b := by
    simp only [plane, hypF, LinearMap.add_apply, LinearMap.proj_apply, Pi.add_apply]
    simp only [Pi.single_apply, F.injX.eq_iff, F.Y_ne_X, hij, ite_false, zero_add]
    exact h₁
  g_a := by
    simp only [plane, hyp, LinearMap.add_apply, LinearMap.proj_apply, map_add, F.polar_X hu,
      F.polar_Y hu]
    simp only [Pi.single_apply, F.injY.eq_iff, F.Y_ne_X, hij, ite_false, zero_add]
    exact h₂
  g_b := by
    simp only [plane, LinearMap.add_apply, LinearMap.proj_apply, map_add, F.polar_X hu]
    simp only [Pi.single_apply, F.Y_ne_X, ite_false, zero_add]
    linear_combination h₃

def plane₀ : Plane Q :=
  F.plane 0 (F.hyp 1) (F.hypF 1) (F.isPolar_hyp 1) (by simp [hyp, F.injX.eq_iff, F.Y_ne_X])
    (by simp [hyp, F.injY.eq_iff, F.X_ne_Y])

def plane₁ : Plane Q :=
  F.plane 1 (F.hyp 0) (F.hypF 0) (F.isPolar_hyp 0) (by simp [hyp, F.injX.eq_iff, F.Y_ne_X])
    (by simp [hyp, F.injY.eq_iff, F.X_ne_Y])

def plane₂ : Plane Q :=
  F.plane 2 F.w F.β F.isPolar_w (F.w_X 2) (F.w_Y 2)

theorem orth₀₂ : F.plane₀.Orth F.plane₂ :=
  F.plane_orth (by decide) (by simp [F.w_X, F.w_Y])
    (by simp [hyp, F.injX.eq_iff, F.injY.eq_iff, F.X_ne_Y, F.Y_ne_X])
    (by simp [hyp, hypF, F.injY.eq_iff, F.Y_ne_X, F.w_X, F.w_Y])

theorem orth₁₂ : F.plane₁.Orth F.plane₂ :=
  F.plane_orth (by decide) (by simp [F.w_X, F.w_Y])
    (by simp [hyp, F.injX.eq_iff, F.injY.eq_iff, F.X_ne_Y, F.Y_ne_X])
    (by simp [hyp, hypF, F.injY.eq_iff, F.Y_ne_X, F.w_X, F.w_Y])

variable [CharP K 2]

theorem orth₀₁ : F.plane₀.Orth F.plane₁ :=
  F.plane_orth (by decide)
    (by simp [hyp, F.X_ne_Y, F.Y_ne_X, CharTwo.add_self_eq_zero])
    (by simp [hyp, F.X_ne_Y, F.Y_ne_X, CharTwo.add_self_eq_zero])
    (by simp [hyp, hypF, F.injX.eq_iff, F.injY.eq_iff, F.X_ne_Y, F.Y_ne_X,
      CharTwo.add_self_eq_zero])

include F in
theorem three_le_pRank_three [Fintype ι] [Finite K] :
    3 ≤ pRank 3 (⊤ : Subgroup (StatedProj (StatedOmega Q))) :=
  Plane.three_le_pRank_three F.orth₀₁ F.orth₀₂ F.orth₁₂

end Frame

end Frames

end OrthRot

end CFSG.SectionRank.ClassicalEven
