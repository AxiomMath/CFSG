module

public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import CFSG.GroupTheory.LocalCores.Components

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open CFSG Subgroup Matrix

variable {K : Type*} [Field K] {n : ℕ}

theorem det_symm_eq_one {G : Type*} [Group G] (A : GL (Fin n) K)
    (e : centralizer ({A} : Set (GL (Fin n) K)) ≃* G) (N : Subgroup G) [Group.IsPerfect N]
    (x : N) : ((e.symm x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 := by
  let ψ : N →* Kˣ := GeneralLinearGroup.det.comp
    ((centralizer ({A} : Set (GL (Fin n) K))).subtype.comp (e.symm.toMonoidHom.comp N.subtype))
  have h1 : x ∈ ψ.ker := Abelianization.commutator_subset_ker ψ (by simp)
  have h2 : ψ x = 1 := h1
  simpa [ψ] using congrArg Units.val h2

@[expose] def liftSL {G : Type*} [Group G] (A : GL (Fin n) K)
    (e : centralizer ({A} : Set (GL (Fin n) K)) ≃* G) (N : Subgroup G) [Group.IsPerfect N] :
    N →* SpecialLinearGroup (Fin n) K where
  toFun x := (⟨((e.symm x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
    det_symm_eq_one A e N x⟩ : SpecialLinearGroup (Fin n) K)
  map_one' := Subtype.ext (by simp)
  map_mul' x y := by
    apply Subtype.ext
    change ((e.symm (x * y) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((e.symm x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((e.symm y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    simp

section lift

variable {G : Type*} [Group G] (A : GL (Fin n) K)
  (e : centralizer ({A} : Set (GL (Fin n) K)) ≃* G) (N : Subgroup G) [Group.IsPerfect N]

theorem coe_liftSL (x : N) :
    ((liftSL A e N x : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((e.symm x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := rfl

theorem toGL_liftSL (x : N) :
    Matrix.SpecialLinearGroup.toGL (liftSL A e N x) = (e.symm x : GL (Fin n) K) := Units.ext rfl

theorem liftSL_injective : Function.Injective (liftSL A e N) := by
  intro x y h
  have h1 : (e.symm x : GL (Fin n) K) = e.symm y := by
    rw [← toGL_liftSL, ← toGL_liftSL, h]
  exact Subtype.ext (e.symm.injective (Subtype.ext h1))

end lift

@[expose] def pullSL {G : Type*} [Group G] (A : GL (Fin n) K)
    (e : centralizer ({A} : Set (GL (Fin n) K)) ≃* G) (N : Subgroup G) :
    Subgroup (SpecialLinearGroup (Fin n) K) :=
  ((N.comap e.toMonoidHom).map (centralizer ({A} : Set (GL (Fin n) K))).subtype).comap
    Matrix.SpecialLinearGroup.toGL

section pull

variable {G : Type*} [Group G] {A : GL (Fin n) K}
  (e : centralizer ({A} : Set (GL (Fin n) K)) ≃* G) (N : Subgroup G)

theorem mem_pullSL {m : SpecialLinearGroup (Fin n) K} :
    m ∈ pullSL A e N ↔ ∃ hm : Matrix.SpecialLinearGroup.toGL m ∈
      centralizer ({A} : Set (GL (Fin n) K)),
      e ⟨_, hm⟩ ∈ N := by
  constructor
  · rintro ⟨B, hB, hBm⟩
    have hm : Matrix.SpecialLinearGroup.toGL m ∈ centralizer ({A} : Set (GL (Fin n) K)) := hBm ▸ B.2
    refine ⟨hm, ?_⟩
    have hB' : B = ⟨_, hm⟩ := Subtype.ext hBm
    rw [← hB']
    exact hB
  · rintro ⟨hm, h⟩
    exact ⟨⟨_, hm⟩, h, rfl⟩

theorem pullSL_le_centralizer {a : SpecialLinearGroup (Fin n) K}
    (ha : Matrix.SpecialLinearGroup.toGL a = A) :
    pullSL A e N ≤ centralizer ({a} : Set (SpecialLinearGroup (Fin n) K)) := by
  intro m hm
  obtain ⟨hm, -⟩ := (mem_pullSL e N).mp hm
  rw [mem_centralizer_singleton_iff] at hm ⊢
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [map_mul, map_mul, ha, hm]

theorem conj_mem_pullSL [N.Normal] {a : SpecialLinearGroup (Fin n) K}
    (ha : Matrix.SpecialLinearGroup.toGL a = A) {y : SpecialLinearGroup (Fin n) K}
    (hy : y ∈ centralizer ({a} : Set (SpecialLinearGroup (Fin n) K)))
    {m : SpecialLinearGroup (Fin n) K} (hm : m ∈ pullSL A e N) :
    y * m * y⁻¹ ∈ pullSL A e N := by
  obtain ⟨hm, hmN⟩ := (mem_pullSL e N).mp hm
  have hY : Matrix.SpecialLinearGroup.toGL y ∈ centralizer ({A} : Set (GL (Fin n) K)) := by
    rw [mem_centralizer_singleton_iff, ← ha, ← map_mul, ← map_mul,
      mem_centralizer_singleton_iff.mp hy]
  have hmem : Matrix.SpecialLinearGroup.toGL (y * m * y⁻¹) ∈
      centralizer ({A} : Set (GL (Fin n) K)) := by
    rw [map_mul, map_mul, map_inv]
    exact mul_mem (mul_mem hY hm) (inv_mem hY)
  have hconj : (⟨_, hY⟩ * ⟨_, hm⟩ * (⟨_, hY⟩ : centralizer ({A} : Set (GL (Fin n) K)))⁻¹ :
      centralizer ({A} : Set (GL (Fin n) K))) = ⟨_, hmem⟩ :=
    Subtype.ext (by simp)
  refine (mem_pullSL e N).mpr ⟨hmem, ?_⟩
  rw [← hconj, map_mul, map_mul, map_inv]
  exact Normal.conj_mem inferInstance _ hmN _

theorem pullSL_eq_range [Group.IsPerfect N] : pullSL A e N = (liftSL A e N).range := by
  ext m
  rw [mem_pullSL]
  constructor
  · rintro ⟨hm, hmN⟩
    refine ⟨⟨_, hmN⟩, Matrix.SpecialLinearGroup.toGL_injective ?_⟩
    rw [toGL_liftSL]
    change ((e.symm (e ⟨_, hm⟩) : centralizer ({A} : Set (GL (Fin n) K))) : GL (Fin n) K) = _
    rw [MulEquiv.symm_apply_apply]
  · rintro ⟨x, rfl⟩
    have h1 : Matrix.SpecialLinearGroup.toGL (liftSL A e N x) ∈
        centralizer ({A} : Set (GL (Fin n) K)) :=
      (toGL_liftSL A e N x) ▸ (e.symm x).2
    refine ⟨h1, ?_⟩
    have h2 : (⟨_, h1⟩ : centralizer ({A} : Set (GL (Fin n) K))) = e.symm x :=
      Subtype.ext (toGL_liftSL A e N x)
    rw [h2, MulEquiv.apply_symm_apply]
    exact x.2

theorem exists_pullSL_eq [Group.IsPerfect N] {x : G} (hx : x ∈ N) :
    ∃ m ∈ pullSL A e N, ∃ hm : Matrix.SpecialLinearGroup.toGL m ∈
      centralizer ({A} : Set (GL (Fin n) K)), e ⟨_, hm⟩ = x := by
  have h1 : Matrix.SpecialLinearGroup.toGL (liftSL A e N ⟨x, hx⟩) ∈
      centralizer ({A} : Set (GL (Fin n) K)) := (toGL_liftSL A e N ⟨x, hx⟩) ▸ (e.symm x).2
  refine ⟨_, (pullSL_eq_range e N).symm ▸ ⟨⟨x, hx⟩, rfl⟩, h1, ?_⟩
  have h2 : (⟨_, h1⟩ : centralizer ({A} : Set (GL (Fin n) K))) = e.symm x :=
    Subtype.ext (toGL_liftSL A e N ⟨x, hx⟩)
  rw [h2, MulEquiv.apply_symm_apply]

theorem isQuasisimple_pullSL (hN : IsQuasisimple N) : IsQuasisimple (pullSL A e N) := by
  have : Group.IsPerfect N := hN.1
  rw [pullSL_eq_range]
  exact LocalCores.isQuasisimple_of_mulEquiv (MonoidHom.ofInjective (liftSL_injective A e N)) hN

theorem exists_noncentral_pullSL [Group.IsPerfect N] (hn : 0 < n) {x : G} (hxN : x ∈ N)
    (hx4 : x ^ 4 = 1) (hxs : ∀ (u : Kˣ) (h : GeneralLinearGroup.scalar (Fin n) u ∈
      centralizer ({A} : Set (GL (Fin n) K))), x ≠ e ⟨_, h⟩) :
    ∃ m ∈ pullSL A e N, m ∉ center (SpecialLinearGroup (Fin n) K) ∧ m ^ 4 = 1 := by
  refine ⟨liftSL A e N ⟨x, hxN⟩, (pullSL_eq_range e N).symm ▸ ⟨_, rfl⟩, fun hc => ?_, ?_⟩
  · obtain ⟨r, hr, hrm⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [zero_pow (by simp; omega)] at hr
      exact zero_ne_one hr
    set u := Units.mk0 r hr0
    have hu : (e.symm x : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) u := by
      apply Units.ext
      have h1 := coe_liftSL A e N ⟨x, hxN⟩
      change _ = ((e.symm x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) at h1
      rw [← h1, ← hrm]
      rfl
    have hmem : GeneralLinearGroup.scalar (Fin n) u ∈ centralizer ({A} : Set (GL (Fin n) K)) :=
      hu ▸ (e.symm x).2
    apply hxs u hmem
    have h1 : e.symm x = ⟨_, hmem⟩ := Subtype.ext hu
    rw [← h1, MulEquiv.apply_symm_apply]
  · rw [← map_pow]
    have : (⟨x, hxN⟩ : N) ^ 4 = 1 := Subtype.ext (by simpa using hx4)
    rw [this, map_one]

end pull

@[expose] def pslCover {X : Type*} [Group X]
    (e₀ : X ≃* ProjectiveSpecialLinearGroup (Fin n) K) : SpecialLinearGroup (Fin n) K →* X :=
  e₀.symm.toMonoidHom.comp (QuotientGroup.mk' _)

theorem pslCover_surjective {X : Type*} [Group X]
    (e₀ : X ≃* ProjectiveSpecialLinearGroup (Fin n) K) : Function.Surjective (pslCover e₀) :=
  e₀.symm.surjective.comp (QuotientGroup.mk'_surjective _)

theorem pslCover_eq_one_iff {X : Type*} [Group X]
    (e₀ : X ≃* ProjectiveSpecialLinearGroup (Fin n) K) (s : SpecialLinearGroup (Fin n) K) :
    pslCover e₀ s = 1 ↔ s ∈ center (SpecialLinearGroup (Fin n) K) := by
  change e₀.symm (QuotientGroup.mk' _ s) = 1 ↔ _
  rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem mem_center_of_mulVec_eq_smul {g : SpecialLinearGroup (Fin n) K} {c : K}
    (h : ∀ v, (g : Matrix (Fin n) (Fin n) K) *ᵥ v = c • v) :
    g ∈ center (SpecialLinearGroup (Fin n) K) := by
  have hg : (g : Matrix (Fin n) (Fin n) K) = scalar (Fin n) c := by
    refine Matrix.ext_iff_mulVec.mpr fun v => ?_
    rw [h, scalar_apply, ← smul_one_eq_diagonal, Matrix.smul_mulVec, Matrix.one_mulVec]
  refine Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨c, ?_, hg.symm⟩
  have h1 := g.2
  rw [hg, scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ] at h1
  exact h1

@[expose] def diagTwo {F : Type*} [One F] {m : ℕ} (x y : F) : Fin m → F :=
  fun i => if (i : ℕ) = 0 then x else if (i : ℕ) = 1 then y else 1

theorem prod_diagTwo {F : Type*} [CommMonoid F] {m : ℕ} (hm : 2 ≤ m) (x y : F) :
    ∏ i, diagTwo (m := m) x y i = x * y := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp [diagTwo]

@[expose] def diagSL {F : Type*} [Field F] {m : ℕ} (hm : 2 ≤ m) (x y : F) (hxy : x * y = 1) :
    SpecialLinearGroup (Fin m) F :=
  ⟨diagonal (diagTwo x y), by rw [det_diagonal, prod_diagTwo hm, hxy]⟩

theorem diagSL_pow_four {F : Type*} [Field F] {m : ℕ} (hm : 2 ≤ m) {x y : F} (hxy : x * y = 1)
    (hx : x ^ 4 = 1) (hy : y ^ 4 = 1) : diagSL hm x y hxy ^ 4 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow]
  change diagonal (diagTwo x y) ^ 4 = 1
  rw [diagonal_pow, ← diagonal_one]
  congr 1
  funext i
  simp only [Pi.pow_apply, diagTwo]
  split_ifs <;> simp [hx, hy]

theorem diagSL_apply_zero {F : Type*} [Field F] {m : ℕ} (hm : 2 ≤ m) {x y : F}
    (hxy : x * y = 1) :
    (diagSL hm x y hxy : Matrix (Fin m) (Fin m) F) ⟨0, by omega⟩ ⟨0, by omega⟩ = x := by
  simp [diagSL, diagTwo]

theorem diagSL_apply_one {F : Type*} [Field F] {m : ℕ} (hm : 2 ≤ m) {x y : F}
    (hxy : x * y = 1) :
    (diagSL hm x y hxy : Matrix (Fin m) (Fin m) F) ⟨1, by omega⟩ ⟨1, by omega⟩ = y := by
  simp [diagSL, diagTwo]

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
