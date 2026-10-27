module

public import CFSG.RankThree.PartOne.CTP.SeitzMaxSL2

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.CTP

namespace RootPairOrth

section Hom

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

@[expose] def quadEmb (P P' : HypPair Q) : Matrix (Fin 2) (Fin 2) K →ₗ[K] V where
  toFun X := (X 0 0 • P.e + X 1 1 • P.f) + (X 0 1 • (-P'.e) + X 1 0 • P'.f)
  map_add' X Y := by simp only [Matrix.add_apply, add_smul]; abel
  map_smul' c X := by
    simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, smul_add, smul_smul]

@[expose] def quadProj (P P' : HypPair Q) : V →ₗ[K] Matrix (Fin 2) (Fin 2) K where
  toFun v := !![polar Q v P.f, -polar Q v P'.f; polar Q v P'.e, polar Q v P.e]
  map_add' v w := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [QuadraticMap.polar_add_left, neg_add_rev, add_comm]
  map_smul' c v := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [QuadraticMap.polar_smul_left]

variable {P P' : HypPair Q}

theorem quadProj_emb (h : P.Orth P') (X : Matrix (Fin 2) (Fin 2) K) :
    quadProj P P' (quadEmb P P' X) = X := by
  have h1 : polar Q P.e P'.e = 0 := h.ee
  have h2 : polar Q P.e P'.f = 0 := h.ef
  have h3 : polar Q P.f P'.e = 0 := h.fe
  have h4 : polar Q P.f P'.f = 0 := h.ff
  have h1' : polar Q P'.e P.e = 0 := by rw [polar_comm]; exact h1
  have h2' : polar Q P'.f P.e = 0 := by rw [polar_comm]; exact h2
  have h3' : polar Q P'.e P.f = 0 := by rw [polar_comm]; exact h3
  have h4' : polar Q P'.f P.f = 0 := by rw [polar_comm]; exact h4
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [quadProj, quadEmb, QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, h1, h2, h3,
      h4, h1', h2', h3', h4', P.Q_e, P.Q_f, P'.Q_e, P'.Q_f, P.polar_ef, P.polar_fe, P'.polar_ef,
      P'.polar_fe]

@[expose] def quadExt (P P' : HypPair Q) (A : Matrix (Fin 2) (Fin 2) K) (v : V) : V :=
  v + quadEmb P P' ((A - 1) * quadProj P P' v)

theorem quadProj_ext (h : P.Orth P') (A : Matrix (Fin 2) (Fin 2) K) (v : V) :
    quadProj P P' (quadExt P P' A v) = A * quadProj P P' v := by
  rw [quadExt, map_add, quadProj_emb h, sub_mul, one_mul]
  abel

theorem quadExt_apply (A : Matrix (Fin 2) (Fin 2) K) (v : V) :
    quadExt P P' A v = v + quadEmb P P' ((A - 1) * quadProj P P' v) := rfl

theorem quadExt_mul (h : P.Orth P') (A B : Matrix (Fin 2) (Fin 2) K) (v : V) :
    quadExt P P' (A * B) v = quadExt P P' A (quadExt P P' B v) := by
  have key : (A * B - 1) * quadProj P P' v =
      (B - 1) * quadProj P P' v + (A - 1) * (B * quadProj P P' v) := by
    simp only [sub_mul, one_mul, mul_assoc]
    abel
  rw [quadExt_apply A (quadExt P P' B v), quadProj_ext h, quadExt_apply B v,
    quadExt_apply (A * B) v, key, map_add]
  abel

theorem quadExt_one (v : V) : quadExt P P' 1 v = v := by simp [quadExt]

@[expose] def quadLin (P P' : HypPair Q) (A : Matrix (Fin 2) (Fin 2) K) : V →ₗ[K] V where
  toFun := quadExt P P' A
  map_add' v w := by
    simp only [quadExt, map_add, mul_add]
    abel
  map_smul' c v := by
    simp only [quadExt, map_smul, Matrix.mul_smul, smul_add, RingHom.id_apply]

@[expose] noncomputable def quadHom (h : P.Orth P') :
    SpecialLinearGroup (Fin 2) K →* (V ≃ₗ[K] V) where
  toFun A := LinearEquiv.ofLinearMap (quadLin P P' (A : Matrix (Fin 2) (Fin 2) K))
    (quadLin P P' ((A⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
    (LinearMap.ext fun v => by
      change quadExt P P' (A : Matrix (Fin 2) (Fin 2) K)
        (quadExt P P' ((A⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) v) = v
      rw [← quadExt_mul h, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one, quadExt_one])
    (LinearMap.ext fun v => by
      change quadExt P P' ((A⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
        (quadExt P P' (A : Matrix (Fin 2) (Fin 2) K) v) = v
      rw [← quadExt_mul h, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one, quadExt_one])
  map_one' := LinearEquiv.ext fun v => by
    change quadExt P P' ((1 : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) v = v
    rw [Matrix.SpecialLinearGroup.coe_one, quadExt_one]
  map_mul' A B := LinearEquiv.ext fun v => by
    change quadExt P P' ((A * B : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) v =
      quadExt P P' (A : Matrix (Fin 2) (Fin 2) K)
        (quadExt P P' (B : Matrix (Fin 2) (Fin 2) K) v)
    rw [Matrix.SpecialLinearGroup.coe_mul, quadExt_mul h]

theorem quadHom_apply (h : P.Orth P') (A : SpecialLinearGroup (Fin 2) K) (v : V) :
    quadHom h A v = v + quadEmb P P' (((A : Matrix (Fin 2) (Fin 2) K) - 1) * quadProj P P' v) :=
  rfl

theorem quadHom_u2 (h : P.Orth P') (x : K) : quadHom h (u2 x) = eichler Q P.e ((-x) • P'.e) := by
  have hw : polar Q P.e ((-x) • P'.e) = 0 := by rw [polar_smul_right_eq, h.ee, mul_zero]
  refine LinearEquiv.ext fun v => ?_
  rw [eichler_apply P.Q_e hw, quadHom_apply, u2_coe]
  simp only [quadEmb, quadProj, LinearMap.coe_mk, AddHom.coe_mk, polar_smul_right_eq,
    map_smul_eq_sq, P'.Q_e]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  module

theorem quadHom_l2 (h : P.Orth P') (x : K) : quadHom h (l2 x) = eichler Q P.f (x • P'.f) := by
  have hw : polar Q P.f (x • P'.f) = 0 := by rw [polar_smul_right_eq, h.ff, mul_zero]
  refine LinearEquiv.ext fun v => ?_
  rw [eichler_apply P.Q_f hw, quadHom_apply, l2_coe]
  simp only [quadEmb, quadProj, LinearMap.coe_mk, AddHom.coe_mk, polar_smul_right_eq,
    map_smul_eq_sq, P'.Q_f]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  module

end Hom

section Plane

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem Q_plane {c₁ c₂ : V} (h1 : Q c₁ = 0) (h2 : Q c₂ = 0) (h12 : polar Q c₁ c₂ = 0) (a b : K) :
    Q (a • c₁ + b • c₂) = 0 := by
  rw [QuadraticMap.map_add Q (a • c₁) (b • c₂), map_smul_eq_sq, map_smul_eq_sq, h1, h2,
    polar_smul_left_eq, polar_smul_right_eq, h12]
  ring

theorem polar_plane {c₁ c₂ : V} (h1 : Q c₁ = 0) (h2 : Q c₂ = 0) (h12 : polar Q c₁ c₂ = 0)
    (a b a' b' : K) : polar Q (a • c₁ + b • c₂) (a' • c₁ + b' • c₂) = 0 := by
  have h21 : polar Q c₂ c₁ = 0 := by rw [polar_comm, h12]
  simp only [polar_add_left, polar_add_right, polar_smul_left_eq, polar_smul_right_eq,
    polar_self_eq_zero h1, polar_self_eq_zero h2, h12, h21]
  ring

theorem eichler_plane_change {c₁ c₂ : V} (h1 : Q c₁ = 0) (h2 : Q c₂ = 0)
    (h12 : polar Q c₁ c₂ = 0) (l₁ l₂ m₁ m₂ s : K) :
    eichler Q (l₁ • c₁ + l₂ • c₂) (s • (m₁ • c₁ + m₂ • c₂)) =
      eichler Q c₁ ((s * (l₁ * m₂ - l₂ * m₁)) • c₂) := by
  have hQ := Q_plane h1 h2 h12
  have hw1 : polar Q c₁ ((s * (l₁ * m₂ - l₂ * m₁)) • c₂) = 0 := by
    rw [polar_smul_right_eq, h12, mul_zero]
  have hw2 : polar Q (l₁ • c₁ + l₂ • c₂) (s • (m₁ • c₁ + m₂ • c₂)) = 0 := by
    rw [polar_smul_right_eq, polar_plane h1 h2 h12, mul_zero]
  refine LinearEquiv.ext fun v => ?_
  rw [eichler_apply (hQ l₁ l₂) hw2, eichler_apply h1 hw1]
  simp only [polar_add_right, polar_smul_right_eq, map_smul_eq_sq, hQ, h2, mul_zero, zero_mul,
    add_zero]
  module

theorem eichler_conj_similarity {g : V ≃ₗ[K] V} {μ : K} (hμ : μ ≠ 0)
    (hg : ∀ v, Q (g v) = μ * Q v) (u w : V) :
    g * eichler Q u w * g⁻¹ = eichler Q (g u) (μ⁻¹ • g w) := by
  have hpol : ∀ x y, polar Q (g x) (g y) = μ * polar Q x y := fun x y => by
    unfold QuadraticMap.polar
    rw [← g.map_add, hg, hg, hg]
    ring
  by_cases h : Q u = 0 ∧ polar Q u w = 0
  · have hgu : Q (g u) = 0 := by rw [hg, h.1, mul_zero]
    have hgw : polar Q (g u) (μ⁻¹ • g w) = 0 := by
      rw [polar_smul_right_eq, hpol, h.2]; simp
    refine LinearEquiv.ext fun x => ?_
    have hx : ∀ y, polar Q (g⁻¹ x) y = μ⁻¹ * polar Q x (g y) := fun y => by
      have := hpol (g⁻¹ x) y
      rw [LinearEquiv.apply_inv_apply'] at this
      rw [this]
      field_simp
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, eichler_apply h.1 h.2,
      eichler_apply hgu hgw, map_sub, map_add, map_smul, map_smul, LinearEquiv.apply_inv_apply', hx,
      hx, polar_smul_right_eq, map_smul_eq_sq, hg]
    field_simp
    module
  · have h' : ¬(Q (g u) = 0 ∧ polar Q (g u) (μ⁻¹ • g w) = 0) := by
      rintro ⟨h1, h2⟩
      apply h
      refine ⟨?_, ?_⟩
      · rw [hg] at h1
        exact (mul_eq_zero.mp h1).resolve_left hμ
      · rw [polar_smul_right_eq, hpol] at h2
        have := (mul_eq_zero.mp h2).resolve_left (inv_ne_zero hμ)
        exact (mul_eq_zero.mp this).resolve_left hμ
    rw [eichler_of_not h, eichler_of_not h', mul_one, mul_inv_cancel]

end Plane

end RootPairOrth

end CFSG.LieType.SeitzGeneration
