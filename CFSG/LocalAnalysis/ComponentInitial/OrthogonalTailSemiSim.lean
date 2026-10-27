module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailLinearRigidity
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailPolar

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module Submodule
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointAction
  (Points pointMk pointMk_submodule exists_eq_pointMk)

variable {K : Type*} [Field K] {V₁ V₂ V₃ : Type*} [AddCommGroup V₁] [Module K V₁]
  [AddCommGroup V₂] [Module K V₂] [AddCommGroup V₃] [Module K V₃]

structure SemiSim (Q₁ : QuadraticForm K V₁) (Q₂ : QuadraticForm K V₂) where
  e : V₁ ≃ V₂
  σ : K ≃+* K
  μ : K
  μ_ne_zero : μ ≠ 0
  map_add' : ∀ x y, e (x + y) = e x + e y
  map_smul' : ∀ (c : K) x, e (c • x) = σ c • e x
  map_quad' : ∀ v, Q₂ (e v) = μ * σ (Q₁ v)

variable {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂} {Q₃ : QuadraticForm K V₃}

section Basic

variable (T : SemiSim Q₁ Q₂)

theorem SemiSim.e_zero : T.e 0 = 0 := by
  rw [← zero_smul K (0 : V₁), T.map_smul', map_zero, zero_smul]

theorem SemiSim.e_neg (x : V₁) : T.e (-x) = -T.e x := by
  rw [← neg_one_smul K x, T.map_smul', map_neg, map_one, neg_one_smul]

theorem SemiSim.e_sub (x y : V₁) : T.e (x - y) = T.e x - T.e y := by
  rw [sub_eq_add_neg, T.map_add', T.e_neg, ← sub_eq_add_neg]

theorem SemiSim.e_ne_zero {x : V₁} (hx : x ≠ 0) : T.e x ≠ 0 := fun h =>
  hx (T.e.injective (by rw [h, T.e_zero]))

theorem SemiSim.polar_e (x y : V₁) :
    polar Q₂ (T.e x) (T.e y) = T.μ * T.σ (polar Q₁ x y) := by
  simp only [QuadraticMap.polar, ← T.map_add', T.map_quad', map_sub]
  ring

theorem SemiSim.polar_e_eq_zero_iff (x y : V₁) :
    polar Q₂ (T.e x) (T.e y) = 0 ↔ polar Q₁ x y = 0 := by
  rw [T.polar_e, mul_eq_zero, or_iff_right T.μ_ne_zero, map_eq_zero_iff T.σ T.σ.injective]

@[expose] def SemiSim.symm : SemiSim Q₂ Q₁ where
  e := T.e.symm
  σ := T.σ.symm
  μ := T.σ.symm T.μ⁻¹
  μ_ne_zero := (map_ne_zero T.σ.symm).2 (inv_ne_zero T.μ_ne_zero)
  map_add' x y := T.e.injective (by
    rw [T.map_add', Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply])
  map_smul' c x := T.e.injective (by
    rw [T.map_smul', Equiv.apply_symm_apply, Equiv.apply_symm_apply, RingEquiv.apply_symm_apply])
  map_quad' v := by
    have h := T.map_quad' (T.e.symm v)
    rw [Equiv.apply_symm_apply] at h
    apply T.σ.injective
    rw [map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, h, ← mul_assoc,
      inv_mul_cancel₀ T.μ_ne_zero, one_mul]

theorem SemiSim.symm_e : T.symm.e = T.e.symm :=
  rfl

theorem SemiSim.symm_σ : T.symm.σ = T.σ.symm :=
  rfl

@[expose] def SemiSim.trans (S : SemiSim Q₂ Q₃) : SemiSim Q₁ Q₃ where
  e := T.e.trans S.e
  σ := T.σ.trans S.σ
  μ := S.μ * S.σ T.μ
  μ_ne_zero := mul_ne_zero S.μ_ne_zero ((map_ne_zero S.σ).2 T.μ_ne_zero)
  map_add' x y := by simp only [Equiv.trans_apply, T.map_add', S.map_add']
  map_smul' c x := by simp only [Equiv.trans_apply, T.map_smul', S.map_smul', RingEquiv.trans_apply]
  map_quad' v := by
    simp only [Equiv.trans_apply, S.map_quad', T.map_quad', map_mul, RingEquiv.trans_apply]
    ring

theorem SemiSim.trans_e (S : SemiSim Q₂ Q₃) (v : V₁) : (T.trans S).e v = S.e (T.e v) :=
  rfl

theorem SemiSim.trans_σ (S : SemiSim Q₂ Q₃) : (T.trans S).σ = T.σ.trans S.σ :=
  rfl

theorem SemiSim.trans_μ (S : SemiSim Q₂ Q₃) : (T.trans S).μ = S.μ * S.σ T.μ :=
  rfl

end Basic

@[expose] def SemiSim.ofLinear (T : V₁ ≃ₗ[K] V₂) {μ : K} (hμ : μ ≠ 0)
    (hT : ∀ v, Q₂ (T v) = μ * Q₁ v) : SemiSim Q₁ Q₂ where
  e := T.toEquiv
  σ := RingEquiv.refl K
  μ := μ
  μ_ne_zero := hμ
  map_add' := T.map_add
  map_smul' c x := T.map_smul c x
  map_quad' := hT

theorem SemiSim.ofLinear_e (T : V₁ ≃ₗ[K] V₂) {μ : K} (hμ : μ ≠ 0)
    (hT : ∀ v, Q₂ (T v) = μ * Q₁ v) (v : V₁) : (SemiSim.ofLinear T hμ hT).e v = T v :=
  rfl

theorem SemiSim.ofLinear_σ (T : V₁ ≃ₗ[K] V₂) {μ : K} (hμ : μ ≠ 0)
    (hT : ∀ v, Q₂ (T v) = μ * Q₁ v) : (SemiSim.ofLinear T hμ hT).σ = RingEquiv.refl K :=
  rfl

section MapSub

variable (T : SemiSim Q₁ Q₂)

@[expose] def SemiSim.mapSub (W : Submodule K V₁) : Submodule K V₂ where
  carrier := {y | T.symm.e y ∈ W}
  add_mem' {x y} hx hy := by
    change T.symm.e (x + y) ∈ W
    rw [T.symm.map_add']
    exact W.add_mem hx hy
  zero_mem' := by
    change T.symm.e 0 ∈ W
    rw [T.symm.e_zero]
    exact W.zero_mem
  smul_mem' c x hx := by
    change T.symm.e (c • x) ∈ W
    rw [T.symm.map_smul']
    exact W.smul_mem _ hx

theorem SemiSim.mem_mapSub {W : Submodule K V₁} {y : V₂} :
    y ∈ T.mapSub W ↔ T.e.symm y ∈ W :=
  Iff.rfl

theorem SemiSim.e_mem_mapSub {W : Submodule K V₁} {x : V₁} : T.e x ∈ T.mapSub W ↔ x ∈ W := by
  rw [T.mem_mapSub, Equiv.symm_apply_apply]

theorem SemiSim.coe_mapSub (W : Submodule K V₁) : (T.mapSub W : Set V₂) = T.e '' W := by
  rw [Equiv.image_eq_preimage_symm]
  rfl

theorem SemiSim.mapSub_mono {W W' : Submodule K V₁} (h : W ≤ W') : T.mapSub W ≤ T.mapSub W' :=
  fun _ hy => h hy

theorem SemiSim.symm_mapSub_mapSub (W : Submodule K V₁) : T.symm.mapSub (T.mapSub W) = W := by
  ext x
  change T.e.symm (T.e x) ∈ W ↔ x ∈ W
  rw [Equiv.symm_apply_apply]

theorem SemiSim.mapSub_symm_mapSub (W : Submodule K V₂) : T.mapSub (T.symm.mapSub W) = W := by
  ext y
  change T.e (T.e.symm y) ∈ W ↔ y ∈ W
  rw [Equiv.apply_symm_apply]

theorem SemiSim.mapSub_le_iff {W W' : Submodule K V₁} : T.mapSub W ≤ T.mapSub W' ↔ W ≤ W' := by
  refine ⟨fun h => ?_, T.mapSub_mono⟩
  rw [← T.symm_mapSub_mapSub W, ← T.symm_mapSub_mapSub W']
  exact T.symm.mapSub_mono h

theorem SemiSim.mapSub_span_singleton (v : V₁) : T.mapSub (K ∙ v) = K ∙ T.e v := by
  ext y
  rw [T.mem_mapSub, mem_span_singleton, mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨T.σ c, ?_⟩
    rw [← T.map_smul', hc, Equiv.apply_symm_apply]
  · rintro ⟨c, rfl⟩
    refine ⟨T.σ.symm c, T.e.injective ?_⟩
    rw [T.map_smul', RingEquiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem SemiSim.totSing_mapSub {W : Submodule K V₁} (hW : ∀ x ∈ W, Q₁ x = 0) :
    ∀ y ∈ T.mapSub W, Q₂ y = 0 := by
  intro y hy
  rw [← Equiv.apply_symm_apply T.e y, T.map_quad', hW (T.e.symm y) hy, map_zero, mul_zero]

theorem SemiSim.ofLinear_mapSub (T : V₁ ≃ₗ[K] V₂) {μ : K} (hμ : μ ≠ 0)
    (hT : ∀ v, Q₂ (T v) = μ * Q₁ v) (W : Submodule K V₁) :
    (SemiSim.ofLinear T hμ hT).mapSub W = W.map (T : V₁ →ₗ[K] V₂) := by
  ext y
  rw [Submodule.mem_map_equiv]
  rfl

end MapSub

section Restrict

variable (S : SemiSim Q₁ Q₂)

@[expose] def SemiSim.restrict (U₁ : Submodule K V₁) (U₂ : Submodule K V₂)
    (hU : S.mapSub U₁ = U₂) : SemiSim (Q₁.comp U₁.subtype) (Q₂.comp U₂.subtype) where
  e := Equiv.subtypeEquiv S.e (fun _ => by rw [← hU]; exact S.e_mem_mapSub.symm)
  σ := S.σ
  μ := S.μ
  μ_ne_zero := S.μ_ne_zero
  map_add' x y := Subtype.ext (by simpa using S.map_add' (x : V₁) (y : V₁))
  map_smul' c x := Subtype.ext (by simpa using S.map_smul' c (x : V₁))
  map_quad' x := by simpa using S.map_quad' (x : V₁)

theorem SemiSim.restrict_e (U₁ : Submodule K V₁) (U₂ : Submodule K V₂)
    (hU : S.mapSub U₁ = U₂) (x : U₁) :
    ((S.restrict U₁ U₂ hU).e x : V₂) = S.e (x : V₁) :=
  rfl

theorem SemiSim.restrict_σ (U₁ : Submodule K V₁) (U₂ : Submodule K V₂)
    (hU : S.mapSub U₁ = U₂) : (S.restrict U₁ U₂ hU).σ = S.σ :=
  rfl

theorem SemiSim.restrict_μ (U₁ : Submodule K V₁) (U₂ : Submodule K V₂)
    (hU : S.mapSub U₁ = U₂) : (S.restrict U₁ U₂ hU).μ = S.μ :=
  rfl

end Restrict

section Prod

variable {E₁ E₂ : Type*} [AddCommGroup E₁] [Module K E₁] [AddCommGroup E₂] [Module K E₂]
  {R₁ : QuadraticForm K E₁} {R₂ : QuadraticForm K E₂}

@[expose] def SemiSim.prod (S : SemiSim Q₁ Q₂) (T : SemiSim R₁ R₂)
    (hσ : T.σ = S.σ) (hμ : T.μ = S.μ) :
    SemiSim (Q₁.prod R₁) (Q₂.prod R₂) where
  e := S.e.prodCongr T.e
  σ := S.σ
  μ := S.μ
  μ_ne_zero := S.μ_ne_zero
  map_add' x y := by
    apply Prod.ext <;> simp [Equiv.prodCongr_apply, S.map_add', T.map_add']
  map_smul' c x := by
    apply Prod.ext <;> simp [Equiv.prodCongr_apply, S.map_smul', T.map_smul', hσ]
  map_quad' x := by
    change Q₂ (S.e x.1) + R₂ (T.e x.2) = S.μ * S.σ (Q₁ x.1 + R₁ x.2)
    rw [S.map_quad', T.map_quad', hμ, hσ, map_add, mul_add]

theorem SemiSim.prod_e (S : SemiSim Q₁ Q₂) (T : SemiSim R₁ R₂)
    (hσ : T.σ = S.σ) (hμ : T.μ = S.μ) (x : V₁ × E₁) :
    (S.prod T hσ hμ).e x = (S.e x.1, T.e x.2) :=
  rfl

theorem SemiSim.prod_σ (S : SemiSim Q₁ Q₂) (T : SemiSim R₁ R₂)
    (hσ : T.σ = S.σ) (hμ : T.μ = S.μ) : (S.prod T hσ hμ).σ = S.σ :=
  rfl

theorem SemiSim.prod_μ (S : SemiSim Q₁ Q₂) (T : SemiSim R₁ R₂)
    (hσ : T.σ = S.σ) (hμ : T.μ = S.μ) : (S.prod T hσ hμ).μ = S.μ :=
  rfl

theorem SemiSim.mapSub_prod (S : SemiSim Q₁ Q₂) (T : SemiSim R₁ R₂)
    (hσ : T.σ = S.σ) (hμ : T.μ = S.μ)
    (P : Submodule K V₁) (W : Submodule K E₁) :
    (S.prod T hσ hμ).mapSub (P.prod W) = (S.mapSub P).prod (T.mapSub W) := by
  ext y
  rw [SemiSim.mem_mapSub, Submodule.mem_prod, Submodule.mem_prod]
  change (S.e.symm y.1 ∈ P ∧ T.e.symm y.2 ∈ W) ↔
    (S.e.symm y.1 ∈ P ∧ T.e.symm y.2 ∈ W)
  rfl

end Prod

theorem SemiSim.exists_extension_prod_isometric
    {K : Type*} [Field K] {V E : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup E] [Module K E]
    {Q : QuadraticForm K V} {R : QuadraticForm K E}
    (S : SemiSim Q Q) (U : Submodule K V) (hU : S.mapSub U = U)
    (j : R.IsometryEquiv (Q.comp U.subtype)) :
    ∃ T : SemiSim (Q.prod R) (Q.prod R),
      T.σ = S.σ ∧ T.μ = S.μ ∧
      (∀ v w, (T.e (v,w)).1 = S.e v) ∧
      (∀ v w, ((j ((T.e (v,w)).2) : U) : V) = S.e ((j w : U) : V)) ∧
      (∀ v, T.e (v,0) = (S.e v,0)) := by
  let e : E ≃ₗ[K] U := j.toLinearEquiv
  let j₁ : SemiSim R (Q.comp U.subtype) :=
    SemiSim.ofLinear e one_ne_zero (fun v => by
      simpa [e] using (j.map_app v).trans (one_mul (R v)).symm)
  let j₂ : SemiSim (Q.comp U.subtype) R :=
    SemiSim.ofLinear e.symm one_ne_zero (fun u => by
      simpa [e] using (j.symm.map_app u).trans
        (one_mul ((Q.comp U.subtype) u)).symm)
  let SU : SemiSim (Q.comp U.subtype) (Q.comp U.subtype) := S.restrict U U hU
  let D : SemiSim R (Q.comp U.subtype) := j₁.trans SU
  let C : SemiSim R R := D.trans j₂
  have hj₁σ : j₁.σ = RingEquiv.refl K := rfl
  have hj₁μ : j₁.μ = 1 := rfl
  have hj₂σ : j₂.σ = RingEquiv.refl K := rfl
  have hj₂μ : j₂.μ = 1 := rfl
  have hSUσ : SU.σ = S.σ := rfl
  have hSUμ : SU.μ = S.μ := rfl
  have hCσ : C.σ = S.σ := by
    have h1 : C.σ = D.σ.trans j₂.σ := SemiSim.trans_σ D j₂
    have h2 : D.σ = j₁.σ.trans SU.σ := SemiSim.trans_σ j₁ SU
    rw [h1, h2, hj₁σ, hSUσ, hj₂σ]
    refine RingEquiv.ext fun x => ?_
    simp
  have hCμ : C.μ = S.μ := by
    have h1 : C.μ = j₂.μ * j₂.σ D.μ := SemiSim.trans_μ D j₂
    have h2 : D.μ = SU.μ * SU.σ j₁.μ := SemiSim.trans_μ j₁ SU
    rw [h1, h2, hj₁μ, hj₂μ, hj₂σ, hSUμ, hSUσ]
    simp
  refine ⟨S.prod C hCσ hCμ, rfl, rfl, ?_, ?_, ?_⟩
  · intro v w
    rfl
  · intro v w
    change ((e (e.symm (SU.e (e w))) : U) : V) = S.e ((j w : U) : V)
    rw [LinearEquiv.apply_symm_apply]
    rw [show ((SU.e (e w) : U) : V) = S.e ((e w : U) : V) from
      SemiSim.restrict_e S U U hU (e w)]
    rfl
  · intro v
    change (S.e v, C.e 0) = (S.e v, 0)
    rw [SemiSim.e_zero C]

section Points

variable (T : SemiSim Q₁ Q₂)

theorem SemiSim.finrank_mapSub_point (L : Points Q₁) : finrank K (T.mapSub L.val) = 1 := by
  obtain ⟨x, hx, hQx, rfl⟩ := exists_eq_pointMk L
  rw [pointMk_submodule, T.mapSub_span_singleton]
  exact finrank_span_singleton (T.e_ne_zero hx)

@[expose] noncomputable def SemiSim.pointEquiv : Points Q₁ ≃ Points Q₂ where
  toFun L := ⟨T.mapSub L.val, T.finrank_mapSub_point L, T.totSing_mapSub L.2.2⟩
  invFun L := ⟨T.symm.mapSub L.val, T.symm.finrank_mapSub_point L, T.symm.totSing_mapSub L.2.2⟩
  left_inv L := Subtype.ext (T.symm_mapSub_mapSub L.val)
  right_inv L := Subtype.ext (T.mapSub_symm_mapSub L.val)

theorem SemiSim.coe_pointEquiv (L : Points Q₁) : (T.pointEquiv L).val = T.mapSub L.val :=
  rfl

theorem SemiSim.coe_pointEquiv_symm (L : Points Q₂) :
    (T.pointEquiv.symm L).val = T.symm.mapSub L.val :=
  rfl

theorem SemiSim.pointEquiv_pointMk (x : V₁) (hx : x ≠ 0) (hQx : Q₁ x = 0) :
    (T.pointEquiv (pointMk x hx hQx)).val = K ∙ T.e x := by
  rw [T.coe_pointEquiv, pointMk_submodule, T.mapSub_span_singleton]

theorem SemiSim.polarOrtho_pointEquiv (L M : Points Q₁) :
    PolarOrtho Q₁ L.val M.val ↔ PolarOrtho Q₂ (T.pointEquiv L).val (T.pointEquiv M).val := by
  obtain ⟨x, hx, hQx, rfl⟩ := exists_eq_pointMk L
  obtain ⟨y, hy, hQy, rfl⟩ := exists_eq_pointMk M
  rw [T.pointEquiv_pointMk, T.pointEquiv_pointMk, pointMk_submodule, pointMk_submodule,
    polarOrtho_span_singleton_iff_polar, polarOrtho_span_singleton_iff_polar,
    T.polar_e_eq_zero_iff]

theorem SemiSim.image_ptsIn_pointEquiv (W : Submodule K V₁) :
    T.pointEquiv '' ptsIn Q₁ W = ptsIn Q₂ (T.mapSub W) := by
  ext L
  constructor
  · rintro ⟨M, hM, rfl⟩
    exact T.mapSub_mono hM
  · intro hL
    refine ⟨T.pointEquiv.symm L, ?_, Equiv.apply_symm_apply _ _⟩
    change T.symm.mapSub L.val ≤ W
    rw [← T.symm_mapSub_mapSub W]
    exact T.symm.mapSub_mono hL

theorem SemiSim.image_ptsIn_pointEquiv_symm (W : Submodule K V₂) :
    T.pointEquiv.symm '' ptsIn Q₂ W = ptsIn Q₁ (T.symm.mapSub W) := by
  ext L
  constructor
  · rintro ⟨M, hM, rfl⟩
    exact T.symm.mapSub_mono hM
  · intro hL
    refine ⟨T.pointEquiv L, ?_, Equiv.symm_apply_apply _ _⟩
    change T.mapSub L.val ≤ W
    rw [← T.mapSub_symm_mapSub W]
    exact T.mapSub_mono hL

variable (φ : Points Q₃ ≃ Points Q₂)
  (hφ : ∀ L M : Points Q₃, PolarOrtho Q₃ L.val M.val ↔ PolarOrtho Q₂ (φ L).val (φ M).val)
include hφ

theorem SemiSim.polarOrtho_trans_symm (L M : Points Q₃) :
    PolarOrtho Q₃ L.val M.val ↔
      PolarOrtho Q₁ ((φ.trans T.pointEquiv.symm) L).val ((φ.trans T.pointEquiv.symm) M).val := by
  have h := T.polarOrtho_pointEquiv (T.pointEquiv.symm (φ L)) (T.pointEquiv.symm (φ M))
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
  rw [hφ, Equiv.trans_apply, Equiv.trans_apply]
  exact h.symm

theorem SemiSim.polarImage₂_trans_symm (h₃ : IsInfOfMax Q₃) {W : Submodule K V₃}
    (hW : ∀ x ∈ W, Q₃ x = 0) :
    polarImage₂ (φ.trans T.pointEquiv.symm) W = T.symm.mapSub (polarImage₂ φ W) := by
  refine (eq_polarImage₂ _ (T.symm.totSing_mapSub (totSing_polarImage₂ φ hφ hW)) ?_).symm
  rw [Equiv.coe_trans, Set.image_comp, ← ptsIn_polarImage₂ φ hφ h₃ hW,
    T.image_ptsIn_pointEquiv_symm]

end Points

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
