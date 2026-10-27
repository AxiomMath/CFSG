module

public import CFSG.LieType.Universal.Spin.RootElements

public section

namespace CFSG.ClassicalInvolution.PhanB3.H

open CliffordAlgebra QuadraticMap CFSG.LieType.Universal.Spin

section Neg
variable {K : Type*} [Field K] {V W : Type*} [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] (Q : QuadraticForm K V) (Q' : QuadraticForm K W)
  (κ : V →ₗ[K] W) (hκ : ∀ v, Q' (κ v) = - Q v)

@[expose] noncomputable def negBil : V →ₗ[K] V →ₗ[K] CliffordAlgebra Q' :=
  -(LinearMap.mul K (CliffordAlgebra Q')).compl₁₂ ((CliffordAlgebra.ι Q').comp κ)
    ((CliffordAlgebra.ι Q').comp κ)

theorem negBil_apply (a b : V) :
    negBil Q' κ a b = -(ι Q' (κ a) * ι Q' (κ b)) := rfl

noncomputable def negEven : CliffordAlgebra.even Q →ₐ[K] CliffordAlgebra Q' :=
  CliffordAlgebra.even.lift Q
    { bilin := negBil Q' κ
      contract := fun m => by
        rw [negBil_apply, ι_sq_scalar, hκ, map_neg, neg_neg]
      contract_mid := fun a b c => by
        rw [negBil_apply, negBil_apply, negBil_apply, neg_mul_neg]
        calc ι Q' (κ a) * ι Q' (κ b) * (ι Q' (κ b) * ι Q' (κ c))
            = ι Q' (κ a) * (ι Q' (κ b) * ι Q' (κ b)) * ι Q' (κ c) := by simp only [mul_assoc]
          _ = Q b • -(ι Q' (κ a) * ι Q' (κ c)) := by
            rw [ι_sq_scalar, hκ, map_neg, mul_neg, neg_mul, smul_neg, neg_inj, Algebra.smul_def,
              ← Algebra.commutes, mul_assoc] }

theorem negEven_ι (a b : V) :
    negEven Q Q' κ hκ ⟨ι Q a * ι Q b, ι_mul_ι_mem_evenOdd_zero Q a b⟩ =
      -(ι Q' (κ a) * ι Q' (κ b)) :=
  CliffordAlgebra.even.lift_ι Q _ a b

theorem one_add_mem_even (w u : V) (c : K) :
    (1 + c • (ι Q w * ι Q u) : CliffordAlgebra Q) ∈ CliffordAlgebra.even Q := by
  refine add_mem (one_mem _) (Subalgebra.smul_mem _ ?_ c)
  exact ι_mul_ι_mem_evenOdd_zero Q w u

theorem negEven_root (w u : V) (c : K) :
    negEven Q Q' κ hκ ⟨1 + c • (ι Q w * ι Q u), one_add_mem_even Q w u c⟩ =
      1 + (-c) • (ι Q' (κ w) * ι Q' (κ u)) := by
  have h : (⟨1 + c • (ι Q w * ι Q u), one_add_mem_even Q w u c⟩ : CliffordAlgebra.even Q) =
      1 + c • ⟨ι Q w * ι Q u, ι_mul_ι_mem_evenOdd_zero Q w u⟩ := rfl
  rw [h, map_add, map_smul, map_one, negEven_ι, smul_neg, neg_smul]

@[expose] noncomputable def negSpinHom : spinGroup Q →* CliffordAlgebra Q' where
  toFun x := negEven Q Q' κ hκ ⟨x, spinGroup.mem_even x.2⟩
  map_one' := by
    have : (⟨((1 : spinGroup Q) : CliffordAlgebra Q), spinGroup.mem_even (1 : spinGroup Q).2⟩ :
        CliffordAlgebra.even Q) = 1 := rfl
    rw [this, map_one]
  map_mul' x y := by
    have : (⟨((x * y : spinGroup Q) : CliffordAlgebra Q), spinGroup.mem_even (x * y).2⟩ :
        CliffordAlgebra.even Q) = ⟨x, spinGroup.mem_even x.2⟩ * ⟨y, spinGroup.mem_even y.2⟩ := rfl
    rw [this, map_mul]

theorem negSpinHom_apply (x : spinGroup Q) :
    negSpinHom Q Q' κ hκ x = negEven Q Q' κ hκ ⟨x, spinGroup.mem_even x.2⟩ := rfl

theorem negSpinHom_root (x : spinGroup Q) {w u : V} {c : K}
    (hx : (x : CliffordAlgebra Q) = 1 + c • (ι Q w * ι Q u)) :
    negSpinHom Q Q' κ hκ x = 1 + (-c) • (ι Q' (κ w) * ι Q' (κ u)) := by
  have : (⟨x, spinGroup.mem_even x.2⟩ : CliffordAlgebra.even Q) =
      ⟨1 + c • (ι Q w * ι Q u), one_add_mem_even Q w u c⟩ := Subtype.ext hx
  show negEven Q Q' κ hκ ⟨x, spinGroup.mem_even x.2⟩ = _
  rw [this, negEven_root]

section Hom
variable {Γ : Type*} [Group Γ] (φ : Γ →* spinGroup Q)

@[expose] noncomputable def thetaC : Γ →* CliffordAlgebra Q' := (negSpinHom Q Q' κ hκ).comp φ

theorem thetaC_mem_inv {g : Γ} (h : thetaC Q Q' κ hκ φ g ∈ spinGroup Q') :
    thetaC Q Q' κ hκ φ g⁻¹ ∈ spinGroup Q' := by
  set y : spinGroup Q' := ⟨_, h⟩ with hy
  have h1 : thetaC Q Q' κ hκ φ g⁻¹ * thetaC Q Q' κ hκ φ g = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  have h2 : (y : CliffordAlgebra Q') * ((y⁻¹ : spinGroup Q') : CliffordAlgebra Q') = 1 := by
    rw [← Submonoid.coe_mul, mul_inv_cancel, Submonoid.coe_one]
  have h3 : thetaC Q Q' κ hκ φ g⁻¹ = ((y⁻¹ : spinGroup Q') : CliffordAlgebra Q') := by
    calc thetaC Q Q' κ hκ φ g⁻¹ = thetaC Q Q' κ hκ φ g⁻¹ * ((y : CliffordAlgebra Q') *
          ((y⁻¹ : spinGroup Q') : CliffordAlgebra Q')) := by rw [h2, mul_one]
      _ = (thetaC Q Q' κ hκ φ g⁻¹ * thetaC Q Q' κ hκ φ g) *
          ((y⁻¹ : spinGroup Q') : CliffordAlgebra Q') := by rw [← mul_assoc]
      _ = _ := by rw [h1, one_mul]
  rw [h3]
  exact (y⁻¹).2

theorem thetaC_mem {S : Set Γ} (hS : Subgroup.closure S = ⊤)
    (hmem : ∀ s ∈ S, thetaC Q Q' κ hκ φ s ∈ spinGroup Q') (g : Γ) :
    thetaC Q Q' κ hκ φ g ∈ spinGroup Q' := by
  have hg : g ∈ Subgroup.closure S := by rw [hS]; trivial
  induction hg using Subgroup.closure_induction with
  | mem s hs => exact hmem s hs
  | one => rw [map_one]; exact one_mem _
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  | inv a _ ha => exact thetaC_mem_inv Q Q' κ hκ φ ha

@[expose] noncomputable def negTheta {S : Set Γ} (hS : Subgroup.closure S = ⊤)
    (hmem : ∀ s ∈ S, thetaC Q Q' κ hκ φ s ∈ spinGroup Q') : Γ →* spinGroup Q' :=
  (thetaC Q Q' κ hκ φ).codRestrict (spinGroup Q') (thetaC_mem Q Q' κ hκ φ hS hmem)

theorem coe_negTheta {S : Set Γ} (hS : Subgroup.closure S = ⊤)
    (hmem : ∀ s ∈ S, thetaC Q Q' κ hκ φ s ∈ spinGroup Q') (g : Γ) :
    ((negTheta Q Q' κ hκ φ hS hmem g : spinGroup Q') : CliffordAlgebra Q') =
      negSpinHom Q Q' κ hκ (φ g) := rfl
end Hom

section Nat
variable {Q Q' κ}

theorem polar_κ (hκ : ∀ v, Q' (κ v) = - Q v) (a b : V) :
    polar Q' (κ a) (κ b) = - polar Q a b := by
  simp only [QuadraticMap.polar, ← map_add, hκ]
  ring

theorem spinAction_negSpinHom_root (hκ : ∀ v, Q' (κ v) = - Q v) (x : spinGroup Q) {w u : V}
    {c : K} (hu : Q u = 0)
    (huw : polar Q u w = 0) (hx : (x : CliffordAlgebra Q) = 1 + c • (ι Q w * ι Q u))
    (y : spinGroup Q') (hy : (y : CliffordAlgebra Q') = negSpinHom Q Q' κ hκ x) (v : V) :
    spinAction Q' y (κ v) = κ (spinAction Q x v) := by
  have hx' : (x : CliffordAlgebra Q) = 1 + ι Q (c • w) * ι Q u := by
    rw [hx, map_smul, smul_mul_assoc]
  have h1 := spinAction_apply_of_coe_eq Q hu (by rw [polar_smul_right, huw, smul_zero]) hx' v
  have hy' : (y : CliffordAlgebra Q') = 1 + ι Q' ((-c) • κ w) * ι Q' (κ u) := by
    rw [hy, negSpinHom_root Q Q' κ hκ x hx, map_smul, smul_mul_assoc]
  have hu' : Q' (κ u) = 0 := by rw [hκ, hu, neg_zero]
  have huw' : polar Q' (κ u) ((-c) • κ w) = 0 := by
    rw [polar_smul_right, polar_κ hκ, huw]; simp
  rw [spinAction_apply_of_coe_eq Q' hu' huw' hy' (κ v), h1]
  simp only [map_add, map_sub, map_smul, polar_κ hκ, polar_smul_right, QuadraticMap.map_smul,
    smul_eq_mul, hκ]
  module

theorem spinAction_negSpinHom_root_fix (hκ : ∀ v, Q' (κ v) = - Q v) (x : spinGroup Q) {w u : V}
    {c : K} (hx : (x : CliffordAlgebra Q) = 1 + c • (ι Q w * ι Q u))
    (y : spinGroup Q') (hy : (y : CliffordAlgebra Q') = negSpinHom Q Q' κ hκ x) {p : W}
    (hp : ∀ v, polar Q' p (κ v) = 0) (hu : Q u = 0) (huw : polar Q u w = 0) :
    spinAction Q' y p = p := by
  have hy' : (y : CliffordAlgebra Q') = 1 + ι Q' ((-c) • κ w) * ι Q' (κ u) := by
    rw [hy, negSpinHom_root Q Q' κ hκ x hx, map_smul, smul_mul_assoc]
  have hu' : Q' (κ u) = 0 := by rw [hκ, hu, neg_zero]
  have huw' : polar Q' (κ u) ((-c) • κ w) = 0 := by
    rw [polar_smul_right, polar_κ hκ, huw]; simp
  rw [spinAction_apply_of_coe_eq Q' hu' huw' hy' p, hp u, polar_smul_right, hp w]
  simp
end Nat

section Master
variable {Γ : Type*} [Group Γ]

theorem exists_negTheta (hκ : ∀ v, Q' (κ v) = - Q v) (φ : Γ →* spinGroup Q) {S : Set Γ}
    (hS : Subgroup.closure S = ⊤)
    (hroot : ∀ s ∈ S, ∃ (w u : V) (c : K), Q u = 0 ∧ polar Q u w = 0 ∧
      (φ s : CliffordAlgebra Q) = 1 + c • (ι Q w * ι Q u))
    (haux : ∃ a : W, IsUnit (Q' a) ∧ ∀ v, polar Q' a (κ v) = 0) :
    ∃ θ : Γ →* spinGroup Q',
      (∀ g, (θ g : CliffordAlgebra Q') = negSpinHom Q Q' κ hκ (φ g)) ∧
      (∀ g v, spinAction Q' (θ g) (κ v) = κ (spinAction Q (φ g) v)) ∧
      (∀ g (p : W), (∀ v, polar Q' p (κ v) = 0) → spinAction Q' (θ g) p = p) := by
  obtain ⟨a, ha, hpa⟩ := haux
  have hmem : ∀ s ∈ S, thetaC Q Q' κ hκ φ s ∈ spinGroup Q' := by
    intro s hs
    obtain ⟨w, u, c, hu, huw, hx⟩ := hroot s hs
    have h1 : thetaC Q Q' κ hκ φ s = 1 + (-c) • (ι Q' (κ w) * ι Q' (κ u)) :=
      negSpinHom_root Q Q' κ hκ (φ s) hx
    rw [h1]
    refine one_add_smul_ι_mul_ι_mem_spinGroup Q' (by rw [hκ, hu, neg_zero]) ?_ ?_ ?_ ha (-c)
    · rw [polar_κ hκ, huw, neg_zero]
    · rw [polar_comm]; exact hpa u
    · rw [polar_comm]; exact hpa w
  set θ := negTheta Q Q' κ hκ φ hS hmem with hθ
  have hcoe : ∀ g, (θ g : CliffordAlgebra Q') = negSpinHom Q Q' κ hκ (φ g) := fun g => rfl
  have hmul : ∀ (a b : Γ) (x : W), spinAction Q' (θ (a * b)) x =
      spinAction Q' (θ a) (spinAction Q' (θ b) x) := by
    intro a b x
    rw [map_mul, map_mul, LinearEquiv.mul_apply]
  have hone : ∀ x : W, spinAction Q' (θ 1) x = x := by
    intro x
    rw [map_one, map_one]
    rfl
  have hinv : ∀ (a : Γ) (x : W), spinAction Q' (θ a) (spinAction Q' (θ a⁻¹) x) = x := by
    intro a x
    rw [← hmul, mul_inv_cancel, hone]
  refine ⟨θ, hcoe, ?_, ?_⟩
  · intro g
    have hg : g ∈ Subgroup.closure S := by rw [hS]; trivial
    induction hg using Subgroup.closure_induction with
    | mem s hs =>
      obtain ⟨w, u, c, hu, huw, hx⟩ := hroot s hs
      intro v
      exact spinAction_negSpinHom_root hκ (φ s) hu huw hx (θ s) (hcoe s) v
    | one => intro v; rw [hone, map_one, map_one]; rfl
    | mul a b _ _ ha hb =>
      intro v
      have e : spinAction Q (φ (a * b)) v = spinAction Q (φ a) (spinAction Q (φ b) v) := by
        rw [map_mul, map_mul, LinearEquiv.mul_apply]
      rw [hmul, hb, ha, e]
    | inv a _ ha =>
      intro v
      apply (spinAction Q' (θ a)).injective
      have e : spinAction Q (φ a) (spinAction Q (φ a⁻¹) v) = v := by
        rw [← LinearEquiv.mul_apply, ← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one]
        rfl
      rw [hinv, ha, e]
  · intro g p hp
    have hg : g ∈ Subgroup.closure S := by rw [hS]; trivial
    induction hg using Subgroup.closure_induction with
    | mem s hs =>
      obtain ⟨w, u, c, hu, huw, hx⟩ := hroot s hs
      exact spinAction_negSpinHom_root_fix hκ (φ s) hx (θ s) (hcoe s) hp hu huw
    | one => exact hone p
    | mul a b _ _ ha hb => rw [hmul, hb, ha]
    | inv a _ ha =>
      apply (spinAction Q' (θ a)).injective
      rw [hinv, ha]
end Master

end Neg

end CFSG.ClassicalInvolution.PhanB3.H
