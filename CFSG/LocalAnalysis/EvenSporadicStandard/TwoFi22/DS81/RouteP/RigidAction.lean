module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Group

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

theorem eq_refl_of_trivial_mod_center_of_sup {Q : Type*} [Group Q] (Z D : Subgroup Q)
    (hZ : Z ≤ Subgroup.center Q) (hgen : D ⊔ commutator Q = ⊤) (β : Q ≃* Q)
    (hD : ∀ d ∈ D, β d = d) (hmod : ∀ q, q⁻¹ * β q ∈ Z) : β = MulEquiv.refl Q := by
  have hmul : ∀ p q : Q, (p * q)⁻¹ * β (p * q) = (p⁻¹ * β p) * (q⁻¹ * β q) := fun p q => by
    have hp : ∀ g, g * (p⁻¹ * β p) = (p⁻¹ * β p) * g :=
      Subgroup.mem_center_iff.1 (hZ (hmod p))
    calc (p * q)⁻¹ * β (p * q) = (q⁻¹ * (p⁻¹ * β p)) * β q := by rw [map_mul]; group
      _ = ((p⁻¹ * β p) * q⁻¹) * β q := by rw [← hp q⁻¹]
      _ = (p⁻¹ * β p) * (q⁻¹ * β q) := by group
  let χ : Q →* Q := { toFun := fun q => q⁻¹ * β q, map_one' := by simp, map_mul' := hmul }
  have hχ : ∀ q, χ q = q⁻¹ * β q := fun q => rfl
  have hcomm : commutator Q ≤ χ.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro p _ q _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.1 (hZ (hmod p)) (χ q)).symm
  have hDker : D ≤ χ.ker := by
    intro d hd
    rw [MonoidHom.mem_ker, hχ, hD d hd, inv_mul_cancel]
  have htop : (⊤ : Subgroup Q) ≤ χ.ker := by
    rw [← hgen]
    exact sup_le hDker hcomm
  ext q
  have hq : χ q = 1 := htop (Subgroup.mem_top q)
  rw [hχ, inv_mul_eq_one] at hq
  exact hq.symm

theorem perm_mem_orbit_of_card_orbit {H X : Type*} [Group H] [MulAction H X]
    (hcard : ∀ y z : X, Nat.card (MulAction.orbit H y) = Nat.card (MulAction.orbit H z) →
      z ∈ MulAction.orbit H y)
    (π : Equiv.Perm X) (hπ : ∀ (h : H) (y : X), π (h • y) = h • π y) (y : X) :
    π y ∈ MulAction.orbit H y := by
  refine hcard y (π y) (Nat.card_congr (Equiv.subtypeEquiv π fun z => ?_))
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨h, (hπ h y).symm⟩
  · rintro ⟨h, hh⟩
    refine ⟨h, π.injective ?_⟩
    exact (hπ h y).trans hh

section Twist

variable {Q X : Type*} [Group Q] [MulAction Q X] [MulAction.IsPretransitive Q X]

@[expose] noncomputable def twistMap (x₀ : X) (β : Q →* Q) (y : X) : X :=
  β (Classical.choose (MulAction.exists_smul_eq Q x₀ y)) • x₀

theorem twistMap_smul_base {x₀ : X} {β : Q →* Q}
    (hβ : ∀ d ∈ MulAction.stabilizer Q x₀, β d = d) (g : Q) :
    twistMap x₀ β (g • x₀) = β g • x₀ := by
  unfold twistMap
  set g' := Classical.choose (MulAction.exists_smul_eq Q x₀ (g • x₀)) with hg'
  have hg'x : g' • x₀ = g • x₀ := Classical.choose_spec (MulAction.exists_smul_eq Q x₀ (g • x₀))
  have hmem : g⁻¹ * g' ∈ MulAction.stabilizer Q x₀ := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, hg'x, inv_smul_smul]
  have h1 : β g' = β g * (g⁻¹ * g') := by
    rw [← hβ _ hmem, ← map_mul, mul_inv_cancel_left]
  rw [h1, mul_smul, MulAction.mem_stabilizer_iff.1 hmem]

theorem twistMap_smul {x₀ : X} {β : Q →* Q} (hβ : ∀ d ∈ MulAction.stabilizer Q x₀, β d = d)
    (q : Q) (y : X) : twistMap x₀ β (q • y) = β q • twistMap x₀ β y := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq Q x₀ y
  rw [← mul_smul, twistMap_smul_base hβ, twistMap_smul_base hβ, map_mul, mul_smul]

theorem twistMap_base {x₀ : X} {β : Q →* Q} (hβ : ∀ d ∈ MulAction.stabilizer Q x₀, β d = d) :
    twistMap x₀ β x₀ = x₀ := by
  have := twistMap_smul_base hβ 1
  rwa [one_smul, map_one, one_smul] at this

@[expose] noncomputable def twistPerm (x₀ : X) (β : Q ≃* Q)
    (hβ : ∀ d ∈ MulAction.stabilizer Q x₀, β d = d) : Equiv.Perm X where
  toFun := twistMap x₀ β.toMonoidHom
  invFun := twistMap x₀ β.symm.toMonoidHom
  left_inv y := by
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq Q x₀ y
    have hβ' : ∀ d ∈ MulAction.stabilizer Q x₀, β.symm.toMonoidHom d = d := fun d hd => by
      show β.symm d = d
      rw [MulEquiv.symm_apply_eq]
      exact (hβ d hd).symm
    show twistMap x₀ β.symm.toMonoidHom (twistMap x₀ β.toMonoidHom (g • x₀)) = g • x₀
    rw [twistMap_smul_base hβ, twistMap_smul_base hβ']
    simp
  right_inv y := by
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq Q x₀ y
    have hβ' : ∀ d ∈ MulAction.stabilizer Q x₀, β.symm.toMonoidHom d = d := fun d hd => by
      show β.symm d = d
      rw [MulEquiv.symm_apply_eq]
      exact (hβ d hd).symm
    show twistMap x₀ β.toMonoidHom (twistMap x₀ β.symm.toMonoidHom (g • x₀)) = g • x₀
    rw [twistMap_smul_base hβ', twistMap_smul_base hβ]
    simp

theorem twistPerm_smul_base (x₀ : X) (β : Q ≃* Q) (hβ : ∀ d ∈ MulAction.stabilizer Q x₀, β d = d)
    (g : Q) : twistPerm x₀ β hβ (g • x₀) = β g • x₀ :=
  twistMap_smul_base (β := β.toMonoidHom) hβ g

theorem twistPerm_smul (x₀ : X) (β : Q ≃* Q) (hβ : ∀ d ∈ MulAction.stabilizer Q x₀, β d = d)
    (q : Q) (y : X) : twistPerm x₀ β hβ (q • y) = β q • twistPerm x₀ β hβ y :=
  twistMap_smul (β := β.toMonoidHom) hβ q y

theorem twistPerm_base (x₀ : X) (β : Q ≃* Q) (hβ : ∀ d ∈ MulAction.stabilizer Q x₀, β d = d) :
    twistPerm x₀ β hβ x₀ = x₀ :=
  twistMap_base (β := β.toMonoidHom) hβ

end Twist

theorem eq_refl_of_rigid_action {Q X : Type*} [Group Q] [MulAction Q X]
    [MulAction.IsPretransitive Q X] (x₀ : X) (H : Subgroup Q)
    (hH : H ≤ MulAction.stabilizer Q x₀) {α : Type*} (R : X → X → α)
    (hR : ∀ (q : Q) (a b : X), R (q • a) (q • b) = R a b)
    (horb : ∀ π : Equiv.Perm X, (∀ h ∈ H, ∀ y, π (h • y) = h • π y) →
      ∀ y, ∃ h ∈ H, π y = h • y)
    (hrigid : ∀ π : Equiv.Perm X, π x₀ = x₀ → (∀ h ∈ H, ∀ y, π (h • y) = h • π y) →
      (∀ a b, R (π a) (π b) = R a b) → π = 1)
    (hker : ∀ q : Q, (∀ y : X, q • y = y) → q ∈ Subgroup.center Q)
    (hgen : MulAction.stabilizer Q x₀ ⊔ commutator Q = ⊤)
    (β : Q ≃* Q) (hβ : ∀ d ∈ MulAction.stabilizer Q x₀, β d = d) : β = MulEquiv.refl Q := by
  obtain ⟨π, hπdef⟩ : ∃ π : Equiv.Perm X, π = twistPerm x₀ β hβ := ⟨_, rfl⟩
  have e1 : ∀ g : Q, π (g • x₀) = β g • x₀ := fun g => by
    rw [hπdef]; exact twistPerm_smul_base x₀ β hβ g
  have e2 : ∀ (q : Q) (y : X), π (q • y) = β q • π y := fun q y => by
    rw [hπdef]; exact twistPerm_smul x₀ β hβ q y
  have e3 : π x₀ = x₀ := by rw [hπdef]; exact twistPerm_base x₀ β hβ
  have hcomm : ∀ h ∈ H, ∀ y, π (h • y) = h • π y := fun h hh y => by
    rw [e2, hβ h (hH hh)]
  have hpres : ∀ a b, R (π a) (π b) = R a b := by
    intro a b
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq Q x₀ a
    obtain ⟨y, rfl⟩ : ∃ y, b = g • y := ⟨g⁻¹ • b, (smul_inv_smul g b).symm⟩
    obtain ⟨h, hh, hy⟩ := horb π hcomm y
    have hhx : h • x₀ = x₀ := MulAction.mem_stabilizer_iff.1 (hH hh)
    calc R (π (g • x₀)) (π (g • y)) = R (β g • x₀) (β g • h • y) := by rw [e1, e2, hy]
      _ = R x₀ (h • y) := hR (β g) x₀ (h • y)
      _ = R (h • x₀) (h • y) := by rw [hhx]
      _ = R x₀ y := hR h x₀ y
      _ = R (g • x₀) (g • y) := (hR g x₀ y).symm
  have hπ1 : π = 1 := hrigid π e3 hcomm hpres
  have hact : ∀ q : Q, ∀ y : X, β q • y = q • y := fun q y => by
    have := e2 q y
    rw [hπ1] at this
    exact this.symm
  refine eq_refl_of_trivial_mod_center_of_sup (MulAction.toPermHom Q X).ker
    (MulAction.stabilizer Q x₀) (fun q hq => hker q fun y => ?_) hgen β hβ fun q => ?_
  · exact Equiv.ext_iff.1 (MonoidHom.mem_ker.1 hq) y
  · rw [MonoidHom.mem_ker]
    ext y
    simp [MulAction.toPermHom_apply, mul_smul, hact]

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
