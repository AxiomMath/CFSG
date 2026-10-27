module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFieldComponentBasic
public import CFSG.Quasithin.Background.A3ComponentsBasic

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane (linearFieldPart linearFieldPart_eq)
open CFSG.Quasithin (perfectCore)

section Fix

variable {P : Type*} [Group P]

@[expose] def autFixSubgroup (α : MulAut P) : Subgroup P where
  carrier := {x | α x = x}
  mul_mem' {a b} ha hb := by
    change α (a * b) = a * b
    rw [map_mul, show α a = a from ha, show α b = b from hb]
  one_mem' := map_one α
  inv_mem' {a} ha := by
    change α a⁻¹ = a⁻¹
    rw [map_inv, show α a = a from ha]

theorem mem_autFixSubgroup {α : MulAut P} {x : P} : x ∈ autFixSubgroup α ↔ α x = x :=
  Iff.rfl

end Fix

section FieldRigid

variable {n : ℕ} {K : Type*} [Field K] [Finite K]

@[expose] def FieldRigid (hn : 3 ≤ n) (X₁ X₂ : Subgroup (projectiveSL n K)) : Prop :=
  ∀ (β₁ β₂ : MulAut (projectiveSL n K)) (φ : X₁ ≃* X₂) (h₁ : ∀ x ∈ X₁, β₁ x ∈ X₁),
    (∀ x : X₁, β₂ (φ x) = φ ⟨β₁ x, h₁ x x.2⟩) →
      linearFieldPart K hn β₁ = linearFieldPart K hn β₂

variable {hn : 3 ≤ n} {X₁ X₂ : Subgroup (projectiveSL n K)}

theorem FieldRigid.linearFieldPart_eq (h : FieldRigid hn X₁ X₂) {H : Type*} [Group H]
    {ι₁ ι₂ : H →* projectiveSL n K} (hι₁ : Function.Injective ι₁)
    (hι₂ : Function.Injective ι₂) (h₁ : ι₁.range = X₁) (h₂ : ι₂.range = X₂) (γ : H →* H)
    {β₁ β₂ : MulAut (projectiveSL n K)} (hβ₁ : ∀ x, β₁ (ι₁ x) = ι₁ (γ x))
    (hβ₂ : ∀ x, β₂ (ι₂ x) = ι₂ (γ x)) :
    linearFieldPart K hn β₁ = linearFieldPart K hn β₂ := by
  subst h₁ h₂
  set e₁ : H ≃* ι₁.range := MonoidHom.ofInjective hι₁ with he₁
  set e₂ : H ≃* ι₂.range := MonoidHom.ofInjective hι₂ with he₂
  have hmem : ∀ x ∈ ι₁.range, β₁ x ∈ ι₁.range := by
    rintro _ ⟨a, rfl⟩
    exact ⟨γ a, (hβ₁ a).symm⟩
  refine h β₁ β₂ (e₁.symm.trans e₂) hmem fun x => ?_
  obtain ⟨a, rfl⟩ := e₁.surjective x
  have hx : (⟨β₁ (e₁ a), hmem _ (e₁ a).2⟩ : ι₁.range) = e₁ (γ a) := by
    apply Subtype.ext
    change β₁ ((e₁ a : ι₁.range) : projectiveSL n K) = ((e₁ (γ a) : ι₁.range) : projectiveSL n K)
    rw [he₁, MonoidHom.ofInjective_apply, MonoidHom.ofInjective_apply, hβ₁]
  rw [hx, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    MulEquiv.symm_apply_apply, he₂, MonoidHom.ofInjective_apply, MonoidHom.ofInjective_apply, hβ₂]

theorem FieldRigid.symm (h : FieldRigid hn X₁ X₂) : FieldRigid hn X₂ X₁ := by
  intro β₁ β₂ φ h₁ hint
  have h₂ : ∀ x ∈ X₁, β₂ x ∈ X₁ := by
    intro x hx
    have hh := hint (φ.symm ⟨x, hx⟩)
    rw [MulEquiv.apply_symm_apply] at hh
    have hh' : β₂ x = ((φ ⟨β₁ (φ.symm ⟨x, hx⟩), h₁ _ (φ.symm ⟨x, hx⟩).2⟩ : X₁) :
        projectiveSL n K) := hh
    rw [hh']
    exact (φ _).2
  refine (h β₂ β₁ φ.symm h₂ fun x => ?_).symm
  have hh := hint (φ.symm x)
  rw [MulEquiv.apply_symm_apply] at hh
  have hx : (⟨β₂ x, h₂ x x.2⟩ : X₁) = φ ⟨β₁ (φ.symm x), h₁ _ (φ.symm x).2⟩ := Subtype.ext hh
  rw [hx, MulEquiv.symm_apply_apply]

theorem FieldRigid.map (h : FieldRigid hn X₁ X₂) (ψ₁ ψ₂ : MulAut (projectiveSL n K)) :
    FieldRigid hn (X₁.map ψ₁.toMonoidHom) (X₂.map ψ₂.toMonoidHom) := by
  intro β₁ β₂ φ h₁ hint
  let ι₁ : X₁.map ψ₁.toMonoidHom →* projectiveSL n K :=
    (ψ₁⁻¹).toMonoidHom.comp (X₁.map ψ₁.toMonoidHom).subtype
  let ι₂ : X₁.map ψ₁.toMonoidHom →* projectiveSL n K :=
    (ψ₂⁻¹).toMonoidHom.comp ((X₂.map ψ₂.toMonoidHom).subtype.comp φ.toMonoidHom)
  let γ : X₁.map ψ₁.toMonoidHom →* X₁.map ψ₁.toMonoidHom :=
    { toFun := fun x => ⟨β₁ (x : projectiveSL n K), h₁ x x.2⟩
      map_one' := Subtype.ext (map_one β₁)
      map_mul' := fun x y => Subtype.ext (map_mul β₁ (x : projectiveSL n K) y) }
  have hι₁ : ∀ x, ι₁ x = (ψ₁⁻¹) (x : projectiveSL n K) := fun x => rfl
  have hι₂ : ∀ x, ι₂ x = (ψ₂⁻¹) ((φ x : X₂.map ψ₂.toMonoidHom) : projectiveSL n K) :=
    fun x => rfl
  have hinj₁ : Function.Injective ι₁ :=
    (ψ₁⁻¹).injective.comp (X₁.map ψ₁.toMonoidHom).subtype_injective
  have hinj₂ : Function.Injective ι₂ :=
    (ψ₂⁻¹).injective.comp ((X₂.map ψ₂.toMonoidHom).subtype_injective.comp φ.injective)
  have hr₁ : ι₁.range = X₁ := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨z, hz, hzy⟩ := y.2
      rw [hι₁, ← hzy, MulEquiv.coe_toMonoidHom, MulAut.inv_apply_self]
      exact hz
    · intro hx
      exact ⟨⟨ψ₁ x, ⟨x, hx, rfl⟩⟩, by rw [hι₁]; exact MulAut.inv_apply_self _ ψ₁ x⟩
  have hr₂ : ι₂.range = X₂ := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨z, hz, hzy⟩ := (φ y).2
      rw [hι₂, ← hzy, MulEquiv.coe_toMonoidHom, MulAut.inv_apply_self]
      exact hz
    · intro hx
      refine ⟨φ.symm ⟨ψ₂ x, ⟨x, hx, rfl⟩⟩, ?_⟩
      rw [hι₂, MulEquiv.apply_symm_apply]
      exact MulAut.inv_apply_self _ ψ₂ x
  have hβ₁ : ∀ x, (ψ₁⁻¹ * β₁ * ψ₁) (ι₁ x) = ι₁ (γ x) := by
    intro x
    rw [hι₁, hι₁, MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self]
    rfl
  have hβ₂ : ∀ x, (ψ₂⁻¹ * β₂ * ψ₂) (ι₂ x) = ι₂ (γ x) := by
    intro x
    rw [hι₂, hι₂, MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self, hint x]
    rfl
  have key := h.linearFieldPart_eq hinj₁ hinj₂ hr₁ hr₂ γ hβ₁ hβ₂
  have hc : ∀ (β ψ : MulAut (projectiveSL n K)),
      linearFieldPart K hn (ψ⁻¹ * β * ψ) = linearFieldPart K hn β := fun β ψ => by
    have := linearFieldPart_conj_eq hn β ψ⁻¹
    rwa [inv_inv] at this
  rw [hc, hc] at key
  exact key

end FieldRigid

section FieldRigidIn

variable {n : ℕ} {K : Type*} [Field K] [Finite K]

@[expose] def FieldRigidIn (hn : 3 ≤ n) (X₁ X₂ : Subgroup (projectiveSL n K)) : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (φ₁ φ₂ : projectiveSL n K →* Γ),
    Function.Injective φ₁ → Function.Injective φ₂ → X₁.map φ₁ = X₂.map φ₂ →
      ∀ (γ : Γ) (β₁ β₂ : MulAut (projectiveSL n K)), (∀ x ∈ X₁, β₁ x ∈ X₁) →
        (∀ x, φ₁ (β₁ x) = γ * φ₁ x * γ⁻¹) → (∀ x, φ₂ (β₂ x) = γ * φ₂ x * γ⁻¹) →
          linearFieldPart K hn β₁ = linearFieldPart K hn β₂

variable {hn : 3 ≤ n} {X₁ X₂ : Subgroup (projectiveSL n K)}

theorem FieldRigid.fieldRigidIn (h : FieldRigid hn X₁ X₂) : FieldRigidIn hn X₁ X₂ := by
  intro Γ _ _ φ₁ φ₂ hφ₁ hφ₂ hX γ β₁ β₂ hβX h₁ h₂
  have hmem : ∀ x : X₁, φ₁ x ∈ φ₂.range := fun x => by
    obtain ⟨z, -, hz⟩ := (hX ▸ (⟨x, x.2, rfl⟩ : φ₁ x ∈ X₁.map φ₁) : φ₁ x ∈ X₂.map φ₂)
    exact ⟨z, hz⟩
  let ι₂ : X₁ →* projectiveSL n K :=
    (MonoidHom.ofInjective hφ₂).symm.toMonoidHom.comp
      ((φ₁.comp X₁.subtype).codRestrict φ₂.range hmem)
  have hι₂ : ∀ x : X₁, φ₂ (ι₂ x) = φ₁ x := fun x => by
    have := MonoidHom.ofInjective_apply hφ₂ (x := ι₂ x)
    rw [show MonoidHom.ofInjective hφ₂ (ι₂ x) = ⟨φ₁ x, hmem x⟩ from
      MulEquiv.apply_symm_apply _ _] at this
    exact this.symm
  have hinj₂ : Function.Injective ι₂ := fun a b hab => by
    have := congrArg φ₂ hab
    rw [hι₂, hι₂] at this
    exact Subtype.ext (hφ₁ this)
  have hr₁ : X₁.subtype.range = X₁ := X₁.range_subtype
  have hr₂ : ι₂.range = X₂ := by
    apply Subgroup.map_injective hφ₂
    rw [← hX, ← MonoidHom.range_comp]
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, (hι₂ x).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, hι₂ ⟨x, hx⟩⟩
  let γ' : X₁ →* X₁ :=
    { toFun := fun x => ⟨β₁ x, hβX x x.2⟩
      map_one' := Subtype.ext (map_one β₁)
      map_mul' := fun x y => Subtype.ext (map_mul β₁ (x : projectiveSL n K) y) }
  refine h.linearFieldPart_eq X₁.subtype_injective hinj₂ hr₁ hr₂ γ' (fun x => rfl) fun x => ?_
  apply hφ₂
  rw [h₂, hι₂, hι₂]
  exact (h₁ x).symm

theorem FieldRigidIn.map (h : FieldRigidIn hn X₁ X₂) (ψ₁ ψ₂ : MulAut (projectiveSL n K)) :
    FieldRigidIn hn (X₁.map ψ₁.toMonoidHom) (X₂.map ψ₂.toMonoidHom) := by
  intro Γ _ _ φ₁ φ₂ hφ₁ hφ₂ hX γ β₁ β₂ hβX h₁ h₂
  have hc : ∀ (β ψ : MulAut (projectiveSL n K)),
      linearFieldPart K hn (ψ⁻¹ * β * ψ) = linearFieldPart K hn β := fun β ψ => by
    have := linearFieldPart_conj_eq hn β ψ⁻¹
    rwa [inv_inv] at this
  rw [← hc β₁ ψ₁, ← hc β₂ ψ₂]
  refine h Γ (φ₁.comp ψ₁.toMonoidHom) (φ₂.comp ψ₂.toMonoidHom) (hφ₁.comp ψ₁.injective)
    (hφ₂.comp ψ₂.injective) ?_ γ _ _ ?_ ?_ ?_
  · rw [← Subgroup.map_map, ← Subgroup.map_map, hX]
  · intro x hx
    obtain ⟨z, hz, hzx⟩ := hβX (ψ₁ x) ⟨x, hx, rfl⟩
    rw [MulAut.mul_apply, MulAut.mul_apply, ← hzx, MulEquiv.coe_toMonoidHom,
      MulAut.inv_apply_self]
    exact hz
  · intro x
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulAut.mul_apply, MulAut.apply_inv_self]
    exact h₁ (ψ₁ x)
  · intro x
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulAut.mul_apply, MulAut.apply_inv_self]
    exact h₂ (ψ₂ x)

theorem FieldRigidIn.of_subsingleton [Subsingleton (K ≃+* K)]
    (X₁ X₂ : Subgroup (projectiveSL n K)) : FieldRigidIn hn X₁ X₂ :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => Subsingleton.elim _ _

end FieldRigidIn

section Blocks

variable {n : ℕ} (K : Type*) [Field K] [Finite K]

@[expose] def InnerGraphFieldRigid (hn : 3 ≤ n) : Prop :=
  ∀ α₁ α₂ : MulAut (projectiveSL n K), α₁ ^ 2 = 1 → α₂ ^ 2 = 1 → α₁ ≠ 1 → α₂ ≠ 1 →
    linearFieldPart K hn α₁ = 1 → linearFieldPart K hn α₂ = 1 →
      FieldRigidIn hn (perfectCore (autFixSubgroup α₁)) (perfectCore (autFixSubgroup α₂))

variable {K}

theorem FieldRigid.of_subsingleton [Subsingleton (K ≃+* K)] {hn : 3 ≤ n}
    (X₁ X₂ : Subgroup (projectiveSL n K)) : FieldRigid hn X₁ X₂ :=
  fun _ _ _ _ _ => Subsingleton.elim _ _

theorem subsingleton_ringEquiv_of_card_eq_two (hK : Nat.card K = 2) : Subsingleton (K ≃+* K) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have h01 : ∀ x : K, x = 0 ∨ x = 1 := by
    intro x
    by_contra h
    push Not at h
    obtain ⟨h0, h1⟩ := h
    have hcard : ({0, 1, x} : Finset K).card = 3 :=
      Finset.card_eq_three.2 ⟨0, 1, x, zero_ne_one, Ne.symm h0, Ne.symm h1, rfl⟩
    have hle := Finset.card_le_univ ({0, 1, x} : Finset K)
    rw [hcard, ← Nat.card_eq_fintype_card, hK] at hle
    omega
  constructor
  intro σ τ
  ext x
  rcases h01 x with rfl | rfl <;> simp

theorem innerGraphFieldRigid_of_card_eq_two (hK : Nat.card K = 2) (hn : 3 ≤ n) :
    InnerGraphFieldRigid K hn := by
  have := subsingleton_ringEquiv_of_card_eq_two hK
  exact fun _ _ _ _ _ _ _ _ => FieldRigidIn.of_subsingleton _ _

theorem linearFieldPart_eq_one_of_forall_apply_eq (hn : 3 ≤ n) (β : MulAut (projectiveSL n K))
    {i j : Fin n} (hij : i ≠ j)
    (hβ : ∀ c : K, β (proj n K (SpecialLinearGroup.transvection hij c)) =
      proj n K (SpecialLinearGroup.transvection hij c)) :
    linearFieldPart K hn β = 1 := by
  have h := apply_eq_mul_linearFieldPart_of_apply_transvection hn β hij id hβ
  refine DFunLike.ext _ _ fun c => ?_
  have hc := h c
  simp only [id, one_mul] at hc
  exact hc.symm

theorem linearFieldPart_eq_of_eqOn_conj_rootGroup (hn : 3 ≤ n)
    (β₁ β₂ : MulAut (projectiveSL n K)) {i j : Fin n} (hij : i ≠ j) (h : projectiveSL n K)
    (hβ : ∀ c : K, β₁ (h * proj n K (SpecialLinearGroup.transvection hij c) * h⁻¹) =
      β₂ (h * proj n K (SpecialLinearGroup.transvection hij c) * h⁻¹)) :
    linearFieldPart K hn β₁ = linearFieldPart K hn β₂ := by
  have h1 : linearFieldPart K hn ((MulAut.conj h)⁻¹ * β₂⁻¹ * β₁ * MulAut.conj h) = 1 := by
    refine linearFieldPart_eq_one_of_forall_apply_eq hn _ hij fun c => ?_
    simp only [MulAut.mul_apply, MulAut.conj_apply]
    rw [hβ c, MulAut.inv_apply_self, ← map_inv, MulAut.conj_apply]
    group
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, linearFieldPart_mulAut_conj, inv_one,
    one_mul, mul_one, inv_mul_eq_one] at h1
  exact h1.symm

end Blocks

end CFSG.SeitzReduction.LinearPilot
