module

public import CFSG.ClassicalInvolution.Asc77.AscC5OStmt
public import CFSG.Goldschmidt75.B1Perfect

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.CX

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank

section Diag

@[expose] def DiagTriv (p : ℕ) {H : Type} [Group H] (α : H ≃* H) : Prop :=
  ∀ u : H, orderOf u = p → ∃ g : H, α u = g * u * g⁻¹

variable {p : ℕ}

theorem DiagTriv.symm {H : Type} [Group H] {α : H ≃* H} (h : DiagTriv p α) :
    DiagTriv p α.symm := by
  intro u hu
  have hu' : orderOf (α.symm u) = p := by rw [MulEquiv.orderOf_eq]; exact hu
  obtain ⟨g, hg⟩ := h (α.symm u) hu'
  rw [MulEquiv.apply_symm_apply] at hg
  refine ⟨g⁻¹, ?_⟩
  calc α.symm u = g⁻¹ * (g * α.symm u * g⁻¹) * g := by group
    _ = g⁻¹ * u * g⁻¹⁻¹ := by rw [← hg]; group

theorem diagTriv_symm_iff {H : Type} [Group H] {α : H ≃* H} :
    DiagTriv p α.symm ↔ DiagTriv p α :=
  ⟨fun h => by simpa using h.symm, DiagTriv.symm⟩

theorem diagTriv_trans_iff_left {H : Type} [Group H] {α β : H ≃* H} (hβ : DiagTriv p β) :
    DiagTriv p (α.trans β) ↔ DiagTriv p α := by
  constructor
  · intro h u hu
    obtain ⟨g, hg⟩ := h u hu
    have hu' : orderOf (α u) = p := by rw [MulEquiv.orderOf_eq]; exact hu
    obtain ⟨k, hk⟩ := hβ.symm (β (α u)) (by rw [MulEquiv.orderOf_eq]; exact hu')
    rw [MulEquiv.symm_apply_apply] at hk
    refine ⟨k * g, ?_⟩
    rw [hk]
    have : β (α u) = g * u * g⁻¹ := hg
    rw [this]
    group
  · intro h u hu
    obtain ⟨g, hg⟩ := h u hu
    have hu' : orderOf (α u) = p := by rw [MulEquiv.orderOf_eq]; exact hu
    obtain ⟨k, hk⟩ := hβ (α u) hu'
    refine ⟨k * g, ?_⟩
    show β (α u) = _
    rw [hk, hg]
    group

theorem diagTriv_trans_iff_right {H : Type} [Group H] {α β : H ≃* H} (hα : DiagTriv p α) :
    DiagTriv p (α.trans β) ↔ DiagTriv p β := by
  constructor
  · intro h u hu
    have hu' : orderOf (α.symm u) = p := by rw [MulEquiv.orderOf_eq]; exact hu
    obtain ⟨g, hg⟩ := h (α.symm u) hu'
    obtain ⟨k, hk⟩ := hα.symm u hu
    have e : β u = β (α (α.symm u)) := by rw [MulEquiv.apply_symm_apply]
    refine ⟨g * k, ?_⟩
    rw [e]
    have : β (α (α.symm u)) = g * α.symm u * g⁻¹ := hg
    rw [this, hk]
    group
  · intro h u hu
    obtain ⟨g, hg⟩ := hα u hu
    obtain ⟨k, hk⟩ := h u hu
    refine ⟨β g * k, ?_⟩
    show β (α u) = _
    rw [hg, map_mul, map_mul, map_inv, hk]
    group

theorem diagTriv_conj_iff {H₁ H₂ : Type} [Group H₁] [Group H₂] (ψ : H₁ ≃* H₂) (α : H₂ ≃* H₂) :
    DiagTriv p (ψ.trans (α.trans ψ.symm)) ↔ DiagTriv p α := by
  constructor
  · intro h u hu
    have hu' : orderOf (ψ.symm u) = p := by rw [MulEquiv.orderOf_eq]; exact hu
    obtain ⟨g, hg⟩ := h (ψ.symm u) hu'
    refine ⟨ψ g, ?_⟩
    have e : ψ.symm (α (ψ (ψ.symm u))) = g * ψ.symm u * g⁻¹ := hg
    rw [MulEquiv.apply_symm_apply] at e
    have e2 := congrArg ψ e
    rw [MulEquiv.apply_symm_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply] at e2
    exact e2
  · intro h u hu
    have hu' : orderOf (ψ u) = p := by rw [MulEquiv.orderOf_eq]; exact hu
    obtain ⟨g, hg⟩ := h (ψ u) hu'
    refine ⟨ψ.symm g, ?_⟩
    show ψ.symm (α (ψ u)) = _
    rw [hg, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]

end Diag

section Twin

structure TwinGroup (K₀ K₀' : Type) [Group K₀] [Group K₀'] where
  X : Type
  [instGroup : Group X]
  [instFinite : Finite X]
  A : Subgroup X
  A' : Subgroup X
  ι : K₀ ≃* A
  ι' : K₀' ≃* A'

attribute [instance] TwinGroup.instGroup TwinGroup.instFinite

variable {K₀ K₀' : Type} [Group K₀] [Group K₀']

@[expose] def TwinGroup.restr {L₁ L₂ : TwinGroup K₀ K₀'} (φ : L₁.X ≃* L₂.X)
    (hA : L₁.A.map (φ : L₁.X →* L₂.X) = L₂.A) : K₀ ≃* K₀ :=
  L₁.ι.trans ((φ.subgroupMap L₁.A).trans ((MulEquiv.subgroupCongr hA).trans L₂.ι.symm))

@[expose] def TwinGroup.restr' {L₁ L₂ : TwinGroup K₀ K₀'} (φ : L₁.X ≃* L₂.X)
    (hA' : L₁.A'.map (φ : L₁.X →* L₂.X) = L₂.A') : K₀' ≃* K₀' :=
  L₁.ι'.trans ((φ.subgroupMap L₁.A').trans ((MulEquiv.subgroupCongr hA').trans L₂.ι'.symm))

@[expose] def TwinGroup.rebase {K₁ K₁' : Type} [Group K₁] [Group K₁'] (L : TwinGroup K₁ K₁')
    (ψ : K₀ ≃* K₁) (ψ' : K₀' ≃* K₁') : TwinGroup K₀ K₀' where
  X := L.X
  A := L.A
  A' := L.A'
  ι := ψ.trans L.ι
  ι' := ψ'.trans L.ι'

variable (p : ℕ)

@[expose] def DiagRel (L₁ L₂ : TwinGroup K₀ K₀') : Prop :=
  ∃ φ : L₁.X ≃* L₂.X, ∃ hA : L₁.A.map (φ : L₁.X →* L₂.X) = L₂.A,
    ∃ hA' : L₁.A'.map (φ : L₁.X →* L₂.X) = L₂.A',
      (DiagTriv p (TwinGroup.restr φ hA) ↔ DiagTriv p (TwinGroup.restr' φ hA'))

@[expose] def TwinIso (L₁ L₂ : TwinGroup K₀ K₀') : Prop :=
  ∃ φ : L₁.X ≃* L₂.X, ∃ hA : L₁.A.map (φ : L₁.X →* L₂.X) = L₂.A,
    ∃ hA' : L₁.A'.map (φ : L₁.X →* L₂.X) = L₂.A',
      DiagTriv p (TwinGroup.restr φ hA) ∧ DiagTriv p (TwinGroup.restr' φ hA')

variable {p}

theorem TwinGroup.map_trans {L₁ L₂ L₃ : TwinGroup K₀ K₀'} (φ : L₁.X ≃* L₂.X)
    (φ' : L₂.X ≃* L₃.X) {B₁ : Subgroup L₁.X} {B₂ : Subgroup L₂.X} {B₃ : Subgroup L₃.X}
    (h₁ : B₁.map (φ : L₁.X →* L₂.X) = B₂) (h₂ : B₂.map (φ' : L₂.X →* L₃.X) = B₃) :
    B₁.map ((φ.trans φ' : L₁.X ≃* L₃.X) : L₁.X →* L₃.X) = B₃ := by
  rw [← h₂, ← h₁, Subgroup.map_map]
  rfl

theorem TwinGroup.map_symm {L₁ L₂ : TwinGroup K₀ K₀'} (φ : L₁.X ≃* L₂.X) {B₁ : Subgroup L₁.X}
    {B₂ : Subgroup L₂.X} (h : B₁.map (φ : L₁.X →* L₂.X) = B₂) :
    B₂.map ((φ.symm : L₂.X ≃* L₁.X) : L₂.X →* L₁.X) = B₁ := by
  rw [← h, Subgroup.map_map]
  ext x
  simp

@[simp]
theorem TwinGroup.restr_apply {L₁ L₂ : TwinGroup K₀ K₀'} (φ : L₁.X ≃* L₂.X)
    (hA : L₁.A.map (φ : L₁.X →* L₂.X) = L₂.A) (k : K₀) :
    ((L₂.ι (TwinGroup.restr φ hA k) : L₂.A) : L₂.X) = φ (L₁.ι k : L₁.X) := by
  simp only [TwinGroup.restr, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  rfl

@[simp]
theorem TwinGroup.restr'_apply {L₁ L₂ : TwinGroup K₀ K₀'} (φ : L₁.X ≃* L₂.X)
    (hA' : L₁.A'.map (φ : L₁.X →* L₂.X) = L₂.A') (k : K₀') :
    ((L₂.ι' (TwinGroup.restr' φ hA' k) : L₂.A') : L₂.X) = φ (L₁.ι' k : L₁.X) := by
  simp only [TwinGroup.restr', MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  rfl

theorem TwinGroup.restr_trans {L₁ L₂ L₃ : TwinGroup K₀ K₀'} (φ : L₁.X ≃* L₂.X)
    (φ' : L₂.X ≃* L₃.X) (hA : L₁.A.map (φ : L₁.X →* L₂.X) = L₂.A)
    (hA₂ : L₂.A.map (φ' : L₂.X →* L₃.X) = L₃.A) :
    TwinGroup.restr (φ.trans φ') (TwinGroup.map_trans φ φ' hA hA₂) =
      (TwinGroup.restr φ hA).trans (TwinGroup.restr φ' hA₂) := by
  ext k
  apply L₃.ι.injective
  apply Subtype.ext
  simp only [MulEquiv.trans_apply]
  rw [TwinGroup.restr_apply, TwinGroup.restr_apply, TwinGroup.restr_apply]
  rfl

theorem TwinGroup.restr'_trans {L₁ L₂ L₃ : TwinGroup K₀ K₀'} (φ : L₁.X ≃* L₂.X)
    (φ' : L₂.X ≃* L₃.X) (hA : L₁.A'.map (φ : L₁.X →* L₂.X) = L₂.A')
    (hA₂ : L₂.A'.map (φ' : L₂.X →* L₃.X) = L₃.A') :
    TwinGroup.restr' (φ.trans φ') (TwinGroup.map_trans φ φ' hA hA₂) =
      (TwinGroup.restr' φ hA).trans (TwinGroup.restr' φ' hA₂) := by
  ext k
  apply L₃.ι'.injective
  apply Subtype.ext
  simp only [MulEquiv.trans_apply]
  rw [TwinGroup.restr'_apply, TwinGroup.restr'_apply, TwinGroup.restr'_apply]
  rfl

theorem TwinGroup.restr_symm {L₁ L₂ : TwinGroup K₀ K₀'} (φ : L₁.X ≃* L₂.X)
    (hA : L₁.A.map (φ : L₁.X →* L₂.X) = L₂.A) :
    TwinGroup.restr φ.symm (TwinGroup.map_symm φ hA) = (TwinGroup.restr φ hA).symm := by
  ext k
  apply L₁.ι.injective
  apply Subtype.ext
  rw [TwinGroup.restr_apply]
  apply φ.injective
  rw [MulEquiv.apply_symm_apply]
  have h1 := TwinGroup.restr_apply φ hA ((TwinGroup.restr φ hA).symm k)
  rw [MulEquiv.apply_symm_apply] at h1
  exact h1

theorem TwinGroup.restr'_symm {L₁ L₂ : TwinGroup K₀ K₀'} (φ : L₁.X ≃* L₂.X)
    (hA : L₁.A'.map (φ : L₁.X →* L₂.X) = L₂.A') :
    TwinGroup.restr' φ.symm (TwinGroup.map_symm φ hA) = (TwinGroup.restr' φ hA).symm := by
  ext k
  apply L₁.ι'.injective
  apply Subtype.ext
  rw [TwinGroup.restr'_apply]
  apply φ.injective
  rw [MulEquiv.apply_symm_apply]
  have h1 := TwinGroup.restr'_apply φ hA ((TwinGroup.restr' φ hA).symm k)
  rw [MulEquiv.apply_symm_apply] at h1
  exact h1

theorem TwinIso.symm {L₁ L₂ : TwinGroup K₀ K₀'} (h : TwinIso p L₁ L₂) : TwinIso p L₂ L₁ := by
  obtain ⟨φ, hA, hA', h₁, h₂⟩ := h
  refine ⟨φ.symm, TwinGroup.map_symm φ hA, TwinGroup.map_symm φ hA', ?_, ?_⟩
  · rw [TwinGroup.restr_symm φ hA]
    exact h₁.symm
  · rw [TwinGroup.restr'_symm φ hA']
    exact h₂.symm

theorem DiagRel.trans_twinIso {L₁ L₂ L₃ : TwinGroup K₀ K₀'} (h : DiagRel p L₁ L₂)
    (h' : TwinIso p L₂ L₃) : DiagRel p L₁ L₃ := by
  obtain ⟨φ, hA, hA', hiff⟩ := h
  obtain ⟨φ', hB, hB', h₁, h₂⟩ := h'
  refine ⟨φ.trans φ', TwinGroup.map_trans φ φ' hA hB, TwinGroup.map_trans φ φ' hA' hB', ?_⟩
  rw [TwinGroup.restr_trans φ φ' hA hB, TwinGroup.restr'_trans φ φ' hA' hB',
    diagTriv_trans_iff_left h₁, diagTriv_trans_iff_left h₂]
  exact hiff

theorem TwinIso.trans_diagRel {L₁ L₂ L₃ : TwinGroup K₀ K₀'} (h : TwinIso p L₁ L₂)
    (h' : DiagRel p L₂ L₃) : DiagRel p L₁ L₃ := by
  obtain ⟨φ, hA, hA', h₁, h₂⟩ := h
  obtain ⟨φ', hB, hB', hiff⟩ := h'
  refine ⟨φ.trans φ', TwinGroup.map_trans φ φ' hA hB, TwinGroup.map_trans φ φ' hA' hB', ?_⟩
  rw [TwinGroup.restr_trans φ φ' hA hB, TwinGroup.restr'_trans φ φ' hA' hB',
    diagTriv_trans_iff_right h₁, diagTriv_trans_iff_right h₂]
  exact hiff

theorem TwinGroup.map_eq_of_compat {L₁ L₂ : TwinGroup K₀ K₀'} (φ : L₁.X ≃* L₂.X)
    {K₁ : Type} [Group K₁] {B₁ : Subgroup L₁.X} {B₂ : Subgroup L₂.X} (ι₁ : K₁ ≃* B₁)
    (ι₂ : K₁ ≃* B₂) (h : ∀ k : K₁, φ (ι₁ k : L₁.X) = (ι₂ k : L₂.X)) :
    B₁.map (φ : L₁.X →* L₂.X) = B₂ := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨k, hk⟩ := ι₁.surjective ⟨x, hx⟩
    have e : x = (ι₁ k : L₁.X) := by rw [hk]
    show φ x ∈ B₂
    rw [e, h k]
    exact (ι₂ k).2
  · intro hy
    obtain ⟨k, hk⟩ := ι₂.surjective ⟨y, hy⟩
    refine ⟨(ι₁ k : L₁.X), (ι₁ k).2, ?_⟩
    show φ _ = y
    rw [h k, hk]

theorem twinIso_of_compat {L₁ L₂ : TwinGroup K₀ K₀'} (φ : L₁.X ≃* L₂.X)
    (h : ∀ k : K₀, φ (L₁.ι k : L₁.X) = (L₂.ι k : L₂.X))
    (h' : ∀ k : K₀', φ (L₁.ι' k : L₁.X) = (L₂.ι' k : L₂.X)) : TwinIso p L₁ L₂ := by
  refine ⟨φ, TwinGroup.map_eq_of_compat φ L₁.ι L₂.ι h,
    TwinGroup.map_eq_of_compat φ L₁.ι' L₂.ι' h', fun u _ => ⟨1, ?_⟩, fun u _ => ⟨1, ?_⟩⟩
  · rw [one_mul, inv_one, mul_one]
    apply L₂.ι.injective
    apply Subtype.ext
    rw [TwinGroup.restr_apply, h u]
  · rw [one_mul, inv_one, mul_one]
    apply L₂.ι'.injective
    apply Subtype.ext
    rw [TwinGroup.restr'_apply, h' u]

theorem diagRel_rebase_iff {K₁ K₁' : Type} [Group K₁] [Group K₁'] {L₁ L₂ : TwinGroup K₁ K₁'}
    (ψ : K₀ ≃* K₁) (ψ' : K₀' ≃* K₁') :
    DiagRel p (L₁.rebase ψ ψ') (L₂.rebase ψ ψ') ↔ DiagRel p L₁ L₂ := by
  have hr : ∀ (φ : L₁.X ≃* L₂.X) (hA : L₁.A.map (φ : L₁.X →* L₂.X) = L₂.A),
      TwinGroup.restr (L₁ := L₁.rebase ψ ψ') (L₂ := L₂.rebase ψ ψ') φ hA =
        ψ.trans ((TwinGroup.restr φ hA).trans ψ.symm) := by
    intro φ hA
    ext k
    rfl
  have hr' : ∀ (φ : L₁.X ≃* L₂.X) (hA' : L₁.A'.map (φ : L₁.X →* L₂.X) = L₂.A'),
      TwinGroup.restr' (L₁ := L₁.rebase ψ ψ') (L₂ := L₂.rebase ψ ψ') φ hA' =
        ψ'.trans ((TwinGroup.restr' φ hA').trans ψ'.symm) := by
    intro φ hA'
    ext k
    rfl
  constructor
  · rintro ⟨φ, hA, hA', hiff⟩
    refine ⟨φ, hA, hA', ?_⟩
    have e1 := hr φ hA
    have e2 := hr' φ hA'
    rw [e1, e2, diagTriv_conj_iff, diagTriv_conj_iff] at hiff
    exact hiff
  · rintro ⟨φ, hA, hA', hiff⟩
    refine ⟨φ, hA, hA', ?_⟩
    rw [hr φ hA, hr' φ hA', diagTriv_conj_iff, diagTriv_conj_iff]
    exact hiff

end Twin

section Layers

@[expose] def fixSubgroup {Y : Type} [Group Y] (β : MulAut Y) : Subgroup Y where
  carrier := {y | β y = y}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [map_mul, ha, hb]
  one_mem' := map_one β
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [map_inv, ha]

@[expose] def centTG {Y : Type} [Group Y] [Finite Y] (A A' : Subgroup Y) (β : MulAut Y)
    (hA : A ≤ Goldschmidt75.perfRes (fixSubgroup β))
    (hA' : A' ≤ Goldschmidt75.perfRes (fixSubgroup β)) : TwinGroup ↥A ↥A' where
  X := ↥(Goldschmidt75.perfRes (fixSubgroup β))
  A := A.subgroupOf _
  A' := A'.subgroupOf _
  ι := (Subgroup.subgroupOfEquivOfLe hA).symm
  ι' := (Subgroup.subgroupOfEquivOfLe hA').symm

variable (p f : ℕ) [Fact p.Prime]

@[expose] def IsOm5 {K₀ K₀' : Type} [Group K₀] [Group K₀'] (L : TwinGroup K₀ K₀') : Prop :=
  ∃ (Φ : Set (Subgroup L.X)) (z' a₀ b₀ : L.X), C5O.Om5Data p f L.X Φ L.A L.A' z' a₀ b₀

structure Om6mData (Y : Type) [Group Y] [Finite Y] (Φ : Set (Subgroup Y)) (A A' : Subgroup Y)
    (z' a₀ b₀ : Y) : Prop where
  odd : p ≠ 2
  five : 5 ≤ p ^ f
  lie : ∃ D : LieSystemData p f Y Φ, D.card = 1 ∧
    ∃ i : Fin D.card, IsOrthTag 6 (!piSign p f) (D.tag i) (D.rank i)
  twin : TwinSect0 Φ A A' z' a₀ b₀
  conj : ∀ J ∈ Φ, ∀ y : Y, conjSub y J ∈ Φ

@[expose] def DiagThree : Prop :=
  ∀ (K₀ K₀' : Type) [Group K₀] [Group K₀'] (L₁ L₂ L₃ : TwinGroup K₀ K₀'),
    IsOm5 p f L₁ → IsOm5 p f L₂ → IsOm5 p f L₃ →
      DiagRel p L₁ L₂ ∨ DiagRel p L₁ L₃ ∨ DiagRel p L₂ L₃

@[expose] def Om6ReflDiag : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Φ : Set (Subgroup Y)) (A A' : Subgroup Y) (z' a₀ b₀ : Y),
    Om6mData p f Y Φ A A' z' a₀ b₀ → ∀ β : MulAut Y,
      (∀ y ∈ A, β y = y) → (∀ y ∈ A', β y = y) → β * β = 1 → β ≠ 1 → β ≠ MulAut.conj z' →
        ∃ (hA : A ≤ Goldschmidt75.perfRes (fixSubgroup β))
          (hA' : A' ≤ Goldschmidt75.perfRes (fixSubgroup β))
          (hB : A ≤ Goldschmidt75.perfRes (fixSubgroup (β * MulAut.conj z')))
          (hB' : A' ≤ Goldschmidt75.perfRes (fixSubgroup (β * MulAut.conj z'))),
          IsOm5 p f (centTG A A' β hA hA') ∧
            IsOm5 p f (centTG A A' (β * MulAut.conj z') hB hB') ∧
            ¬ DiagRel p (centTG A A' β hA hA') (centTG A A' (β * MulAut.conj z') hB hB')

end Layers

end CFSG.ClassicalInvolution.Asc77.CX
