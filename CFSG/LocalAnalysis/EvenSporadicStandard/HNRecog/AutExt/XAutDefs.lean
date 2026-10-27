module

public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

@[expose] def XAutInner (X : Type*) [Group X] (A : X) : Prop :=
  ∀ σ : X ≃* X, σ A = A → ∃ g : X, ∀ x ∈ commutator X, σ x = g * x * g⁻¹

@[expose] def XAutCent (X : Type*) [Group X] (T : X) : Prop :=
  ∀ σ : X ≃* X, (∀ x : X, x * T = T * x → σ x = x) →
    (∀ x : X, σ x = x) ∨ ∀ x : X, σ x = T * x * T⁻¹

theorem mulEquiv_mem_commutator {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {x : X}
    (hx : x ∈ commutator X) : e x ∈ commutator Y := by
  have h1 : (commutator X).map e.toMonoidHom = commutator Y := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective]
  rw [← h1]
  exact Subgroup.mem_map_of_mem _ hx

theorem XAutInner.map {X Y : Type*} [Group X] [Group Y] {A : X} (h : XAutInner X A) (e : X ≃* Y) :
    XAutInner Y (e A) := by
  intro σ' hσ'
  obtain ⟨g, hg⟩ := h (e.trans (σ'.trans e.symm)) (by
    simp only [MulEquiv.trans_apply, hσ', MulEquiv.symm_apply_apply])
  refine ⟨e g, fun y hy => ?_⟩
  have hx : e.symm y ∈ commutator X := mulEquiv_mem_commutator e.symm hy
  have h1 := hg _ hx
  simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply] at h1
  have h2 := congrArg e h1
  simpa only [MulEquiv.apply_symm_apply, map_mul, map_inv] using h2

theorem XAutCent.map {X Y : Type*} [Group X] [Group Y] {T : X} (h : XAutCent X T) (e : X ≃* Y) :
    XAutCent Y (e T) := by
  intro σ' hσ'
  have hfix : ∀ x : X, x * T = T * x →
      (e.trans (σ'.trans e.symm)) x = x := by
    intro x hx
    have h1 : e x * e T = e T * e x := by rw [← map_mul, ← map_mul, hx]
    simp only [MulEquiv.trans_apply, hσ' _ h1, MulEquiv.symm_apply_apply]
  rcases h (e.trans (σ'.trans e.symm)) hfix with hid | hconj
  · left
    intro y
    have h1 := hid (e.symm y)
    simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply] at h1
    have h2 := congrArg e h1
    simpa only [MulEquiv.apply_symm_apply] using h2
  · right
    intro y
    have h1 := hconj (e.symm y)
    simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply] at h1
    have h2 := congrArg e h1
    simpa only [MulEquiv.apply_symm_apply, map_mul, map_inv] using h2

@[expose] def relA {X : Type*} [Group X] (x y : X) : X :=
  x * x * y * x⁻¹ * y⁻¹ * x * y * x⁻¹ * x⁻¹ * y * x⁻¹ * y * x⁻¹ * y⁻¹

theorem map_relA {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (x y : X) :
    e (relA x y) = relA (e x) (e y) := by
  simp only [relA, map_mul, map_inv]

end CFSG.EvenSporadicStandard.HNRecog.Section4
