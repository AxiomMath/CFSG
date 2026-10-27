module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6SqOddCommon
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6SqOdd

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.EvenSporadicStandard.HSStd (autCentralizer)

@[expose] def A6Shape (t : StatedLieTag) (n f : ℕ) : Prop :=
  (t = .PSL ∧ n = 2 ∧ f = 4) ∨ (t = .PSL ∧ n = 3 ∧ f = 2) ∨ (t = .PSL ∧ n = 4 ∧ f = 1) ∨
  (t = .PSU ∧ n = 3 ∧ f = 2) ∨ (t = .PSU ∧ n = 4 ∧ f = 1) ∨ (t = .PSp ∧ n = 2 ∧ f = 1) ∨
  (t = .PSp ∧ n = 2 ∧ f = 2) ∨ (t = .POmegaOdd ∧ n = 3 ∧ f = 1) ∨
  (t = .POmegaMinus ∧ n = 4 ∧ f = 1)

@[expose] def A6Hyp {S : Type} [Group S] (σ : MulAut S) (D : Subgroup ↥(fixedSubgroup σ)) : Prop :=
  D.Normal ∧ Nonempty (↥D ≃* alternatingGroup (Fin 6)) ∧
    ∀ P : Subgroup ↥(fixedSubgroup σ), ⁅P, P⁆ = P → P ≤ D

@[expose] def A6ShapeConcl (t : StatedLieTag) (n p f : ℕ) {S : Type} [Group S] (σ : MulAut S)
    (D : Subgroup ↥(fixedSubgroup σ)) : Prop :=
  p = 3 ∧ A6Shape t n f ∧
    (t = .PSp → n = 2 → f = 2 → ∃ a b : ↥(fixedSubgroup σ), a * b * a⁻¹ * b⁻¹ ∉ D)

@[expose] def A6SmallConcl (t : StatedLieTag) (n f : ℕ) {S : Type} [Group S] (σ : MulAut S)
    (D : Subgroup ↥(fixedSubgroup σ)) : Prop :=
  (σ ∈ (MulAut.conj : S →* MulAut S).range → 1440 < Nat.card (fixedSubgroup σ)) ∧
  (σ ∉ (MulAut.conj : S →* MulAut S).range → Nat.card (fixedSubgroup σ) ≤ 720 →
    Nat.card (fixedSubgroup σ) = 720 ∧
    ((∃ x : ↥(fixedSubgroup σ), orderOf x = 2 ∧ x ∉ D) ∨ (t = .PSU ∧ n = 4 ∧ f = 1)))

@[expose] def OddA6Shape (t : StatedLieTag) : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (n p f : ℕ), p.Prime → p ≠ 2 → StatedLieAdmissible t n p f →
    LieModel S t n p f → ∀ σ : MulAut S, orderOf σ = 2 →
    ∀ D : Subgroup ↥(fixedSubgroup σ), A6Hyp σ D → A6ShapeConcl t n p f σ D

@[expose] def OddA6Small (t : StatedLieTag) : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (n p f : ℕ), p.Prime → p ≠ 2 → StatedLieAdmissible t n p f →
    LieModel S t n p f → p = 3 → A6Shape t n f → ∀ σ : MulAut S, orderOf σ = 2 →
    ∀ D : Subgroup ↥(fixedSubgroup σ), A6Hyp σ D → A6SmallConcl t n f σ D

theorem a6sq_derived_data {S : Type} [Group S] (σ : MulAut S)
    (e : ↥(commutator ↥(autCentralizer σ)) ≃* alternatingGroup (Fin 6)) :
    ∃ D : Subgroup ↥(fixedSubgroup σ), D = commutator ↥(fixedSubgroup σ) ∧ D.Normal ∧
      Nonempty (↥D ≃* alternatingGroup (Fin 6)) := by
  let φ : ↥(autCentralizer σ) ≃* ↥(fixedSubgroup σ) :=
    MulEquiv.subgroupCongr (autCentralizer_eq_fixedSubgroup σ)
  have h : (commutator ↥(autCentralizer σ)).map φ.toMonoidHom = commutator ↥(fixedSubgroup σ) := by
    have h1 : commutator ↥(autCentralizer σ) = ⁅(⊤ : Subgroup ↥(autCentralizer σ)), ⊤⁆ := rfl
    have h2 : commutator ↥(fixedSubgroup σ) = ⁅(⊤ : Subgroup ↥(fixedSubgroup σ)), ⊤⁆ := rfl
    rw [h1, h2, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ φ.surjective]
  refine ⟨commutator ↥(fixedSubgroup σ), rfl, inferInstance, ⟨?_⟩⟩
  exact (MulEquiv.subgroupCongr h.symm).trans
    (((commutator ↥(autCentralizer σ)).equivMapOfInjective φ.toMonoidHom φ.injective).symm.trans e)

theorem a6Hyp_of_derived {S : Type} [Group S] (σ : MulAut S)
    (e : ↥(commutator ↥(autCentralizer σ)) ≃* alternatingGroup (Fin 6)) :
    ∃ D : Subgroup ↥(fixedSubgroup σ), D = commutator ↥(fixedSubgroup σ) ∧ A6Hyp σ D := by
  obtain ⟨D, hDeq, hDn, hD⟩ := a6sq_derived_data σ e
  refine ⟨D, hDeq, hDn, hD, fun P hP => ?_⟩
  rw [hDeq]
  calc P = ⁅P, P⁆ := hP.symm
    _ ≤ ⁅(⊤ : Subgroup ↥(fixedSubgroup σ)), ⊤⁆ := Subgroup.commutator_mono le_top le_top

theorem oddA6Family_of_shape (hO : LieOrderFormulasInput) {t : StatedLieTag}
    (h : OddA6Shape t) : OddA6Family t := by
  intro S _ _ n p f hp hp2 hadm hm σ hσ _hC hC' h129
  obtain ⟨e6⟩ := hC'
  obtain ⟨D, hDeq, hDhyp⟩ := a6Hyp_of_derived σ e6
  obtain ⟨hp3, hshape, hswap⟩ := h S n p f hp hp2 hadm hm σ hσ D hDhyp
  subst hp3
  by_cases hc : t = .PSp ∧ n = 2 ∧ f = 2
  · obtain ⟨rfl, rfl, rfl⟩ := hc
    obtain ⟨a, b, hab⟩ := hswap rfl rfl rfl
    apply hab
    rw [hDeq]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
  · refine a6sq_order_not_dvd hO hadm hm ?_ h129
    rcases hshape with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
    · exact Or.inl ⟨h1.1, h1.2.1, rfl, h1.2.2⟩
    · exact Or.inr (Or.inl ⟨h2.1, h2.2.1, rfl, h2.2.2⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h3.1, h3.2.1, rfl, h3.2.2⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h4.1, h4.2.1, rfl, h4.2.2⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h5.1, h5.2.1, rfl, h5.2.2⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h6.1, h6.2.1, rfl, h6.2.2⟩)))))
    · exact absurd h7 hc
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h8.1, h8.2.1, rfl, h8.2.2⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h9.1, h9.2.1, rfl, h9.2.2⟩))))))

theorem a6OddArm_of_shapes (hO : LieOrderFormulasInput) (h : ∀ t, OddA6Shape t) : A6OddArm :=
  a6OddArm_of_families fun t => oddA6Family_of_shape hO (h t)

end CFSG.ComponentClassification.CatFC
