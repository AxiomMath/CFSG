module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm46FS.SporCentreBasic

public section

namespace CFSG.EvenSporadicStandard.Induction.SporCentre

open CFSG CFSG.LocalCores Subgroup

theorem nonempty_center_equiv_of_component {S : Type*} [Group S] {C : Subgroup S} {E : Type*}
    [Group E] (g : ↥C ≃* E) {V : Type*} [Group V]
    (h : ∀ B : Subgroup E, IsComponent B → Nonempty (center B ≃* V)) {Q : Subgroup S}
    (hQC : Q ≤ C) (hQ : IsComponent (Q.subgroupOf C)) : Nonempty (center Q ≃* V) := by
  obtain ⟨c⟩ := h _ (isComponent_map_mulEquiv g hQ)
  obtain ⟨c'⟩ := nonempty_center_equiv_map g hQC
  exact ⟨c'.trans c⟩

theorem center_eq_bot_of_component_equiv {S : Type*} [Group S] {C : Subgroup S} {E : Type*}
    [Group E] (g : ↥C ≃* E) (h : ∀ B : Subgroup E, IsComponent B → center B = ⊥)
    {Q : Subgroup S} (hQC : Q ≤ C) (hQ : IsComponent (Q.subgroupOf C)) : center Q = ⊥ := by
  have h0 := h _ (isComponent_map_mulEquiv g hQ)
  obtain ⟨c⟩ := nonempty_center_equiv_map g hQC
  have hc := Nat.card_congr c.toEquiv
  rw [h0, Subgroup.card_bot] at hc
  exact Subgroup.eq_bot_of_card_eq _ hc

noncomputable def centralizerEquivInf {M : Type*} [Group M] (P : Subgroup M) {S : Type*}
    [Group S] (f : S ≃* P) (a : S) :
    ↥(centralizer ({a} : Set S)) ≃* ↥(P ⊓ centralizer ({(f a : M)} : Set M)) := by
  have hinj : Function.Injective (P.subtype.comp f.toMonoidHom) :=
    P.subtype_injective.comp f.injective
  refine ((centralizer ({a} : Set S)).equivMapOfInjective _ hinj).trans
    (MulEquiv.subgroupCongr ?_)
  ext y
  simp only [mem_map, mem_inf, mem_centralizer_singleton_iff, MonoidHom.comp_apply,
    coe_subtype, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(f x).2, ?_⟩
    have := congrArg (fun w => ((f w : P) : M)) hx
    simpa using this
  · rintro ⟨hyP, hyc⟩
    refine ⟨f.symm ⟨y, hyP⟩, ?_, by simp⟩
    apply f.injective
    apply Subtype.ext
    simp only [map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul]
    exact hyc

end CFSG.EvenSporadicStandard.Induction.SporCentre
