module

public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20Red
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20AltSub

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.I1420

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

theorem le_of_isSubnormal' {G : Type*} [Group G] {H X : Subgroup G} (h : IsSubnormal H X) :
    H ≤ X :=
  h.le

theorem isSubnormal_subgroupOf' {G : Type*} [Group G] {H X : Subgroup G} (h : IsSubnormal H X) :
    (H.subgroupOf X).IsSubnormal :=
  CFSG.Open.IsSubnormal.subgroupOf h

theorem isSubnormalQuotient_of_open {P : Type*} [Group P] {X H : Subgroup P}
    (h : IsSubnormal H X) {L : Type*} [Group L] (f : H →* L) (hf : Function.Surjective f) :
    IsSubnormalQuotient ↥X L :=
  ⟨H.subgroupOf X, isSubnormal_subgroupOf' h,
    f.comp (Subgroup.subgroupOfEquivOfLe (le_of_isSubnormal' h)).toMonoidHom,
    hf.comp (MulEquiv.surjective _)⟩

theorem fixedSub_congr {S S' : Type} [Group S] [Group S'] (e : S ≃* S') (α : MulAut S) :
    fixedSub (MulAut.congr e α) = (fixedSub α).map e.toMonoidHom := by
  ext s'
  rw [mem_fixedSub, Subgroup.mem_map_equiv, mem_fixedSub]
  show e (α (e.symm s')) = s' ↔ _
  exact (Equiv.eq_symm_apply e.toEquiv).symm

theorem Fi22Cfg.of_mulEquiv {S S' : Type} [Group S] [Group S'] (e : S ≃* S') {α : MulAut S}
    (h : Fi22Cfg S α) : Fi22Cfg S' (MulAut.congr e α) := by
  obtain ⟨H, hH, N, hN, hc, ⟨φ⟩⟩ := h
  refine ⟨H.map e.toMonoidHom, ?_, ?_⟩
  · rw [fixedSub_congr]
    exact isSubnormal_map' e.toMonoidHom hH
  · let t : ↥H ≃* ↥(H.map e.toMonoidHom) := H.equivMapOfInjective e.toMonoidHom e.injective
    have hN' : (N.map t.toMonoidHom).Normal := Subgroup.Normal.map hN t.toMonoidHom t.surjective
    refine ⟨N.map t.toMonoidHom, hN', ?_, ?_⟩
    · rw [Subgroup.card_map_of_injective t.injective]
      exact hc
    · exact ⟨(QuotientGroup.congr N (N.map t.toMonoidHom) t rfl).symm.trans φ⟩

theorem Fi22Cfg.subnormalQuotient {S : Type} [Group S] {α : MulAut S} (h : Fi22Cfg S α) :
    ∃ H : Subgroup S, IsSubnormal H (fixedSub α) ∧ ∃ f : H →* Fi22G, Function.Surjective f := by
  obtain ⟨H, hH, N, hN, -, ⟨φ⟩⟩ := h
  exact ⟨H, hH, φ.toMonoidHom.comp (QuotientGroup.mk' N),
    φ.surjective.comp (QuotientGroup.mk'_surjective N)⟩

end CFSG.HardMathSupport.Solomon.Coordinator.I1420
