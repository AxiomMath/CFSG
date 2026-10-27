module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.Lift
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.SylowTwo
public import CFSG.Sporadic.Schreier.RuAutInner

public section

namespace CFSG.EvenSporadicStandard.TwoRu

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Sporadic.RuSchreier
  CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

theorem forall_eq_conj_of_mulEquiv' {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : ∀ α : MulAut X, ∃ g, α = MulAut.conj g) : ∀ α : MulAut Y, ∃ g, α = MulAut.conj g := by
  intro α
  obtain ⟨g, hg⟩ := h ((MulAut.congr e).symm α)
  refine ⟨e g, ?_⟩
  have := congrArg (MulAut.congr e) hg
  rw [MulEquiv.apply_symm_apply] at this
  rw [this]
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem exists_surjection_ker_eq {L Y : Type*} [Group L] [Group Y] {N : Subgroup L} [N.Normal]
    (f : L ⧸ N ≃* Y) : ∃ q : L →* Y, Function.Surjective q ∧ q.ker = N := by
  refine ⟨f.toMonoidHom.comp (QuotientGroup.mk' N),
    f.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩
  ext x
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    QuotientGroup.mk'_apply]
  rw [map_eq_one_iff _ f.injective, QuotientGroup.eq_one_iff]

theorem allInner_of_mulEquiv_ruP
    {Y : Type*} [Group Y] (f : ruP ≃* Y) : ∀ α : MulAut Y, ∃ g, α = MulAut.conj g :=
  forall_eq_conj_of_mulEquiv' f fun α => mulAut_inner α

theorem nonempty_mulEquiv_ruP_of_isSporadic
    {Y : Type} [Group Y]
    (h : IsSporadic Y .Ru) : Nonempty (Y ≃* ruP) := by
  obtain ⟨e⟩ := h
  exact ⟨e.trans ruEquivP⟩

theorem hypothesisOne_of_isSporadic_ru {Y : Type} [Group Y] (h : IsSporadic Y .Ru)
    (hI : HypothesisOne NativeSporadic.Ru) : HypothesisOne Y := by
  obtain ⟨e⟩ := h
  exact CFSG.EvenSmallLie.hypothesisOne_of_mulEquiv e.symm hI

theorem twoRu_not_standard_of_hypothesisOne
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (h : StdHyp G L)
    (h2 : Nat.card (center L) = 2) (hQ : IsSporadic (L ⧸ center L) .Ru)
    (hI : HypothesisOne NativeSporadic.Ru) : False := by
  obtain ⟨f⟩ := nonempty_mulEquiv_ruP_of_isSporadic hQ
  have hinn : ∀ α : MulAut (L ⧸ center L), ∃ q, α = MulAut.conj q :=
    allInner_of_mulEquiv_ruP f.symm
  have hI' : HypothesisOne (L ⧸ center L) := hypothesisOne_of_isSporadic_ru hQ hI
  have hS := h.card_sylow_eq_two_of_inner hI' hinn
  refine h.false_of_fourthPowerDichotomy hS h2 hinn fun z hz hz1 => ?_
  have : Group.IsPerfect L := Group.isPerfect_def.2 h.standard.1.1
  obtain ⟨q, hq, hkerq⟩ := exists_surjection_ker_eq f
  have hz2 : orderOf z = 2 := by
    have hd : orderOf (⟨z, hz⟩ : center L) ∣ 2 := h2 ▸ orderOf_dvd_natCard _
    have h1 : orderOf (⟨z, hz⟩ : center L) ≠ 1 := fun h1 => hz1 (by
      have := orderOf_eq_one_iff.1 h1
      exact congrArg Subtype.val this)
    exact (Subgroup.orderOf_coe (⟨z, hz⟩ : center L)).trans
      ((Nat.dvd_prime Nat.prime_two).1 hd |>.resolve_left h1)
  have hzp : zpowers z = center L := by
    refine Subgroup.eq_of_le_of_card_ge (zpowers_le.2 hz) ?_
    rw [Nat.card_zpowers, hz2, h2]
  exact ru_fourthPowerDichotomy hq hz2 (hkerq.trans hzp.symm) hzp.le

end CFSG.EvenSporadicStandard.TwoRu
