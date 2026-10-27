module

public import CFSG.HardMathSupport.Solomon.Coordinator.ONAut
public import CFSG.Sporadic.Schreier.SteinbergBIONOuterTwo

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.ComponentClassification.OuterAutomorphisms

theorem inputOutON_of_hatON :
    ∀ (X : Type) [Group X] [Finite X], LocalBalance.IsHatON X →
      (MulAut.conj : X →* MulAut X).range.index ∣ 2 := by
  intro X _ _ hX
  obtain ⟨hperf, -, ⟨e⟩⟩ := hX
  obtain ⟨b0⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  have b : CFSG.Blueprint.NativeSporadic.ON ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group := b0
  have hout : Nat.card (Outer (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group) ∣ 2 :=
    CFSG.Sporadic.SteinbergBI.cti_on_outer_order_divides_two ⟨b.symm⟩
  let f : MulAut X →* MulAut (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group :=
    (MulAut.congr e).toMonoidHom.comp (mulAutQuotCenter X)
  have hf : Function.Injective f :=
    (MulAut.congr e).injective.comp (mulAutQuotCenter_injective hperf)
  have hconj : ∀ x : X, f (MulAut.conj x) = MulAut.conj (e (QuotientGroup.mk x)) := by
    intro x
    have h1 : mulAutQuotCenter X (MulAut.conj x) = MulAut.conj (QuotientGroup.mk x) := by
      apply MulEquiv.ext
      intro q
      induction q using QuotientGroup.induction_on with
      | H y => rfl
    show MulAut.congr e (mulAutQuotCenter X (MulAut.conj x)) = _
    rw [h1, congr_conj]
  have hEq : (MulAut.conj : X →* MulAut X).range =
      (inner (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group).comap f := by
    ext α
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨e (QuotientGroup.mk x), (hconj x).symm⟩
    · rintro ⟨t, ht⟩
      obtain ⟨q, rfl⟩ := e.surjective t
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨x, hf (by rw [hconj x]; exact ht)⟩
  rw [hEq, Subgroup.index_comap]
  exact (Subgroup.relIndex_dvd_index_of_normal _ _).trans hout

end CFSG.HardMathSupport.Solomon.Coordinator
