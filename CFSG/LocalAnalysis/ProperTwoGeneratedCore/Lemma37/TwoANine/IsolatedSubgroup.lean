module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.IsolatedQuotient

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Subgroup CFSG.ProperTwoGeneratedCore.Assembly

variable {X : Type} [Group X] [Finite X]

@[expose] def centralizerInclusion (H : Subgroup X) (t : H) :
    centralizer ({t} : Set H) →* centralizer ({(t : X)} : Set X) :=
  (H.subtype.comp (centralizer ({t} : Set H)).subtype).codRestrict _ fun c =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp c.2))

omit [Finite X] in
@[simp] theorem coe_centralizerInclusion_apply (H : Subgroup X) (t : H)
    (c : centralizer ({t} : Set H)) : (centralizerInclusion H t c : X) = ((c : H) : X) :=
  rfl

omit [Finite X] in
theorem centralizerInclusion_injective (H : Subgroup X) (t : H) :
    Function.Injective (centralizerInclusion H t) := fun c d h => by
  have h' := congrArg (fun x : centralizer ({(t : X)} : Set X) => (x : X)) h
  exact Subtype.ext (Subtype.ext h')

theorem nonempty_escapingQuotient_mulEquiv_of_subgroup {H : Subgroup X} (t : H)
    (hcov : ∀ m ∈ centralizer ({(t : X)} : Set X), ∃ n ∈ H,
      n ∈ centralizer ({(t : X)} : Set X) ∧ n⁻¹ * m ∈ oddCentralizer (t : X)) :
    Nonempty (EscapingQuotient t ≃* EscapingQuotient (t : X)) := by
  refine nonempty_mulEquiv_quotient_pPrimeCore (centralizerInclusion H t) ?_ fun y => ?_
  · rw [(MonoidHom.ker_eq_bot_iff _).mpr (centralizerInclusion_injective H t), Subgroup.card_bot]
    exact odd_one
  · obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective _ y
    obtain ⟨n, hnH, hnt, hnm⟩ := hcov m m.2
    have hnt' : (⟨n, hnH⟩ : H) ∈ centralizer ({t} : Set H) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hnt))
    refine ⟨⟨⟨n, hnH⟩, hnt'⟩, ?_⟩
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have h := (coe_mem_oddCentralizer_iff
      (c := (centralizerInclusion H t ⟨⟨n, hnH⟩, hnt'⟩)⁻¹ * m)).mp hnm
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h

theorem IsTwoANine.escapingQuotient_of_subgroup {H : Subgroup X} (t : H)
    (hcov : ∀ m ∈ centralizer ({(t : X)} : Set X), ∃ n ∈ H,
      n ∈ centralizer ({(t : X)} : Set X) ∧ n⁻¹ * m ∈ oddCentralizer (t : X))
    (hJ : IsTwoANine (EscapingQuotient (t : X))) : IsTwoANine (EscapingQuotient t) :=
  hJ.of_mulEquiv (nonempty_escapingQuotient_mulEquiv_of_subgroup t hcov).some.symm

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
