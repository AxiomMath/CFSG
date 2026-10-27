module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Mult
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47eOmega
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.LieType.Steinberg.CentralExt.GriessExceptional
public import CFSG.LieType.Steinberg.CentralExt.TrialityClosed

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Multiplier
  CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.Steinberg.CentralExt
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.GH74.GLS.IVK.Proofs2.Ivk47
  CFSG.LieType.Steinberg.CentralExt.GriessExceptional

theorem triality_hopfMultiplier_of_three_le {K : Type} [Field K] [Finite K]
    {σ : K →+* K} {q : ℕ} (hq : 3 ≤ q) (hK : Nat.card K = q ^ 3) (hσq : ∀ c, σ c = c ^ q) :
    Subsingleton (CFSG.Open.griessHopfMultiplier
        (DerivedCentralQuotient (twistedFixedGroup .D4 K σ))) := by
  set e := twistedGroupEquivDerived σ (by omega) hK hσq
  have : Group.IsPerfect (twistedGroup σ) := twistedGroup_isPerfect_of_card (by omega) hK hσq
  have : Group.IsPerfect ↥⁅twistedFixedGroup .D4 K σ, twistedFixedGroup .D4 K σ⁆ :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hZ := SectionRank.center_eq_bot_of_mulEquiv' e
    (TrialityClosed.twistedGroup_center_eq_bot_of_card (by omega) hK hσq)
  refine (FieldFour.hopfMultiplier_subsingleton hZ fun E _ _ π hπ hcen => ?_).2
  set π' : E →* twistedGroup σ := e.symm.toMonoidHom.comp π
  have hπ' : Function.Surjective π' := e.symm.surjective.comp hπ
  have hcen' : π'.ker ≤ Subgroup.center E := fun x hx => hcen (by
    rw [MonoidHom.mem_ker] at hx ⊢
    have := congrArg e hx
    simpa [π'] using this)
  obtain ⟨s, hs⟩ : ∃ s : twistedGroup σ →* E, ∀ g, π' (s g) = g :=
    TrialityClosed.triality_exists_section_of_central hq hK hσq hπ' hcen'
  refine ⟨s.comp e.symm.toMonoidHom, fun g => ?_⟩
  have h := congrArg e (hs (e.symm g))
  simpa [π'] using h

theorem d4_center_eq_bot {L : Type} [Group L] [Finite L] {p f : ℕ} (hL : CFSG.IsQuasisimple L)
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : LieModel (L ⧸ Subgroup.center L) .trialityD4 0 p f) : Subgroup.center L = ⊥ := by
  obtain ⟨K, _, _, hK, σ, hσ, ⟨e⟩⟩ := twisted_of_lieModel_D4 hmodel
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hq3 : 3 ≤ p ^ f := hp3.trans (Nat.le_self_pow (by omega) p)
  exact center_eq_bot_of_hopf_subsingleton hL e
    (triality_hopfMultiplier_of_three_le hq3 hK (σ := σ) hσ)

end CFSG.GH74.GLS.Stage2.Bender.Thm1
