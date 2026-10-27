module

public import CFSG.LieType.Steinberg.CentralExt.TrialityClosed
public import CFSG.LieType.Steinberg.CentralExt.GriessExceptional
public import CFSG.LieType.Steinberg.CentralExt.FieldTwoMultiplier
public import CFSG.LieType.Chevalley.TrialityFieldTwoCover
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication

public section

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Multiplier
  CFSG.LieType.Steinberg.TwistedD4

namespace CFSG.LieType.Steinberg.CentralExt.GriessExceptional

theorem lieModel_triality_two {K : Type} [Field K] [Finite K] {σ : K →+* K}
    (hK : Nat.card K = 2 ^ 3) (hσq : ∀ c, σ c = c ^ 2) :
    CFSG.Blueprint.LieModel (DerivedCentralQuotient (twistedFixedGroup .D4 K σ)) .trialityD4 0 2 1 :=
  Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, le_rfl, rfl⟩, K, inferInstance, inferInstance,
    by rw [hK]; rfl, σ, fun c => by rw [hσq, pow_one], ⟨MulEquiv.refl _⟩⟩)

theorem triality_two_exists_section {K : Type} [Field K]
    [Finite K] {σ : K →+* K} (hK : Nat.card K = 2 ^ 3) (hσq : ∀ c, σ c = c ^ 2) {E : Type}
    [Group E] [Finite E] {π : E →* twistedGroup σ} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) : ∃ s : twistedGroup σ →* E, ∀ g, π (s g) = g := by
  have hσ : ∀ c, σ (σ (σ c)) = c := sigma_three_of_card hK hσq
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (k := 3) (by norm_num) hK
  have : Group.IsPerfect (twistedGroup σ) := twistedGroup_isPerfect_of_card le_rfl hK hσq
  set e := twistedGroupEquivDerived σ le_rfl hK hσq
  have hZ := SectionRank.center_eq_bot_of_mulEquiv' e
    (TrialityClosed.twistedGroup_center_eq_bot_of_card le_rfl hK hσq)
  set θ : twistedGroup σ →* DerivedCentralQuotient (twistedFixedGroup .D4 K σ) :=
    (QuotientGroup.mk' _).comp e.toMonoidHom
  have hθs : Function.Surjective θ := (QuotientGroup.mk'_surjective _).comp e.surjective
  have hθi : Function.Injective θ := by
    refine (MonoidHom.ker_eq_bot_iff θ).1 (eq_bot_iff.2 fun x hx => ?_)
    have h1 : e x ∈ Subgroup.center _ := by
      rw [← QuotientGroup.ker_mk' (Subgroup.center _)]
      exact hx
    rw [hZ, Subgroup.mem_bot] at h1
    exact (Subgroup.mem_bot).2 (e.map_eq_one_iff.1 h1)
  exact CoprimeSplit.exists_section_of_parts (p := 2) hπ hcen
    (fun E' _ _ π' hπ' hcen' hp' => FieldFour.exists_section_of_ker_eq_bot
      (fun P _ _ _ η hη hC h2 => FieldTwo.ker_eq_bot_of_injective hθs hθi
        (fun η' hη' hC' h2' => (CFSG.LieType.Chevalley.triality_field_two_central_two_cover_trivial
          η' hη' hC' h2' (lieModel_triality_two hK hσq)).1) η hη hC h2)
      E' π' hπ' hcen' hp')
    (fun E' _ _ π' hπ' hcen' hc' =>
      TrialityClosed.triality_exists_section_of_coprime hσ hπ' hcen' hc')

theorem triality_hopfMultiplier {K : Type} [Field K] [Finite K]
    {σ : K →+* K} {q : ℕ} (hq : 2 ≤ q) (hK : Nat.card K = q ^ 3) (hσq : ∀ c, σ c = c ^ q) :
    commutator (DerivedCentralQuotient (twistedFixedGroup .D4 K σ)) = ⊤ ∧
      Subsingleton (CFSG.Open.griessHopfMultiplier
        (DerivedCentralQuotient (twistedFixedGroup .D4 K σ))) := by
  set e := twistedGroupEquivDerived σ (by omega) hK hσq
  have : Group.IsPerfect (twistedGroup σ) := twistedGroup_isPerfect_of_card (by omega) hK hσq
  have : Group.IsPerfect ↥⁅twistedFixedGroup .D4 K σ, twistedFixedGroup .D4 K σ⁆ :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hZ := SectionRank.center_eq_bot_of_mulEquiv' e
    (TrialityClosed.twistedGroup_center_eq_bot_of_card (by omega) hK hσq)
  refine FieldFour.hopfMultiplier_subsingleton hZ fun E _ _ π hπ hcen => ?_
  set π' : E →* twistedGroup σ := e.symm.toMonoidHom.comp π
  have hπ' : Function.Surjective π' := e.symm.surjective.comp hπ
  have hcen' : π'.ker ≤ Subgroup.center E := fun x hx => hcen (by
    rw [MonoidHom.mem_ker] at hx ⊢
    have := congrArg e hx
    simpa [π'] using this)
  obtain ⟨s, hs⟩ : ∃ s : twistedGroup σ →* E, ∀ g, π' (s g) = g := by
    rcases (show q = 2 ∨ 3 ≤ q by omega) with rfl | hq3
    · exact triality_two_exists_section hK hσq hπ' hcen'
    · exact TrialityClosed.triality_exists_section_of_central hq3 hK hσq hπ' hcen'
  refine ⟨s.comp e.symm.toMonoidHom, fun g => ?_⟩
  have h := congrArg e (hs (e.symm g))
  simpa [π'] using h

variable
  {X : Type} [Group X] {n p f : ℕ}

theorem trialityD4_row
    (hmodel : CFSG.Models.LieModel X .trialityD4 n p f) :
    commutator X = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier X ≃*
        generic .trialityD4 n p f × exceptional .trialityD4 n p f) := by
  obtain ⟨-, hcl | ⟨-, ⟨d, hv⟩, hd, ⟨e⟩⟩⟩ := hmodel
  · exact hcl.2.elim
  · cases d with
    | trialityD4 q =>
      obtain ⟨rfl, rfl⟩ := hd
      have : Fact q.p.Prime := ⟨q.prime_p⟩
      set K := GaloisField q.p (3 * q.exponent)
      have hK3 : Nat.card K = q.card ^ 3 := by
        rw [TauCeti.PrimePower.card_def, GaloisField.card _ _ (by have := q.exponent_pos; omega),
          ← pow_mul, mul_comm]
      have hK : Nat.card K = q.card ^ CFSG.Blueprint.Chevalley.TwistTag.D4.order := hK3
      let σ : K →+* K := iterateFrobenius K q.p q.exponent
      have hσ : ∀ x, σ x = x ^ q.card := fun x => by
        rw [TauCeti.PrimePower.card_def]
        exact iterateFrobenius_def q.p q.exponent x
      obtain ⟨b⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).trialityD4 q hv K hK σ hσ
      have hq : 2 ≤ q.card := by
        rw [TauCeti.PrimePower.card_def]
        exact q.prime_p.two_le.trans (Nat.le_self_pow q.exponent_pos.ne' _)
      have hM := triality_hopfMultiplier hq hK3 hσ
      refine GriessClassical.of_mulEquiv (e.trans b.symm) (row_of_subsingleton rfl ?_ hM)
      unfold exceptionalOrders
      split <;> simp_all
    | _ => simp [CFSG.Models.NamesTag] at hd

end CFSG.LieType.Steinberg.CentralExt.GriessExceptional
