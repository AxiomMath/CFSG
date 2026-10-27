module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.ExcModel
public import CFSG.LieType.Steinberg.CentralExt.GriessTwistedE6
public import CFSG.LieType.Steinberg.CentralExt.TrialityClosed

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.Blueprint CFSG.Blueprint.Chevalley TauCeti CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedD4

theorem exists_frobenius_field (q : PrimePower) {m : ℕ} (hm : 0 < m) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K →+* K),
      Nat.card K = (q.p ^ q.exponent) ^ m ∧ (∀ c, σ c = c ^ (q.p ^ q.exponent)) := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  refine ⟨GaloisField q.p (q.exponent * m), inferInstance, inferInstance,
    iterateFrobenius (GaloisField q.p (q.exponent * m)) q.p q.exponent, ?_, ?_⟩
  · rw [GaloisField.card _ _ (Nat.mul_ne_zero q.exponent_pos.ne' hm.ne'), pow_mul]
  · intro c
    exact iterateFrobenius_def q.p q.exponent c

section Twisted


theorem exists_twistedGroup_model_of_lie_trialityD4
    {L : Type} [Group L] [Finite L] (hperf : Group.IsPerfect L) {q : PrimePower}
    (hv : (LieTypeIndex.trialityD4 q).Valid) (hp2 : q.p ≠ 2)
    (e : L ⧸ Subgroup.center L ≃* (CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group) :
    Subgroup.center L = ⊥ ∧
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K →+* K),
        Nat.card K = (q.p ^ q.exponent) ^ 3 ∧ (∀ c, σ c = c ^ (q.p ^ q.exponent)) ∧
          Nonempty (L ⧸ Subgroup.center L ≃* twistedGroup σ) := by
  obtain ⟨K, hKf, hKfin, σ, hK, hσ⟩ := exists_frobenius_field q (m := 3) (by norm_num)
  have hq3 : 3 ≤ q.p ^ q.exponent := by
    rcases eq_three_or_five_le_of_odd_prime_pow q.prime_p hp2 q.exponent_pos with h | h <;> omega
  have hKq : Nat.card K = q.card ^ TwistTag.D4.order := by
    rw [hK, PrimePower.card_def]; rfl
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Twisted.twistedBridge_trialityD4 q hv hp2 K hKq σ
    (fun x => by rw [PrimePower.card_def]; exact hσ x)
  let e' : L ⧸ Subgroup.center L ≃*
      CFSG.Blueprint.DerivedCentralQuotient (twistedFixedGroup .D4 K σ) := e.trans b.symm
  have hdvd := CFSG.AGLEmbedding.card_center_dvd_card_griessHopfMultiplier hperf e'
  have hZtw := CFSG.LieType.Steinberg.CentralExt.TrialityClosed.twistedGroup_center_eq_bot_of_card
    (σ := σ) (q := q.p ^ q.exponent) (by omega) hK hσ
  set eT := twistedGroupEquivDerived σ (q := q.p ^ q.exponent) (by omega) hK hσ
  have hZ : Subgroup.center ↥⁅twistedFixedGroup .D4 K σ, twistedFixedGroup .D4 K σ⁆ = ⊥ :=
    CFSG.SectionRank.center_eq_bot_of_mulEquiv' eT hZtw
  have hsub : Subsingleton (CFSG.Open.griessHopfMultiplier
      (CFSG.Blueprint.DerivedCentralQuotient (twistedFixedGroup .D4 K σ))) := by
    have : Group.IsPerfect (twistedGroup σ) :=
      twistedGroup_isPerfect_of_card (by omega) hK hσ
    have : Group.IsPerfect ↥⁅twistedFixedGroup .D4 K σ, twistedFixedGroup .D4 K σ⁆ :=
      Group.IsPerfect.ofSurjective (f := eT.toMonoidHom) eT.surjective
    refine (CFSG.LieType.Steinberg.CentralExt.FieldFour.hopfMultiplier_subsingleton hZ
      fun E _ _ π hπ hcen => ?_).2
    set π' : E →* twistedGroup σ := eT.symm.toMonoidHom.comp π
    have hπ' : Function.Surjective π' := eT.symm.surjective.comp hπ
    have hcen' : π'.ker ≤ Subgroup.center E := fun x hx => hcen (by
      rw [MonoidHom.mem_ker] at hx ⊢
      have := congrArg eT hx
      simpa [π'] using this)
    obtain ⟨s, hs⟩ := CFSG.LieType.Steinberg.CentralExt.TrialityClosed.triality_exists_section_of_central
      hq3 hK hσ hπ' hcen'
    refine ⟨s.comp eT.symm.toMonoidHom, fun g => ?_⟩
    have h := congrArg eT (hs (eT.symm g))
    simpa [π'] using h
  have hM : Nat.card (CFSG.Open.griessHopfMultiplier
      (CFSG.Blueprint.DerivedCentralQuotient (twistedFixedGroup .D4 K σ))) = 1 := Nat.card_of_subsingleton 1
  rw [hM] at hdvd
  refine ⟨Subgroup.eq_bot_of_card_eq _ (Nat.dvd_one.1 hdvd), K, hKf, hKfin, σ, hK, hσ, ⟨?_⟩⟩
  exact e'.trans
    (((QuotientGroup.quotientMulEquivOfEq hZ).trans
      (QuotientGroup.quotientBot (G := ↥⁅twistedFixedGroup .D4 K σ,
        twistedFixedGroup .D4 K σ⁆))).trans eT.symm)

theorem exists_graphFixed_model_of_lie_twistedE6
    {L : Type} [Group L] [Finite L] (hperf : Group.IsPerfect L) {q : PrimePower}
    (hv : (LieTypeIndex.twistedE6 q).Valid) (hp2 : q.p ≠ 2)
    (e : L ⧸ Subgroup.center L ≃* (CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group) :
    ¬ q.p ∣ Nat.card (Subgroup.center L) ∧ Nat.card (Subgroup.center L) ≤ 3 ∧
      ∃ (k : Type) (_ : Field k) (_ : Finite k) (σ : k →+* k),
        Nat.card k = (q.p ^ q.exponent) ^ 2 ∧ (∀ c, σ c = c ^ (q.p ^ q.exponent)) ∧
          Nonempty (L ⧸ Subgroup.center L ≃* ↥(graphFixedRootGroup TwistTag.E6 k σ)) := by
  obtain ⟨K, hKf, hKfin, σ, hK, hσ⟩ := exists_frobenius_field q (m := 2) (by norm_num)
  have hq3 : 3 ≤ q.p ^ q.exponent := by
    rcases eq_three_or_five_le_of_odd_prime_pow q.prime_p hp2 q.exponent_pos with h | h <;> omega
  have hKq : Nat.card K = q.card ^ TwistTag.E6.order := by
    rw [hK, PrimePower.card_def]; rfl
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Twisted.twistedBridge_twistedE6 q hv hp2 K hKq σ
    (fun x => by rw [PrimePower.card_def]; exact hσ x)
  let e' : L ⧸ Subgroup.center L ≃*
      CFSG.Blueprint.DerivedCentralQuotient (twistedFixedGroup .E6 K σ) := e.trans b.symm
  have hdvd := CFSG.AGLEmbedding.card_center_dvd_card_griessHopfMultiplier hperf e'
  obtain ⟨-, hM⟩ := CFSG.LieType.Steinberg.CentralExt.GriessExceptional.twistedE6_hopfMultiplier
    hq3 hK hσ
  have hMc : Nat.card (CFSG.Open.griessHopfMultiplier
      (CFSG.Blueprint.DerivedCentralQuotient (twistedFixedGroup .E6 K σ))) =
        Nat.gcd 3 (q.p ^ q.exponent + 1) := card_eq_of_zmod_equiv hM
  rw [hMc] at hdvd
  have hp1 : ¬ q.p ∣ Nat.card (Subgroup.center L) := by
    intro hp
    have h4 : q.p ∣ q.p ^ q.exponent + 1 := hp.trans (hdvd.trans (Nat.gcd_dvd_right _ _))
    have h5 : q.p ∣ q.p ^ q.exponent := dvd_pow_self q.p q.exponent_pos.ne'
    exact q.prime_p.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h5).1 h4))
  refine ⟨hp1, Nat.le_of_dvd (by norm_num) (hdvd.trans (Nat.gcd_dvd_left _ _)), K, hKf, hKfin, σ,
    hK, hσ, ⟨?_⟩⟩
  have hK4 : 4 ≤ Nat.card K := by rw [hK]; nlinarith
  have hθ : ∀ c, σ (σ c) = c :=
    CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.theta_theta_of_card hK hσ
  have hZ := CFSG.LieType.Steinberg.CentralExt.GriessExceptional.twistedE6_center_derived_eq_bot
    hθ hK4
  have hchar : ringChar K ≠ 2 := by
    intro h2
    have : CharP K 2 := h2 ▸ ringChar.charP K
    have := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    have hodd : Odd (Fintype.card K) := by
      rw [← Nat.card_eq_fintype_card, hK]; exact (Odd.pow (q.prime_p.eq_two_or_odd'.resolve_left hp2)).pow
    rw [hn] at hodd
    exact absurd hodd (by simp [Nat.not_odd_iff_even, Nat.even_pow])
  let σe : K ≃+* K := RingEquiv.ofBijective σ ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩
  have hσe : σe.toRingHom = σ := RingHom.ext fun _ => rfl
  have hroot := (odd_diagram_fixed_root_group_perfect TwistTag.E6 K hchar σe).2.2
  rw [hσe] at hroot
  exact e'.trans (((QuotientGroup.quotientMulEquivOfEq hZ).trans
    (QuotientGroup.quotientBot (G := ↥⁅twistedFixedGroup .E6 K σ,
      twistedFixedGroup .E6 K σ⁆))).trans (MulEquiv.subgroupCongr hroot))

end Twisted

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
