module

public import CFSG.LieType.SeitzGeneration.QuasiHigh5E6CoverUni
public import CFSG.LieType.SeitzGeneration.UniPlaneCoverLift
public import CFSG.LieType.SeitzGeneration.QuasiHigh5Rest

public section

namespace CFSG.LieType.SeitzGeneration.QuasiHigh5E6Cover

open CFSG.Open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.QuasiHigh CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ (ExcIndex IsSixIndex)


@[expose] def TwE6ThreeOpenPlanes : Prop :=
  Inputs2311c.UniSeitzPlanes fun d p E => p = 3 ∧
    (∃ q : TauCeti.PrimePower, d.1 = .twistedE6 q ∧ q.card % 3 = 2 ∧ q.card ≠ 2) ∧
    ((InnerPlane d p E ∧ ¬ NormalizesRSubgroup d E) ∨
      (¬ InnerPlane d p E ∧
        (∃ q : TauCeti.PrimePower, d.1 = .twistedE6 q ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K)
          (σ : K ≃+* K), Nat.card K = (q.p ^ q.exponent) ^ 2 ∧ (∀ c, σ c = c ^ (q.p ^ q.exponent)) ∧
          ∃ e : Cat d ≃* twistedE6RootGroup K σ,
            E.map (MulAut.congr e).toMonoidHom ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ) ∧
        ¬ Inputs2311d.IsTwE6DiagParabolicPlane d E))

@[expose] def TwE6ThreeOpenInner : Prop :=
  Inputs2311c.UniSeitzPlanes fun d p E => InnerPlane d p E ∧ p = 3 ∧
    (∃ q : TauCeti.PrimePower, d.1 = .twistedE6 q ∧ q.card % 3 = 2 ∧ q.card ≠ 2) ∧
    ¬ NormalizesRSubgroup d E

@[expose] def TwE6ThreeOpenDiag : Prop :=
  Inputs2311c.UniSeitzPlanes fun d p E => p = 3 ∧
    (∃ q : TauCeti.PrimePower, d.1 = .twistedE6 q ∧ q.card % 3 = 2 ∧ q.card ≠ 2) ∧
    ¬ InnerPlane d p E ∧
    (∃ q : TauCeti.PrimePower, d.1 = .twistedE6 q ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K)
      (σ : K ≃+* K), Nat.card K = (q.p ^ q.exponent) ^ 2 ∧ (∀ c, σ c = c ^ (q.p ^ q.exponent)) ∧
      ∃ e : Cat d ≃* twistedE6RootGroup K σ,
        E.map (MulAut.congr e).toMonoidHom ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ) ∧
    ¬ Inputs2311d.IsTwE6DiagParabolicPlane d E

theorem twE6ThreeOpenPlanes_of (hI : TwE6ThreeOpenInner) (hD : TwE6ThreeOpenDiag) :
    TwE6ThreeOpenPlanes := by
  intro d p hp hp2 hpd hex E hE hc hs
  obtain ⟨hp3, hq, hcase⟩ := hs
  subst hp3
  rcases hcase with ⟨hin, hn⟩ | ⟨hin, hmodel, hpar⟩
  · exact hI d 3 hp hp2 hpd hex E hE hc ⟨hin, rfl, hq, hn⟩
  · exact hD d 3 hp hp2 hpd hex E hE hc ⟨rfl, hq, hin, hmodel, hpar⟩

theorem uniSeitzPlanes_E6_three_one :
    Inputs2311c.UniSeitzPlanes fun d p _ =>
      p = 3 ∧ ∃ q : TauCeti.PrimePower, d.1 = .E6 q ∧ q.card % 3 = 1 := by
  intro d p hp hp2 hpd hex E hE hc hs
  obtain ⟨hp3, q, hdq, hqmod⟩ := hs
  subst hp3
  by_cases hin : InnerPlane d 3 E
  · by_cases hn : NormalizesRSubgroup d E
    · exact Inputs2311c.uniSeitzPlanes_excParabolic d 3 hp hp2 hpd hex E hE hc
        ⟨hin, Or.inl (Or.inr (Or.inr (Or.inl ⟨q, hdq⟩))), hn⟩
    · exact uniSeitzPlanes_E6_inner_three_one d 3 hp hp2 hpd hex E hE hc
        ⟨hin, rfl, ⟨q, hdq, hqmod⟩, hn⟩
  · by_cases hdiag : Inputs2311d.IsE6DiagPlane d E
    · exact Inputs2311d.uniSeitzPlanes_E6_diag d 3 hp hp2 hpd hex E hE hc ⟨hin, rfl, hdiag⟩
    · exact uniSeitzPlanes_E6_field_one d 3 hp hp2 hpd hex E hE hc
        ⟨hin, rfl, ⟨q, hdq, hqmod⟩, hdiag⟩

theorem uniSeitzPlanes_twE6_three_two_of_open (h : TwE6ThreeOpenPlanes) :
    Inputs2311c.UniSeitzPlanes fun d p E => p = 3 ∧
      ∃ q : TauCeti.PrimePower, d.1 = .twistedE6 q ∧ q.card % 3 = 2 ∧ q.card ≠ 2 ∧
        (q.card = 8 → InnerPlane d p E) := by
  intro d p hp hp2 hpd hex E hE hc hs
  obtain ⟨hp3, q, hdq, hqmod, hqne, h8⟩ := hs
  subst hp3
  by_cases hin : InnerPlane d 3 E
  · by_cases hn : NormalizesRSubgroup d E
    · exact Inputs2311c.uniSeitzPlanes_excParabolic d 3 hp hp2 hpd hex E hE hc
        ⟨hin, Or.inr (Or.inr ⟨q, hdq⟩), hn⟩
    · exact h d 3 hp hp2 hpd hex E hE hc
        ⟨rfl, ⟨q, hdq, hqmod, hqne⟩, Or.inl ⟨hin, hn⟩⟩
  · have hq8 : q.card ≠ 8 := fun hq8 => hin (h8 hq8)
    by_cases hmodel : ∃ q : TauCeti.PrimePower, d.1 = .twistedE6 q ∧
        ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K),
          Nat.card K = (q.p ^ q.exponent) ^ 2 ∧ (∀ c, σ c = c ^ (q.p ^ q.exponent)) ∧
          ∃ e : Cat d ≃* twistedE6RootGroup K σ,
            E.map (MulAut.congr e).toMonoidHom ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ
    · by_cases hpar : Inputs2311d.IsTwE6DiagParabolicPlane d E
      · exact Inputs2311d.uniSeitzPlanes_twE6_diag_parabolic d 3 hp hp2 hpd hex E hE hc
          ⟨hin, rfl, hpar⟩
      · exact h d 3 hp hp2 hpd hex E hE hc
          ⟨rfl, ⟨q, hdq, hqmod, hqne⟩, Or.inr ⟨hin, hmodel, hpar⟩⟩
    · exact uniSeitzPlanes_twE6_field_ne_eight d 3 hp hp2 hpd hex E hE hc
        ⟨hin, rfl, ⟨q, hdq, hq8⟩, hmodel⟩

theorem seitzCoverFamExcRest2Rest_E6 :
    ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    ∀ d : TauCeti.ValidLieTypeIndex,
    Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
    p ≠ d.1.characteristic → ¬ (p = 3 ∧ IsLThreeFour (K ⧸ Subgroup.center K)) →
    p ∣ Nat.card (Subgroup.center K) → CoverIndex p d.1 →
    ∀ E : Subgroup (MulAut K), IsElemAbelian p E → Nat.card E = p ^ 2 →
      (¬ ExcIndex p d.1 ∨ (IsSixIndex d.1 ∧ E ≤ (MulAut.conj : K →* MulAut K).range)) →
      ¬ CoverScope d p E → ¬ ExcIsotropic d E →
      (∃ q, d.1 = TauCeti.LieTypeIndex.E6 q) →
        seitzHyperGamma p E = ⊤ := by
  intro p hp hp2 K _ _ hq d hd hpd _ _ hci E hE hcard hex _ _ ⟨q, hdq⟩
  obtain ⟨e⟩ := hd
  rw [hdq] at hci
  obtain ⟨hp3, h3⟩ := hci
  subst hp3
  have hD2 : ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException 3 d.1 := by
    rw [hdq]
    simp [CFSG.AGLEmbeddingD2.IsD2SeitzException]
  have hcardq : 2 ≤ q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact le_trans q.prime_p.two_le (Nat.le_self_pow q.exponent_pos.ne' q.p)
  have hqmod : q.card % 3 = 1 := by omega
  set Ē : Subgroup (MulAut (Cat d)) := coverImage e E with hĒ
  have hEĒ : IsElemAbelian 3 Ē := isElemAbelian_coverImage e hE
  have hcardĒ : Nat.card Ē = 3 ^ 2 := by
    rw [hĒ]
    exact card_coverImage hq.1 e E ▸ hcard
  have hgen : Inputs2311c.UniPlaneGen d.1.characteristic Ē :=
    uniSeitzPlanes_E6_three_one d 3 hp hp2 hpd hD2 Ē hEĒ hcardĒ ⟨rfl, ⟨q, hdq, hqmod⟩⟩
  have hr : Nat.Prime d.1.characteristic := by
    rw [hdq, TauCeti.LieTypeIndex.characteristic_E6]
    exact q.prime_p
  refine seitzHyperGamma_eq_top_of_uniPlaneGen hq.1 e hp hr ?_ hE hcard hgen
  exact fun h => hpd h.symm

theorem seitzCoverFamExcRest2Rest_of_open (h : TwE6ThreeOpenPlanes) :
    QuasiHigh5.SeitzCoverFamExcRest2Rest := by
  intro p hp hp2 K _ _ hq d hd hpd hL34 hz hci E hE hcard hex hCS hiso hde
  rcases hde with hE6 | hT
  · exact seitzCoverFamExcRest2Rest_E6 p hp hp2 K hq d hd hpd hL34 hz hci E hE hcard hex
      hCS hiso hE6
  · obtain ⟨q, hdq⟩ := hT
    obtain ⟨e⟩ := hd
    rw [hdq] at hci
    obtain ⟨hp3, h3⟩ := hci
    subst hp3
    have hD2 : ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException 3 d.1 := by
      rw [hdq]
      simp [CFSG.AGLEmbeddingD2.IsD2SeitzException]
    have hcardq : 2 ≤ q.card := by
      rw [TauCeti.PrimePower.card_def]
      exact le_trans q.prime_p.two_le (Nat.le_self_pow q.exponent_pos.ne' q.p)
    have hqmod : q.card % 3 = 2 := by omega
    have hqne2 : q.card ≠ 2 := by
      intro hq2
      have hq2card : q.p ^ q.exponent = 2 := by
        rw [← TauCeti.PrimePower.card_def]
        exact hq2
      obtain ⟨hp2, hexp1⟩ := (Nat.Prime.pow_eq_iff Nat.prime_two).mp hq2card
      have hexc : ExcIndex 3 d.1 := by
        rw [hdq]
        exact Or.inr ⟨rfl, Or.inr (Or.inr (Or.inl ⟨hp2, hexp1⟩))⟩
      have hsix : IsSixIndex d.1 := by
        rcases hex with h | h
        · exact absurd hexc h
        · exact h.1
      rw [hdq] at hsix
      have htwo : IsTwoPow q 3 := by
        simpa [IsSixIndex, IsF4EightIndex, IsD4FourIndex, FourIndex] using hsix
      obtain ⟨-, hexp3⟩ := htwo
      omega
    set Ē : Subgroup (MulAut (Cat d)) := coverImage e E with hĒ
    have hEĒ : IsElemAbelian 3 Ē := isElemAbelian_coverImage e hE
    have hcardĒ : Nat.card Ē = 3 ^ 2 := by
      rw [hĒ]
      exact card_coverImage hq.1 e E ▸ hcard
    have h8 : q.card = 8 → InnerPlane d 3 Ē := by
      intro hq8card
      have hq8' : q.p ^ q.exponent = 2 ^ 3 := by
        rw [← TauCeti.PrimePower.card_def, hq8card]
        norm_num
      have hp2 : q.p = 2 := by
        have hdvd : q.p ∣ 2 ^ 3 := by
          rw [← hq8']
          exact dvd_pow_self q.p q.exponent_pos.ne'
        exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1
          (q.prime_p.dvd_of_dvd_pow hdvd)
      have hexp3 : q.exponent = 3 := by
        apply Nat.pow_right_injective (a := 2) (by norm_num : 2 ≤ 2)
        simpa [hp2] using hq8'
      have htwo : IsTwoPow q 3 := ⟨hp2, hexp3⟩
      have hsix : IsSixIndex d.1 := by
        rw [hdq]
        exact Or.inr (Or.inr htwo)
      have hexc : ExcIndex 3 d.1 :=
        Or.inr ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr hsix)))⟩
      have hrange : E ≤ (MulAut.conj : K →* MulAut K).range := by
        rcases hex with h | h
        · exact absurd hexc h
        · exact h.2
      exact coverImage_le_range_conj e hrange
    have hgen : Inputs2311c.UniPlaneGen d.1.characteristic Ē :=
      uniSeitzPlanes_twE6_three_two_of_open h d 3 hp hp2 hpd hD2 Ē hEĒ hcardĒ
        ⟨rfl, ⟨q, hdq, hqmod, hqne2, h8⟩⟩
    have hr : Nat.Prime d.1.characteristic := by
      rw [hdq, TauCeti.LieTypeIndex.characteristic_twistedE6]
      exact q.prime_p
    refine seitzHyperGamma_eq_top_of_uniPlaneGen hq.1 e hp hr ?_ hE hcard hgen
    exact fun h' => hpd h'.symm

end CFSG.LieType.SeitzGeneration.QuasiHigh5E6Cover
