module

public import CFSG.LieType.SeitzGeneration.RankVacuity
public import CFSG.LieType.SeitzGeneration.DiagPlanesUnitary
public import CFSG.LieType.SeitzGeneration.NonabHeisThree
public import CFSG.LieType.SeitzGeneration.InnerLinearThreeAb
public import CFSG.LieType.SeitzGeneration.InnerUnitaryThree
public import CFSG.LieType.SeitzGeneration.UnitaryNonsplit
public import CFSG.LieType.SeitzGeneration.OrthExLift

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.AGLEmbeddingD2

@[expose] def SeitzInnerUnitaryThreeNonab : Prop :=
  SeitzPlanes fun d p E => InnerPlane d p E ∧ p = 3 ∧
    ∃ q : TauCeti.PrimePower, d.1 = .twistedA 2 q ∧ 3 ∣ q.card + 1

section Arith

theorem prime_eq_three_or_five_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : p = 3 ∨ 5 ≤ p := by
  have h2 := hp.two_le
  rcases (by omega : p = 3 ∨ p = 4 ∨ 5 ≤ p) with h | h | h
  · exact Or.inl h
  · subst h
    exact absurd hp (by norm_num)
  · exact Or.inr h

theorem primePower_card_two {q : TauCeti.PrimePower} (h : q.card = 2) :
    q.p = 2 ∧ q.exponent = 1 := by
  have hp2 : q.p = 2 := by
    have h1 : q.p ∣ q.p ^ q.exponent := dvd_pow_self q.p q.exponent_pos.ne'
    rw [← TauCeti.PrimePower.card_def, h] at h1
    exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 h1
  refine ⟨hp2, ?_⟩
  have h1 : 2 ^ q.exponent = 2 ^ 1 := by
    have h2 := h
    rw [TauCeti.PrimePower.card_def, hp2] at h2
    rw [h2]
    norm_num
  exact Nat.pow_right_injective (le_refl 2) h1

theorem isD2SeitzException_unitary_four {q : TauCeti.PrimePower} (h : q.card = 2) :
    IsD2SeitzException 3 (.twistedA 3 q) :=
  Or.inl ⟨rfl, Or.inr (Or.inr (Or.inl ⟨q, (primePower_card_two h).1, (primePower_card_two h).2,
    rfl⟩))⟩

end Arith

section InnerEx

theorem innerEx_linear : InnerExFor fun d => IsLinearIndex d.1 := by
  rintro ⟨d, hv⟩ ⟨m, q, rfl⟩ p hp hp2 hpd hex ⟨E, hEa, hc, hinner⟩
  rcases prime_eq_three_or_five_le hp hp2 with rfl | hp5
  · refine ⟨E, hEa, hc, hinner, ?_⟩
    by_cases hlift : CentralPrimeFree 3 (.A m q)
    · exact seitzInnerLinearThreeAb ⟨.A m q, hv⟩ 3 hp hp2 hpd hex E hEa hc
        ⟨hinner, rfl, ⟨m, q, rfl⟩, hlift⟩
    · exact seitzInnerLinearThree ⟨.A m q, hv⟩ 3 hp hp2 hpd hex E hEa hc
        ⟨hinner, rfl, ⟨m, q, rfl⟩, hlift⟩
  · by_cases hlift : CentralPrimeFree p (.A m q)
    · exact ⟨E, hEa, hc, hinner, seitzInnerLinear ⟨.A m q, hv⟩ p hp hp2 hpd hex E hEa hc
        ⟨hinner, hp5, ⟨m, q, rfl⟩, hlift⟩⟩
    · have hl : p ∣ q.card - 1 ∧ p ∣ m + 1 := by simpa [CentralPrimeFree] using hlift
      have hm : 4 ≤ m := by
        have := Nat.le_of_dvd (by omega) hl.2
        omega
      exact innerEx_linear_diag hv hp hl.1 hm ⟨E, hEa, hc, hinner⟩

theorem innerEx_unitary (hU3 : SeitzInnerUnitaryThreeNonab) :
    InnerExFor fun d => IsUnitaryIndex' d.1 := by
  rintro ⟨d, hv⟩ ⟨m, q, rfl⟩ p hp hp2 hpd hex ⟨E, hEa, hc, hinner⟩
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hm2 : 2 ≤ m := hrange.1
  rcases prime_eq_three_or_five_le hp hp2 with rfl | hp5
  · by_cases hq2 : q.card = 2
    · rcases eq_or_ne m 3 with rfl | hm3
      · exact absurd (isD2SeitzException_unitary_four hq2) hex
      · exact innerEx_unitaryTwo ⟨.twistedA m q, hv⟩ ⟨m, q, rfl, hq2, by omega⟩ 3 rfl hpd hex
          ⟨E, hEa, hc, hinner⟩
    · by_cases hlift : CentralPrimeFree 3 (.twistedA m q)
      · exact ⟨E, hEa, hc, hinner, seitzInnerUnitaryThree ⟨.twistedA m q, hv⟩ 3 hp hp2 hpd hex E
          hEa hc ⟨hinner, rfl, ⟨m, q, rfl⟩, hlift, fun m' q' h => by
            cases h
            exact hq2⟩⟩
      · have hl : 3 ∣ q.card + 1 ∧ 3 ∣ m + 1 := by simpa [CentralPrimeFree] using hlift
        rcases eq_or_ne m 2 with rfl | hm
        · exact ⟨E, hEa, hc, hinner, hU3 ⟨.twistedA 2 q, hv⟩ 3 hp hp2 hpd hex E hEa hc
            ⟨hinner, rfl, q, rfl, hl.1⟩⟩
        · have hm4 : 4 ≤ m := by
            obtain ⟨k, hk⟩ := hl.2
            omega
          exact innerEx_unitary_diag hv hp hl.1 hq2 hm4 ⟨E, hEa, hc, hinner⟩
  · by_cases hlift : CentralPrimeFree p (.twistedA m q)
    · exact ⟨E, hEa, hc, hinner, seitzInnerUnitary_of_nontoral unitarySUNontoral
        ⟨.twistedA m q, hv⟩ p hp hp2 hpd hex E hEa hc ⟨hinner, hp5, ⟨m, q, rfl⟩, hlift⟩⟩
    · have hl : p ∣ q.card + 1 ∧ p ∣ m + 1 := by simpa [CentralPrimeFree] using hlift
      have hm : 4 ≤ m := by
        have := Nat.le_of_dvd (by omega) hl.2
        omega
      have hq2 : q.card ≠ 2 := by
        have := Nat.le_of_dvd (by omega) hl.1
        omega
      exact innerEx_unitary_diag hv hp hl.1 hq2 hm ⟨E, hEa, hc, hinner⟩

theorem innerEx_symplectic : InnerExFor fun d => IsSymplecticIndex d.1 := by
  rintro ⟨d, hv⟩ hsp p hp hp2 hpd hex ⟨E, hEa, hc, hinner⟩
  by_cases hB2 : ∃ q : TauCeti.PrimePower, d = .B 2 q
  · obtain ⟨q, rfl⟩ := hB2
    exact ⟨E, hEa, hc, hinner, seitzInnerSymplecticTwo ⟨.B 2 q, hv⟩ p hp hp2 hpd hex E hEa hc
      ⟨hinner, q, rfl⟩⟩
  · have hhigh : IsSymplecticHigh d := by
      rcases hsp with h | h
      · exact absurd h hB2
      · exact h
    rcases prime_eq_three_or_five_le hp hp2 with rfl | hp5
    · exact innerEx_symplecticHigh_three ⟨d, hv⟩ hhigh 3 rfl hpd hex ⟨E, hEa, hc, hinner⟩
    · exact ⟨E, hEa, hc, hinner, seitzInnerSymplectic ⟨d, hv⟩ p hp hp2 hpd hex E hEa hc
        ⟨hinner, hp5, hsp⟩⟩

theorem innerExFor_classical (hU3 : SeitzInnerUnitaryThreeNonab) (hO : OrthSelfDualTwoBlocks) :
    InnerExFor fun d => IsClassicalIndex d.1 := by
  intro d hcl p hp hp2 hpd hex hE
  have hrange : d.1.InStandardRange := ((TauCeti.LieTypeIndex.valid_iff _).1 d.2).1
  rcases (isClassicalIndex_iff hrange).1 hcl with h | h | h | h
  · exact innerEx_linear d h p hp hp2 hpd hex hE
  · exact innerEx_unitary hU3 d h p hp hp2 hpd hex hE
  · exact innerEx_symplectic d h p hp hp2 hpd hex hE
  · exact seitzInnerEx_orth hO d h p hp hp2 hpd hex hE

end InnerEx

section InnerLow

theorem seitzInnerLow_linear :
    SeitzPlanes fun d p E => InnerPlane d p E ∧ RankLE2 p (Cat d) ∧ IsLinearIndex d.1 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hEa hc ⟨hinner, hrk, ⟨m, q, rfl⟩⟩
  rcases prime_eq_three_or_five_le hp hp2 with rfl | hp5
  · by_cases hlift : CentralPrimeFree 3 (.A m q)
    · exact seitzInnerLinearThreeAb ⟨.A m q, hv⟩ 3 hp hp2 hpd hex E hEa hc
        ⟨hinner, rfl, ⟨m, q, rfl⟩, hlift⟩
    · exact seitzInnerLinearThree ⟨.A m q, hv⟩ 3 hp hp2 hpd hex E hEa hc
        ⟨hinner, rfl, ⟨m, q, rfl⟩, hlift⟩
  · by_cases hlift : CentralPrimeFree p (.A m q)
    · exact seitzInnerLinear ⟨.A m q, hv⟩ p hp hp2 hpd hex E hEa hc
        ⟨hinner, hp5, ⟨m, q, rfl⟩, hlift⟩
    · have hl : p ∣ q.card - 1 ∧ p ∣ m + 1 := by simpa [CentralPrimeFree] using hlift
      have hm : 4 ≤ m := by
        have := Nat.le_of_dvd (by omega) hl.2
        omega
      exact absurd hrk (not_rankLE2_linear hv hp hl.1 hm)

theorem seitzInnerLow_unitary (hU3 : SeitzInnerUnitaryThreeNonab) :
    SeitzPlanes fun d p E => InnerPlane d p E ∧ RankLE2 p (Cat d) ∧ IsUnitaryIndex' d.1 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hEa hc ⟨hinner, hrk, ⟨m, q, rfl⟩⟩
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hm2 : 2 ≤ m := hrange.1
  rcases prime_eq_three_or_five_le hp hp2 with rfl | hp5
  · by_cases hq2 : q.card = 2
    · rcases eq_or_ne m 3 with rfl | hm3
      · exact absurd (isD2SeitzException_unitary_four hq2) hex
      · exact absurd hrk (not_rankLE2_unitary hv hp (by omega) (by omega))
    · by_cases hlift : CentralPrimeFree 3 (.twistedA m q)
      · exact seitzInnerUnitaryThree ⟨.twistedA m q, hv⟩ 3 hp hp2 hpd hex E hEa hc
          ⟨hinner, rfl, ⟨m, q, rfl⟩, hlift, fun m' q' h => by
            cases h
            exact hq2⟩
      · have hl : 3 ∣ q.card + 1 ∧ 3 ∣ m + 1 := by simpa [CentralPrimeFree] using hlift
        rcases eq_or_ne m 2 with rfl | hm
        · exact hU3 ⟨.twistedA 2 q, hv⟩ 3 hp hp2 hpd hex E hEa hc ⟨hinner, rfl, q, rfl, hl.1⟩
        · have hm4 : 4 ≤ m := by
            obtain ⟨k, hk⟩ := hl.2
            omega
          exact absurd hrk (not_rankLE2_unitary hv hp hl.1 hm4)
  · by_cases hlift : CentralPrimeFree p (.twistedA m q)
    · exact seitzInnerUnitary_of_nontoral unitarySUNontoral ⟨.twistedA m q, hv⟩ p hp hp2 hpd hex
        E hEa hc ⟨hinner, hp5, ⟨m, q, rfl⟩, hlift⟩
    · have hl : p ∣ q.card + 1 ∧ p ∣ m + 1 := by simpa [CentralPrimeFree] using hlift
      have hm : 4 ≤ m := by
        have := Nat.le_of_dvd (by omega) hl.2
        omega
      exact absurd hrk (not_rankLE2_unitary hv hp hl.1 hm)

theorem seitzInnerLow_symplectic :
    SeitzPlanes fun d p E => InnerPlane d p E ∧ RankLE2 p (Cat d) ∧ IsSymplecticIndex d.1 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hEa hc ⟨hinner, hrk, hsp⟩
  by_cases hB2 : ∃ q : TauCeti.PrimePower, d = .B 2 q
  · obtain ⟨q, rfl⟩ := hB2
    exact seitzInnerSymplecticTwo ⟨.B 2 q, hv⟩ p hp hp2 hpd hex E hEa hc ⟨hinner, q, rfl⟩
  · have hhigh : IsSymplecticHigh d := by
      rcases hsp with h | h
      · exact absurd h hB2
      · exact h
    rcases prime_eq_three_or_five_le hp hp2 with rfl | hp5
    · exact absurd hrk (not_rankLE2_symplecticHigh_three ⟨d, hv⟩ hhigh 3 rfl hpd)
    · exact seitzInnerSymplectic ⟨d, hv⟩ p hp hp2 hpd hex E hEa hc ⟨hinner, hp5, hsp⟩

theorem seitzInnerLowClassical (hU3 : SeitzInnerUnitaryThreeNonab) (hO : OrthSelfDualTwoBlocks) :
    SeitzInnerLowClassical := by
  intro d p hp hp2 hpd hex E hEa hc ⟨hinner, hrk, hcl⟩
  have hrange : d.1.InStandardRange := ((TauCeti.LieTypeIndex.valid_iff _).1 d.2).1
  rcases (isClassicalIndex_iff hrange).1 hcl with h | h | h | h
  · exact seitzInnerLow_linear d p hp hp2 hpd hex E hEa hc ⟨hinner, hrk, h⟩
  · exact seitzInnerLow_unitary hU3 d p hp hp2 hpd hex E hEa hc ⟨hinner, hrk, h⟩
  · exact seitzInnerLow_symplectic d p hp hp2 hpd hex E hEa hc ⟨hinner, hrk, h⟩
  · exact seitzInnerLow_orth hO d p hp hp2 hpd hex E hEa hc ⟨hinner, hrk, h⟩

end InnerLow

end CFSG.LieType.SeitzGeneration
