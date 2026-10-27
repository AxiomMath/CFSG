module

public import CFSG.LieType.SeitzGeneration.Regimes
public import CFSG.LieType.SeitzGeneration.UnitaryHeisCoreMain
public import CFSG.LieType.SeitzGeneration.InnerSymplecticThree
public import CFSG.LieType.SeitzGeneration.InnerLinearThreeAb
public import CFSG.LieType.SeitzGeneration.InnerUnitaryThree
public import CFSG.LieType.SeitzGeneration.NonabHeisThree
public import CFSG.LieType.SeitzGeneration.UnitaryToralNine

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.AGLEmbeddingD2

@[expose] def SeitzInnerThreeUnitaryTwo : Prop :=
  SeitzPlanes fun d p E => InnerPlane d p E ∧ p = 3 ∧
    ∃ (m : ℕ) (q : TauCeti.PrimePower), d.1 = .twistedA m q ∧ q.card = 2

@[expose] def SeitzInnerThreeUnitaryNonabHigh : Prop :=
  SeitzPlanes fun d p E => InnerPlane d p E ∧ p = 3 ∧
    ∃ (m : ℕ) (q : TauCeti.PrimePower), d.1 = .twistedA m q ∧ q.card ≠ 2 ∧ 3 ∣ q.card + 1 ∧
      3 ∣ m + 1 ∧ 3 ≤ m

@[expose] def SeitzInnerThreeSymplecticHigh : Prop :=
  SeitzPlanes fun d p E => InnerPlane d p E ∧ p = 3 ∧ IsSymplecticHigh d.1

@[expose] def SeitzInnerThreeOrthogonal : Prop :=
  SeitzPlanes fun d p E => InnerPlane d p E ∧ p = 3 ∧ IsOrthogonalIndex d.1

section Assembly


theorem seitzInnerThreeClassical_of_leaves (hU2 : SeitzInnerThreeUnitaryTwo)
    (hU3 : SeitzInnerThreeUnitaryNonabHigh) (hSp : SeitzInnerThreeSymplecticHigh)
    (hO : SeitzInnerThreeOrthogonal) : SeitzInnerThreeClassical := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hinner, hp3, hcl⟩
  have hrange : d.InStandardRange := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  subst hp3
  rcases (isClassicalIndex_iff hrange).1 hcl with ⟨m, q, hd⟩ | ⟨m, q, hd⟩ | hsp | hor
  ·
    subst hd
    by_cases hlift : CentralPrimeFree 3 (.A m q)
    · exact seitzInnerLinearThreeAb ⟨.A m q, hv⟩ 3 hp hp2 hpd hex E hE hc
        ⟨hinner, rfl, ⟨m, q, rfl⟩, hlift⟩
    · exact seitzInnerLinearThree ⟨.A m q, hv⟩ 3 hp hp2 hpd hex E hE hc
        ⟨hinner, rfl, ⟨m, q, rfl⟩, hlift⟩
  ·
    subst hd
    have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).1 hrange
    by_cases hq2 : q.card = 2
    · exact hU2 ⟨.twistedA m q, hv⟩ 3 hp hp2 hpd hex E hE hc ⟨hinner, rfl, m, q, rfl, hq2⟩
    · by_cases hlift : CentralPrimeFree 3 (.twistedA m q)
      · exact seitzInnerUnitaryThree ⟨.twistedA m q, hv⟩ 3 hp hp2 hpd hex E hE hc
          ⟨hinner, rfl, ⟨m, q, rfl⟩, hlift, fun m' q' h => by cases h; exact hq2⟩
      · have hl : 3 ∣ q.card + 1 ∧ 3 ∣ m + 1 := by simpa [CentralPrimeFree] using hlift
        rcases eq_or_ne m 2 with rfl | hm2
        · exact seitzInnerUnitaryNonab unitaryHeisCore unitaryToralNine ⟨.twistedA 2 q, hv⟩ 3 hp hp2
            hpd hex E hE hc ⟨hinner, rfl, q, rfl, hl.1⟩
        · have hm3 : 3 ≤ m := by have := hr.1; omega
          exact hU3 ⟨.twistedA m q, hv⟩ 3 hp hp2 hpd hex E hE hc
            ⟨hinner, rfl, m, q, rfl, hq2, hl.1, hl.2, hm3⟩
  ·
    by_cases hB2 : ∃ q : TauCeti.PrimePower, d = .B 2 q
    · obtain ⟨q, rfl⟩ := hB2
      exact seitzInnerSymplecticTwo ⟨.B 2 q, hv⟩ 3 hp hp2 hpd hex E hE hc ⟨hinner, q, rfl⟩
    · have hhigh : IsSymplecticHigh d := by
        rcases hsp with h | h
        · exact absurd h hB2
        · exact h
      exact hSp ⟨d, hv⟩ 3 hp hp2 hpd hex E hE hc ⟨hinner, rfl, hhigh⟩
  · exact hO ⟨d, hv⟩ 3 hp hp2 hpd hex E hE hc ⟨hinner, rfl, hor⟩

end Assembly

end CFSG.LieType.SeitzGeneration
