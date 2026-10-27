module

public import CFSG.LieType.SeitzGeneration.InnerUnitary
public import CFSG.LieType.SeitzGeneration.UnitarySplit

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.AGLEmbeddingD2

theorem seitzInnerUnitaryThree :
    SeitzPlanes fun d p E =>
      InnerPlane d p E ∧ p = 3 ∧ IsUnitaryIndex' d.1 ∧ CentralPrimeFree p d.1 ∧
        ∀ (m : ℕ) (q : TauCeti.PrimePower), d.1 = .twistedA m q → q.card ≠ 2 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hinner, hp3, ⟨m, q, hd⟩, hlift, hq2⟩
  subst hd
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hm2 : 2 ≤ m := hrange.1
  have hq2' : q.card ≠ 2 := hq2 m q rfl
  set ℓ := TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA m q, hv⟩ with hℓ
  set f := TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA m q, hv⟩ with hf
  have hU := CFSG.RankThree.PartTwo.Census.unitaryFieldData_galoisField ℓ f
    (TauCeti.ValidLieTypeIndex.fieldExponent_pos ⟨.twistedA m q, hv⟩)
  have hqcard : ℓ ^ f = q.card := by simp [hℓ, hf, TauCeti.ValidLieTypeIndex.characteristic,
    TauCeti.ValidLieTypeIndex.fieldExponent, TauCeti.PrimePower.card_def]
  have hqne : ℓ ^ f ≠ 2 := hqcard ▸ hq2'
  refine planeGen_inner_unitary hv hp hlift ?_ hE hc hinner
  intro E' hcomm hexp hcard
  by_cases hpq : p ∣ ℓ ^ f + 1
  · exact CFSG.RankThree.PartOne.CTP.closure_centralizers_unitarySU_of_dvd_add_one hU hp hpq hqne
      E' hcomm hexp hcard
  ·
    have hℓp : p ≠ ℓ := hpd
    have hpN : ¬ p ∣ ℓ ^ f := fun h =>
      hℓp ((Nat.prime_dvd_prime_iff_eq hp hU.prime).mp (hp.dvd_of_dvd_pow h))
    have hpq' : p ∣ ℓ ^ f - 1 := by
      subst hp3
      omega
    exact unitarySU_planeGen_split hU hp hp2 hpq' (by omega) E' hcomm hexp hcard

end CFSG.LieType.SeitzGeneration
