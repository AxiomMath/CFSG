module

public import CFSG.LieType.SeitzGeneration.ExcPlaneModel
public import CFSG.LieType.SeitzGeneration.ExcParabolicPlane
public import CFSG.LieType.SeitzGeneration.ExcParabolicIndex
public import CFSG.LieType.SeitzGeneration.ExcParabolicMod
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LieType.SeitzGeneration.ExcPrimeSplit

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.TauCetiBridge TauCeti
  CFSG.Timmesfeld.ExceptionalOrders

section Proved


theorem normalizesRSubgroup_E6_phi4 (q : PrimePower) (hv : (LieTypeIndex.E6 q).Valid) {p : ℕ}
    (hp : p.Prime) (hpq : p ∣ q.card ^ 2 + 1) {E : Subgroup (MulAut (Cat ⟨.E6 q, hv⟩))}
    (hEp : IsPGroup p E) (hin : InnerPlane ⟨.E6 q, hv⟩ p E) :
    NormalizesRSubgroup ⟨.E6 q, hv⟩ E := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e6 q hv
  have : Fintype (WeylGroup .E6) := Fintype.ofFinite _
  have hr : ∃ n, Nat.card K = q.p ^ n := ⟨q.exponent, by rw [hK, PrimePower.card_def]⟩
  have hidx : ¬ p ∣ (parabolicSubgroup .E6 K (maskSet .E6 31)).relIndex (adjointGroup .E6 K) := by
    rw [relIndex_parabolicSubgroup_E6, hK]
    exact not_dvd_index_E6 hp hpq
  obtain ⟨R, hR0, hRr, hR⟩ :=
    exists_normalized_of_not_dvd_relIndex e hr maskSet_E6_ne_univ hidx hEp hin
  exact ⟨R, hR0, by simpa using hRr, hR⟩

theorem normalizesRSubgroup_E7_phi4 (q : PrimePower) (hv : (LieTypeIndex.E7 q).Valid) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ q.card ^ 2 + 1)
    {E : Subgroup (MulAut (Cat ⟨.E7 q, hv⟩))}
    (hEp : IsPGroup p E) (hin : InnerPlane ⟨.E7 q, hv⟩ p E) :
    NormalizesRSubgroup ⟨.E7 q, hv⟩ E := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e7 q hv
  have : Fintype (WeylGroup .E7) := Fintype.ofFinite _
  have hr : ∃ n, Nat.card K = q.p ^ n := ⟨q.exponent, by rw [hK, PrimePower.card_def]⟩
  have hidx : ¬ p ∣ (parabolicSubgroup .E7 K (maskSet .E7 63)).relIndex (adjointGroup .E7 K) := by
    rw [relIndex_parabolicSubgroup_E7, hK]
    exact not_dvd_index_E7 hp hp2 hpq
  obtain ⟨R, hR0, hRr, hR⟩ :=
    exists_normalized_of_not_dvd_relIndex e hr maskSet_E7_ne_univ hidx hEp hin
  exact ⟨R, hR0, by simpa using hRr, hR⟩

theorem seitzExcAnisotropicForAt_E6_phi4 :
    SeitzExcAnisotropicForAt IsE6Index fun d p =>
      ∃ q : PrimePower, d = .E6 q ∧ p ∣ q.card ^ 2 + 1 := by
  rintro d p hp hp2 - - E - hc ⟨hin, -, ⟨q, hdq, hpq⟩, -, hn⟩
  obtain ⟨d, hv⟩ := d
  obtain rfl : d = LieTypeIndex.E6 q := hdq
  exact absurd (normalizesRSubgroup_E6_phi4 q hv hp hpq (IsPGroup.of_card hc) hin) hn

theorem seitzExcAnisotropicForAt_E7_phi4 :
    SeitzExcAnisotropicForAt IsE7Index fun d p =>
      ∃ q : PrimePower, d = .E7 q ∧ p ∣ q.card ^ 2 + 1 := by
  rintro d p hp hp2 - - E - hc ⟨hin, -, ⟨q, hdq, hpq⟩, -, hn⟩
  obtain ⟨d, hv⟩ := d
  obtain rfl : d = LieTypeIndex.E7 q := hdq
  exact absurd (normalizesRSubgroup_E7_phi4 q hv hp hp2 hpq (IsPGroup.of_card hc) hin) hn

end Proved

end CFSG.LieType.SeitzGeneration
