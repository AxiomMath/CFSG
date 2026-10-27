module

public import CFSG.LieType.SeitzGeneration.ExcPlaneModel
public import CFSG.RankThree.PartOne.Q1327C.BNoCube
public import CFSG.LieType.SeitzGeneration.ExcParabolicReeG2
public import CFSG.LieType.SeitzGeneration.ExcPlaneBridge
public import CFSG.LieType.SeitzGeneration.ExcPlaneFamilies

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.TauCetiBridge TauCeti
  CFSG.LieType.Ree

section Ree


theorem rankLE2_adjointGroup_G2 (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpq : ¬ p ∣ Nat.card K) : RankLE2 p ↥(adjointGroup .G2 K) :=
  rankLE2_of_noPowThree hp fun _ hE hc =>
    CFSG.RankThree.PartOne.Q1327C.false_of_pow_three_G2_five K hp hp5 hpq hE hc

theorem excPlaneReeG2 : ExcPlaneReeG2 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex ⟨m, rfl⟩ hr
  exfalso
  apply hr
  obtain ⟨X, _, _, _, hX, ⟨e⟩⟩ := exists_reeGamma_equiv_cat_G2 hv
  have hp3 : p ≠ 3 := by simpa using hpd
  have hp5 : 5 ≤ p := (eq_three_or_five_le hp hp2).resolve_left hp3
  have hpq : ¬ p ∣ Nat.card X := by
    rw [hX]
    exact fun h => hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h))
  let f : ReeTag.G2.reeGamma X m →* adjointGroup ReeTag.G2.tag X :=
    { toFun := fun g => ⟨g, (ReeTag.mem_reeGamma.1 g.2).1⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := fun g₁ g₂ h => by
    have h' := congrArg Subtype.val h
    exact Subtype.ext h'
  exact RankLE2.of_injective (f.comp e.toMonoidHom) (hf.comp e.injective)
    (rankLE2_adjointGroup_G2 X hp hp5 hpq)

end Ree

section Untwisted


theorem excPlaneG2Five : ExcPlaneG2Five := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex ⟨⟨q, rfl⟩, hp5⟩ hr
  exfalso
  apply hr
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.g2 q hv
  have hpq : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne hp (by simpa using hpd)
  exact RankLE2.of_injective e.toMonoidHom e.injective (rankLE2_adjointGroup_G2 K hp hp5 hpq)

end Untwisted

end CFSG.LieType.SeitzGeneration
