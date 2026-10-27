module

public import CFSG.GroupTheory.Fitting.SimpleNormal
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG

theorem pPrimeCore_eq_bot_of_isSimpleGroup_generalizedFitting {X : Type*} [Group X] [Finite X]
    {p : ℕ} [Fact p.Prime] (hF : IsSimpleGroup ↥(generalizedFitting X))
    (hp : p ∣ Nat.card ↥(generalizedFitting X)) : pPrimeCore p X = ⊥ := by
  by_contra hne
  have : (generalizedFitting X).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := X)).2
  have hle : generalizedFitting X ≤ pPrimeCore p X :=
    CFSG.GroupTheory.generalizedFitting_le_of_normal hF pPrimeCore_normal hne
  have hpdvd : p ∣ Nat.card ↥(pPrimeCore p X) :=
    hp.trans (Subgroup.card_dvd_of_le hle)
  exact (Fact.out : p.Prime).coprime_iff_not_dvd.mp pPrimeCore_coprime_card hpdvd

theorem subsingleton_of_pPrimeCore_two_eq_bot_of_odd_card_generalizedFitting {X : Type*}
    [Group X] [Finite X] (hO : pPrimeCore 2 X = ⊥)
    (hodd : Odd (Nat.card (generalizedFitting X))) : Subsingleton X := by
  by_contra hsub
  have hnormal : (generalizedFitting X).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := X)).2
  have hbot : generalizedFitting X = ⊥ :=
    (pPrimeCore_eq_bot_iff (p := 2) (G := X)).1 hO (generalizedFitting X) hnormal
      (Nat.coprime_two_left.mpr hodd)
  have hle := CFSG.centralizer_generalizedFitting_le X
  rw [hbot] at hle
  have htop : Subgroup.centralizer ((⊥ : Subgroup X) : Set X) = ⊤ := by
    ext g
    simp [Subgroup.mem_centralizer_iff]
  rw [htop] at hle
  exact hsub (Subgroup.subsingleton_iff.mp (subsingleton_of_top_le_bot hle))

theorem even_card_generalizedFitting_of_pPrimeCore_two_eq_bot {X : Type*} [Group X] [Finite X]
    (hO : pPrimeCore 2 X = ⊥) (hnt : Nontrivial X) :
    Even (Nat.card (generalizedFitting X)) := by
  by_contra h
  exact (not_subsingleton_iff_nontrivial.mpr hnt)
    (subsingleton_of_pPrimeCore_two_eq_bot_of_odd_card_generalizedFitting hO
      (Nat.not_even_iff_odd.mp h))

end CFSG
