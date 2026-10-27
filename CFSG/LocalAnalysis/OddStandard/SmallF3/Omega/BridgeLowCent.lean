module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeLowCore
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeLowCenter
import CFSG.GH74.Orders.LieType

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem natCard_center_omegaGroup_five (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 5) : Nat.card (Subgroup.center (omegaGroup hQ)) = 1 := by
  have hquot : Nat.card (omegaGroup hQ ⧸ Subgroup.center (omegaGroup hQ)) = 25920 := by
    have h := CFSG.GH74.card_of_lieModel_PSp (G := omegaGroup hQ ⧸ Subgroup.center (omegaGroup hQ))
      (n := 2) (p := 3) (f := 1) (by norm_num) (by norm_num)
      (lieModel_quotient_center_omegaGroup_five hQ hdim)
    rw [show CFSG.Open.ordBC 2 (3 ^ 1) = 25920 by decide] at h
    exact h
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (omegaGroup hQ))
  rw [natCard_omegaGroup_five hQ hdim, hquot] at hcard
  have h1 : (1 : ℕ) = Nat.card (Subgroup.center (omegaGroup hQ)) :=
    Nat.eq_of_mul_eq_mul_left (show 0 < 25920 by norm_num)
      (by rw [mul_one]; exact hcard)
  exact h1.symm

theorem natCard_center_omegaGroup_six_plus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hs : quadSign Q = 1) :
    Nat.card (Subgroup.center (omegaGroup hQ)) = 1 := by
  have hquot : Nat.card (omegaGroup hQ ⧸ Subgroup.center (omegaGroup hQ)) = 6065280 := by
    have h := CFSG.GH74.card_of_lieModel_PSL (G := omegaGroup hQ ⧸ Subgroup.center (omegaGroup hQ))
      (n := 4) (p := 3) (f := 1) (by norm_num)
      (lieModel_quotient_center_omegaGroup_six_plus hQ hdim hs)
    rw [show CFSG.Open.ordA (4 - 1) (3 ^ 1) = 6065280 by decide] at h
    exact h
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (omegaGroup hQ))
  rw [natCard_omegaGroup_six_plus hQ hdim hs, hquot] at hcard
  have h1 : (1 : ℕ) = Nat.card (Subgroup.center (omegaGroup hQ)) :=
    Nat.eq_of_mul_eq_mul_left (show 0 < 6065280 by norm_num)
      (by rw [mul_one]; exact hcard)
  exact h1.symm

theorem natCard_center_omegaGroup_six_minus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hs : quadSign Q = -1) :
    Nat.card (Subgroup.center (omegaGroup hQ)) = 2 := by
  have hquot : Nat.card (omegaGroup hQ ⧸ Subgroup.center (omegaGroup hQ)) = 3265920 := by
    have h := CFSG.GH74.card_of_lieModel_PSU (G := omegaGroup hQ ⧸ Subgroup.center (omegaGroup hQ))
      (n := 4) (p := 3) (f := 1) (by norm_num) (by norm_num)
      (lieModel_quotient_center_omegaGroup_six_minus hQ hdim hs)
    rw [show CFSG.Open.ordTwistedA (4 - 1) (3 ^ 1) = 3265920 by decide] at h
    exact h
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (omegaGroup hQ))
  rw [natCard_omegaGroup_six_minus hQ hdim hs, hquot] at hcard
  have h1 : (2 : ℕ) = Nat.card (Subgroup.center (omegaGroup hQ)) :=
    Nat.eq_of_mul_eq_mul_left (show 0 < 3265920 by norm_num)
      (by rw [show 3265920 * 2 = 6531840 by norm_num]; exact hcard)
  exact h1.symm

end CFSG.OddStandard.SmallF3.Omega
