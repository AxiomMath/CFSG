module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Core
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.ConsBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CSetup

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup

variable {G : Type} [Group G] [Finite G] {L E : Subgroup G} {t z : G}

theorem cCore (hs : StdHyp G L) (c : Core0 E t z) (H0 : TwoFi22.O2In (Cz z) = zpowers z) :
    CCore (czInv z c.klein.z_sq c.klein.z_ne) := by
  have hz2 : orderOf z = 2 := orderOf_eq_prime c.klein.z_sq c.klein.z_ne
  refine ⟨?_, ?_, ?_⟩
  · intro M hM hodd
    have hcore : CFSG.Open.standardComponentOddCore ↥(Cz z) = ⊥ := hs.oddCore z hz2
    have hle : M ≤ CFSG.Open.standardComponentOddCore ↥(Cz z) := le_sSup ⟨hM, hodd⟩
    rw [hcore] at hle
    exact le_antisymm hle bot_le
  · intro Q hQ hQ2
    let Q0 : Subgroup G := Q.map (Cz z).subtype
    have hQ0le : Q0 ≤ Cz z := by
      intro x hx
      obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hx
      exact y.2
    have hQ0norm : (Q0.subgroupOf (Cz z)).Normal := by
      have hEq : Q0.subgroupOf (Cz z) = Q := by
        show Q0.comap (Cz z).subtype = Q
        dsimp only [Q0]
        exact Subgroup.comap_map_eq_self_of_injective (Cz z).subtype_injective Q
      rw [hEq]
      exact hQ
    have hQ02 : IsPGroup 2 Q0 := hQ2.map (Cz z).subtype
    have hle : Q0 ≤ TwoFi22.O2In (Cz z) := TwoB.le_O2In hQ0le hQ0norm hQ02
    rw [H0] at hle
    intro x hx
    rw [mem_zpowers_czInv]
    exact hle (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  · intro hdvd
    have hdvdG : 2 ^ 22 ∣ Nat.card G :=
      dvd_trans hdvd (Subgroup.card_subgroup_dvd_card (Cz z))
    let S : Sylow 2 G := default
    have hS : Nat.card ↥S = 2 ^ 21 := c.zdata.syl S
    have hSm : Nat.card ↥S = 2 ^ Nat.factorization (Nat.card G) 2 :=
      Sylow.card_eq_multiplicity S
    have hfac : Nat.factorization (Nat.card G) 2 = 21 :=
      Nat.pow_right_injective (a := 2) (by norm_num) (hSm.symm.trans hS)
    have hle : 22 ≤ Nat.factorization (Nat.card G) 2 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp hdvdG
    omega

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
