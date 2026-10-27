module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModel
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Defs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87MultMilestone
public import CFSG.ClassicalInvolution.Balance.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.Blueprint.Multiplier

theorem ff_card_center_dvd_two_psl (hGA : CFSG.Open.GriessAllModelsStatement) {L : Type}
    [Group L] [Finite L] (hq : CFSG.IsQuasisimple L)
    (hm : LieModel (L ⧸ center L) .PSL 4 3 1) : Nat.card (center L) ∣ 2 := by
  have hM : CFSG.Models.LieModel (L ⧸ center L) .PSL 4 3 1 :=
    CFSG.GH74.Generic.models_of_blueprint_of_ne_zero (by norm_num) hm
  have hgen : genericOrders .PSL 4 3 1 = (2, 1) := by
    have h : genericOrders .PSL 4 3 1 = (Nat.gcd 4 (3 ^ 1 - 1), 1) := by
      unfold genericOrders; rfl
    rw [h]
    norm_num
  have hex : exceptionalOrders .PSL 4 3 1 = (1, 1) := by decide
  have h := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_center_dvd_table hGA hq hM
    (by rw [hex, hgen]; norm_num)
  rw [hex, hgen] at h
  simpa using h

theorem ff_card_center_dvd_two_psp (hGA : CFSG.Open.GriessAllModelsStatement) {L : Type}
    [Group L] [Finite L] (hq : CFSG.IsQuasisimple L)
    (hm : LieModel (L ⧸ center L) .PSp 2 3 1) : Nat.card (center L) ∣ 2 := by
  have hM : CFSG.Models.LieModel (L ⧸ center L) .PSp 2 3 1 :=
    CFSG.GH74.Generic.models_of_blueprint_of_ne_zero (by norm_num) hm
  have hgen : genericOrders .PSp 2 3 1 = (2, 1) := by
    have h : genericOrders .PSp 2 3 1 = (Nat.gcd 2 (3 ^ 1 - 1), 1) := by
      unfold genericOrders; rfl
    rw [h]
    norm_num
  have hex : exceptionalOrders .PSp 2 3 1 = (1, 1) := by decide
  have h := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_center_dvd_table hGA hq hM
    (by rw [hex, hgen]; norm_num)
  rw [hex, hgen] at h
  simpa using h

theorem ff_odd_card_oddCore (X : Type) [Group X] [Finite X] : Odd (Nat.card (CFSG.oddCore X)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.oddCore_eq_piCore, ← CFSG.pPrimeCore_eq_piCore 2 (G := X)]
  exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

theorem ff_center_eq_oddCore_of_simple {L : Type} [Group L] [Finite L]
    (hq : CFSG.IsQuasisimple L) (hs : IsSimpleGroup (L ⧸ oddCore L)) :
    center L = oddCore L := by
  haveI : Group.IsPerfect L := hq.1
  have h' : CFSG.Open.IsQuasisimple L := ⟨hq.1.commutator_eq_top, hq.2.1⟩
  have hle : oddCore L ≤ center L :=
    CFSG.ClassicalInvolution.Balance.oddCore_le_center_of_isQuasisimple h'
  refine le_antisymm (fun x hx => ?_) hle
  have hQ : center (L ⧸ oddCore L) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (L ⧸ oddCore L)) with h | h
    · exact h
    · exfalso
      haveI : IsMulCommutative (L ⧸ oddCore L) := center_eq_top_iff.mp h
      exact Group.IsPerfect.not_isMulCommutative (L ⧸ oddCore L) inferInstance
  have hxQ : (QuotientGroup.mk x : L ⧸ oddCore L) ∈ center (L ⧸ oddCore L) := by
    refine mem_center_iff.mpr fun q => ?_
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mem_center_iff.mp hx y]
  rw [hQ, mem_bot] at hxQ
  exact (QuotientGroup.eq_one_iff x).mp hxQ

theorem ff_oddCore_eq_bot_of_card_center_dvd_two {L : Type} [Group L] [Finite L]
    (hq : CFSG.IsQuasisimple L) (hs : IsSimpleGroup (L ⧸ oddCore L))
    (hd : Nat.card (center L) ∣ 2) : oddCore L = ⊥ := by
  have hc := ff_center_eq_oddCore_of_simple hq hs
  have hodd : Odd (Nat.card (center L)) := by
    rw [hc]
    exact ff_odd_card_oddCore L
  have h1 : Nat.card (center L) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  rw [← hc]
  exact Subgroup.card_eq_one.mp h1

theorem ff_schurOmega5 (hGA : CFSG.Open.GriessAllModelsStatement) : Asc82SchurOmega5 := by
  intro L _ _ hq hm
  have hs : IsSimpleGroup (L ⧸ oddCore L) :=
    (CFSG.LieType.Simplicity.fam_classical_converse (L ⧸ oddCore L)
      ⟨.PSp, 2, 3, 1, hm.statedClassicalModel_of_ne_zero (by norm_num : (2 : ℕ) ≠ 0)⟩).2.2
  have hc := ff_center_eq_oddCore_of_simple hq hs
  have hlie : LieModel (L ⧸ center L) .PSp 2 3 1 :=
    LieModel.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hc).symm hm
  exact ff_oddCore_eq_bot_of_card_center_dvd_two hq hs (ff_card_center_dvd_two_psp hGA hq hlie)

variable {G : Type} [Group G]

theorem ff_oddCore_eq_bot_six_plus (hGA : CFSG.Open.GriessAllModelsStatement) [Finite G]
    {L : Subgroup G} (h : IsOm6P L) : oddCore ↥L = ⊥ := by
  have hs := ff_isSimpleGroup_oddCore_six_plus h
  exact ff_oddCore_eq_bot_of_card_center_dvd_two h.1 hs
    (ff_card_center_dvd_two_psl hGA h.1 (ff_lieModel_center_six_plus h))

theorem ff_center_eq_bot_six_plus (hGA : CFSG.Open.GriessAllModelsStatement) [Finite G]
    {L : Subgroup G} (h : IsOm6P L) : center ↥L = ⊥ := by
  rw [ff_center_eq_oddCore_six_plus h]
  exact ff_oddCore_eq_bot_six_plus hGA h

theorem ff_centerIn_eq_bot_six_plus (hGA : CFSG.Open.GriessAllModelsStatement) [Finite G]
    {L : Subgroup G} (h : IsOm6P L) : centerIn L = ⊥ := by
  have hc := ff_center_eq_bot_six_plus hGA h
  rw [eq_bot_iff]
  rintro x ⟨c, hc', rfl⟩
  have hc'' : c ∈ (⊥ : Subgroup ↥L) := hc ▸ hc'
  rw [mem_bot] at hc''
  simp [hc'']

end CFSG.OddStandard.SmallF3.Omega
