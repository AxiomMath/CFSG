module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Orders
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3PocketLemmas
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B517Q
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open scoped commutatorElement

section U33

variable {X : Type} [Group X]

theorem l515S_simple_of_u33 (h : LieModel X .PSU 3 3 1) : IsSimpleGroup X :=
  (CFSG.LieType.Simplicity.fam_classical_converse X
    ⟨.PSU, 3, 3, 1, h.statedClassicalModel_of_ne_zero (by norm_num)⟩).2.2

theorem l515S_card_u33 (h : LieModel X .PSU 3 3 1) : Nat.card X = 6048 := by
  rw [(CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := X)
    (show (3 : ℕ) ≠ 2 by norm_num) (h.statedClassicalModel_of_ne_zero (by norm_num))).2.1 rfl]
  decide +kernel

theorem l515S_noncomm_of_u33 (h : LieModel X .PSU 3 3 1) : ∃ a b : X, a * b ≠ b * a := by
  have hs := l515S_simple_of_u33 h
  have hfin : Finite X := Nat.finite_of_card_ne_zero (by rw [l515S_card_u33 h]; norm_num)
  by_contra hne
  push Not at hne
  letI : CommGroup X := { (inferInstance : Group X) with mul_comm := fun a b => hne a b }
  have hp : (Nat.card X).Prime := IsSimpleGroup.prime_card (α := X)
  rw [l515S_card_u33 h] at hp
  exact absurd hp (by norm_num)

theorem l515S_isQuasisimple_of_simple (hs : IsSimpleGroup X) (hnc : ∃ a b : X, a * b ≠ b * a) :
    IsQuasisimple X := by
  have hc : center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := hnc
      exact absurd ((mem_center_iff.mp (h ▸ mem_top b)) a) hab
  have e : X ⧸ center X ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  have hperf : Group.IsPerfect X := by
    rw [Group.isPerfect_def]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      have h1 : ⁅a, b⁆ = 1 := by
        rw [← Subgroup.mem_bot, ← h]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      exact hab (commutatorElement_eq_one_iff_mul_comm.mp h1)
    · exact h
  refine ⟨hperf, e.isSimpleGroup, ?_⟩
  obtain ⟨a, b, hab⟩ := hnc
  exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩

theorem l515S_isQuasisimple_of_u33 (h : LieModel X .PSU 3 3 1) : IsQuasisimple X :=
  l515S_isQuasisimple_of_simple (l515S_simple_of_u33 h) (l515S_noncomm_of_u33 h)

private theorem l515S_odd_card_oddCore (Y : Type) [Group Y] [Finite Y] :
    Odd (Nat.card (CFSG.oddCore Y)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.oddCore_eq_piCore, ← CFSG.pPrimeCore_eq_piCore 2 (G := Y)]
  exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := Y))

theorem l515S_oddCore_eq_bot_of_u33 (h : LieModel X .PSU 3 3 1) : CFSG.oddCore X = ⊥ := by
  have hs := l515S_simple_of_u33 h
  have hfin : Finite X := Nat.finite_of_card_ne_zero (by rw [l515S_card_u33 h]; norm_num)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.oddCore X) with h0 | h0
  · exact h0
  · exfalso
    have hodd := l515S_odd_card_oddCore X
    rw [h0, Subgroup.card_top, l515S_card_u33 h] at hodd
    exact absurd hodd (by decide)

theorem l515S_lieModel_quot_u33 (h : LieModel X .PSU 3 3 1) :
    LieModel (X ⧸ CFSG.oddCore X) .PSU 3 3 1 :=
  LieModel.of_mulEquiv ((QuotientGroup.quotientBot (G := X)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq (l515S_oddCore_eq_bot_of_u33 h).symm)) h

end U33

section Sub

variable {G : Type} [Group G] [Finite G] {E : Subgroup G}

theorem l515S_isL3Eps3_of_u33 (h : LieModel ↥E .PSU 3 3 1) : IsL3Eps3 E :=
  Or.inr (l515S_lieModel_quot_u33 h)

theorem l515S_ctrQ_of_u33 (h : LieModel ↥E .PSU 3 3 1) : ctrQ E = 6048 :=
  ctrQ_of_u33 (l515S_isQuasisimple_of_u33 h) (l515S_lieModel_quot_u33 h)

theorem l515S_inFStar_of_u33 {H : Subgroup G} (hE : IsComponentIn E H)
    (h : LieModel ↥E .PSU 3 3 1) : InFStar E :=
  inFStar_of_isL3Eps3 hE (l515S_isL3Eps3_of_u33 h)

end Sub

section Orders

variable {G : Type} [Group G]

theorem l515S_orderOf_eq_two {x : G} (hx2 : x * x = 1) (hx1 : x ≠ 1) : orderOf x = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1

theorem l515S_orderOf_eq_four {a z : G} (ha2 : a * a = z) (hz2 : z * z = 1) (hz1 : z ≠ 1) :
    orderOf a = 4 := by
  have h1 : ¬ a ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two, ha2]
    exact hz1
  have h2 : a ^ 2 ^ (1 + 1) = 1 := by
    rw [show (2 : ℕ) ^ (1 + 1) = 2 + 2 from rfl, pow_add, pow_two, ha2, hz2]
  have := orderOf_eq_prime_pow h1 h2
  simpa using this

end Orders

section Quad

variable {G : Type} [Group G] {K : Fin 4 → Subgroup G} {z : G}

theorem Sec5B517Quad.mul_invol (hq : Sec5B517Quad K z) {i j : Fin 4} (hij : i ≠ j) {a b : G}
    (ha : a ∈ K i) (hb : b ∈ K j) (ha2 : a * a = z) (hb2 : b * b = z) :
    (a * b) * (a * b) = 1 ∧ a * b ≠ 1 ∧ a * b ≠ z := by
  have hab : Commute a b := hq.comm i j hij a ha b hb
  have hsq : (a * b) * (a * b) = 1 := by
    rw [← pow_two (a * b), hab.mul_pow 2, pow_two a, pow_two b, ha2, hb2, hq.z_sq]
  have haKj : a ∉ K j := by
    intro haj
    have hcent : ∀ v ∈ K i, a * v = v * a := fun v hv => hq.comm j i hij.symm a haj v hv
    rcases hq.eq_of_central ha hcent with h | h
    · rw [h] at ha2
      exact hq.z_ne (by simpa using ha2.symm)
    · rw [h, hq.z_sq] at ha2
      exact hq.z_ne ha2.symm
  refine ⟨hsq, ?_, ?_⟩
  · intro h
    exact haKj (by
      rw [show a = b⁻¹ from eq_inv_of_mul_eq_one_left h]
      exact (K j).inv_mem hb)
  · intro h
    exact haKj (by
      rw [show a = z * b⁻¹ from by rw [← h, mul_assoc, mul_inv_cancel, mul_one]]
      exact (K j).mul_mem (hq.z_mem j) ((K j).inv_mem hb))

end Quad

end CFSG.OddStandard.SmallF3.Omega
