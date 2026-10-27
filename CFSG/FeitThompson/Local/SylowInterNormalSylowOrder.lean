module

public import Mathlib.GroupTheory.Sylow
import CFSG.FeitThompson.Foundations.SylowContainmentConjugacy
import CFSG.FeitThompson.Foundations.NormalHallIntersectionHall

open Pointwise

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {G : Type*} [Group G] {p : ℕ}

theorem natCard_map_subtype_sylow [Finite G] [Fact p.Prime] (N : Subgroup G) (R : Sylow p N) :
    Nat.card ((R : Subgroup N).map N.subtype) = p ^ (Nat.card N).factorization p := by
  rw [Subgroup.card_map_of_injective N.subtype_injective, R.card_eq_multiplicity]

variable [Fact p.Prime]

theorem pow_factorization_dvd_natCard_inf_sylow [Finite G] (N : Subgroup G) [N.Normal]
    (S : Sylow p G) :
    p ^ (Nat.card N).factorization p ∣ Nat.card (N ⊓ (S : Subgroup G) : Subgroup G) := by
  obtain ⟨R⟩ := (inferInstance : Nonempty (Sylow p N))
  set R' : Subgroup G := (R : Subgroup N).map N.subtype with hR'def
  have hR'card : Nat.card R' = p ^ (Nat.card N).factorization p :=
    natCard_map_subtype_sylow N R
  have hR'N : R' ≤ N := Subgroup.map_subtype_le _
  have hR'p : IsPGroup p R' := IsPGroup.of_card hR'card
  obtain ⟨g, hg⟩ := exists_forall_inv_mul_mul_mem S.card_eq_multiplicity hR'p
  have hle : (MulAut.conj g⁻¹ • R' : Subgroup G) ≤ N ⊓ (S : Subgroup G) := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mp hx
    have hxy : x = g⁻¹ * y * g := by rw [← hyx]; simp [MulAut.conj]
    exact ⟨hxy ▸ Subgroup.Normal.conj_mem' inferInstance y (hR'N hy) g, hxy ▸ hg y hy⟩
  calc p ^ (Nat.card N).factorization p = Nat.card (MulAut.conj g⁻¹ • R' : Subgroup G) := by
        rw [natCard_conj_smul, hR'card]
    _ ∣ _ := Subgroup.card_dvd_of_le hle

theorem natCard_inf_sylow [Finite G] (N : Subgroup G) [N.Normal] (S : Sylow p G) :
    Nat.card (N ⊓ (S : Subgroup G) : Subgroup G) = p ^ (Nat.card N).factorization p := by
  have hp : IsPGroup p (N ⊓ (S : Subgroup G) : Subgroup G) := IsPGroup.to_inf_right S.isPGroup'
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have hdvd : p ^ (Nat.card N).factorization p ∣ p ^ n :=
    hn ▸ pow_factorization_dvd_natCard_inf_sylow N S
  have hdvdN : p ^ n ∣ Nat.card N := hn ▸ Subgroup.card_dvd_of_le inf_le_left
  have hle : n ≤ (Nat.card N).factorization p :=
    (Nat.Prime.pow_dvd_iff_le_factorization Fact.out Nat.card_pos.ne').mp hdvdN
  have hge : (Nat.card N).factorization p ≤ n :=
    (Nat.pow_dvd_pow_iff_le_right (Fact.out : p.Prime).one_lt).mp hdvd
  rw [hn, le_antisymm hle hge]

theorem natCard_inf_sylow_subgroupOf [Finite G] (N : Subgroup G) [N.Normal] (S : Sylow p G) :
    Nat.card ((N ⊓ (S : Subgroup G)).subgroupOf N) = p ^ (Nat.card N).factorization p := by
  rw [inf_comm N (S : Subgroup G), natCard_inf_subgroupOf, inf_comm, natCard_inf_sylow]

def sylowInfNormal [Finite G] (N : Subgroup G) [N.Normal] (S : Sylow p G) : Sylow p N :=
  Sylow.ofCard ((N ⊓ (S : Subgroup G)).subgroupOf N) (natCard_inf_sylow_subgroupOf N S)

@[simp]
theorem coe_sylowInfNormal [Finite G] (N : Subgroup G) [N.Normal] (S : Sylow p G) :
    (sylowInfNormal N S : Subgroup N) = (N ⊓ (S : Subgroup G)).subgroupOf N := (rfl)

@[simp]
theorem mem_sylowInfNormal [Finite G] (N : Subgroup G) [N.Normal] (S : Sylow p G) (x : N) :
    x ∈ sylowInfNormal N S ↔ (x : G) ∈ (S : Subgroup G) := by
  change x ∈ (sylowInfNormal N S : Subgroup N) ↔ _
  rw [coe_sylowInfNormal, Subgroup.mem_subgroupOf]
  simp [x.2]

theorem map_subtype_sylowInfNormal [Finite G] (N : Subgroup G) [N.Normal] (S : Sylow p G) :
    (sylowInfNormal N S : Subgroup N).map N.subtype = N ⊓ (S : Subgroup G) := by
  rw [coe_sylowInfNormal, Subgroup.map_subgroupOf_eq_of_le inf_le_left]

theorem exists_sylow_coe_eq_inf_sylow [Finite G] (N : Subgroup G) [N.Normal] (S : Sylow p G) :
    ∃ P : Sylow p N, (P : Subgroup N) = (N ⊓ (S : Subgroup G)).subgroupOf N :=
  ⟨sylowInfNormal N S, coe_sylowInfNormal N S⟩

end

end CFSG.FeitThompson
