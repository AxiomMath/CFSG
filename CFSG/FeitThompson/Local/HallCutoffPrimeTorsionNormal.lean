module

public import Mathlib.GroupTheory.Sylow
import CFSG.FeitThompson.Foundations.PrimeCoreLargestNormalPSubgroup
import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {E : Type*} [Group E] {p : ℕ} {K : Subgroup E}

def powEqOneSubgroup (p : ℕ) (Q : Subgroup E) [IsMulCommutative Q] : Subgroup E where
  carrier := {x | x ∈ Q ∧ x ^ p = 1}
  one_mem' := ⟨one_mem Q, one_pow p⟩
  mul_mem' := by
    rintro a b ⟨haQ, hap⟩ ⟨hbQ, hbp⟩
    refine ⟨mul_mem haQ hbQ, ?_⟩
    have hcomm : Commute a b := setLike_mul_comm haQ hbQ
    rw [hcomm.mul_pow, hap, hbp, one_mul]
  inv_mem' := by
    rintro a ⟨haQ, hap⟩
    exact ⟨inv_mem haQ, by rw [inv_pow, hap, inv_one]⟩

section API

variable {Q : Subgroup E} [IsMulCommutative Q]

@[simp] theorem mem_powEqOneSubgroup {x : E} :
    x ∈ powEqOneSubgroup p Q ↔ x ∈ Q ∧ x ^ p = 1 := (Iff.rfl)

theorem powEqOneSubgroup_le : powEqOneSubgroup p Q ≤ Q := fun _ hx => hx.1

theorem pow_eq_one_of_mem_powEqOneSubgroup {x : E} (hx : x ∈ powEqOneSubgroup p Q) : x ^ p = 1 :=
  hx.2

theorem mem_powEqOneSubgroup_of_pow_eq_one {x : E} (hxQ : x ∈ Q) (hx : x ^ p = 1) :
    x ∈ powEqOneSubgroup p Q := ⟨hxQ, hx⟩

theorem isPGroup_powEqOneSubgroup : IsPGroup p (powEqOneSubgroup p Q) := fun g =>
  ⟨1, Subtype.ext (by simpa [pow_one] using g.2.2)⟩

instance powEqOneSubgroup_characteristic :
    ((powEqOneSubgroup p Q).subgroupOf Q).Characteristic := by
  refine Subgroup.characteristic_iff_map_le.2 fun φ y hy => ?_
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
  have hxp : ((x : Q) : E) ^ p = 1 := (Subgroup.mem_subgroupOf.1 hx).2
  have hx1 : (x : Q) ^ p = 1 := Subtype.ext (by simpa using hxp)
  refine Subgroup.mem_subgroupOf.2 ⟨(φ x).2, ?_⟩
  have : (φ x) ^ p = 1 := by rw [← map_pow, hx1, map_one]
  simpa [Subtype.ext_iff] using this

end API

variable [Finite E]

theorem powEqOneSubgroup_subgroupOf_sup_characteristic (hp : p.Prime) (P : Sylow p E)
    [IsMulCommutative (P : Subgroup E)] [K.Normal]
    (hKA : ⁅K, powEqOneSubgroup p (P : Subgroup E)⁆ = ⊥) :
    ((powEqOneSubgroup p (P : Subgroup E)).subgroupOf (K ⊔ (P : Subgroup E))).Characteristic := by
  have : Fact p.Prime := ⟨hp⟩
  set A : Subgroup E := powEqOneSubgroup p (P : Subgroup E) with hAdef
  set L : Subgroup E := K ⊔ (P : Subgroup E) with hLdef
  have hPL : (P : Subgroup E) ≤ L := le_sup_right
  have hAP : A ≤ (P : Subgroup E) := powEqOneSubgroup_le
  have hPcent : (P : Subgroup E) ≤ Subgroup.centralizer (A : Set E) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact setLike_mul_comm (hAP ha) hx
  have hKcent : K ≤ Subgroup.centralizer (A : Set E) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hKA
  have hLnorm : L ≤ Subgroup.normalizer (A : Set E) :=
    sup_le (hKcent.trans (Subgroup.centralizer_le_normalizer _))
      (hPcent.trans (Subgroup.centralizer_le_normalizer _))
  have hA'normal : (A.subgroupOf L).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hLnorm
  have hA'pg : IsPGroup p (A.subgroupOf L) :=
    isPGroup_powEqOneSubgroup.comap_of_injective L.subtype (Subgroup.subtype_injective L)
  have hA'core : A.subgroupOf L ≤ pCore p L := le_pCore hp hA'normal hA'pg
  have hcoreP : pCore p L ≤ (P : Subgroup E).subgroupOf L := by
    have h := pCore_le_sylow hp (P.subtype hPL)
    rwa [Sylow.coe_subtype] at h
  refine Subgroup.characteristic_iff_map_le.2 fun φ y hy => ?_
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
  have hxp : ((x : L) : E) ^ p = 1 :=
    pow_eq_one_of_mem_powEqOneSubgroup (Subgroup.mem_subgroupOf.1 hx)
  have h1 : φ x ∈ pCore p L := by
    rw [← map_pCore p L φ]
    exact Subgroup.mem_map_of_mem _ (hA'core hx)
  have h2 : ((φ x : L) : E) ^ p = 1 := by
    have hx1 : (φ x) ^ p = 1 := by
      rw [← map_pow, show (x : L) ^ p = 1 from Subtype.ext (by simpa using hxp), map_one]
    simpa [Subtype.ext_iff] using hx1
  exact Subgroup.mem_subgroupOf.2 (mem_powEqOneSubgroup_of_pow_eq_one (hcoreP h1) h2)

theorem powEqOneSubgroup_sylow_normal (hp : p.Prime) (P : Sylow p E)
    [IsMulCommutative (P : Subgroup E)] [K.Normal] (_hKp : (Nat.card K).Coprime p)
    (hL : (K ⊔ (P : Subgroup E)).Normal)
    (hKA : ⁅K, powEqOneSubgroup p (P : Subgroup E)⁆ = ⊥) :
    (powEqOneSubgroup p (P : Subgroup E)).Normal := by
  have : (K ⊔ (P : Subgroup E)).Normal := hL
  have := powEqOneSubgroup_subgroupOf_sup_characteristic hp P hKA
  exact normal_of_characteristic_subgroupOf_of_normal (K := K ⊔ (P : Subgroup E))
    (powEqOneSubgroup_le.trans le_sup_right)

end CFSG.FeitThompson
