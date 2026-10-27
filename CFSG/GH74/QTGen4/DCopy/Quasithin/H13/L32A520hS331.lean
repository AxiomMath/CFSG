module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.L32A520h

public section
namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped Pointwise

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

omit [CFSG.GH74.QTGen4.Finite4 G] in
theorem relIndex_lineOf_F4 {Y : Subgroup G} {w : G} (hwY : w ∈ Y) (hwQ : w ∉ pCoreOf 2 Y)
    (hw3 : w ^ 3 ∈ pCoreOf 2 Y) : (pCoreOf 2 Y).relIndex (lineOf Y w) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := (pCoreOf 2 Y).subgroupOf Y with hN
  have hle : lineOf Y w ≤ Y := sup_le (Subgroup.zpowers_le.mpr hwY) (pCoreOf_le 2 Y)
  rw [relIndex_eq_card_map hle]
  have e : ((lineOf Y w).subgroupOf Y).map (QuotientGroup.mk' N) =
      Subgroup.zpowers (QuotientGroup.mk' N ⟨w, hwY⟩) := by
    apply le_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      have hz' : (z : G) ∈ pCoreOf 2 Y ⊔ Subgroup.zpowers w := by
        rw [sup_comm]
        exact Subgroup.mem_subgroupOf.mp hz
      obtain ⟨a, ha, b, hb, hab⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes
        (Subgroup.zpowers_le.mpr (le_normalizer_pCoreOf 2 Y hwY))).mp hz'
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      refine ⟨m, ?_⟩
      have hzq : z = ⟨a, pCoreOf_le 2 Y ha⟩ * ⟨w, hwY⟩ ^ m := Subtype.ext (by simp [hab])
      have ha1 : QuotientGroup.mk' N ⟨a, pCoreOf_le 2 Y ha⟩ = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact Subgroup.mem_subgroupOf.mpr ha
      rw [hzq, map_mul, ha1, one_mul, map_zpow]
    · rw [Subgroup.zpowers_le]
      exact ⟨⟨w, hwY⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left (Subgroup.mem_zpowers w)),
        rfl⟩
  rw [e, Nat.card_zpowers]
  apply orderOf_eq_prime
  · rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr (by simpa using hw3)
  · intro h
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    exact hwQ (Subgroup.mem_subgroupOf.mp h)

end CFSG.Quasithin.H13.L32A
