module

public import CFSG.HardMathSupport.Curtis.Proving.ActsTrivially
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs

public section

namespace CFSG.HardMathSupport.Curtis.Proving

open CFSG.QuasithinUnique CFSG.AGLEmbedding
open scoped commutatorElement

variable {G : Type} [Group G]

theorem commutator_barM_le {M Q : Subgroup G} :
    ⁅barM M Q, barM M Q⁆ ≤ barM M ⁅Q, Q⁆ := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hb
  rw [← map_commutatorElement]
  refine Subgroup.mem_map.mpr ⟨⁅x, y⁆, ?_, rfl⟩
  rw [Subgroup.mem_subgroupOf]
  have h1 := Subgroup.mem_subgroupOf.1 hx
  have h2 := Subgroup.mem_subgroupOf.1 hy
  have := Subgroup.commutator_mem_commutator h1 h2
  simpa [commutatorElement_def] using this

theorem exists_lift_mem_barM {M X : Subgroup G} (t : G) (htM : t ∈ M)
    (h : QuotientGroup.mk' (CFSG.pCore 2 M) (⟨t, htM⟩ : M) ∈ barM M X) :
    ∃ c o : G, c ∈ X ∧ t = c * o ∧ ∃ k : ℕ, o ^ (2 ^ k) = 1 := by
  obtain ⟨x, hx, hxt⟩ := Subgroup.mem_map.mp h
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hxt
  refine ⟨(x : G), (x : G)⁻¹ * t, Subgroup.mem_subgroupOf.1 hx, by group, ?_⟩
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 M)) ⟨x⁻¹ * ⟨t, htM⟩, hxt⟩
  refine ⟨k, ?_⟩
  have h := congrArg Subtype.val (congrArg Subtype.val hk)
  simpa using h

theorem hstep_of_commutator_actsTriv {M L Q : Subgroup G} (hML : IsTwoPrimeComponent M L)
    (hQQ : ⁅Q, Q⁆ ≤ actsTrivSubgroup L) :
    ∀ t : ↥L, Odd (orderOf (t : G)) →
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) (⟨(t : G), hML.le t.2⟩ : ↥M) ∈
        ⁅barM M Q, barM M Q⁆ →
      ⁅blockU L, Subgroup.zpowers (t : G)⁆ ≤ blockZ L := by
  intro t ht hmem
  obtain ⟨c, o, hc, hto, k, hok⟩ :=
    exists_lift_mem_barM (M := M) (X := ⁅Q, Q⁆) (t : G) (hML.le t.2) (commutator_barM_le hmem)
  have hcT : ActsTriv L c := mem_actsTrivSubgroup_iff.1 (hQQ hc)
  have htN : (t : G) ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer t.2
  have htr : (t : G) ^ orderOf (t : G) = 1 := pow_orderOf_eq_one _
  have htA : ActsTriv L (t : G) :=
    actsTriv_of_parity hcT htN hto ht htr hok
  exact commutator_blockU_zpowers_le htA

end CFSG.HardMathSupport.Curtis.Proving

end
