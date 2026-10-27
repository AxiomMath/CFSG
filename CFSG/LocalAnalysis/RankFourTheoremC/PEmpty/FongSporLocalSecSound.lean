module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalPermSound
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalPermSecDefs
public import Mathlib.GroupTheory.Subgroup.Simple

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open Subgroup

theorem PGen.holdsBase_of_checkBase {G : Type*} [Group G] [DecidableEq G] (a b : G) (c : PGen)
    (h : c.checkBase a b = true) : c.holdsBase a b := by
  unfold PGen.checkBase at h
  unfold PGen.holdsBase
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.any_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, h2, fun w hw => ⟨(h3 w hw).1.1, (h3 w hw).1.2, (h3 w hw).2⟩,
    fun n hn => h4 n hn, fun m hm => ?_⟩
  obtain ⟨w, hw, hx⟩ := h5 m hm
  exact ⟨w, hw, hx⟩

theorem subgroupOf_transport_simple {G : Type*} [Group G] (N K : Subgroup G) (hKN : K ≤ N)
    (hS : IsSimpleGroup ↥K) (hC : ¬ IsMulCommutative ↥K) (h3 : 3 ∣ Nat.card ↥K) :
    IsSimpleGroup ↥(K.subgroupOf N) ∧ ¬ IsMulCommutative ↥(K.subgroupOf N) ∧
      3 ∣ Nat.card ↥(K.subgroupOf N) := by
  refine ⟨(MulEquiv.isSimpleGroup_congr (Subgroup.subgroupOfEquivOfLe hKN)).mpr hS, ?_, ?_⟩
  · intro h
    apply hC
    rw [isMulCommutative_iff] at h ⊢
    intro a b
    apply (Subgroup.subgroupOfEquivOfLe hKN).symm.injective
    rw [map_mul, map_mul]
    exact h _ _
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKN).toEquiv]
    exact h3

theorem secW_exists_of_parts {G : Type*} [Group G] (a b : G) (c : PSec) (hp : c.base.p.Prime)
    (hbase : c.base.holdsBase a b)
    (hS : IsSimpleGroup ↥(Subgroup.closure ({evalIdx (c.base.regs a b) c.h1,
        evalIdx (c.base.regs a b) c.h2} : Set G)) ∧
      ¬ IsMulCommutative ↥(Subgroup.closure ({evalIdx (c.base.regs a b) c.h1,
        evalIdx (c.base.regs a b) c.h2} : Set G)) ∧
      evalPW a b c.base.z ∈ Subgroup.closure ({evalIdx (c.base.regs a b) c.h1,
        evalIdx (c.base.regs a b) c.h2} : Set G) ∧
      3 ∣ Nat.card ↥(Subgroup.closure ({evalIdx (c.base.regs a b) c.h1,
        evalIdx (c.base.regs a b) c.h2} : Set G))) :
    ∃ (z₀ : ↥(Subgroup.closure ({a, b} : Set G)))
      (ns ms : Set ↥(Subgroup.closure ({a, b} : Set G)))
      (H : Subgroup ↥(Subgroup.closure ({a, b} : Set G))),
      orderOf z₀ = c.base.p ∧
      (∀ n ∈ ns, n ∈ Subgroup.normalizer (Subgroup.zpowers z₀ : Set ↥(Subgroup.closure ({a, b} : Set G)))) ∧
      (∀ m ∈ ms, ∃ t : ↥(Subgroup.closure ({a, b} : Set G)), t * t = 1 ∧ t ≠ 1 ∧
        z₀ * t = t * z₀ ∧ m * t = t * m) ∧
      H ≤ Subgroup.closure (ns ∪ ms) ∧ IsSimpleGroup ↥H ∧ ¬ IsMulCommutative ↥H ∧ z₀ ∈ H ∧
      3 ∣ Nat.card ↥H := by
  have hfact : Fact c.base.p.Prime := ⟨hp⟩
  obtain ⟨hS1, hS2, hS3, hS4⟩ := hS
  have hregsN : ∀ x ∈ c.base.regs a b, x ∈ Subgroup.closure ({a, b} : Set G) := by
    intro x hx
    simp only [PGen.regs, List.mem_append, List.mem_map] at hx
    rcases hx with ⟨n, _, rfl⟩ | ⟨m, _, rfl⟩
    · exact evalPW_mem a b _
    · exact evalPW_mem a b _
  have hKN : Subgroup.closure ({evalIdx (c.base.regs a b) c.h1,
      evalIdx (c.base.regs a b) c.h2} : Set G) ≤ Subgroup.closure ({a, b} : Set G) := by
    rw [Subgroup.closure_le]
    exact Set.insert_subset_iff.mpr ⟨evalIdx_mem _ _ hregsN c.h1,
      Set.singleton_subset_iff.mpr (evalIdx_mem _ _ hregsN c.h2)⟩
  obtain ⟨hT1, hT2, hT3⟩ := subgroupOf_transport_simple _ _ hKN hS1 hS2 hS4
  have hU : ∀ x ∈ c.base.regs a b, x ∈ (Subgroup.closure (genSet a b c.base)).map
      (Subgroup.closure ({a, b} : Set G)).subtype := by
    intro x hx
    simp only [PGen.regs, List.mem_append, List.mem_map] at hx
    rcases hx with ⟨n, hn, rfl⟩ | ⟨m, hm, rfl⟩
    · exact Subgroup.mem_map.mpr
        ⟨evalPWN a b n.1, Subgroup.subset_closure (mem_genSet_ns a b c.base hn), rfl⟩
    · exact Subgroup.mem_map.mpr
        ⟨evalPWN a b m.1, Subgroup.subset_closure (mem_genSet_ms a b c.base hm), rfl⟩
  have hKU : Subgroup.closure ({evalIdx (c.base.regs a b) c.h1,
      evalIdx (c.base.regs a b) c.h2} : Set G) ≤ (Subgroup.closure (genSet a b c.base)).map
      (Subgroup.closure ({a, b} : Set G)).subtype := by
    rw [Subgroup.closure_le]
    exact Set.insert_subset_iff.mpr ⟨evalIdx_mem _ _ hU c.h1,
      Set.singleton_subset_iff.mpr (evalIdx_mem _ _ hU c.h2)⟩
  refine ⟨evalPWN a b c.base.z, {x | ∃ n ∈ c.base.ns, x = evalPWN a b n.1},
    {x | ∃ m ∈ c.base.ms, x = evalPWN a b m.1},
    (Subgroup.closure ({evalIdx (c.base.regs a b) c.h1,
      evalIdx (c.base.regs a b) c.h2} : Set G)).subgroupOf (Subgroup.closure ({a, b} : Set G)),
    ?_, ?_, ?_, ?_, hT1, hT2, ?_, hT3⟩
  · have hz : evalPWN a b c.base.z ^ c.base.p = 1 := Subtype.ext (by simpa using hbase.1)
    have hz1 : evalPWN a b c.base.z ≠ 1 :=
      fun e => hbase.2.1 (by simpa using congrArg Subtype.val e)
    exact orderOf_eq_prime hz hz1
  · rintro x ⟨n, hn, rfl⟩
    obtain ⟨h4, h5⟩ := hbase.2.2.2.1 n hn
    exact mem_normalizer_zpowers_of _ _ n.2.1 n.2.2
      (Subtype.ext (by simpa using h4)) (Subtype.ext (by simpa using h5))
  · rintro x ⟨m, hm, rfl⟩
    obtain ⟨w, hw, hcomm⟩ := hbase.2.2.2.2 m hm
    obtain ⟨hw1, hw2, hw3⟩ := hbase.2.2.1 w hw
    refine ⟨evalPWN a b w, Subtype.ext (by simpa using hw1),
      fun e => hw2 (by simpa using congrArg Subtype.val e),
      Subtype.ext (by simpa using hw3), Subtype.ext (by simpa using hcomm)⟩
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (hKU (Subgroup.mem_subgroupOf.mp hx))
    obtain rfl : y = x := Subtype.ext hyx
    exact hy
  · exact Subgroup.mem_subgroupOf.mpr hS3

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
