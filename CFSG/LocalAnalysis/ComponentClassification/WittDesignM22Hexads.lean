
module

public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22HexadsBase

public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Count
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignSteiner3
public import CFSG.Monster.B.Classical.PlaneData
public meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Count
public meta import CFSG.Monster.B.Classical.PlaneData
public import CFSG.Sporadic.Schreier.M22Data
public meta import CFSG.Sporadic.Schreier.M22Data
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22HexadsInputs
public import Certificates.Certificate2031
public import Certificates.Data.CFSGNative.Mathieu.M22

public section

namespace CFSG.ComponentClassification.WittDesign

open scoped Pointwise
open CFSG.Sporadic.Mathieu CFSG.Monster.B.Classical.Plane

theorem hexadList_checks : hexadList.length = 77 ∧ hexadList.Nodup ∧ hexad0 ∈ hexadList ∧
    hexadList.all (fun B => B.card == 6) = true ∧
    hexadList.all (fun B => hexadMasks.contains (mask (B.map m22gA.toEmbedding)) &&
      hexadMasks.contains (mask (B.map m22gB.toEmbedding))) = true :=
  Certificates.certificate2031.1

theorem hexadList_facts : hexadList.length = 77 ∧ hexadList.Nodup ∧ hexad0 ∈ hexadList ∧
    (∀ B ∈ hexadList, B.card = 6) ∧
    (∀ B ∈ hexadList, mask (B.map m22gA.toEmbedding) ∈ hexadMasks ∧
      mask (B.map m22gB.toEmbedding) ∈ hexadMasks) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hexadList_checks
  refine ⟨h1, h2, h3, fun B hB => ?_, fun B hB => ?_⟩
  · simpa using List.all_eq_true.1 h4 B hB
  · simpa using List.all_eq_true.1 h5 B hB

theorem hexadMasks_triples : ∀ x y z : Fin 22, x ≠ y → x ≠ z → y ≠ z →
    (hexadMasks.filter fun m => m.testBit x && m.testBit y && m.testBit z).length = 1 :=
  Certificates.certificate2031.2.1

theorem hexadMasks_intersections : ∀ m ∈ hexadMasks,
    (hexadMasks.filter fun m' => interBits m m' == 0).length = 16 ∧
      (hexadMasks.filter fun m' => interBits m m' == 2).length = 60 :=
  Certificates.certificate2031.2.2.1

theorem count_stabilizer_hexad0 : m22Count (fun g => ∀ x ∈ hexad0, g x ∈ hexad0) = 5760 :=
  Certificates.certificate2031.2.2.2

theorem card_hexads : hexads.card = 77 := by
  rw [hexads, List.toFinset_card_of_nodup hexadList_facts.2.1, hexadList_facts.1]

theorem hexad0_mem : hexad0 ∈ hexads := mem_hexads.2 hexadList_facts.2.2.1

theorem card_of_mem_hexads {B : Finset (Fin 22)} (hB : B ∈ hexads) : B.card = 6 :=
  hexadList_facts.2.2.2.1 B (mem_hexads.1 hB)

theorem card_filter_hexads (P : Finset (Fin 22) → Prop) [DecidablePred P] (q : ℕ → Bool)
    (hq : ∀ B, decide (P B) = q (mask B)) :
    (hexads.filter P).card = (hexadMasks.filter q).length := by
  have e : hexads.filter P = (hexadList.filter fun B => decide (P B)).toFinset := by
    ext B
    simp [hexads]
  rw [e, List.toFinset_card_of_nodup (hexadList_facts.2.1.filter _), hexadMasks, List.filter_map,
    List.length_map]
  congr 1
  exact List.filter_congr fun B _ => hq B

theorem isSteinerTriple_hexads : IsSteinerTriple hexads := by
  refine ⟨by simp, fun B hB => card_of_mem_hexads hB, fun T hT => ?_⟩
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.1 hT
  have h1 : (hexads.filter fun B => x ∈ B ∧ y ∈ B ∧ z ∈ B).card = 1 := by
    rw [card_filter_hexads _ (fun m => m.testBit x && m.testBit y && m.testBit z)]
    · exact hexadMasks_triples x y z hxy hxz hyz
    · intro B
      rw [Bool.eq_iff_iff, decide_eq_true_iff, Bool.and_eq_true, Bool.and_eq_true, testBit_mask,
        testBit_mask, testBit_mask, and_assoc]
  obtain ⟨B, hB⟩ := Finset.card_eq_one.1 h1
  have hmem : ∀ C, C ∈ hexads ∧ {x, y, z} ⊆ C ↔ C = B := by
    intro C
    rw [← Finset.mem_singleton, ← hB, Finset.mem_filter, Finset.insert_subset_iff,
      Finset.insert_subset_iff, Finset.singleton_subset_iff]
  exact ⟨B, (hmem B).2 rfl, fun C hC => (hmem C).1 hC⟩

theorem hexads_intersections {B : Finset (Fin 22)} (hB : B ∈ hexads) :
    (hexads.filter fun B' => Disjoint B B').card = 16 ∧
      (hexads.filter fun B' => (B ∩ B').card = 2).card = 60 := by
  have hm : mask B ∈ hexadMasks := List.mem_map_of_mem (mem_hexads.1 hB)
  obtain ⟨h16, h60⟩ := hexadMasks_intersections _ hm
  refine ⟨?_, ?_⟩
  · rw [card_filter_hexads _ (fun m' => interBits (mask B) m' == 0)]
    · exact h16
    · intro B'
      rw [Bool.eq_iff_iff, decide_eq_true_iff, beq_iff_eq, ← card_inter_eq_interBits,
        Finset.card_eq_zero, Finset.disjoint_iff_inter_eq_empty]
  · rw [card_filter_hexads _ (fun m' => interBits (mask B) m' == 2)]
    · exact h60
    · intro B'
      rw [Bool.eq_iff_iff, decide_eq_true_iff, beq_iff_eq, ← card_inter_eq_interBits]

theorem smul_mem_hexads_of_gen {σ : Equiv.Perm (Fin 22)} (hσ : σ = m22gA ∨ σ = m22gB)
    {B : Finset (Fin 22)} (hB : B ∈ hexads) : σ • B ∈ hexads := by
  have h := hexadList_facts.2.2.2.2 B (mem_hexads.1 hB)
  have hm : mask (σ • B) ∈ hexadMasks := by
    rw [smul_finset_eq_map]
    rcases hσ with rfl | rfl
    · exact h.1
    · exact h.2
  obtain ⟨C, hC, e⟩ := List.mem_map.1 hm
  rw [← mask_injective e]
  exact mem_hexads.2 hC

theorem smul_hexads (g : M22) : (g : Equiv.Perm (Fin 22)) • hexads = hexads := by
  have hgen : ∀ σ : Equiv.Perm (Fin 22), (σ = m22gA ∨ σ = m22gB) → σ • hexads = hexads := by
    intro σ hσ
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro C hC
      obtain ⟨B, hB, rfl⟩ := Finset.mem_smul_finset.1 hC
      exact smul_mem_hexads_of_gen hσ hB
    · rw [Finset.card_smul_finset]
  have hle : M22 ≤ MulAction.stabilizer (Equiv.Perm (Fin 22)) hexads := by
    change Subgroup.closure _ ≤ _
    rw [Subgroup.closure_le]
    intro σ hσ
    exact hgen σ hσ
  exact hle g.2

theorem smul_mem_hexads (g : M22) {B : Finset (Fin 22)} (hB : B ∈ hexads) : g • B ∈ hexads := by
  rw [← smul_hexads g, Subgroup.smul_def]
  exact Finset.smul_mem_smul_finset hB

theorem card_stabilizer_hexad0 : Nat.card (MulAction.stabilizer M22 hexad0) = 5760 := by
  rw [← count_stabilizer_hexad0, ← card_m22_subtype]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun g => mem_stabilizer_finset_iff)

theorem orbit_hexad0 : MulAction.orbit M22 hexad0 = (hexads : Set (Finset (Fin 22))) := by
  have hsub : MulAction.orbit M22 hexad0 ⊆ (hexads : Set (Finset (Fin 22))) := by
    rintro _ ⟨g, rfl⟩
    exact smul_mem_hexads g hexad0_mem
  have hcard : Nat.card (MulAction.orbit M22 hexad0) = 77 := by
    have h := card_orbit_mul_card_stabilizer hexad0
    rw [card_stabilizer_hexad0, show (443520 : ℕ) = 77 * 5760 by norm_num] at h
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h
  refine Set.eq_of_subset_of_ncard_le hsub ?_ (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset, card_hexads, ← Nat.card_coe_set_eq, hcard]

theorem mem_hexads_iff {B : Finset (Fin 22)} : B ∈ hexads ↔ ∃ g : M22, g • hexad0 = B := by
  rw [← Finset.mem_coe, ← orbit_hexad0]
  rfl

theorem card_stabilizer_hexad {B : Finset (Fin 22)} (hB : B ∈ hexads) :
    Nat.card (MulAction.stabilizer M22 B) = 5760 := by
  obtain ⟨g, rfl⟩ := mem_hexads_iff.1 hB
  have h := card_orbit_mul_card_stabilizer (g • hexad0)
  rw [MulAction.orbit_smul, orbit_hexad0, Nat.card_coe_set_eq, Set.ncard_coe_finset,
    card_hexads, show (443520 : ℕ) = 77 * 5760 by norm_num] at h
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h

end CFSG.ComponentClassification.WittDesign
