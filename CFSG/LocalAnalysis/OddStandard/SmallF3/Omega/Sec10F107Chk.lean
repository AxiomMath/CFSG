
module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10ModelB0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10ModelF1051Base
public import Certificates.Data.OmegaS107Facts
public import CFSG.Sporadic.Th.Max3.Data
public import Certificates.Certificate3018

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.GH74.KGroups CFSG.Sporadic.Schreier
  CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.ClassicalInvolution.Q3.TA3.Check
  CFSG.ComponentClassification.GSThmB

local notation "P45" => Equiv.Perm (Fin 45)

namespace Mo107

open Certificates.OmegaS107

theorem memB_iff {l : List P45} {x : P45} : memB l x = true ↔ x ∈ l := by
  simp [memB, List.any_eq_true]

theorem memB_eq_false {l : List P45} {x : P45} : memB l x = false ↔ x ∉ l := by
  rw [← memB_iff]
  simp

structure B2Sound (T T0 Q B2 : List P45) : Prop where
  len : B2.length = 16
  nodup : B2.Nodup
  one : (1 : P45) ∈ B2
  mem_T : ∀ a ∈ B2, a ∈ T
  sq : ∀ a ∈ B2, a * a = 1
  inQ : ∀ a ∈ B2, a ∈ T0 → a ∈ Q
  comm : ∀ a ∈ B2, ∀ b ∈ B2, a * b = b * a
  mul : ∀ a ∈ B2, ∀ b ∈ B2, a * b ∈ B2
  normal : ∀ g ∈ T, ∀ b ∈ B2, g * b * g⁻¹ ∈ B2

theorem b2Group_sound {T T0 Q B2 : List P45} (h : b2Group T T0 Q B2 = true) :
    B2Sound T T0 Q B2 := by
  simp only [b2Group, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', memB_iff, memB_eq_false] at h
  obtain ⟨⟨⟨⟨hlen, hnd⟩, h1⟩, ha⟩, hn⟩ := h
  refine ⟨hlen, hnd, h1, fun a hA => (ha a hA).1.1.1, fun a hA => (ha a hA).1.1.2,
    fun a hA hT0 => ?_, fun a hA b hB => ((ha a hA).2 b hB).1, fun a hA b hB =>
    ((ha a hA).2 b hB).2, fun g hg b hB => hn g hg b hB⟩
  rcases (ha a hA).1.2 with h | h
  · exact absurd hT0 h
  · exact h

structure OuterSound (T T0 B2 : List P45) (y : P45) : Prop where
  nc : y ∈ B2 ∨ ∃ g ∈ T, (g * y * g⁻¹) * y ≠ y * (g * y * g⁻¹)
  cen : y ∈ B2 ∨ ((centIn T y).length = 16 ∧ ∃ y' ∈ centIn T y, y' ∈ B2 ∧ y' ∉ T0)
  gen : y ∈ B2 → ∀ b ∈ B2, ∃ c ∈ prod2 (conjList T y), ∃ d ∈ prod2 (conjList T y), b = c * d

theorem outerChk_sound {T T0 B2 : List P45} {y : P45} (h : outerChk T T0 B2 y = true) :
    OuterSound T T0 B2 y := by
  simp only [outerChk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.any_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', memB_iff, memB_eq_false, ne_eq, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨?_, ?_, fun hy b hb => ?_⟩
  · rcases h1 with h | ⟨g, hg, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨g, hg, h⟩
  · rcases h2 with h | ⟨hl, y', hy', h⟩
    · exact Or.inl h
    · exact Or.inr ⟨hl, y', hy', h.1, h.2⟩
  · rcases h3 with h | h
    · exact absurd hy h
    · exact h b hb

structure WSound (T0 Q B0 L : List P45) (w : P45) : Prop where
  nodup : (tList T0 w).Nodup
  normB0 : ∀ g ∈ tList T0 w, ∀ b ∈ B0, g * b * g⁻¹ ∈ B0
  ex : ∃ y2 ∈ outInv T0 w, y2 ∈ L ∧ y2 ∉ T0 ∧ B2Sound (tList T0 w) T0 Q (b2List Q y2) ∧
    ∀ y ∈ outInv T0 w, OuterSound (tList T0 w) T0 (b2List Q y2) y

theorem wChk_sound {T0 Q B0 L : List P45} {w : P45} (h : wChk T0 Q B0 L w = true) :
    WSound T0 Q B0 L w := by
  simp only [wChk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.any_eq_true,
    Bool.not_eq_true', memB_iff, memB_eq_false] at h
  obtain ⟨⟨hnd, hB⟩, y2, hy2, ⟨hL, hT0⟩, hb2, hout⟩ := h
  refine ⟨hnd, hB, y2, hy2, hL, hT0,
    b2Group_sound hb2, fun y hy => outerChk_sound (hout y hy)⟩

theorem mem_tList {T0 : List P45} {w x : P45} :
    x ∈ tList T0 w ↔ x ∈ T0 ∨ ∃ a ∈ T0, a * w = x := by
  simp [tList]

theorem mem_outInv {T0 : List P45} {w y : P45} :
    y ∈ outInv T0 w ↔ (∃ a ∈ T0, a * w = y) ∧ y * y = 1 := by
  simp [outInv, List.mem_filter, List.mem_map]

theorem mem_centIn {T : List P45} {y x : P45} : x ∈ centIn T y ↔ x ∈ T ∧ x * y = y * x := by
  simp [centIn, List.mem_filter]

theorem mem_b2List {Q : List P45} {y2 x : P45} :
    x ∈ b2List Q y2 ↔ (x ∈ Q ∧ x * y2 = y2 * x) ∨ ∃ c ∈ Q, c * y2 = y2 * c ∧ c * y2 = x := by
  simp only [b2List, List.mem_append, List.mem_filter, decide_eq_true_eq, List.mem_map]
  constructor
  · rintro (h | ⟨c, ⟨hc, hc2⟩, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨c, hc, hc2, rfl⟩
  · rintro (h | ⟨c, hc, hc2, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨c, ⟨hc, hc2⟩, rfl⟩

theorem mem_conjList {T : List P45} {y c : P45} :
    c ∈ conjList T y ↔ c = 1 ∨ ∃ g ∈ T, g * y * g⁻¹ = c := by
  simp [conjList, List.mem_dedup, List.mem_map]

theorem mem_prod2 {cl : List P45} {x : P45} : x ∈ prod2 cl ↔ ∃ c ∈ cl, ∃ d ∈ cl, c * d = x := by
  simp [prod2, List.mem_flatMap, List.mem_map]

theorem gensT0_mem {g : P45} (hg : g ∈ gensT0 ()) : g ∈ QT0.originalSubgroup := by
  rw [QT0, certificate_originalSubgroup]
  exact Subgroup.subset_closure hg

theorem mem_wList_iff {w : P45} :
    w ∈ wList (elemsT QA45) (elemsT QP45) (elemsT QT0) ↔
      w ∈ QA45.originalSubgroup ∧ w ∉ QP45.originalSubgroup ∧
        ∀ g ∈ gensT0 (), w * g * w⁻¹ ∈ QT0.originalSubgroup := by
  simp only [wList, List.mem_filter, List.all_eq_true, Bool.not_eq_true', memB_iff,
    memB_eq_false, mem_elemsT QA45 QA45_ok, mem_elemsT QP45 QP45_ok,
    mem_elemsT QT0 QT0_valid.1]
  tauto

end Mo107

end CFSG.OddStandard.SmallF3.Omega
