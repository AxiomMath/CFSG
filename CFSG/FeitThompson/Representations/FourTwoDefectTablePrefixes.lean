module

public import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Ring.RingNF

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Finset Matrix

def labVec (d : ℕ) (a : ℤ) : Fin d → ℤ := fun k => if (k : ℕ) + 1 = a.natAbs then a.sign else 0

theorem labVec_apply (d : ℕ) (a : ℤ) (k : Fin d) :
    labVec d a k = if (k : ℕ) + 1 = a.natAbs then a.sign else 0 := (rfl)

theorem labVec_eq_zero_of_le {d : ℕ} {a : ℤ} {r : ℕ} (har : a.natAbs ≤ r) {k : Fin d}
    (hk : r ≤ (k : ℕ)) : labVec d a k = 0 := by
  rw [labVec_apply, if_neg (by omega)]

theorem labVec_eq_zero_of_gt {d : ℕ} {a : ℤ} (hd : d < a.natAbs) : labVec d a = 0 := by
  funext k
  rw [labVec_apply, if_neg (by omega)]
  rfl

def labIdx {d : ℕ} (a : ℤ) (ha0 : a ≠ 0) (ha : a.natAbs ≤ d) : Fin d :=
  ⟨a.natAbs - 1, by have := Int.natAbs_pos.mpr ha0; omega⟩

theorem labVec_eq_single_sign {d : ℕ} {a : ℤ} (ha0 : a ≠ 0) (ha : a.natAbs ≤ d) :
    labVec d a = Pi.single (labIdx a ha0 ha) a.sign := by
  have hpos : 0 < a.natAbs := Int.natAbs_pos.mpr ha0
  funext k
  rw [labVec_apply, Pi.single_apply]
  have h : ((k : ℕ) + 1 = a.natAbs) ↔ k = labIdx a ha0 ha := by
    rw [labIdx, Fin.ext_iff]; simp; omega
  simp only [h]

def labOf {d : ℕ} (i : Fin d) (s : ℤ) : ℤ := s * ((i : ℕ) + 1)

theorem labOf_def {d : ℕ} (i : Fin d) (s : ℤ) : labOf i s = s * ((i : ℕ) + 1) := (rfl)

@[simp] theorem labOf_one {d : ℕ} (i : Fin d) : labOf i 1 = (i : ℕ) + 1 := by
  rw [labOf_def, one_mul]

theorem natAbs_labOf {d : ℕ} (i : Fin d) {s : ℤ} (hs : s = 1 ∨ s = -1) :
    (labOf i s).natAbs = (i : ℕ) + 1 := by
  rcases hs with h | h <;> subst h <;> simp only [labOf] <;> omega

theorem labOf_ne_zero {d : ℕ} (i : Fin d) {s : ℤ} (hs : s = 1 ∨ s = -1) : labOf i s ≠ 0 := by
  intro h
  have h' := natAbs_labOf i hs
  rw [h] at h'
  simp at h'

theorem natAbs_labOf_le {d : ℕ} (i : Fin d) {s : ℤ} (hs : s = 1 ∨ s = -1) :
    (labOf i s).natAbs ≤ d := by
  rw [natAbs_labOf i hs]; omega

theorem labVec_labOf {d : ℕ} (i : Fin d) {s : ℤ} (hs : s = 1 ∨ s = -1) :
    labVec d (labOf i s) = Pi.single i s := by
  funext k
  rw [labVec_apply, Pi.single_apply, natAbs_labOf i hs]
  have h2 : (labOf i s).sign = s := by
    rcases hs with h | h <;> subst h <;> simp only [labOf]
    · rw [one_mul, Int.sign_eq_one_iff_pos]; positivity
    · rw [Int.sign_eq_neg_one_iff_neg]; nlinarith [Int.natCast_nonneg (i : ℕ)]
  rw [h2]
  have h3 : ((k : ℕ) + 1 = (i : ℕ) + 1) ↔ k = i := by
    rw [Nat.add_right_cancel_iff, Fin.ext_iff]
  simp only [h3]

@[expose] def labDot (a b : ℤ) : ℤ := if a = b then 1 else if a = -b then -1 else 0

theorem labVec_dotProduct (d : ℕ) {a b : ℤ} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (ha : a.natAbs ≤ d) (hb : b.natAbs ≤ d) : labVec d a ⬝ᵥ labVec d b = labDot a b := by
  have h1 : 0 < a.natAbs := Int.natAbs_pos.mpr ha0
  have h2 : 0 < b.natAbs := Int.natAbs_pos.mpr hb0
  rw [labVec_eq_single_sign ha0 ha, single_dotProduct, labVec_eq_single_sign hb0 hb,
    Pi.single_apply, labDot]
  have hidx : (labIdx a ha0 ha = labIdx b hb0 hb) ↔ a.natAbs = b.natAbs := by
    rw [labIdx, labIdx, Fin.ext_iff]; simp only []; omega
  have hsa : a.sign = 1 ∧ 0 < a ∨ a.sign = -1 ∧ a < 0 := by
    rcases lt_trichotomy a 0 with h | h | h
    · exact Or.inr ⟨by rwa [Int.sign_eq_neg_one_iff_neg], h⟩
    · exact absurd h ha0
    · exact Or.inl ⟨by rwa [Int.sign_eq_one_iff_pos], h⟩
  have hsb : b.sign = 1 ∧ 0 < b ∨ b.sign = -1 ∧ b < 0 := by
    rcases lt_trichotomy b 0 with h | h | h
    · exact Or.inr ⟨by rwa [Int.sign_eq_neg_one_iff_neg], h⟩
    · exact absurd h hb0
    · exact Or.inl ⟨by rwa [Int.sign_eq_one_iff_pos], h⟩
  by_cases h : a.natAbs = b.natAbs
  · rw [if_pos (hidx.mpr h)]
    rcases hsa with ⟨e1, p1⟩ | ⟨e1, p1⟩ <;> rcases hsb with ⟨e2, p2⟩ | ⟨e2, p2⟩ <;> rw [e1, e2]
    · rw [if_pos (by omega)]; ring
    · rw [if_neg (by omega), if_pos (by omega)]; ring
    · rw [if_neg (by omega), if_pos (by omega)]; ring
    · rw [if_pos (by omega)]; ring
  · rw [if_neg (fun hc => h (hidx.mp hc)), if_neg (by omega), if_neg (by omega), mul_zero]

def labVec3 (d : ℕ) (L : ℤ × ℤ × ℤ) : Fin d → ℤ :=
  labVec d L.1 + labVec d L.2.1 + labVec d L.2.2

theorem labVec3_apply (d : ℕ) (L : ℤ × ℤ × ℤ) (k : Fin d) :
    labVec3 d L k = labVec d L.1 k + labVec d L.2.1 k + labVec d L.2.2 k := (rfl)

theorem labVec3_eq (d : ℕ) (L : ℤ × ℤ × ℤ) :
    labVec3 d L = labVec d L.1 + labVec d L.2.1 + labVec d L.2.2 := (rfl)

theorem labVec3_of_labOf {d : ℕ} (i j k : Fin d) {s t r : ℤ} (hs : s = 1 ∨ s = -1)
    (ht : t = 1 ∨ t = -1) (hr : r = 1 ∨ r = -1) :
    labVec3 d (labOf i s, labOf j t, labOf k r) =
      Pi.single i s + Pi.single j t + Pi.single k r := by
  rw [labVec3_eq, labVec_labOf i hs, labVec_labOf j ht, labVec_labOf k hr]

theorem labVec3_eq_zero_of_le {d : ℕ} {L : ℤ × ℤ × ℤ} {r : ℕ} (h1 : L.1.natAbs ≤ r)
    (h2 : L.2.1.natAbs ≤ r) (h3 : L.2.2.natAbs ≤ r) {k : Fin d} (hk : r ≤ (k : ℕ)) :
    labVec3 d L k = 0 := by
  rw [labVec3_apply, labVec_eq_zero_of_le h1 hk, labVec_eq_zero_of_le h2 hk,
    labVec_eq_zero_of_le h3 hk, add_zero, add_zero]

theorem labVec3_castLE {d d' : ℕ} (h : d ≤ d') (L : ℤ × ℤ × ℤ) (k' : Fin d') :
    labVec3 d' L k' = if hk : (k' : ℕ) < d then labVec3 d L ⟨k', hk⟩ else
      labVec3 d' L k' := by
  by_cases hk : (k' : ℕ) < d
  · rw [dif_pos hk, labVec3_apply, labVec3_apply, labVec_apply, labVec_apply, labVec_apply,
      labVec_apply, labVec_apply, labVec_apply]
  · rw [dif_neg hk]

@[expose] def triDot (L M : ℤ × ℤ × ℤ) : ℤ :=
  labDot L.1 M.1 + labDot L.1 M.2.1 + labDot L.1 M.2.2 +
  labDot L.2.1 M.1 + labDot L.2.1 M.2.1 + labDot L.2.1 M.2.2 +
  labDot L.2.2 M.1 + labDot L.2.2 M.2.1 + labDot L.2.2 M.2.2

@[expose] def LabBounded (d : ℕ) (L : ℤ × ℤ × ℤ) : Prop :=
  (L.1 ≠ 0 ∧ L.1.natAbs ≤ d) ∧ (L.2.1 ≠ 0 ∧ L.2.1.natAbs ≤ d) ∧ (L.2.2 ≠ 0 ∧ L.2.2.natAbs ≤ d)

theorem labVec3_dotProduct {d : ℕ} {L M : ℤ × ℤ × ℤ} (hL : LabBounded d L)
    (hM : LabBounded d M) : labVec3 d L ⬝ᵥ labVec3 d M = triDot L M := by
  obtain ⟨⟨hL1, hLd1⟩, ⟨hL2, hLd2⟩, ⟨hL3, hLd3⟩⟩ := hL
  obtain ⟨⟨hM1, hMd1⟩, ⟨hM2, hMd2⟩, ⟨hM3, hMd3⟩⟩ := hM
  simp only [labVec3, add_dotProduct, dotProduct_add,
    labVec_dotProduct d hL1 hM1 hLd1 hMd1, labVec_dotProduct d hL1 hM2 hLd1 hMd2,
    labVec_dotProduct d hL1 hM3 hLd1 hMd3, labVec_dotProduct d hL2 hM1 hLd2 hMd1,
    labVec_dotProduct d hL2 hM2 hLd2 hMd2, labVec_dotProduct d hL2 hM3 hLd2 hMd3,
    labVec_dotProduct d hL3 hM1 hLd3 hMd1, labVec_dotProduct d hL3 hM2 hLd3 hMd2,
    labVec_dotProduct d hL3 hM3 hLd3 hMd3, triDot]
  ring

@[expose] def oldLabels (r : ℕ) : List ℤ :=
  (List.range r).map (fun i : ℕ => (i : ℤ) + 1) ++
    (List.range r).map (fun i : ℕ => -((i : ℤ) + 1))

theorem mem_oldLabels {r : ℕ} {a : ℤ} : a ∈ oldLabels r ↔ a ≠ 0 ∧ a.natAbs ≤ r := by
  rw [oldLabels, List.mem_append]
  constructor
  · rintro (h | h) <;> obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h <;>
      rw [List.mem_range] at hi <;> exact ⟨by omega, by omega⟩
  · rintro ⟨h0, hle⟩
    rcases Int.natAbs_eq a with h | h
    · refine Or.inl (List.mem_map.mpr ⟨a.natAbs - 1, List.mem_range.mpr (by omega), ?_⟩)
      omega
    · refine Or.inr (List.mem_map.mpr ⟨a.natAbs - 1, List.mem_range.mpr (by omega), ?_⟩)
      omega

@[expose] def labLevel (r : ℕ) (a : ℤ) : ℕ := max r a.natAbs

@[expose] def triLevel (r : ℕ) (L : ℤ × ℤ × ℤ) : ℕ :=
  labLevel (labLevel (labLevel r L.1) L.2.1) L.2.2

theorem le_labLevel (r : ℕ) (a : ℤ) : r ≤ labLevel r a := le_max_left _ _

theorem natAbs_le_labLevel (r : ℕ) (a : ℤ) : a.natAbs ≤ labLevel r a := le_max_right _ _

@[expose] def IsFreshLab (r : ℕ) (a : ℤ) : Prop := a.natAbs ≤ r ∨ a = (r : ℤ) + 1

instance (r : ℕ) (a : ℤ) : Decidable (IsFreshLab r a) :=
  decidable_of_iff (a.natAbs ≤ r ∨ a = (r : ℤ) + 1) Iff.rfl

theorem IsFreshLab.ne_zero {r : ℕ} {a : ℤ} (h : IsFreshLab r a) (h0 : a.natAbs ≠ 0) : a ≠ 0 :=
  fun hz => h0 (by rw [hz]; rfl)

theorem IsFreshLab.natAbs_le_succ {r : ℕ} {a : ℤ} (h : IsFreshLab r a) : a.natAbs ≤ r + 1 := by
  rcases h with h | h <;> omega

theorem IsFreshLab.labLevel_le_succ {r : ℕ} {a : ℤ} (h : IsFreshLab r a) :
    labLevel r a ≤ r + 1 := by
  rw [labLevel]
  have := h.natAbs_le_succ
  omega

@[expose] def IsNormalTri (r : ℕ) (L : ℤ × ℤ × ℤ) : Prop :=
  L.1 ≠ 0 ∧ L.1.natAbs < L.2.1.natAbs ∧ L.2.1.natAbs < L.2.2.natAbs ∧
    IsFreshLab r L.1 ∧ IsFreshLab (labLevel r L.1) L.2.1 ∧
      IsFreshLab (labLevel (labLevel r L.1) L.2.1) L.2.2

instance (r : ℕ) (L : ℤ × ℤ × ℤ) : Decidable (IsNormalTri r L) :=
  decidable_of_iff (L.1 ≠ 0 ∧ L.1.natAbs < L.2.1.natAbs ∧ L.2.1.natAbs < L.2.2.natAbs ∧
    IsFreshLab r L.1 ∧ IsFreshLab (labLevel r L.1) L.2.1 ∧
      IsFreshLab (labLevel (labLevel r L.1) L.2.1) L.2.2) Iff.rfl

theorem IsNormalTri.labBounded {r : ℕ} {L : ℤ × ℤ × ℤ} (hL : IsNormalTri r L) {d : ℕ}
    (hd : triLevel r L ≤ d) : LabBounded d L := by
  obtain ⟨h0, hlt1, hlt2, hf1, hf2, hf3⟩ := hL
  have hna : 0 < L.1.natAbs := Int.natAbs_pos.mpr h0
  have hle3 : L.2.2.natAbs ≤ d := le_trans (natAbs_le_labLevel _ _) hd
  refine ⟨⟨h0, by omega⟩, ⟨?_, by omega⟩, ⟨?_, hle3⟩⟩
  · exact fun h => by rw [h] at hlt1; simp only [Int.natAbs_zero] at hlt1; omega
  · exact fun h => by rw [h] at hlt2; simp only [Int.natAbs_zero] at hlt2; omega

theorem labVec_dotProduct_self (d : ℕ) {a : ℤ} (ha0 : a ≠ 0) :
    labVec d a ⬝ᵥ labVec d a = if a.natAbs ≤ d then 1 else 0 := by
  by_cases h : a.natAbs ≤ d
  · rw [if_pos h, labVec_dotProduct d ha0 ha0 h h, labDot, if_pos rfl]
  · rw [if_neg h, labVec_eq_zero_of_gt (by omega), zero_dotProduct]

theorem labVec_dotProduct_eq_zero (d : ℕ) {a b : ℤ} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hab : a.natAbs ≠ b.natAbs) : labVec d a ⬝ᵥ labVec d b = 0 := by
  by_cases h : a.natAbs ≤ d ∧ b.natAbs ≤ d
  · rw [labVec_dotProduct d ha0 hb0 h.1 h.2, labDot, if_neg (by omega), if_neg (by omega)]
  · rcases Nat.lt_or_ge d a.natAbs with hda | hda
    · rw [labVec_eq_zero_of_gt hda, zero_dotProduct]
    · rw [labVec_eq_zero_of_gt (show d < b.natAbs by by_contra hc; exact h ⟨hda, by omega⟩),
        dotProduct_zero]

theorem labBounded_of_dotProduct_self_eq_three {d : ℕ} {L : ℤ × ℤ × ℤ} (h0 : L.1 ≠ 0)
    (h1 : L.1.natAbs < L.2.1.natAbs) (h2 : L.2.1.natAbs < L.2.2.natAbs)
    (hL : labVec3 d L ⬝ᵥ labVec3 d L = 3) : LabBounded d L := by
  have hb0 : L.2.1 ≠ 0 := fun h => by rw [h] at h1; simp only [Int.natAbs_zero] at h1; omega
  have hc0 : L.2.2 ≠ 0 := fun h => by rw [h] at h2; simp only [Int.natAbs_zero] at h2; omega
  simp only [labVec3, add_dotProduct, dotProduct_add,
    labVec_dotProduct_self d h0, labVec_dotProduct_self d hb0, labVec_dotProduct_self d hc0,
    labVec_dotProduct_eq_zero d h0 hb0 (by omega : L.1.natAbs ≠ L.2.1.natAbs),
    labVec_dotProduct_eq_zero d h0 hc0 (by omega : L.1.natAbs ≠ L.2.2.natAbs),
    labVec_dotProduct_eq_zero d hb0 h0 (by omega : L.2.1.natAbs ≠ L.1.natAbs),
    labVec_dotProduct_eq_zero d hb0 hc0 (by omega : L.2.1.natAbs ≠ L.2.2.natAbs),
    labVec_dotProduct_eq_zero d hc0 h0 (by omega : L.2.2.natAbs ≠ L.1.natAbs),
    labVec_dotProduct_eq_zero d hc0 hb0 (by omega : L.2.2.natAbs ≠ L.2.1.natAbs),
    add_zero, zero_add] at hL
  refine ⟨⟨h0, ?_⟩, ⟨hb0, ?_⟩, ⟨hc0, ?_⟩⟩ <;>
    (split at hL <;> split at hL <;> split at hL <;> omega)

theorem IsNormalTri.labBounded_of_dotProduct_self {r d : ℕ} {L : ℤ × ℤ × ℤ}
    (hL : IsNormalTri r L) (h : labVec3 d L ⬝ᵥ labVec3 d L = 3) : LabBounded d L :=
  labBounded_of_dotProduct_self_eq_three hL.1 hL.2.1 hL.2.2.1 h

@[expose] def freshTriples (r : ℕ) : List (ℤ × ℤ × ℤ) :=
  ((oldLabels r).flatMap fun c => (oldLabels (c.natAbs - 1)).flatMap fun b =>
      (oldLabels (b.natAbs - 1)).map fun a => (a, b, c)) ++
  (((oldLabels r).flatMap fun b => (oldLabels (b.natAbs - 1)).map fun a =>
      (a, b, (r : ℤ) + 1)) ++
  (((oldLabels r).map fun a => (a, (r : ℤ) + 1, (r : ℤ) + 2)) ++
  [((r : ℤ) + 1, (r : ℤ) + 2, (r : ℤ) + 3)]))

theorem mem_freshTriples_of_isNormalTri {r : ℕ} {L : ℤ × ℤ × ℤ} (hL : IsNormalTri r L) :
    L ∈ freshTriples r := by
  obtain ⟨h0, hlt1, hlt2, hf1, hf2, hf3⟩ := hL
  have hna : 0 < L.1.natAbs := Int.natAbs_pos.mpr h0
  have hb0 : L.2.1 ≠ 0 := fun h => by rw [h] at hlt1; simp only [Int.natAbs_zero] at hlt1; omega
  have hc0 : L.2.2 ≠ 0 := fun h => by rw [h] at hlt2; simp only [Int.natAbs_zero] at hlt2; omega
  have hLeq : (L.1, L.2.1, L.2.2) = L := rfl
  rw [freshTriples]
  rcases hf1 with hA | hA
  · have hlev1 : labLevel r L.1 = r := by rw [labLevel]; omega
    rw [hlev1] at hf2
    rcases hf2 with hB | hB
    · have hlev2 : labLevel (labLevel r L.1) L.2.1 = r := by rw [hlev1, labLevel]; omega
      rw [hlev2] at hf3
      rcases hf3 with hC | hC
      · exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨L.2.2, mem_oldLabels.mpr ⟨hc0, hC⟩,
          List.mem_flatMap.mpr ⟨L.2.1, mem_oldLabels.mpr ⟨hb0, by omega⟩,
            List.mem_map.mpr ⟨L.1, mem_oldLabels.mpr ⟨h0, by omega⟩, hLeq⟩⟩⟩)
      · exact List.mem_append_right _ (List.mem_append_left _ (List.mem_flatMap.mpr
          ⟨L.2.1, mem_oldLabels.mpr ⟨hb0, hB⟩, List.mem_map.mpr
            ⟨L.1, mem_oldLabels.mpr ⟨h0, by omega⟩, by rw [← hC]⟩⟩))
    · have hlev2 : labLevel (labLevel r L.1) L.2.1 = r + 1 := by rw [hlev1, labLevel]; omega
      rw [hlev2] at hf3
      have hC : L.2.2 = (r : ℤ) + 2 := by rcases hf3 with h | h <;> omega
      exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _
        (List.mem_map.mpr ⟨L.1, mem_oldLabels.mpr ⟨h0, hA⟩, by rw [← hB, ← hC]⟩)))
  · have hlev1 : labLevel r L.1 = r + 1 := by rw [labLevel]; omega
    rw [hlev1] at hf2
    have hB : L.2.1 = (r : ℤ) + 2 := by rcases hf2 with h | h <;> omega
    have hlev2 : labLevel (labLevel r L.1) L.2.1 = r + 2 := by rw [hlev1, labLevel]; omega
    rw [hlev2] at hf3
    have hC : L.2.2 = (r : ℤ) + 3 := by rcases hf3 with h | h <;> omega
    exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
      (List.mem_singleton.mpr (by rw [← hLeq, hA, hB, hC]))))

private theorem sum_card_three {α : Type*} [AddCommMonoid α] {d : ℕ} (S : Finset (Fin d))
    (h : #S = 3) (f : Fin d → α) :
    ∑ k ∈ S, f k =
      f (S.orderIsoOfFin h 0) + f (S.orderIsoOfFin h 1) + f (S.orderIsoOfFin h 2) := by
  rw [← Finset.sum_coe_sort S f, ← Equiv.sum_comp (S.orderIsoOfFin h).toEquiv, Fin.sum_univ_three]
  rfl

theorem exists_sorted_support {d : ℕ} (u : Fin d → ℤ)
    (hcard : #({i | u i ≠ 0} : Finset (Fin d)) = 3) :
    ∃ i₀ i₁ i₂ : Fin d, (i₀ : ℕ) < (i₁ : ℕ) ∧ (i₁ : ℕ) < (i₂ : ℕ) ∧
      u i₀ ≠ 0 ∧ u i₁ ≠ 0 ∧ u i₂ ≠ 0 ∧
      u = Pi.single i₀ (u i₀) + Pi.single i₁ (u i₁) + Pi.single i₂ (u i₂) := by
  have h1 : u = ∑ k ∈ ({i | u i ≠ 0} : Finset (Fin d)), Pi.single k (u k) := by
    funext m
    rw [Finset.sum_apply, Finset.sum_pi_single]
    by_cases h : u m = 0 <;> simp [h]
  have hkey := sum_card_three ({i | u i ≠ 0} : Finset (Fin d)) hcard fun k => Pi.single k (u k)
  set e := ({i | u i ≠ 0} : Finset (Fin d)).orderIsoOfFin hcard with he
  have hmem : ∀ j : Fin 3, u (e j : Fin d) ≠ 0 := fun j => by
    have h := (e j).2
    rw [Finset.mem_filter] at h
    exact h.2
  exact ⟨e 0, e 1, e 2, by exact_mod_cast e.strictMono (a := 0) (b := 1) (by decide),
    by exact_mod_cast e.strictMono (a := 1) (b := 2) (by decide), hmem 0, hmem 1, hmem 2,
    h1.trans hkey⟩

theorem exists_normalTri_labVec3_eq {d : ℕ} {u : Fin d → ℤ} (hu : u ⬝ᵥ u = 3) :
    ∃ L : ℤ × ℤ × ℤ, L.1 ≠ 0 ∧ L.1.natAbs < L.2.1.natAbs ∧ L.2.1.natAbs < L.2.2.natAbs ∧
      L.2.2.natAbs ≤ d ∧ u = labVec3 d L := by
  classical
  have hsq : ∀ i : Fin d, u i ≠ 0 → u i = 1 ∨ u i = -1 := by
    intro i hi
    have hmem : i ∈ (Finset.univ : Finset (Fin d)) := Finset.mem_univ i
    have hle : u i * u i ≤ 3 := by
      rw [← hu, dotProduct]
      exact Finset.single_le_sum (f := fun k => u k * u k)
        (fun k _ => mul_self_nonneg (u k)) hmem
    have h1 : u i ≠ 0 := hi
    rcases lt_trichotomy (u i) 0 with h | h | h
    · right; nlinarith
    · exact absurd h h1
    · left; nlinarith
  have hcard : #({i | u i ≠ 0} : Finset (Fin d)) = 3 := by
    have hsum : ∑ k, u k * u k = ∑ k ∈ ({i | u i ≠ 0} : Finset (Fin d)), (1 : ℤ) := by
      rw [← Finset.sum_filter_ne_zero (Finset.univ : Finset (Fin d))
        (f := fun k => u k * u k)]
      refine Finset.sum_congr ?_ fun k hk => ?_
      · refine Finset.filter_congr fun k _ => ?_
        constructor
        · intro h hz; exact h (by rw [hz]; ring)
        · intro h hz
          rcases mul_eq_zero.mp hz with h' | h' <;> exact h h'
      · rw [Finset.mem_filter] at hk
        rcases hsq k hk.2 with h | h <;> rw [h] <;> ring
    rw [Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
    rw [dotProduct] at hu
    have : ((#({i | u i ≠ 0} : Finset (Fin d)) : ℤ)) = 3 := by rw [← hsum, hu]
    omega
  obtain ⟨i₀, i₁, i₂, h01, h12, hu0, hu1, hu2, heq⟩ := exists_sorted_support u hcard
  refine ⟨(labOf i₀ (u i₀), labOf i₁ (u i₁), labOf i₂ (u i₂)),
    labOf_ne_zero i₀ (hsq i₀ hu0), ?_, ?_, ?_, ?_⟩
  · rw [natAbs_labOf i₀ (hsq i₀ hu0), natAbs_labOf i₁ (hsq i₁ hu1)]; omega
  · rw [natAbs_labOf i₁ (hsq i₁ hu1), natAbs_labOf i₂ (hsq i₂ hu2)]; omega
  · rw [natAbs_labOf i₂ (hsq i₂ hu2)]; omega
  · rw [labVec3, labVec_labOf i₀ (hsq i₀ hu0), labVec_labOf i₁ (hsq i₁ hu1),
      labVec_labOf i₂ (hsq i₂ hu2)]
    exact heq

@[expose] def labA : ℤ × ℤ × ℤ := (1, 2, 3)

@[expose] def labB : ℤ × ℤ × ℤ := (1, 4, 5)

@[expose] def labC : ℤ × ℤ × ℤ := (2, 4, 6)

@[expose] def labE : ℕ → ℤ × ℤ × ℤ
  | 1 => (1, 6, 7)
  | 2 => (2, 5, 7)
  | 3 => (3, 4, 7)
  | _ => (3, 5, 6)

theorem labE_cases (t : ℕ) : labE t = (1, 6, 7) ∨ labE t = (2, 5, 7) ∨ labE t = (3, 4, 7) ∨
    labE t = (3, 5, 6) := by
  match t with
  | 1 => exact Or.inl rfl
  | 2 => exact Or.inr (Or.inl rfl)
  | 3 => exact Or.inr (Or.inr (Or.inl rfl))
  | 0 => exact Or.inr (Or.inr (Or.inr rfl))
  | (n + 4) => exact Or.inr (Or.inr (Or.inr rfl))

theorem labBounded_labA {d : ℕ} (hd : 7 ≤ d) : LabBounded d labA := by
  rw [LabBounded, labA]
  exact ⟨⟨by decide, by simpa using by omega⟩, ⟨by decide, by simpa using by omega⟩,
    ⟨by decide, by simpa using by omega⟩⟩

theorem labBounded_labB {d : ℕ} (hd : 7 ≤ d) : LabBounded d labB := by
  rw [LabBounded, labB]
  exact ⟨⟨by decide, by simpa using by omega⟩, ⟨by decide, by simpa using by omega⟩,
    ⟨by decide, by simpa using by omega⟩⟩

theorem labBounded_labC {d : ℕ} (hd : 7 ≤ d) : LabBounded d labC := by
  rw [LabBounded, labC]
  exact ⟨⟨by decide, by simpa using by omega⟩, ⟨by decide, by simpa using by omega⟩,
    ⟨by decide, by simpa using by omega⟩⟩

theorem labBounded_labE {d : ℕ} (hd : 7 ≤ d) (t : ℕ) : LabBounded d (labE t) := by
  rcases labE_cases t with h | h | h | h <;> rw [LabBounded, h] <;>
    exact ⟨⟨by decide, by simpa using by omega⟩, ⟨by decide, by simpa using by omega⟩,
      ⟨by decide, by simpa using by omega⟩⟩

@[expose] def defectTable : List (ℕ × (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ)) :=
  [(1, (3, 8, 9), (5, 8, 10), (6, -7, 8)),
   (1, (3, 8, 9), (5, 9, 10), (6, -7, 9)),
   (1, (3, 8, 9), (-2, 3, 4), (4, -5, 8)),
   (1, (3, 8, 9), (-2, 3, 4), (4, -5, 9)),
   (1, (2, -4, 5), (5, 8, 9), (2, -3, 8)),
   (1, (2, -4, 5), (5, 8, 9), (2, -3, 9)),
   (2, (3, 8, 9), (4, -6, 8), (-1, 3, 4)),
   (2, (3, 8, 9), (4, -6, 9), (-1, 3, 4)),
   (2, (3, 8, 9), (5, -7, 8), (6, 8, 10)),
   (2, (3, 8, 9), (5, -7, 9), (6, 9, 10)),
   (2, (1, -4, 6), (1, -3, 8), (6, 8, 9)),
   (3, (1, -5, 8), (1, -2, 6), (6, 8, 9)),
   (3, (2, -6, 8), (5, 8, 9), (-1, 2, 5)),
   (3, (3, -7, 8), (5, 8, 9), (6, 8, 10))]

theorem length_defectTable : defectTable.length = 14 := by rw [defectTable]; rfl

theorem labVec3_labA (d : ℕ) (hd : 3 ≤ d) :
    labVec3 d labA = Pi.single ⟨0, by omega⟩ 1 + Pi.single ⟨1, by omega⟩ 1
      + Pi.single ⟨2, by omega⟩ 1 := by
  have h : labA = (labOf (⟨0, by omega⟩ : Fin d) 1, labOf (⟨1, by omega⟩ : Fin d) 1,
      labOf (⟨2, by omega⟩ : Fin d) 1) := by
    rw [labA, Prod.ext_iff, Prod.ext_iff]
    refine ⟨?_, ?_, ?_⟩ <;> rw [labOf_one] <;> norm_num
  rw [h, labVec3_of_labOf _ _ _ (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)]

@[expose] def IsDefectRowU (t : ℕ) (U : ℤ × ℤ × ℤ) : Prop :=
  triDot U labA = 1 ∧ triDot U labB = 0 ∧ triDot U labC = 0 ∧ triDot U (labE t) = 0

instance (t : ℕ) (U : ℤ × ℤ × ℤ) : Decidable (IsDefectRowU t U) :=
  decidable_of_iff (triDot U labA = 1 ∧ triDot U labB = 0 ∧ triDot U labC = 0 ∧
    triDot U (labE t) = 0) Iff.rfl

@[expose] def IsDefectRowV (t : ℕ) (U V : ℤ × ℤ × ℤ) : Prop :=
  triDot V labB = 1 ∧ triDot V labA = 0 ∧ triDot V labC = 0 ∧ triDot V (labE t) = 0 ∧
    triDot U V = 1

instance (t : ℕ) (U V : ℤ × ℤ × ℤ) : Decidable (IsDefectRowV t U V) :=
  decidable_of_iff (triDot V labB = 1 ∧ triDot V labA = 0 ∧ triDot V labC = 0 ∧
    triDot V (labE t) = 0 ∧ triDot U V = 1) Iff.rfl

@[expose] def IsDefectRowW (t : ℕ) (U V W : ℤ × ℤ × ℤ) : Prop :=
  triDot W labC = 1 ∧ triDot W labA = 0 ∧ triDot W labB = 0 ∧ triDot W (labE t) = 0 ∧
    triDot U W = 1 ∧ triDot V W = 1

instance (t : ℕ) (U V W : ℤ × ℤ × ℤ) : Decidable (IsDefectRowW t U V W) :=
  decidable_of_iff (triDot W labC = 1 ∧ triDot W labA = 0 ∧ triDot W labB = 0 ∧
    triDot W (labE t) = 0 ∧ triDot U W = 1 ∧ triDot V W = 1) Iff.rfl

set_option synthInstance.maxSize 1024

private theorem defect_enum_one : ∀ U ∈ freshTriples 7, IsDefectRowU 1 U →
    ∀ V ∈ freshTriples (triLevel 7 U), IsDefectRowV 1 U V →
    ∀ W ∈ freshTriples (triLevel (triLevel 7 U) V), IsDefectRowW 1 U V W →
    (1, U, V, W) ∈ defectTable := by decide +kernel

private theorem defect_enum_two : ∀ U ∈ freshTriples 7, IsDefectRowU 2 U →
    ∀ V ∈ freshTriples (triLevel 7 U), IsDefectRowV 2 U V →
    ∀ W ∈ freshTriples (triLevel (triLevel 7 U) V), IsDefectRowW 2 U V W →
    (2, U, V, W) ∈ defectTable := by decide +kernel

private theorem defect_enum_three : ∀ U ∈ freshTriples 7, IsDefectRowU 3 U →
    ∀ V ∈ freshTriples (triLevel 7 U), IsDefectRowV 3 U V →
    ∀ W ∈ freshTriples (triLevel (triLevel 7 U) V), IsDefectRowW 3 U V W →
    (3, U, V, W) ∈ defectTable := by decide +kernel

private theorem defect_enum_four : ∀ U ∈ freshTriples 7, IsDefectRowU 4 U →
    ∀ V ∈ freshTriples (triLevel 7 U), IsDefectRowV 4 U V →
    ∀ W ∈ freshTriples (triLevel (triLevel 7 U) V), IsDefectRowW 4 U V W →
    (4, U, V, W) ∈ defectTable := by decide +kernel

theorem forall_mem_defectTable_isNormalTri_and_isDefectRow :
    ∀ q ∈ defectTable, (q.1 = 1 ∨ q.1 = 2 ∨ q.1 = 3 ∨ q.1 = 4) ∧
      IsNormalTri 7 q.2.1 ∧ IsNormalTri (triLevel 7 q.2.1) q.2.2.1 ∧
      IsNormalTri (triLevel (triLevel 7 q.2.1) q.2.2.1) q.2.2.2 ∧
      IsDefectRowU q.1 q.2.1 ∧ IsDefectRowV q.1 q.2.1 q.2.2.1 ∧
      IsDefectRowW q.1 q.2.1 q.2.2.1 q.2.2.2 := by decide

theorem defectTriple_mem_defectTable {t : ℕ} (ht : t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4)
    {U V W : ℤ × ℤ × ℤ} (hU : IsNormalTri 7 U) (hV : IsNormalTri (triLevel 7 U) V)
    (hW : IsNormalTri (triLevel (triLevel 7 U) V) W)
    (hrU : IsDefectRowU t U) (hrV : IsDefectRowV t U V) (hrW : IsDefectRowW t U V W) :
    (t, U, V, W) ∈ defectTable := by
  have hmU := mem_freshTriples_of_isNormalTri hU
  have hmV := mem_freshTriples_of_isNormalTri hV
  have hmW := mem_freshTriples_of_isNormalTri hW
  rcases ht with rfl | rfl | rfl | rfl
  · exact defect_enum_one U hmU hrU V hmV hrV W hmW hrW
  · exact defect_enum_two U hmU hrU V hmV hrV W hmW hrW
  · exact defect_enum_three U hmU hrU V hmV hrV W hmW hrW
  · exact defect_enum_four U hmU hrU V hmV hrV W hmW hrW

theorem defect_mem_defectTable {d : ℕ} (hd : 10 ≤ d) {t : ℕ}
    (ht : t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4) {u v w : Fin d → ℤ} {U V W : ℤ × ℤ × ℤ}
    (hU : IsNormalTri 7 U) (hV : IsNormalTri (triLevel 7 U) V)
    (hW : IsNormalTri (triLevel (triLevel 7 U) V) W)
    (huU : u = labVec3 d U) (hvV : v = labVec3 d V) (hwW : w = labVec3 d W)
    (hu : u ⬝ᵥ u = 3) (hv : v ⬝ᵥ v = 3) (hw : w ⬝ᵥ w = 3)
    (huA : u ⬝ᵥ labVec3 d labA = 1) (huB : u ⬝ᵥ labVec3 d labB = 0)
    (huC : u ⬝ᵥ labVec3 d labC = 0) (huE : u ⬝ᵥ labVec3 d (labE t) = 0)
    (hvB : v ⬝ᵥ labVec3 d labB = 1) (hvA : v ⬝ᵥ labVec3 d labA = 0)
    (hvC : v ⬝ᵥ labVec3 d labC = 0) (hvE : v ⬝ᵥ labVec3 d (labE t) = 0) (huv : u ⬝ᵥ v = 1)
    (hwC : w ⬝ᵥ labVec3 d labC = 1) (hwA : w ⬝ᵥ labVec3 d labA = 0)
    (hwB : w ⬝ᵥ labVec3 d labB = 0) (hwE : w ⬝ᵥ labVec3 d (labE t) = 0)
    (huw : u ⬝ᵥ w = 1) (hvw : v ⬝ᵥ w = 1) :
    (t, U, V, W) ∈ defectTable := by
  subst huU hvV hwW
  have hbU : LabBounded d U := hU.labBounded_of_dotProduct_self hu
  have hbV : LabBounded d V := hV.labBounded_of_dotProduct_self hv
  have hbW : LabBounded d W := hW.labBounded_of_dotProduct_self hw
  have hbA : LabBounded d labA := labBounded_labA (by omega)
  have hbB : LabBounded d labB := labBounded_labB (by omega)
  have hbC : LabBounded d labC := labBounded_labC (by omega)
  have hbE : LabBounded d (labE t) := labBounded_labE (by omega) t
  refine defectTriple_mem_defectTable ht hU hV hW
    ⟨?_, ?_, ?_, ?_⟩ ⟨?_, ?_, ?_, ?_, ?_⟩ ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← labVec3_dotProduct hbU hbA]; exact huA
  · rw [← labVec3_dotProduct hbU hbB]; exact huB
  · rw [← labVec3_dotProduct hbU hbC]; exact huC
  · rw [← labVec3_dotProduct hbU hbE]; exact huE
  · rw [← labVec3_dotProduct hbV hbB]; exact hvB
  · rw [← labVec3_dotProduct hbV hbA]; exact hvA
  · rw [← labVec3_dotProduct hbV hbC]; exact hvC
  · rw [← labVec3_dotProduct hbV hbE]; exact hvE
  · rw [← labVec3_dotProduct hbU hbV]; exact huv
  · rw [← labVec3_dotProduct hbW hbC]; exact hwC
  · rw [← labVec3_dotProduct hbW hbA]; exact hwA
  · rw [← labVec3_dotProduct hbW hbB]; exact hwB
  · rw [← labVec3_dotProduct hbW hbE]; exact hwE
  · rw [← labVec3_dotProduct hbU hbW]; exact huw
  · rw [← labVec3_dotProduct hbV hbW]; exact hvw

end CFSG.FeitThompson
