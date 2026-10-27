module

public import Certificates.Data.Kernel.SmithL6KEa
public import CFSG.Mathlib.Decide.Nodup
public import CFSG.Certificates.Kernel.SmithL6KWedge

public section

namespace CFSG.SmithL6.K

open CFSG.SmithL6
open CFSG.SmithE (applyCols)

theorem split_SR {c : Nat} (hc : c < 2 ^ 20) : (c &&& 983055) ^^^ (c &&& 65520) = c := by
  rw [← Nat.and_xor_distrib_left, (by decide : (983055 ^^^ 65520 : Nat) = 2 ^ 20 - 1),
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hc]

theorem applyCols_S {A : Array Nat} (hA : ∀ m ∈ eaBits, applyCols A (2 ^ m) = 2 ^ m) :
    ∀ c < 2 ^ 20, applyCols A (c &&& 983055) = c &&& 983055 := by
  refine xorAdd_ext (F := fun c => applyCols A (c &&& 983055)) (G := fun c => c &&& 983055)
    (fun a b => by simp only [Nat.and_xor_distrib_right, applyCols_xorL])
    (fun a b => Nat.and_xor_distrib_right) 20 fun m hm => ?_
  have key : ∀ m < 20, (2 ^ m &&& 983055 = 2 ^ m ∧ m ∈ eaBits) ∨ 2 ^ m &&& 983055 = 0 := by
    decide
  rcases key m hm with ⟨h1, h2⟩ | h1
  · simp only [h1]
    exact hA m h2
  · simp only [h1, applyCols_zeroL]

theorem low_parts (c : Nat) : c &&& 65520 = 16 * ((c &&& 65520) / 16) ∧ (c &&& 65520) / 16 < 4096 := by
  have h1 : (c &&& 65520) % 16 = 0 := by
    have e : (65520 : Nat) &&& (2 ^ 4 - 1) = 0 := by decide
    rw [(by decide : (16 : Nat) = 2 ^ 4), ← Nat.and_two_pow_sub_one_eq_mod, Nat.and_assoc, e,
      Nat.and_zero]
  have h2 : c &&& 65520 ≤ 65520 := Nat.and_le_right
  omega

theorem xor_left_inj' {a x y : Nat} (h : a ^^^ x = a ^^^ y) : x = y := by
  have := congrArg (a ^^^ ·) h
  simp only [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] at this
  exact this

theorem supp_iff {c : Nat} (hc : c < 2 ^ 20) : eaSupp c = true ↔ c &&& 65520 = 0 := by
  have hR : ∀ m < 20, (65520 : Nat).testBit m = !eaBits.contains m := by decide
  unfold eaSupp
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true']
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.zero_testBit]
    by_cases hi : i < 20
    · rcases h i hi with h | h
      · rw [hR i hi, h]
        simp
      · rw [h]
        simp
    · have : (65520 : Nat).testBit i = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le (by decide : (65520 : Nat) < 2 ^ 20)
          (Nat.pow_le_pow_right (by decide) (by omega)))
      rw [this]
      simp
  · intro h m hm
    cases hb : eaBits.contains m
    · right
      have e := congrArg (fun x => x.testBit m) h
      simp only [Nat.testBit_and, Nat.zero_testBit, hR m hm, hb] at e
      simpa using e
    · left
      rfl

theorem fixed_iff_supp {A B : Array Nat} (hA : ∀ m ∈ eaBits, applyCols A (2 ^ m) = 2 ^ m)
    (hB : ∀ m ∈ eaBits, applyCols B (2 ^ m) = 2 ^ m)
    (hlow : ∀ j < 4096, (applyCols A (16 * j) = 16 * j ∧ applyCols B (16 * j) = 16 * j) ↔ j = 0)
    {c : Nat} (hc : c < 2 ^ 20) :
    (applyCols A c = c ∧ applyCols B c = c) ↔ eaSupp c = true := by
  obtain ⟨hr, hj⟩ := low_parts c
  have key : ∀ {M : Array Nat}, (∀ m ∈ eaBits, applyCols M (2 ^ m) = 2 ^ m) →
      (applyCols M c = c ↔ applyCols M (c &&& 65520) = c &&& 65520) := by
    intro M hM
    have e : applyCols M c = (c &&& 983055) ^^^ applyCols M (c &&& 65520) := by
      conv_lhs => rw [← split_SR hc]
      rw [applyCols_xorL, applyCols_S hM c hc]
    rw [e]
    constructor
    · intro h
      conv_rhs at h => rw [← split_SR hc]
      exact xor_left_inj' h
    · intro h
      rw [h]
      exact split_SR hc
  rw [key hA, key hB, supp_iff hc, hr, hlow _ hj]
  omega

section Packed

variable {C I : Nat} (hC : ∀ k < 1953, fldW 12 C k = codeOf (tvPair k))
  (hI : ∀ n < 4096, fldW 11 I n = tvIdxTab[n]!)
include hC

theorem conjC_code {a b : Nat} (ha : a < 1953) (hb : b < 1953) :
    conjC (codeOf (tvPair a)) (codeOf (tvPair b)) = codeOf (tvPair (tvImg a b)) := by
  rw [conjC_codeOf (tvP_tvPair ha) (tvP_tvPair hb), tvPair_tvImg ha hb]

theorem eaRel_eq {a b : Nat} (ha : a < 1953) (hb : b < 1953) :
    eaRel a b = eaRelC (fldW 12 C a) (fldW 12 C b) := by
  rw [hC a ha, hC b hb]
  have i1 : a = b ↔ codeOf (tvPair a) = codeOf (tvPair b) :=
    ⟨fun h => congrArg (fun x => codeOf (tvPair x)) h, codeOf_tvPair_inj ha hb⟩
  have i2 : tvImg a b = b ↔ conjC (codeOf (tvPair a)) (codeOf (tvPair b)) = codeOf (tvPair b) := by
    rw [conjC_code hC ha hb]
    exact ⟨fun h => congrArg (fun x => codeOf (tvPair x)) h,
      codeOf_tvPair_inj (tvImg_lt ha hb) hb⟩
  have i3 : tvImg a b = tvImg b a ↔ conjC (codeOf (tvPair a)) (codeOf (tvPair b)) =
      conjC (codeOf (tvPair b)) (codeOf (tvPair a)) := by
    rw [conjC_code hC ha hb, conjC_code hC hb ha]
    exact ⟨fun h => congrArg (fun x => codeOf (tvPair x)) h,
      codeOf_tvPair_inj (tvImg_lt ha hb) (tvImg_lt hb ha)⟩
  unfold eaRel eaRelC
  simp only [i1, i2, i3]

include hI

theorem eaI_eq : eaI = eaIK C I := by
  unfold eaI eaIK
  refine List.filter_congr fun p hp => ?_
  have hp' := List.mem_range.mp hp
  rw [tvImgP_eq hC hI hp' (a := 0) (by decide), tvImgP_eq hC hI hp' (a := 31) (by decide)]

theorem mem_eaBase_lt {f : Nat} (hf : f ∈ eaBase) : f < 1953 := by
  unfold eaBase at hf
  rw [eaI_eq hC hI] at hf
  simp only [List.mem_cons] at hf
  rcases hf with rfl | rfl | hf
  · decide
  · decide
  · unfold eaIK at hf
    exact List.mem_range.mp (List.mem_filter.mp hf).1

theorem mem_eaF1 {G : List Nat} (h : rig1K C I G = true) {g : Nat} (hg : g ∈ G) :
    g < 1953 ∧ g ∈ eaF1 := by
  unfold rig1K at h
  simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hg1, h2⟩ := h g hg
  refine ⟨hg1, ?_⟩
  unfold eaF1
  refine List.mem_filter.mpr ⟨List.mem_range.mpr hg1, ?_⟩
  unfold eaUniq
  rw [List.all_eq_true]
  intro q hq
  have h3 := h2 q hq
  have hq' := List.mem_range.mp hq
  rw [Bool.or_eq_true] at h3 ⊢
  refine h3.imp id fun h4 => ?_
  rw [List.any_eq_true] at h4 ⊢
  obtain ⟨f, hf, hne⟩ := h4
  have hfb : f ∈ eaBase := by
    unfold eaBase
    rw [eaI_eq hC hI]
    exact hf
  have hf' := mem_eaBase_lt hC hI hfb
  refine ⟨f, hfb, ?_⟩
  rw [eaRel_eq hC hg1 hf', eaRel_eq hC hq' hf']
  exact hne

omit hC hI in
theorem prof_inj {G : List Nat}
    (h : CFSG.Decide.bitsetNodup ((List.range 1953).map (profKey C G)) = true) {q q' : Nat}
    (hq : q < 1953) (hq' : q' < 1953) (hp : profC C G q = profC C G q') : q = q' := by
  have hk : profKey C G q = profKey C G q' := by
    unfold profKey
    rw [hp]
  exact List.inj_on_of_nodup_map (CFSG.Decide.nodup_of_bitsetNodup_nat h)
    (List.mem_range.mpr hq) (List.mem_range.mpr hq') hk

theorem chkRig_of {G : List Nat} (h1 : rig1K C I G = true)
    (h2 : CFSG.Decide.bitsetNodup ((List.range 1953).map (profKey C G)) = true) :
    eaChkRig = true := by
  unfold eaChkRig
  rw [List.all_eq_true]
  intro q hq
  have hq1 := List.mem_range.mp hq
  unfold eaUniq
  rw [List.all_eq_true]
  intro q' hq'
  have hq1' := List.mem_range.mp hq'
  rw [Bool.or_eq_true, beq_iff_eq]
  by_cases e : q' = q
  · exact Or.inl e
  · right
    have hne : profC C G q ≠ profC C G q' := fun hp => e (prof_inj h2 hq1 hq1' hp).symm
    have : ∃ g ∈ G, eaRelC (fldW 12 C q) (fldW 12 C g) ≠ eaRelC (fldW 12 C q') (fldW 12 C g) := by
      by_contra hall
      push Not at hall
      exact hne (List.map_congr_left hall)
    obtain ⟨g, hg, hd⟩ := this
    obtain ⟨hg1, hg2⟩ := mem_eaF1 hC hI h1 hg
    rw [List.any_eq_true]
    refine ⟨g, hg2, ?_⟩
    rw [eaRel_eq hC hq1 hg1, eaRel_eq hC hq1' hg1]
    exact bne_iff_ne.mpr hd

end Packed

end CFSG.SmithL6.K
