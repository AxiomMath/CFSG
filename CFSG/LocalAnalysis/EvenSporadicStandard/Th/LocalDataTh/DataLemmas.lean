module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalDataTh.Data

public section

namespace CFSG.EvenSporadicStandard.ThStd.LocalDataTh

open CFSG.Sporadic.Th.Max3
open scoped Matrix

theorem B1_eq : B1 = matOfCols 8 B1c := by decide

theorem B2_eq : B2 = matOfCols 8 B2c := by decide

theorem matOfCols_idCols : matOfCols 8 (idCols 8) = 1 := by decide

theorem matOfCols_letterCols (l : Gen) : matOfCols 8 (letterCols l) = Gen.eval B1 B2 l := by
  cases l
  · exact B1_eq.symm
  · exact B2_eq.symm

theorem matOfCols_wordCols (w : List Gen) : matOfCols 8 (wordCols w) = wordMat w := by
  induction w with
  | nil => simpa [wordCols, wordMat] using matOfCols_idCols
  | cons l w ih =>
    have e : wordCols (l :: w) = mulCols 8 (letterCols l) (wordCols w) := by
      simp [wordCols]
    rw [e, matOfCols_mulCols, matOfCols_letterCols, ih]
    simp [wordMat]

theorem mem_Pt_iff {T : Mat8} : T ∈ Pt ↔ ∃ a ∈ Pc, matOfCols 8 a = T := by
  simp [Pt]

theorem wordMat_mem_Pt {s : String} (hs : s ∈ pWordStrings) : wordMat (wordOfString s) ∈ Pt :=
  mem_Pt_iff.2 ⟨wordCols (wordOfString s), List.mem_map.2 ⟨s, hs, rfl⟩,
    matOfCols_wordCols _⟩

theorem exists_word_of_mem_Pt {T : Mat8} (hT : T ∈ Pt) :
    ∃ s ∈ pWordStrings, wordMat (wordOfString s) = T := by
  obtain ⟨a, ha, rfl⟩ := mem_Pt_iff.1 hT
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ha
  exact ⟨s, hs, (matOfCols_wordCols _).symm⟩

theorem foldl_xor_lt (cs : List ℕ) (hcs : ∀ x ∈ cs, x < 256) (v : ℕ) (l : List ℕ) (a : ℕ)
    (ha : a < 256) :
    l.foldl (fun acc j => if v.testBit j then acc ^^^ cs.getD j 0 else acc) a < 256 := by
  induction l generalizing a with
  | nil => exact ha
  | cons j l ih =>
    refine ih _ ?_
    show (if v.testBit j = true then a ^^^ cs.getD j 0 else a) < 256
    by_cases hj : v.testBit j = true
    · rw [ite_eq_left hj]
      have hc : cs.getD j 0 < 256 := by
        rw [List.getD_eq_getElem?_getD]
        rcases h : cs[j]? with _ | c
        · simp
        · exact hcs c (List.mem_of_getElem? h)
      exact Nat.xor_lt_two_pow (n := 8) ha hc
    · rw [ite_eq_right hj]
      exact ha

theorem applyCols_lt {a : List ℕ} (ha : ∀ x ∈ a, x < 256) (v : ℕ) : applyCols 8 a v < 256 :=
  foldl_xor_lt a ha v _ 0 (by norm_num)

theorem Kc_lt : ∀ (k : ℕ), ∀ c ∈ Kc k, c < 256
  | 0, c, hc => by
    simp only [Kc, List.mem_singleton] at hc
    omega
  | k + 1, c, hc => by
    simp only [Kc, Kstep, List.mem_filter, List.mem_range] at hc
    exact hc.1

theorem mem_Kc_succ {k c : ℕ} :
    c ∈ Kc (k + 1) ↔ c < 256 ∧ ∀ a ∈ Pc, (applyCols 8 a c ^^^ c) ∈ Kc k := by
  simp [Kc, Kstep, List.mem_filter, List.mem_range]

@[expose] def Ksem (k : ℕ) : Set Vec := {v | ∃ c ∈ Kc k, codeVec 8 c = v}

theorem Ksem_zero {v : Vec} : v ∈ Ksem 0 ↔ v = 0 := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    simp only [Kc, List.mem_singleton] at hc
    rw [hc, codeVec_zero]
  · rintro rfl
    exact ⟨0, by simp [Kc], codeVec_zero 8⟩

theorem codeVec_inj_of_lt {a b : ℕ} (ha : a < 256) (hb : b < 256)
    (h : codeVec 8 a = codeVec 8 b) : a = b :=
  codeVec_injOn 8 (by simpa using ha) (by simpa using hb) h

theorem add_one_mulVec_codeVec {a : List ℕ} (c : ℕ) :
    (matOfCols 8 a + 1) *ᵥ codeVec 8 c = codeVec 8 (applyCols 8 a c ^^^ c) := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, matOfCols_mulVec, codeVec_xor]

theorem Ksem_step (hwf : ∀ a ∈ Pc, ∀ x ∈ a, x < 256) (k : ℕ) (v : Vec) :
    (∀ T ∈ Pt, (T + 1) *ᵥ v ∈ Ksem k) ↔ v ∈ Ksem (k + 1) := by
  obtain ⟨c₀, hc₀, rfl⟩ := exists_codeVec 8 v
  have hc₀' : c₀ < 256 := by simpa using hc₀
  constructor
  · intro h
    refine ⟨c₀, mem_Kc_succ.2 ⟨hc₀', fun a ha => ?_⟩, rfl⟩
    have h1 := h (matOfCols 8 a) (mem_Pt_iff.2 ⟨a, ha, rfl⟩)
    rw [add_one_mulVec_codeVec] at h1
    obtain ⟨d, hd, hdeq⟩ := h1
    have hlt : applyCols 8 a c₀ ^^^ c₀ < 256 :=
      Nat.xor_lt_two_pow (n := 8) (applyCols_lt (hwf a ha) c₀) hc₀'
    rwa [← codeVec_inj_of_lt (Kc_lt k d hd) hlt hdeq]
  · rintro ⟨c, hc, hce⟩ T hT
    obtain ⟨a, ha, rfl⟩ := mem_Pt_iff.1 hT
    have hcc : c = c₀ := codeVec_inj_of_lt (Kc_lt _ c hc) hc₀' hce
    subst hcc
    obtain ⟨-, hstep⟩ := mem_Kc_succ.1 hc
    exact ⟨_, hstep a ha, (add_one_mulVec_codeVec c).symm⟩

end CFSG.EvenSporadicStandard.ThStd.LocalDataTh
