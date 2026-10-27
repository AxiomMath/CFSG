module

public import Certificates.Certificate24217
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalDataTh.TransvAa
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.ThStd.LocalDataTh

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 CFSG.Sporadic.Th.Native CFSG.Sporadic.ThSchreier
open scoped Matrix

section Codes

theorem tfacts_spec (h : TFacts = true) {cs : List ℕ} (hcs : cs ∈ allMat4)
    (h8 : 8 ≤ fixedCount cs) (hid : cs ≠ idCols 4) (hinv : invCode cs = true) :
    ∃ p ∈ convTab, p.1 = cs ∧ wf4 p.2 = true ∧ invCode p.2 = true ∧
      mulCols 4 p.2 T0cols = mulCols 4 cs p.2 := by
  have h1 := List.all_eq_true.1 h cs hcs
  rcases Bool.or_eq_true_iff.1 h1 with h2 | h2
  · exfalso
    have hA : decide (8 ≤ fixedCount cs) = true := decide_eq_true h8
    have hB : (cs != idCols 4) = true := bne_iff_ne.2 hid
    simp [hA, hB, hinv] at h2
  · obtain ⟨p, hp, hp2⟩ := List.any_eq_true.1 h2
    simp only [Bool.and_eq_true, beq_iff_eq] at hp2
    obtain ⟨⟨⟨h3, h4⟩, h5⟩, h6⟩ := hp2
    exact ⟨p, hp, h3, h4, h5, h6⟩

theorem mem_allMat4_of_wf4 {cs : List ℕ} (h : wf4 cs = true) : cs ∈ allMat4 := by
  obtain ⟨hl, hlt⟩ := Bool.and_eq_true_iff.1 h
  have hl' : cs.length = 4 := beq_iff_eq.1 hl
  have hlt' := List.all_eq_true.1 hlt
  match cs, hl' with
  | [a, b, c, d], _ =>
    simp only [allMat4, List.mem_flatMap, List.mem_range, List.mem_map]
    exact ⟨a, by simpa using hlt' a (by simp), b, by simpa using hlt' b (by simp), c,
      by simpa using hlt' c (by simp), d, by simpa using hlt' d (by simp), rfl⟩

theorem exists_codes (T : Matrix (Fin 4) (Fin 4) (ZMod 2)) :
    ∃ cs : List ℕ, cs ∈ allMat4 ∧ matOfCols 4 cs = T := by
  choose code hlt hcode using fun j : Fin 4 => exists_codeVec 4 (fun i => T i j)
  have hlt' : ∀ j, code j < 16 := fun j => lt_of_lt_of_eq (hlt j) (by norm_num)
  refine ⟨[code 0, code 1, code 2, code 3], ?_, ?_⟩
  · simp only [allMat4, List.mem_flatMap, List.mem_range, List.mem_map]
    exact ⟨code 0, hlt' 0, code 1, hlt' 1, code 2, hlt' 2, code 3, hlt' 3, rfl⟩
  · have hgetD : ∀ j : Fin 4, [code 0, code 1, code 2, code 3].getD (j : ℕ) 0 = code j := by
      intro j
      fin_cases j <;> rfl
    ext i j
    simp only [matOfCols, Matrix.of_apply, hgetD]
    have h1 := congrFun (hcode j) i
    simpa [codeVec] using h1

theorem invCode_of_inj {cs : List ℕ} (hT : ∀ e, matOfCols 4 cs *ᵥ e = 0 → e = 0) :
    invCode cs = true := by
  unfold invCode
  rw [List.all_eq_true]
  intro s hs
  rw [List.mem_range] at hs
  have hne : applyCols 4 cs (s + 1) ≠ 0 := by
    intro h0
    have h1 : matOfCols 4 cs *ᵥ codeVec 4 (s + 1) = 0 := by
      rw [matOfCols_mulVec, h0, codeVec_zero]
    have h2 := hT _ h1
    have h3 : codeVec 4 (s + 1) = codeVec 4 0 := by rw [h2, codeVec_zero]
    have h4 := codeVec_injOn 4 (by norm_num; omega) (by norm_num) h3
    omega
  simpa using hne

end Codes

section Light

theorem exists_acts {n : J} (h : ∀ x ∈ A, n * x * n⁻¹ ∈ A) :
    ∃ T : Matrix (Fin 4) (Fin 4) (ZMod 2), Acts n T := by
  have hcol : ∀ j : Fin 4, ∃ e : Vec4, cA e = n * aGen j * n⁻¹ := fun j =>
    exists_cA (h _ (aGen_mem j))
  choose col hcol using hcol
  refine ⟨Matrix.of fun i j => col j i, Acts.of_gens fun j => ?_⟩
  have : (Matrix.of fun i j => col j i) *ᵥ Pi.single j 1 = col j := by
    funext i
    simp
  rw [this]
  exact (hcol j).symm

theorem mem_B_of_acts_one {n : J} (h : Acts n 1) : n ∈ B := by
  rw [mem_B_iff]
  intro a ha
  obtain ⟨e, rfl⟩ := exists_cA ha
  have := h e
  rw [Matrix.one_mulVec] at this
  calc n * cA e = n * cA e * n⁻¹ * n := by group
    _ = cA e * n := by rw [this]

end Light

section Certified

theorem exists_conj_q1 {g : J}
    (hgA : ∀ a ∈ A, g * a * g⁻¹ ∈ A) (hgB : g ∉ B)
    (hH : ∃ H : Subgroup J, H ≤ A ∧ Nat.card H = 8 ∧ ∀ a ∈ H, g * a = a * g) :
    ∃ h w : J, (∀ a ∈ A, h * a * h⁻¹ ∈ A) ∧ w ∈ B ∧ g = h * q 1 * w * h⁻¹ := by
  obtain ⟨T, hT⟩ := exists_acts hgA
  obtain ⟨cs, hcs, hcsT⟩ := exists_codes T
  obtain ⟨H, hHA, hHc, hHg⟩ := hH
  have hT1 : T ≠ 1 := fun h1 => hgB (mem_B_of_acts_one (h1 ▸ hT))
  have hTinj : ∀ e, T *ᵥ e = 0 → e = 0 := fun e he => by
    apply eq_zero_of_cA_eq_one
    have h2 := hT e
    rw [he, cA_zero] at h2
    exact mul_eq_left.1 (mul_inv_eq_one.1 h2)
  have hfix : 8 ≤ fixedCount cs := by
    have : Finite H := Nat.finite_of_card_ne_zero (by rw [hHc]; norm_num)
    have : Fintype H := Fintype.ofFinite H
    have hmemA : ∀ h : H, ∃ e : Vec4, cA e = (h : J) := fun h => exists_cA (hHA h.2)
    choose e he using hmemA
    have hcode : ∀ h : H, ∃ c : ℕ, c < 16 ∧ codeVec 4 c = e h := fun h => by
      obtain ⟨c, hc, hce⟩ := exists_codeVec 4 (e h)
      exact ⟨c, lt_of_lt_of_eq hc (by norm_num), hce⟩
    choose c hc16 hce using hcode
    have hTe : ∀ h : H, T *ᵥ e h = e h := fun h => by
      apply cA_injective
      rw [← hT (e h), he h]
      have h1 := hHg h h.2
      rw [h1, mul_inv_cancel_right]
    have hfixc : ∀ h : H, codeVec 4 (applyCols 4 cs (c h)) = codeVec 4 (c h) := fun h => by
      rw [← matOfCols_mulVec, hcsT, hce, hTe]
    have hinj : Function.Injective c := fun h h' hh => by
      apply Subtype.ext
      rw [← he h, ← he h']
      congr 1
      rw [← hce h, ← hce h', hh]
    have hnd : ((List.range 16).filter fun c =>
        decide (codeVec 4 (applyCols 4 cs c) = codeVec 4 c)).Nodup :=
      (List.nodup_range).filter _
    have hmem : ∀ h : H, c h ∈ ((List.range 16).filter fun c =>
        decide (codeVec 4 (applyCols 4 cs c) = codeVec 4 c)).toFinset := fun h => by
      simp only [List.mem_toFinset, List.mem_filter, List.mem_range, decide_eq_true_eq]
      exact ⟨hc16 h, hfixc h⟩
    unfold fixedCount
    calc 8 = Fintype.card H := by rw [← Nat.card_eq_fintype_card, hHc]
      _ = (Finset.univ : Finset H).card := Finset.card_univ.symm
      _ ≤ ((List.range 16).filter fun c =>
          decide (codeVec 4 (applyCols 4 cs c) = codeVec 4 c)).toFinset.card :=
        Finset.card_le_card_of_injOn c (fun h _ => hmem h) (fun h _ h' _ hh => hinj hh)
      _ = _ := List.toFinset_card_of_nodup hnd
  have hid : cs ≠ idCols 4 := fun h => hT1 (by rw [← hcsT, h, matOfCols_idCols_four])
  have hinvcs : invCode cs = true := invCode_of_inj (by rw [hcsT]; exact hTinj)
  obtain ⟨p, hp, hp1, hp2, hp3, hp4⟩ :=
    tfacts_spec Certificates.certificate24217 hcs hfix hid hinvcs
  have hglp : p.2 ∈ glList := (glFacts_parts.1 p.2 (mem_allMat4_of_wf4 hp2) hp3)
  obtain ⟨h, hh⟩ := glList_acts p.2 hglp
  have hHT : matOfCols 4 p.2 * matOfCols 4 T0cols = T * matOfCols 4 p.2 := by
    calc matOfCols 4 p.2 * matOfCols 4 T0cols = matOfCols 4 (mulCols 4 p.2 T0cols) :=
          (matOfCols_mulCols 4 _ _).symm
      _ = matOfCols 4 (mulCols 4 cs p.2) := by rw [hp4]
      _ = matOfCols 4 cs * matOfCols 4 p.2 := matOfCols_mulCols 4 _ _
      _ = T * matOfCols 4 p.2 := by rw [hcsT]
  have hA1 : Acts (h * q 1) (matOfCols 4 p.2 * matOfCols 4 T0cols) := hh.mul acts_q1
  have hA2 : Acts (g * h) (T * matOfCols 4 p.2) := hT.mul hh
  rw [hHT] at hA1
  refine ⟨h, (h * q 1)⁻¹ * (g * h), normalizes_of_acts hh, ?_, ?_⟩
  · rw [mem_B_iff]
    intro a ha
    obtain ⟨e, rfl⟩ := exists_cA ha
    have e3 : (g * h) * cA e * (g * h)⁻¹ = (h * q 1) * cA e * (h * q 1)⁻¹ := by
      rw [hA2 e, hA1 e]
    calc (h * q 1)⁻¹ * (g * h) * cA e
        = (h * q 1)⁻¹ * ((g * h) * cA e * (g * h)⁻¹) * (g * h) := by group
      _ = (h * q 1)⁻¹ * ((h * q 1) * cA e * (h * q 1)⁻¹) * (g * h) := by rw [e3]
      _ = cA e * ((h * q 1)⁻¹ * (g * h)) := by group
  · group

end Certified

end CFSG.EvenSporadicStandard.ThStd.LocalDataTh
