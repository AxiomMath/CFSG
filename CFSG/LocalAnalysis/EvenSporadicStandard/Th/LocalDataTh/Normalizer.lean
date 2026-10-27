module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalDataTh.ABasis
public import CFSG.Sporadic.ThSchreier.BFS
public import Certificates.Certificate24202
public import Certificates.Certificate24203

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.ThStd.LocalDataTh

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 CFSG.Sporadic.Th.Max3.AllConj
  CFSG.Sporadic.Th.Native CFSG.Sporadic.LySchreier CFSG.Sporadic.ThSchreier
open scoped Matrix

section Rows


@[expose] noncomputable def n1 : J := x * y

@[expose] noncomputable def n2 : J := wordProd [.y, .x, .y] * fusionConjQ0

theorem isRows_n1 : IsRows rowsN1 n1 := isRows_x.mul isRows_y

theorem isRows_n2 : IsRows rowsN2 n2 :=
  (IsRows.word isRows_x isRows_y [.y, .x, .y]).mul isRows_fusionConjQ0

theorem bitsOf_eq (n : ℕ) (i : Fin 8) : bitsOf n i = (codeVec 8 n i).val :=
  (bitZ_val n i).symm

theorem nf_zero_codeVec (n : ℕ) : nf 0 (codeVec 8 n) = nfN 0 (bitsOf n) := by
  have h : (fun i : Fin 8 => (codeVec 8 n i).val) = bitsOf n :=
    funext fun i => (bitsOf_eq n i).symm
  rw [nf_eq_nfN]
  show nfN (0 : ZMod 2).val (fun i : Fin 8 => (codeVec 8 n i).val) = _
  rw [h]
  rfl

theorem isRows_nf_zero (n : ℕ) : IsRows (rowsNf 0 (bitsOf n)) (nf 0 (codeVec 8 n)) := by
  rw [nf_zero_codeVec]
  exact isRows_nfN 0 (bitsOf n)

theorem aGen_zero : aGen 0 = z := by simp [aGen]

theorem isRows_aGen_zero : IsRows rowsZ (aGen 0) := by
  rw [aGen_zero]
  exact isRows_z

theorem isRows_aGen_one : IsRows rowsA1 (aGen 1) := isRows_nf_zero 1

theorem isRows_aGen_two : IsRows rowsA2 (aGen 2) := isRows_nf_zero 50

theorem isRows_aGen_three : IsRows rowsA3 (aGen 3) := isRows_nf_zero 100

theorem isRows_cA (c : ℕ) : IsRows (rowsAEl c) (cA (codeVec 4 c)) := by
  have h0 : (codeVec 4 c 0).val = c % 2 := by simp [codeVec, bitZ_val]
  have h1 : (codeVec 4 c 1).val = c / 2 % 2 := by simp [codeVec, bitZ_val]
  have h2 : (codeVec 4 c 2).val = c / 4 % 2 := by
    simp only [codeVec, bitZ_val]
    norm_num
  have h3 : (codeVec 4 c 3).val = c / 8 % 2 := by
    simp only [codeVec, bitZ_val]
    norm_num
  unfold cA
  rw [h0, h1, h2, h3]
  exact (((isRows_aGen_zero.pow _).mul (isRows_aGen_one.pow _)).mul
    (isRows_aGen_two.pow _)).mul (isRows_aGen_three.pow _)

theorem conj_gen_of_eqRows {n g : J} {R Rg : Array V4} (hR : IsRows R n) (hg : IsRows Rg g)
    {c : ℕ} (h : eqRows (mulRows R Rg) (mulRows (rowsAEl c) R) = true) :
    n * g * n⁻¹ = cA (codeVec 4 c) := by
  have e := (hR.mul hg).eq_of_eqRows ((isRows_cA c).mul hR) h
  rw [e]
  simp

end Rows

section Acts


theorem acts_n1 : Acts n1 (matOfCols 4 T1c) := by
  obtain ⟨h0, h1, h2, h3, -⟩ := Certificates.certificate24202
  have c0 : n1 * aGen 0 * n1⁻¹ = cA (matOfCols 4 T1c *ᵥ Pi.single 0 1) := by
    rw [matOfCols_mulVec_single, aGen_zero]
    exact conj_gen_of_eqRows isRows_n1 isRows_z h0
  have c1 : n1 * aGen 1 * n1⁻¹ = cA (matOfCols 4 T1c *ᵥ Pi.single 1 1) := by
    rw [matOfCols_mulVec_single]
    exact conj_gen_of_eqRows isRows_n1 isRows_aGen_one h1
  have c2 : n1 * aGen 2 * n1⁻¹ = cA (matOfCols 4 T1c *ᵥ Pi.single 2 1) := by
    rw [matOfCols_mulVec_single]
    exact conj_gen_of_eqRows isRows_n1 isRows_aGen_two h2
  have c3 : n1 * aGen 3 * n1⁻¹ = cA (matOfCols 4 T1c *ᵥ Pi.single 3 1) := by
    rw [matOfCols_mulVec_single]
    exact conj_gen_of_eqRows isRows_n1 isRows_aGen_three h3
  apply Acts.of_gens
  intro j
  fin_cases j
  · exact c0
  · exact c1
  · exact c2
  · exact c3

theorem acts_n2 : Acts n2 (matOfCols 4 T2c) := by
  obtain ⟨-, -, -, -, h0, h1, h2, h3⟩ := Certificates.certificate24202
  have c0 : n2 * aGen 0 * n2⁻¹ = cA (matOfCols 4 T2c *ᵥ Pi.single 0 1) := by
    rw [matOfCols_mulVec_single, aGen_zero]
    exact conj_gen_of_eqRows isRows_n2 isRows_z h0
  have c1 : n2 * aGen 1 * n2⁻¹ = cA (matOfCols 4 T2c *ᵥ Pi.single 1 1) := by
    rw [matOfCols_mulVec_single]
    exact conj_gen_of_eqRows isRows_n2 isRows_aGen_one h1
  have c2 : n2 * aGen 2 * n2⁻¹ = cA (matOfCols 4 T2c *ᵥ Pi.single 2 1) := by
    rw [matOfCols_mulVec_single]
    exact conj_gen_of_eqRows isRows_n2 isRows_aGen_two h2
  have c3 : n2 * aGen 3 * n2⁻¹ = cA (matOfCols 4 T2c *ᵥ Pi.single 3 1) := by
    rw [matOfCols_mulVec_single]
    exact conj_gen_of_eqRows isRows_n2 isRows_aGen_three h3
  apply Acts.of_gens
  intro j
  fin_cases j
  · exact c0
  · exact c1
  · exact c2
  · exact c3

end Acts

section GLSection


theorem matOfCols_idCols_four : matOfCols 4 (idCols 4) = 1 := by decide

theorem glList_def : glList = bfsList [mulCols 4 T1c, mulCols 4 T2c] (idCols 4) 20160 := rfl

theorem glList_acts : ∀ cs ∈ glList, ∃ n : J, Acts n (matOfCols 4 cs) := by
  intro cs hcs
  rw [glList_def] at hcs
  refine bfsList_mem_of_closed (S := {cs | ∃ n : J, Acts n (matOfCols 4 cs)})
    [mulCols 4 T1c, mulCols 4 T2c] (idCols 4) ⟨1, ?_⟩ ?_ 20160 cs hcs
  · rw [matOfCols_idCols_four]
    exact Acts.one
  · intro g hg cs' hcs'
    obtain ⟨n, hn⟩ := hcs'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact ⟨n1 * n, by rw [matOfCols_mulCols]; exact acts_n1.mul hn⟩
    · exact ⟨n2 * n, by rw [matOfCols_mulCols]; exact acts_n2.mul hn⟩


theorem glFacts_parts : (∀ cs ∈ allMat4, invCode cs = true → cs ∈ glList) ∧
    (∀ s < 15, ∃ cs ∈ glList, cs.getD 0 0 = s + 1) := by
  have h : GLFacts = true := Certificates.certificate24203
  have h' : ((glList.length == 20160 &&
      allMat4.all (fun cs => !invCode cs || glList.contains cs)) &&
      (List.range 15).all fun s => glList.any fun cs => cs.getD 0 0 == s + 1) = true := h
  obtain ⟨h12, h3⟩ := Bool.and_eq_true_iff.1 h'
  obtain ⟨-, h2⟩ := Bool.and_eq_true_iff.1 h12
  refine ⟨fun cs hcs hinv => ?_, fun s hs => ?_⟩
  · have h4 := List.all_eq_true.1 h2 cs hcs
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at h4
    rcases h4 with h5 | h5
    · rw [hinv] at h5
      exact absurd h5 (by decide)
    · exact List.contains_iff_mem.1 h5
  · have h4 := List.all_eq_true.1 h3 s (List.mem_range.2 hs)
    obtain ⟨cs, hcs, h5⟩ := List.any_eq_true.1 h4
    exact ⟨cs, hcs, beq_iff_eq.1 h5⟩

theorem normalizes_of_acts {n : J} {T : Matrix (Fin 4) (Fin 4) (ZMod 2)} (h : Acts n T) :
    ∀ x ∈ A, n * x * n⁻¹ ∈ A := by
  intro x hx
  obtain ⟨e, rfl⟩ := exists_cA hx
  rw [h e]
  exact cA_mem _

theorem trans_A : ∀ a ∈ A, a ≠ 1 → ∃ n : J, (∀ x ∈ A, n * x * n⁻¹ ∈ A) ∧ n * z * n⁻¹ = a := by
  intro a ha ha1
  obtain ⟨e, rfl⟩ := exists_cA ha
  have he : e ≠ 0 := fun h0 => ha1 (by rw [h0, cA_zero])
  obtain ⟨c, hc, hce⟩ := exists_codeVec 4 e
  have hc16 : c < 16 := lt_of_lt_of_eq hc (by norm_num)
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact he (by rw [← hce, codeVec_zero])
  obtain ⟨cs, hcs, hcs0⟩ := glFacts_parts.2 (c - 1) (by omega)
  obtain ⟨n, hn⟩ := glList_acts cs hcs
  refine ⟨n, normalizes_of_acts hn, ?_⟩
  have hcol : matOfCols 4 cs *ᵥ Pi.single 0 1 = e := by
    rw [matOfCols_mulVec_single]
    have h0 : cs.getD ((0 : Fin 4) : ℕ) 0 = c := by
      show cs.getD 0 0 = c
      omega
    rw [h0, hce]
  have h1 := hn (Pi.single 0 1)
  rw [cA_single, hcol] at h1
  rw [← aGen_zero]
  exact h1

theorem surj_A (f : J → J) (hmem : ∀ a ∈ A, f a ∈ A)
    (hmul : ∀ a ∈ A, ∀ b ∈ A, f (a * b) = f a * f b)
    (hinj : ∀ a ∈ A, ∀ b ∈ A, f a = f b → a = b) : ∃ n : J, ∀ a ∈ A, n * a * n⁻¹ = f a := by
  have hcol : ∀ j : Fin 4, ∃ e : Vec4, cA e = f (aGen j) := fun j =>
    exists_cA (hmem _ (aGen_mem j))
  choose col hcol using hcol
  set T : Matrix (Fin 4) (Fin 4) (ZMod 2) := Matrix.of fun i j => col j i with hT
  have hTcol : ∀ j, T *ᵥ Pi.single j 1 = col j := by
    intro j
    funext i
    simp [hT]
  have hfT : ∀ e, f (cA e) = cA (T *ᵥ e) := by
    intro e
    rw [map_cA f hmul e, mulVec_eq_sum4 T e]
    simp only [hTcol]
    rw [cA_sum col e]
    simp only [hcol]
  have hf1 : f 1 = 1 := by simpa using hmul 1 A.one_mem 1 A.one_mem
  have hTinj : ∀ e, T *ᵥ e = 0 → e = 0 := by
    intro e he
    have h1 : f (cA e) = f 1 := by rw [hfT, he, cA_zero, hf1]
    exact eq_zero_of_cA_eq_one (hinj _ (cA_mem e) _ A.one_mem h1)
  choose code hcodelt hcode using fun j => exists_codeVec 4 (col j)
  set cs : List ℕ := [code 0, code 1, code 2, code 3] with hcs
  have hgetD : ∀ j : Fin 4, cs.getD (j : ℕ) 0 = code j := by
    intro j
    fin_cases j <;> rfl
  have hcsT : matOfCols 4 cs = T := by
    ext i j
    simp only [matOfCols, Matrix.of_apply, hgetD, hT]
    have h1 := congrFun (hcode j) i
    simpa [codeVec] using h1
  have hlt : ∀ j, code j < 16 := fun j => lt_of_lt_of_eq (hcodelt j) (by norm_num)
  have hmemMat : cs ∈ allMat4 := by
    simp only [allMat4, List.mem_flatMap, List.mem_range, List.mem_map]
    exact ⟨code 0, hlt 0, code 1, hlt 1, code 2, hlt 2, code 3, hlt 3, rfl⟩
  have hinv : invCode cs = true := by
    unfold invCode
    rw [List.all_eq_true]
    intro s hs
    rw [List.mem_range] at hs
    have hne : applyCols 4 cs (s + 1) ≠ 0 := by
      intro h0
      have h1 : T *ᵥ codeVec 4 (s + 1) = 0 := by
        rw [← hcsT, matOfCols_mulVec, h0, codeVec_zero]
      have h2 := hTinj _ h1
      have h3 : codeVec 4 (s + 1) = codeVec 4 0 := by rw [h2, codeVec_zero]
      have h4 := codeVec_injOn 4 (by norm_num; omega) (by norm_num) h3
      omega
    simpa using hne
  obtain ⟨n, hn⟩ := glList_acts cs (glFacts_parts.1 cs hmemMat hinv)
  rw [hcsT] at hn
  refine ⟨n, fun a ha => ?_⟩
  obtain ⟨e, rfl⟩ := exists_cA ha
  rw [hn e, hfT e]

end GLSection

end CFSG.EvenSporadicStandard.ThStd.LocalDataTh
