module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55WtApply
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55WordG
public import CFSG.Sporadic.Recognition.McLASEnum
public import CFSG.Sporadic.SmallOddCore.McL
public import Certificates.Certificate5186
public import Certificates.Certificate5254
public import Certificates.Data.GH74.McLWeights
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.Sporadic.Recognition.McLASSpec

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.McLWt

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Recognition.McLAS
  CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.WordG

@[expose] noncomputable def wtG (i : ℕ) : Equiv.Perm (Fin 275) := tablePerm 275 (wtElem i)

@[expose] noncomputable def wtLetterG (z : ℤ) : Equiv.Perm (Fin 275) :=
  if 0 < z then wtG (z.natAbs - 1) else (wtG (z.natAbs - 1))⁻¹

structure WtFacts : Prop where
  rep : ∀ i < 6, Rep 275 (wtElem i) (wtG i)
  mem : ∀ i < 6, wtG i ∈ mclP
  inv : ∀ i < 6, invOK 275 (wtElem i) (invT 275 (wtElem i)) = true
  rels : ∀ r ∈ wtRels, wordT 275 wtLetterT r.1 = wordT 275 wtLetterT r.2
  ne : ∀ r ∈ wtNe, r.2.2 < 275 ∧ ap (wordT 275 wtLetterT r.1) r.2.2 ≠
    ap (wordT 275 wtLetterT r.2.1) r.2.2

theorem wtFacts :
    WtFacts := by
  obtain ⟨hsub, -⟩ := Certificates.certificate5186
  have F := subEnumOK_spec mcl_groupData hsub
  have hW : wtCertificate () = true := Certificates.certificate5254
  simp only [wtCertificate, wtCheck, Bool.and_eq_true, beq_iff_eq] at hW
  obtain ⟨⟨⟨⟨-, hidx⟩, hinv⟩, hrels⟩, hne⟩ := hW
  have hlt : ∀ i < 6, wtIdx[i]! < sylTwoEnum.size := fun i hi => by
    have hk := (allIn_eq_true.1 hidx) i (Nat.zero_le _) hi
    simpa using hk
  refine ⟨fun i hi => F.enum.rep _ (hlt i hi), fun i hi => F.le (F.enum.mem _ (hlt i hi)),
    fun i hi => (allIn_eq_true.1 hinv) i (Nat.zero_le _) hi, fun r hr => ?_, fun r hr => ?_⟩
  · have := List.all_eq_true.1 hrels r hr
    simpa using this
  · have := List.all_eq_true.1 hne r hr
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne] at this
    exact this

theorem rep_letter (hF : WtFacts) {z : ℤ} (hz : z ≠ 0 ∧ z.natAbs ≤ 6) :
    Rep 275 (wtLetterT z) (wtLetterG z) := by
  have hi : z.natAbs - 1 < 6 := by omega
  unfold wtLetterT wtLetterG
  by_cases hz' : 0 < z
  · rw [ite_eq_left hz', ite_eq_left hz']
    exact hF.rep _ hi
  · rw [ite_eq_right hz', ite_eq_right hz']
    exact Rep.inv_of_invOK (hF.rep _ hi) (hF.inv _ hi)

theorem rep_word (hF : WtFacts) (w : List ℤ) (hw : ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 6) :
    Rep 275 (wordT 275 wtLetterT w) (wordG wtLetterG w) :=
  Rep.wordT (by norm_num) w fun l hl => rep_letter hF (hw l hl)

theorem wtRels_letters : ∀ r ∈ wtRels, ∀ l ∈ r.1 ++ r.2, l ≠ 0 ∧ l.natAbs ≤ 6 := by
  decide +kernel

theorem wtNe_letters : ∀ r ∈ wtNe, ∀ l ∈ r.1 ++ r.2.1, l ≠ 0 ∧ l.natAbs ≤ 6 := by
  decide +kernel

section


theorem wt_rels : ∀ r ∈ wtRels, wordG wtLetterG r.1 = wordG wtLetterG r.2 := by
  have hF := wtFacts
  intro r hr
  have h1 := rep_word hF r.1 fun l hl => wtRels_letters r hr l (List.mem_append_left _ hl)
  have h2 := rep_word hF r.2 fun l hl => wtRels_letters r hr l (List.mem_append_right _ hl)
  rw [hF.rels r hr] at h1
  exact rep_unique h1 h2

theorem wt_ne : ∀ r ∈ wtNe, wordG wtLetterG r.1 ≠ wordG wtLetterG r.2.1 := by
  have hF := wtFacts
  intro r hr heq
  have h1 := rep_word hF r.1 fun l hl => wtNe_letters r hr l (List.mem_append_left _ hl)
  have h2 := rep_word hF r.2.1 fun l hl => wtNe_letters r hr l (List.mem_append_right _ hl)
  obtain ⟨hpt, hne⟩ := hF.ne r hr
  have e1 := h1 r.2.2 hpt
  have e2 := h2 r.2.2 hpt
  rw [heq] at e1
  exact hne (e1.trans e2.symm)

theorem wtL1 : wtLetterG 1 = wtG 0 := by simp [wtLetterG]
theorem wtL2 : wtLetterG 2 = wtG 1 := by simp [wtLetterG]
theorem wtL3 : wtLetterG 3 = wtG 2 := by simp [wtLetterG]
theorem wtL4 : wtLetterG 4 = wtG 3 := by simp [wtLetterG]
theorem wtL5 : wtLetterG 5 = wtG 4 := by simp [wtLetterG]
theorem wtL6 : wtLetterG 6 = wtG 5 := by simp [wtLetterG]
theorem wtLn5 : wtLetterG (-5) = (wtG 4)⁻¹ := by simp [wtLetterG]
theorem wtLn6 : wtLetterG (-6) = (wtG 5)⁻¹ := by simp [wtLetterG]

local macro "wt_use " h:term : tactic =>
  `(tactic| simpa only [wordG_cons, wordG_nil, mul_one, mul_assoc, wtL1, wtL2, wtL3, wtL4, wtL5,
    wtL6, wtLn5, wtLn6] using $h)

theorem mcl_weights : ∃ a u₁ u₂ u₃ x y : Equiv.Perm (Fin 275), a ∈ mclP ∧ u₁ ∈ mclP ∧ u₂ ∈ mclP ∧
    u₃ ∈ mclP ∧ x ∈ mclP ∧ y ∈ mclP ∧ orderOf a = 2 ∧
      CFSG.GroupTheory.TwoWeights.Data a u₁ u₂ u₃ x y := by
  have hF := wtFacts
  have R := wt_rels
  have hmem : ∀ i < 6, wtG i ∈ mclP := hF.mem
  have haa : wtG 0 * wtG 0 = 1 := by
    have h := R ([1, 1], []) (by decide +kernel)
    simp only [wordG_cons, wordG_nil, mul_one, wtL1] at h
    exact h
  have hne1 : wtG 0 ≠ 1 := by
    have h := wt_ne ([1], [], 1) (by decide +kernel)
    simp only [wordG_cons, wordG_nil, mul_one, wtL1] at h
    exact h
  have ho : orderOf (wtG 0) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact haa) hne1
  refine ⟨wtG 0, wtG 1, wtG 2, wtG 3, wtG 4, wtG 5, hmem 0 (by norm_num), hmem 1 (by norm_num),
    hmem 2 (by norm_num), hmem 3 (by norm_num), hmem 4 (by norm_num), hmem 5 (by norm_num), ho,
    haa, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · wt_use R ([2, 2], []) (by decide +kernel)
  · wt_use R ([3, 3], []) (by decide +kernel)
  · wt_use R ([4, 4], []) (by decide +kernel)
  · wt_use R ([2, 3], [3, 2]) (by decide +kernel)
  · wt_use R ([2, 4], [4, 2]) (by decide +kernel)
  · wt_use R ([2, 1], [1, 2]) (by decide +kernel)
  · wt_use R ([3, 4], [4, 3]) (by decide +kernel)
  · wt_use R ([3, 1], [1, 3]) (by decide +kernel)
  · wt_use R ([4, 1], [1, 4]) (by decide +kernel)
  · wt_use R ([1, 5], [5, 1]) (by decide +kernel)
  · wt_use R ([1, 6], [6, 1]) (by decide +kernel)
  · wt_use R ([5, 2], [2, 1, 5]) (by decide +kernel)
  · wt_use R ([5, 3], [4, 1, 5]) (by decide +kernel)
  · wt_use R ([5, 4], [3, 1, 5]) (by decide +kernel)
  · wt_use R ([-5, 2], [2, 1, -5]) (by decide +kernel)
  · wt_use R ([-5, 3], [4, 1, -5]) (by decide +kernel)
  · wt_use R ([-5, 4], [3, 1, -5]) (by decide +kernel)
  · wt_use R ([6, 2], [2, 6]) (by decide +kernel)
  · wt_use R ([6, 3], [3, 1, 6]) (by decide +kernel)
  · wt_use R ([6, 4], [2, 4, 1, 6]) (by decide +kernel)
  · wt_use R ([-6, 2], [2, -6]) (by decide +kernel)
  · wt_use R ([-6, 3], [3, 1, -6]) (by decide +kernel)
  · wt_use R ([-6, 4], [2, 4, 1, -6]) (by decide +kernel)
  · wt_use R ([5, 5], [1]) (by decide +kernel)
  · wt_use R ([6, 6], [1]) (by decide +kernel)
  · wt_use R ([5, 6, 5, 6, 5, 6, 5, 6], [1]) (by decide +kernel)

end

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.McLWt
