module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoSuz.SylowSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoSuz.Model
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Suzuki
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoSuz.SylowCheck

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoSuz

open Subgroup
open scoped commutatorElement

section GenSysLemmas

theorem GenSys.letterU_odd (G : GenSys) (h : G.valid = true) (i : ℕ) :
    G.letterU h (2 * i + 1) = (G.letterU h (2 * i))⁻¹ := by
  refine Units.ext ?_
  have h1 : (2 * i + 1) % 2 = 1 := by omega
  have h2 : (2 * i + 1) / 2 = i := by omega
  have h3 : (2 * i) % 2 = 0 := by omega
  have h4 : (2 * i) / 2 = i := by omega
  simp only [GenSys.letterU, h1, h2, h3, h4, ite_true, one_ne_zero, ite_false]
  rfl

theorem GenSys.vm_letterU (G : GenSys) (h : G.valid = true) (c : ℕ) :
    vm (G.letterU h c) = ofMt (G.letter c) := G.val_letterU h c

theorem GenSys.evalU_append (G : GenSys) (h : G.valid = true) (v w : List ℕ) :
    G.evalU h (v ++ w) = G.evalU h v * G.evalU h w := by
  simp [GenSys.evalU, List.map_append, List.prod_append]

theorem GenSys.evalU_cons (G : GenSys) (h : G.valid = true) (c : ℕ) (w : List ℕ) :
    G.evalU h (c :: w) = G.letterU h c * G.evalU h w := by
  simp [GenSys.evalU]

theorem GenSys.letterU_flip (G : GenSys) (h : G.valid = true) (c : ℕ) :
    G.letterU h (if c % 2 = 0 then c + 1 else c - 1) = (G.letterU h c)⁻¹ := by
  rcases Nat.even_or_odd' c with ⟨i, rfl | rfl⟩
  · have h1 : (2 * i) % 2 = 0 := by omega
    rw [ite_eq_left h1]
    exact G.letterU_odd h i
  · have h1 : ¬ (2 * i + 1) % 2 = 0 := by omega
    rw [ite_eq_right h1, show 2 * i + 1 - 1 = 2 * i by omega, G.letterU_odd h i, inv_inv]

theorem GenSys.evalU_invWord (G : GenSys) (h : G.valid = true) (w : List ℕ) :
    G.evalU h (invWord w) = (G.evalU h w)⁻¹ := by
  induction w with
  | nil => simp [invWord, GenSys.evalU]
  | cons c w ih =>
    have e : invWord (c :: w) = invWord w ++ [if c % 2 = 0 then c + 1 else c - 1] := by
      simp [invWord]
    rw [e, G.evalU_append, ih, GenSys.evalU_cons, G.evalU_cons]
    simp [GenSys.evalU, G.letterU_flip, mul_inv_rev]

theorem canonB_foldl (G : GenSys) (w : List ℕ) (acc : Mt) (h : canonB acc = true) :
    canonB (w.foldl (fun a c => mulM a (G.letter c)) acc) = true := by
  induction w generalizing acc with
  | nil => exact h
  | cons c w ih =>
    rw [List.foldl_cons]
    exact ih _ (canonB_mulM _ _)

theorem canonB_eval (G : GenSys) (w : List ℕ) : canonB (G.eval w) = true :=
  canonB_foldl G w oneM canonB_oneM

theorem GenSys.letterU_one (G : GenSys) (h : G.valid = true) {c : ℕ}
    (hc : G.mats.getD (c / 2) oneM = oneM) (hi : G.invs.getD (c / 2) oneM = oneM) :
    G.letterU h c = 1 := by
  refine Units.ext ?_
  rw [GenSys.val_letterU, GenSys.letter]
  split_ifs
  · rw [hc, ofMt_oneM]; rfl
  · rw [hi, ofMt_oneM]; rfl

end GenSysLemmas

section LhatMembership

open CFSG.Sporadic.Recognition.SuzMultiplier (suzD gcS)

theorem getD_oneM_of_le (A : Array Mt) {i : ℕ} (h : A.size ≤ i) : A.getD i oneM = oneM := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h, Option.getD_none]


noncomputable abbrev Lhat : Subgroup GL12 := rho.range

theorem negOne_mem : (-1 : GL12) ∈ (Lhat : Subgroup GL12) :=
  ⟨PresentedGroup.of suzD ^ 2, rho_sq_d⟩

theorem coverGS_size : coverGS.mats.size = 7 ∧ coverGS.invs.size = 7 := by
  have h := coverCheck_facts.1
  simp [coverGS, h]

theorem coverGS_letterU_even_mem (i : ℕ) :
    coverGS.letterU coverGS_valid (2 * i) ∈ (Lhat : Subgroup GL12) := by
  by_cases hi : i < 7
  · have h7 : gcS = 7 := rfl
    have : coverGS.letterU coverGS_valid (2 * i) =
        rho (PresentedGroup.of (⟨i, by omega⟩ : Fin gcS)) := by
      rw [rho_of]; rfl
    rw [this]
    exact ⟨_, rfl⟩
  · have hs := coverGS_size
    have h1 : coverGS.mats.getD (2 * i / 2) oneM = oneM := by
      rw [show 2 * i / 2 = i by omega]
      exact getD_oneM_of_le _ (by omega)
    have h2 : coverGS.invs.getD (2 * i / 2) oneM = oneM := by
      rw [show 2 * i / 2 = i by omega]
      exact getD_oneM_of_le _ (by omega)
    rw [GenSys.letterU_one coverGS coverGS_valid h1 h2]
    exact one_mem _

theorem coverGS_letterU_mem (c : ℕ) :
    coverGS.letterU coverGS_valid c ∈ (Lhat : Subgroup GL12) := by
  rcases Nat.even_or_odd' c with ⟨i, rfl | rfl⟩
  · exact coverGS_letterU_even_mem i
  · rw [GenSys.letterU_odd]
    exact inv_mem (coverGS_letterU_even_mem i)

theorem coverGS_evalU_mem (w : List ℕ) :
    coverGS.evalU coverGS_valid w ∈ (Lhat : Subgroup GL12) := by
  unfold GenSys.evalU
  exact Subgroup.list_prod_mem _ fun x hx => by
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx
    exact coverGS_letterU_mem c

theorem mem_of_neg_mul {m : Mt} {w : List ℕ}
    (h : mulM negM m = coverGS.eval w) : ∃ u ∈ (Lhat : Subgroup GL12), vm u = ofMt m := by
  have hnn : (-1 : GL12) * (-1 : GL12) = 1 := by rw [neg_one_mul, neg_neg]
  refine ⟨(-1 : GL12) * coverGS.evalU coverGS_valid w,
    mul_mem negOne_mem (coverGS_evalU_mem _), ?_⟩
  have h2 : vm (-1 : GL12) * ofMt m = vm (coverGS.evalU coverGS_valid w) := by
    have h3 : ofMt (mulM negM m) = vm (coverGS.evalU coverGS_valid w) := by
      rw [h]; exact GenSys.ofMt_eval coverGS coverGS_valid w
    rw [ofMt_mulM, ofMt_negM] at h3
    exact h3
  rw [vm_mul, ← h2, ← mul_assoc, ← vm_mul, hnn]
  exact one_mul _

theorem matA_mem : ∃ u ∈ (Lhat : Subgroup GL12), vm u = ofMt matA :=
  mem_of_neg_mul coverCheck_facts.2.2.2.2.2.1

theorem matB_mem : ∃ u ∈ (Lhat : Subgroup GL12), vm u = ofMt matB :=
  mem_of_neg_mul coverCheck_facts.2.2.2.2.2.2

theorem abGS_vm_even (hv : abGS.valid = true) (k : ℕ) :
    vm (abGS.letterU hv (2 * k)) = ofMt (abGS.mats.getD k oneM) := by
  rw [GenSys.vm_letterU, GenSys.letter, ite_eq_left (by omega), show 2 * k / 2 = k by omega]

theorem abGS_mats_0 : abGS.mats.getD 0 oneM = matA := by simp [abGS]
theorem abGS_mats_1 : abGS.mats.getD 1 oneM = matA2 := by simp [abGS]
theorem abGS_mats_2 : abGS.mats.getD 2 oneM = matA3 := by simp [abGS]
theorem abGS_mats_3 : abGS.mats.getD 3 oneM = matB := by simp [abGS]
theorem abGS_mats_4 : abGS.mats.getD 4 oneM = matB2 := by simp [abGS]

theorem abGS_letterU_even_mem (hv : abGS.valid = true) (k : ℕ) :
    abGS.letterU hv (2 * k) ∈ (Lhat : Subgroup GL12) := by
  obtain ⟨uA, huA, hA⟩ := matA_mem
  obtain ⟨uB, huB, hB⟩ := matB_mem
  by_cases hk : k < 5
  · interval_cases k
    · have : abGS.letterU hv (2 * 0) = uA := vm_inj (by rw [abGS_vm_even, abGS_mats_0, hA])
      rw [this]; exact huA
    · have : abGS.letterU hv (2 * 1) = uA * uA :=
        vm_inj (by rw [abGS_vm_even, abGS_mats_1, vm_mul, hA]; exact ofMt_mulM matA matA)
      rw [this]; exact mul_mem huA huA
    · have : abGS.letterU hv (2 * 2) = uA * uA * uA :=
        vm_inj (by
          rw [abGS_vm_even, abGS_mats_2, vm_mul, vm_mul, hA]
          show ofMt (mulM matA2 matA) = _
          rw [ofMt_mulM]
          exact congrArg (· * ofMt matA) (ofMt_mulM matA matA))
      rw [this]; exact mul_mem (mul_mem huA huA) huA
    · have : abGS.letterU hv (2 * 3) = uB := vm_inj (by rw [abGS_vm_even, abGS_mats_3, hB])
      rw [this]; exact huB
    · have : abGS.letterU hv (2 * 4) = uB * uB :=
        vm_inj (by rw [abGS_vm_even, abGS_mats_4, vm_mul, hB]; exact ofMt_mulM matB matB)
      rw [this]; exact mul_mem huB huB
  · have hs : abGS.mats.size = 5 ∧ abGS.invs.size = 5 := by simp [abGS]
    have h1 : abGS.mats.getD (2 * k / 2) oneM = oneM := by
      rw [show 2 * k / 2 = k by omega]
      exact getD_oneM_of_le _ (by omega)
    have h2 : abGS.invs.getD (2 * k / 2) oneM = oneM := by
      rw [show 2 * k / 2 = k by omega]
      exact getD_oneM_of_le _ (by omega)
    rw [GenSys.letterU_one abGS hv h1 h2]
    exact one_mem _

theorem abGS_evalU_mem (hv : abGS.valid = true) (w : List ℕ) :
    abGS.evalU hv w ∈ (Lhat : Subgroup GL12) := by
  unfold GenSys.evalU
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx
  rcases Nat.even_or_odd' c with ⟨i, rfl | rfl⟩
  · exact abGS_letterU_even_mem hv i
  · rw [GenSys.letterU_odd]
    exact inv_mem (abGS_letterU_even_mem hv i)

end LhatMembership

end CFSG.EvenSporadicStandard.TwoSuz
