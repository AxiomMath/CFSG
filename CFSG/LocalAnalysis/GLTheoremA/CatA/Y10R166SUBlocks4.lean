module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166SUBlocks
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KD26h.Glue
public import CFSG.LocalAnalysis.StandardType.GGLinearFusionSURepairBlock
public import CFSG.RankThree.SubgroupLists.UnitaryThreeFamily

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.ClassicalGroups.UnitaryFlag CFSG.SeitzReduction.UnitaryPilot CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.SeitzReduction.LinearPilot (blockDiagSL mem_blockDiagSL_iff_mul)
open Matrix

section Blocks

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ} (h : UnitaryFieldData p f K)

theorem unitaryBlockDiag_inf_le (I J : Finset (Fin n)) :
    unitaryBlockDiag h I ⊓ unitaryBlockDiag h J ≤ unitaryBlockDiag h (I ∩ J) := by
  intro g hg
  rw [Subgroup.mem_inf] at hg
  rw [mem_unitaryBlockDiag]
  intro i j hij
  have h1 := (mem_unitaryBlockDiag (h := h)).1 hg.1 i j
  have h2 := (mem_unitaryBlockDiag (h := h)).1 hg.2 i j
  by_cases hi : i ∈ I ∩ J
  · obtain ⟨hiI, hiJ⟩ := Finset.mem_inter.1 hi
    have hj : j ∉ I ∩ J := hij.1 hi
    by_cases hjI : j ∈ I
    · exact h2 (iff_of_true hiJ fun hjJ => hj (Finset.mem_inter.2 ⟨hjI, hjJ⟩))
    · exact h1 (iff_of_true hiI hjI)
  · by_cases hj : j ∈ I ∩ J
    · obtain ⟨hjI, hjJ⟩ := Finset.mem_inter.1 hj
      by_cases hiI : i ∈ I
      · exact h2 (iff_of_false (fun hiJ => hi (Finset.mem_inter.2 ⟨hiI, hiJ⟩))
          (by simpa using hjJ))
      · exact h1 (iff_of_false hiI (by simpa using hjI))
    · exact absurd (hij.2 hj) hi

theorem unitaryBlockDiag_le_normalizer_unitaryBlock (I : Finset (Fin n)) :
    unitaryBlockDiag h I ≤
      Subgroup.normalizer (unitaryBlock h I : Set (unitarySU p f K n)) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hg' : toSL h n g ∈ blockDiagSL (K := K) I := hg
  have hmul := (mem_blockDiagSL_iff_mul (K := K)).1 hg'
  rw [coe_toSL] at hmul
  exact map_conj_unitaryBlock_of_mul_eq h g hmul.symm

theorem glaPLayer_ne_bot_of_unitaryBlock_le [Finite K] {q : ℕ} (hq : q.Prime)
    {I : Finset (Fin n)} {H : Subgroup (unitarySU p f K n)}
    (h1 : unitaryBlock h I ≤ H) (h2 : H ≤ unitaryBlockDiag h I)
    (hLq : CFSG.IsQuasisimple ↥(unitaryBlock h I))
    (hqL : q ∣ Nat.card ↥(unitaryBlock h I)) :
    GLAPLayer q H ≠ ⊥ := by
  refine CFSG.LocalAnalysis.GLTheoremA.glaPLayer_ne_bot_of_block hq h1 hLq ?_ hqL
  intro g hg y hy
  have hnorm : g ∈ Subgroup.normalizer
      (unitaryBlock h I : Set (unitarySU p f K n)) :=
    unitaryBlockDiag_le_normalizer_unitaryBlock h I (h2 hg)
  exact (Subgroup.mem_normalizer_iff.mp hnorm y).1 hy

theorem glaPLayer_ne_bot_of_map_unitaryBlock_le [Finite K] {q : ℕ} (hq : q.Prime)
    {I : Finset (Fin n)} (hIc : ∃ i, i ∉ I) {H : Subgroup (unitaryPSU h n)}
    (h1 : (unitaryBlock h I).map (unitaryProj h n) ≤ H)
    (h2 : H ≤ (unitaryBlockDiag h I).map (unitaryProj h n))
    (hLq : CFSG.IsQuasisimple ↥(unitaryBlock h I))
    (hqL : q ∣ Nat.card ↥(unitaryBlock h I)) :
    GLAPLayer q H ≠ ⊥ := by
  have hIn : I.card < n := by
    obtain ⟨i, hi⟩ := hIc
    have h1 : (insert i I).card = I.card + 1 := Finset.card_insert_of_notMem hi
    have h2 : (insert i I).card ≤ n := by
      simpa using Finset.card_le_univ (insert i I)
    omega
  have e : ↥(unitaryBlock h I) ≃* ↥(blockSU h I) :=
    (unitaryBlockEquiv h I).symm.trans (blockSUEquiv h hIn)
  have hq' : CFSG.IsQuasisimple ↥(blockSU h I) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e hLq
  have hdvd : q ∣ Nat.card ↥(blockSU h I) := by
    rw [← Nat.card_congr e.toEquiv]
    exact hqL
  refine CFSG.LocalAnalysis.GLTheoremA.glaPLayer_ne_bot_of_block hq h1 hq' ?_ hdvd
  intro g hg y hy
  obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.1 (h2 hg)
  obtain ⟨a, ha, rfl⟩ := (mem_blockSU h).1 hy
  have hdad : d * a * d⁻¹ ∈ unitaryBlock h I := by
    have hnorm : d ∈ Subgroup.normalizer
        (unitaryBlock h I : Set (unitarySU p f K n)) :=
      unitaryBlockDiag_le_normalizer_unitaryBlock h I hd
    exact (Subgroup.mem_normalizer_iff.mp hnorm a).1 ha
  have hπ : unitaryProj h n d * unitaryProj h n a * (unitaryProj h n d)⁻¹ =
      unitaryProj h n (d * a * d⁻¹) := by
    simp only [map_mul, map_inv]
  rw [hπ]
  exact unitaryProj_mem_blockSU h hdad

theorem glaPLayer_ne_bot_of_map_unitaryBlockDiag_inf [Finite K] {q : ℕ} (hq : q.Prime)
    {I J₁ J₂ : Finset (Fin n)} (hI : I = J₁ ∩ J₂) (hIc : ∃ i, i ∉ I)
    {H : Subgroup (unitaryPSU h n)}
    (h1 : (unitaryBlock h I).map (unitaryProj h n) ≤ H)
    (h2 : H ≤ (unitaryBlockDiag h J₁ ⊓ unitaryBlockDiag h J₂).map (unitaryProj h n))
    (hLq : CFSG.IsQuasisimple ↥(unitaryBlock h I))
    (hqL : q ∣ Nat.card ↥(unitaryBlock h I)) :
    GLAPLayer q H ≠ ⊥ :=
  glaPLayer_ne_bot_of_map_unitaryBlock_le h hq hIc h1
    (h2.trans (Subgroup.map_mono (hI.symm ▸ unitaryBlockDiag_inf_le h J₁ J₂))) hLq hqL

end Blocks

section CharTwo

variable {f : ℕ} {K : Type} [Field K] [Finite K] {n : ℕ}

theorem isQuasisimple_unitaryBlock_of_card_eq_two (h : UnitaryFieldData 2 f K)
    {I : Finset (Fin n)} (hI : I.card = 2) (hf : 2 ≤ f) :
    CFSG.IsQuasisimple ↥(unitaryBlock h I) := by
  have hq : CFSG.IsQuasisimple ↥(unitarySU 2 f K I.card) := by
    rw [hI]
    exact CFSG.StandardType.SURepair.isQuasisimple_unitarySU_two h hf
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (unitaryBlockEquiv h I) hq

theorem dvd_card_unitaryBlock_of_card_eq_two (h : UnitaryFieldData 2 f K)
    {I : Finset (Fin n)} (hI : I.card = 2) {q : ℕ} (hq : q.Prime)
    (hqd : q ∣ 2 ^ (2 * f) - 1) :
    q ∣ Nat.card ↥(unitaryBlock h I) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := h.charP
  have hK : Nat.card K = (2 ^ f) ^ 2 := by
    rw [h.card, ← pow_mul, mul_comm]
  have hcard : Nat.card (unitarySU 2 f K 2) = 2 ^ f * ((2 ^ f) ^ 2 - 1) :=
    CFSG.RankThree.SubgroupLists.card_statedSU_two (r := 2) (f := f) hK
  have hblock : Nat.card ↥(unitaryBlock h I) = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
    rw [← Nat.card_congr (unitaryBlockEquiv h I).toEquiv, hI]
    exact hcard
  rw [hblock]
  have hq' : q ∣ (2 ^ f) ^ 2 - 1 := by
    rw [show (2 ^ f) ^ 2 = 2 ^ (2 * f) by rw [← pow_mul, mul_comm f 2]]
    exact hqd
  exact dvd_mul_of_dvd_right hq' (2 ^ f)

theorem glaPLayer_ne_bot_of_map_unitaryBlockDiag_inf_card_eq_two (h : UnitaryFieldData 2 f K)
    {q : ℕ} (hq : q.Prime) (hf : 2 ≤ f) {I J₁ J₂ : Finset (Fin n)} (hI : I = J₁ ∩ J₂)
    (hIcard : I.card = 2) (hIc : ∃ i, i ∉ I) {H : Subgroup (unitaryPSU h n)}
    (h1 : (unitaryBlock h I).map (unitaryProj h n) ≤ H)
    (h2 : H ≤ (unitaryBlockDiag h J₁ ⊓ unitaryBlockDiag h J₂).map (unitaryProj h n))
    (hqd : q ∣ 2 ^ (2 * f) - 1) : GLAPLayer q H ≠ ⊥ :=
  glaPLayer_ne_bot_of_map_unitaryBlockDiag_inf h hq hI hIc h1 h2
    (isQuasisimple_unitaryBlock_of_card_eq_two h hIcard hf)
    (dvd_card_unitaryBlock_of_card_eq_two h hIcard hq hqd)

end CharTwo

end CFSG.LocalAnalysis.GLTheoremA.Y10F
