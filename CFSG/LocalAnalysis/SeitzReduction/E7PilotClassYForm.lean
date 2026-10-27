module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7ResCentU
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7CentLevel
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClassYBruhat

public section
open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction.E6Pilot (rootProd rootProd_injective RootCommFamily conjCoeff)

open CFSG.ComponentClassification.RankTwoExceptional.E7Sec8 (linConjSubgroup
  pinnedX_mem_linConjSubgroup torusGroup_le_linConjSubgroup conjCoeff_apply_ite)

open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootChar rootChar_add rootDiagUnit)

namespace CFSG.SeitzReduction.E7Pilot

local instance yFormNeZeroRank : NeZero Tag.E7.rank := ⟨by decide⟩

@[expose] def yFormR0 : Fin Tag.E7.rank → ℤ := ![0, 1, 1, 2, 2, 2, 1]
@[expose] def yFormR1 : Fin Tag.E7.rank → ℤ := ![2, 2, 3, 4, 3, 2, 1]
@[expose] def yFormR2 : Fin Tag.E7.rank → ℤ := ![1, 1, 1, 2, 2, 2, 1]
@[expose] def yFormR3 : Fin Tag.E7.rank → ℤ := ![1, 2, 3, 4, 3, 2, 1]
@[expose] def yFormR4 : Fin Tag.E7.rank → ℤ := ![1, 1, 2, 2, 2, 2, 1]
@[expose] def yFormR5 : Fin Tag.E7.rank → ℤ := ![1, 2, 2, 4, 3, 2, 1]
@[expose] def yFormR6 : Fin Tag.E7.rank → ℤ := ![1, 1, 2, 3, 2, 2, 1]
@[expose] def yFormR7 : Fin Tag.E7.rank → ℤ := ![1, 2, 2, 3, 3, 2, 1]
@[expose] def yFormR8 : Fin Tag.E7.rank → ℤ := ![1, 1, 2, 3, 3, 2, 1]
@[expose] def yFormR9 : Fin Tag.E7.rank → ℤ := ![1, 2, 2, 3, 2, 2, 1]

@[expose] def yFormE (j : Fin Tag.E7.rank) : Fin Tag.E7.rank → ℤ := Pi.single j 1

@[expose] def yPairRoots : List ((Fin Tag.E7.rank → ℤ) × (Fin Tag.E7.rank → ℤ)) :=
  [(![0, 1, 1, 2, 2, 2, 1], ![2, 2, 3, 4, 3, 2, 1]),
   (![1, 1, 1, 2, 2, 2, 1], ![1, 2, 3, 4, 3, 2, 1]),
   (![1, 1, 2, 2, 2, 2, 1], ![1, 2, 2, 4, 3, 2, 1]),
   (![1, 1, 2, 3, 2, 2, 1], ![1, 2, 2, 3, 3, 2, 1]),
   (![1, 1, 2, 3, 3, 2, 1], ![1, 2, 2, 3, 2, 2, 1])]

@[expose] def yQc {K : Type} [CommRing K] (c : (Fin Tag.E7.rank → ℤ) → K) : K :=
  (yPairRoots.map fun p => c p.1 * c p.2).sum

theorem yForm_pair_eq :
    yPairRoots = [(yFormR0, yFormR1), (yFormR2, yFormR3), (yFormR4, yFormR5),
      (yFormR6, yFormR7), (yFormR8, yFormR9)] := rfl

variable {K : Type} [Field K] [CharP K 2]

theorem yForm_shift_e0 (t : K) (c : (Fin Tag.E7.rank → ℤ) → K) :
    yQc (fun ρ => c ρ + if ρ - yFormE 0 ∈ yPsi then
      t * c (ρ - yFormE 0) else 0) = yQc c := by
  have s1 : yFormR2 - yFormE 0 = yFormR0 := by decide +kernel
  have s2 : yFormR1 - yFormE 0 = yFormR3 := by decide +kernel
  simp only [yQc, yForm_pair_eq]
  simp +decide [yPsi, yFrame, yLow, yHigh, oddDerivE7YFrame, s1, s2]
  ring_nf
  simp [CharTwo.two_eq_zero]

theorem yForm_shift_neg_e0 (t : K) (c : (Fin Tag.E7.rank → ℤ) → K) :
    yQc (fun ρ => c ρ + if ρ - (-yFormE 0) ∈ yPsi then
      t * c (ρ - (-yFormE 0)) else 0) = yQc c := by
  have s1 : yFormR0 + yFormE 0 = yFormR2 := by decide +kernel
  have s2 : yFormR3 + yFormE 0 = yFormR1 := by decide +kernel
  simp only [yQc, yForm_pair_eq]
  simp +decide [yPsi, yFrame, yLow, yHigh, oddDerivE7YFrame, s1, s2]
  ring_nf
  simp [CharTwo.two_eq_zero]

theorem yForm_shift_e1 (t : K) (c : (Fin Tag.E7.rank → ℤ) → K) :
    yQc (fun ρ => c ρ + if ρ - yFormE 1 ∈ yPsi then
      t * c (ρ - yFormE 1) else 0) = yQc c := by
  have s1 : yFormR9 - yFormE 1 = yFormR6 := by decide +kernel
  have s2 : yFormR7 - yFormE 1 = yFormR8 := by decide +kernel
  simp only [yQc, yForm_pair_eq]
  simp +decide [yPsi, yFrame, yLow, yHigh, oddDerivE7YFrame, s1, s2]
  ring_nf
  simp [CharTwo.two_eq_zero]

theorem yForm_shift_neg_e1 (t : K) (c : (Fin Tag.E7.rank → ℤ) → K) :
    yQc (fun ρ => c ρ + if ρ - (-yFormE 1) ∈ yPsi then
      t * c (ρ - (-yFormE 1)) else 0) = yQc c := by
  have s1 : yFormR8 + yFormE 1 = yFormR7 := by decide +kernel
  have s2 : yFormR6 + yFormE 1 = yFormR9 := by decide +kernel
  simp only [yQc, yForm_pair_eq]
  simp +decide [yPsi, yFrame, yLow, yHigh, oddDerivE7YFrame, s1, s2]
  ring_nf
  simp [CharTwo.two_eq_zero]

theorem yForm_shift_e2 (t : K) (c : (Fin Tag.E7.rank → ℤ) → K) :
    yQc (fun ρ => c ρ + if ρ - yFormE 2 ∈ yPsi then
      t * c (ρ - yFormE 2) else 0) = yQc c := by
  have s1 : yFormR4 - yFormE 2 = yFormR2 := by decide +kernel
  have s2 : yFormR3 - yFormE 2 = yFormR5 := by decide +kernel
  simp only [yQc, yForm_pair_eq]
  simp +decide [yPsi, yFrame, yLow, yHigh, oddDerivE7YFrame, s1, s2]
  ring_nf
  simp [CharTwo.two_eq_zero]

theorem yForm_shift_neg_e2 (t : K) (c : (Fin Tag.E7.rank → ℤ) → K) :
    yQc (fun ρ => c ρ + if ρ - (-yFormE 2) ∈ yPsi then
      t * c (ρ - (-yFormE 2)) else 0) = yQc c := by
  have s1 : yFormR2 + yFormE 2 = yFormR4 := by decide +kernel
  have s2 : yFormR5 + yFormE 2 = yFormR3 := by decide +kernel
  simp only [yQc, yForm_pair_eq]
  simp +decide [yPsi, yFrame, yLow, yHigh, oddDerivE7YFrame, s1, s2]
  ring_nf
  simp [CharTwo.two_eq_zero]

theorem yForm_shift_e3 (t : K) (c : (Fin Tag.E7.rank → ℤ) → K) :
    yQc (fun ρ => c ρ + if ρ - yFormE 3 ∈ yPsi then
      t * c (ρ - yFormE 3) else 0) = yQc c := by
  have s1 : yFormR6 - yFormE 3 = yFormR4 := by decide +kernel
  have s2 : yFormR5 - yFormE 3 = yFormR7 := by decide +kernel
  simp only [yQc, yForm_pair_eq]
  simp +decide [yPsi, yFrame, yLow, yHigh, oddDerivE7YFrame, s1, s2]
  ring_nf
  simp [CharTwo.two_eq_zero]

theorem yForm_shift_neg_e3 (t : K) (c : (Fin Tag.E7.rank → ℤ) → K) :
    yQc (fun ρ => c ρ + if ρ - (-yFormE 3) ∈ yPsi then
      t * c (ρ - (-yFormE 3)) else 0) = yQc c := by
  have s1 : yFormR4 + yFormE 3 = yFormR6 := by decide +kernel
  have s2 : yFormR7 + yFormE 3 = yFormR5 := by decide +kernel
  simp only [yQc, yForm_pair_eq]
  simp +decide [yPsi, yFrame, yLow, yHigh, oddDerivE7YFrame, s1, s2]
  ring_nf
  simp [CharTwo.two_eq_zero]

theorem yForm_shift_e4 (t : K) (c : (Fin Tag.E7.rank → ℤ) → K) :
    yQc (fun ρ => c ρ + if ρ - yFormE 4 ∈ yPsi then
      t * c (ρ - yFormE 4) else 0) = yQc c := by
  have s1 : yFormR8 - yFormE 4 = yFormR6 := by decide +kernel
  have s2 : yFormR7 - yFormE 4 = yFormR9 := by decide +kernel
  simp only [yQc, yForm_pair_eq]
  simp +decide [yPsi, yFrame, yLow, yHigh, oddDerivE7YFrame, s1, s2]
  ring_nf
  simp [CharTwo.two_eq_zero]

theorem yForm_shift_neg_e4 (t : K) (c : (Fin Tag.E7.rank → ℤ) → K) :
    yQc (fun ρ => c ρ + if ρ - (-yFormE 4) ∈ yPsi then
      t * c (ρ - (-yFormE 4)) else 0) = yQc c := by
  have s1 : yFormR9 + yFormE 4 = yFormR7 := by decide +kernel
  have s2 : yFormR6 + yFormE 4 = yFormR8 := by decide +kernel
  simp only [yQc, yForm_pair_eq]
  simp +decide [yPsi, yFrame, yLow, yHigh, oddDerivE7YFrame, s1, s2]
  ring_nf
  simp [CharTwo.two_eq_zero]

theorem yForm_shift_e6 (t : K) (c : (Fin Tag.E7.rank → ℤ) → K) :
    yQc (fun ρ => c ρ + if ρ - yFormE 6 ∈ yPsi then
      t * c (ρ - yFormE 6) else 0) = yQc c := by
  simp only [yQc, yForm_pair_eq]
  simp +decide [yPsi, yFrame, yLow, yHigh, oddDerivE7YFrame]

theorem yForm_shift_neg_e6 (t : K) (c : (Fin Tag.E7.rank → ℤ) → K) :
    yQc (fun ρ => c ρ + if ρ - (-yFormE 6) ∈ yPsi then
      t * c (ρ - (-yFormE 6)) else 0) = yQc c := by
  simp only [yQc, yForm_pair_eq]
  simp +decide [yPsi, yFrame, yLow, yHigh, oddDerivE7YFrame]

theorem yForm_pair_sum :
    ∀ p ∈ yPairRoots, p.1 + p.2 = yOmega := by
  decide +kernel

theorem yForm_pair_mem :
    ∀ p ∈ yPairRoots, p.1 ∈ yPsi ∧ p.2 ∈ yPsi := by
  decide +kernel

theorem yQc_congr {R : Type} [CommRing R] {c d : (Fin Tag.E7.rank → ℤ) → R}
    (h : ∀ β ∈ yPsi, c β = d β) : yQc c = yQc d := by
  simp only [yQc]
  congr 1
  refine List.map_congr_left fun p hp => ?_
  obtain ⟨h1, h2⟩ := yForm_pair_mem p hp
  rw [h p.1 h1, h p.2 h2]

theorem yQc_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (c : (Fin Tag.E7.rank → ℤ) → R) : yQc (fun β => f (c β)) = f (yQc c) := by
  unfold yQc
  rw [map_list_sum, List.map_map]
  congr 1
  refine List.map_congr_left fun p _ => ?_
  simp only [Function.comp_apply, map_mul]

theorem yForm_yQc_yCoeff : yQc (yCoeff (K := K)) = 1 := by
  simp only [yQc, yPairRoots, yCoeff, yFrame, oddDerivE7YFrame]
  simp +decide

theorem yForm_list_sum_sq (l : List K) : l.sum ^ 2 = (l.map (· ^ 2)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.sum_cons, List.map_cons, List.sum_cons, add_sq, ih]
    simp [CharTwo.two_eq_zero]

theorem yForm_yQc_sq {c : (Fin Tag.E7.rank → ℤ) → K}
    (hc : ∀ β ∈ yPsi, c β ^ 2 = c β) : yQc c ^ 2 = yQc c := by
  simp only [yQc]
  rw [yForm_list_sum_sq, List.map_map]
  congr 1
  refine List.map_congr_left fun p hp => ?_
  obtain ⟨h1, h2⟩ := yForm_pair_mem p hp
  simp only [Function.comp_apply]
  rw [mul_pow, hc p.1 h1, hc p.2 h2]

section Certs

theorem yForm_rootChar_smul (a : Fin Tag.E7.rank → Kˣ)
    (c : (Fin Tag.E7.rank → ℤ) → K) :
    yQc (fun β => (rootChar a β : K) * c β) = (rootChar a yOmega : K) * yQc c := by
  simp only [yQc]
  rw [← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun p hp => ?_
  have hsum := yForm_pair_sum p hp
  have hχ : (rootChar a p.1 : K) * (rootChar a p.2 : K) = (rootChar a yOmega : K) := by
    rw [← Units.val_mul, ← rootChar_add, hsum]
  calc ((rootChar a p.1 : K) * c p.1) * ((rootChar a p.2 : K) * c p.2)
      = ((rootChar a p.1 : K) * (rootChar a p.2 : K)) * (c p.1 * c p.2) := by ring
    _ = (rootChar a yOmega : K) * (c p.1 * c p.2) := by rw [hχ]

theorem yForm_rootDiag_conj {a : Fin Tag.E7.rank → Kˣ}
    (hh : rootDiagUnit .E7 a ∈ torusGroup .E7 K) (c : (Fin Tag.E7.rank → ℤ) → K) :
    rootDiagUnit .E7 a * rootProd .E7 K yPsi c * (rootDiagUnit .E7 a)⁻¹ =
      rootProd .E7 K yPsi (fun β => (rootChar a β : K) * c β) := by
  rw [E6Pilot.conj_rootProd_of_mem_torusGroup hh (fun _ hβ => isRoot_of_mem_yPsi hβ) c]
  refine E6Pilot.rootProd_congr fun β hβ => ?_
  rw [torusRootChar_eq_of_apply (isRoot_of_mem_yPsi hβ)
    (rootDiag_rootVec a (isRoot_of_mem_yPsi hβ))]
theorem yForm_yLevel_single {j : Fin Tag.E7.rank} (hj : j ≠ 5) :
    yLevel (yFormE j) = 0 := by
  simp only [yFormE, yLevel]
  exact Pi.single_eq_of_ne (M := fun _ => ℤ) (Ne.symm hj) (1 : ℤ)

theorem yForm_yLevel_neg_single {j : Fin Tag.E7.rank} (hj : j ≠ 5) :
    yLevel (-yFormE j) = 0 := by
  rw [yLevel_neg, yForm_yLevel_single hj, neg_zero]

theorem yForm_ne_sub_of_level_zero {α ρ : Fin Tag.E7.rank → ℤ} (hα0 : yLevel α = 0)
    (hρ : ρ ∈ yPsi) (h : α = ρ - α) : False := by
  have hρ2 := level_of_mem_yPsi hρ
  have e : ρ = α + α := by
    calc ρ = (ρ - α) + α := by abel
      _ = α + α := by rw [← h]
  rw [e, yLevel_add, hα0, add_zero] at hρ2
  omega

theorem yForm_conjCoeff_apply {α : Fin Tag.E7.rank → ℤ} (hα0 : yLevel α = 0) (t : K)
    (c : (Fin Tag.E7.rank → ℤ) → K) {ρ : Fin Tag.E7.rank → ℤ} (hρ : ρ ∈ yPsi) :
    conjCoeff α t yPsi c ρ = c ρ + if ρ - α ∈ yPsi then t * c (ρ - α) else 0 := by
  rw [conjCoeff_apply_ite yPsi_nodup (fun _ h => isRoot_of_mem_yPsi h) α t c hρ]
  by_cases h : ρ - α ∈ yPsi
  · rw [ite_eq_left ⟨h, fun he => yForm_ne_sub_of_level_zero hα0 hρ he⟩, ite_eq_left h]
  · rw [ite_eq_right fun h' => h h'.1, ite_eq_right h]

theorem yForm_conjCoeff_single {j : Fin Tag.E7.rank} (hj : j ≠ 5) (t : K)
    (c : (Fin Tag.E7.rank → ℤ) → K) :
    yQc (conjCoeff (yFormE j) t yPsi c) = yQc c := by
  have hα0 := yForm_yLevel_single hj
  have hshift : yQc (fun ρ => c ρ + if ρ - yFormE j ∈ yPsi then
      t * c (ρ - yFormE j) else 0) = yQc c := by
    fin_cases j
    · exact yForm_shift_e0 t c
    · exact yForm_shift_e1 t c
    · exact yForm_shift_e2 t c
    · exact yForm_shift_e3 t c
    · exact yForm_shift_e4 t c
    · exact (hj rfl).elim
    · exact yForm_shift_e6 t c
  exact (yQc_congr fun ρ hρ => yForm_conjCoeff_apply hα0 t c hρ).trans hshift

theorem yForm_conjCoeff_neg_single {j : Fin Tag.E7.rank} (hj : j ≠ 5) (t : K)
    (c : (Fin Tag.E7.rank → ℤ) → K) :
    yQc (conjCoeff (-yFormE j) t yPsi c) = yQc c := by
  have hα0 := yForm_yLevel_neg_single hj
  have hshift : yQc (fun ρ => c ρ + if ρ - (-yFormE j) ∈ yPsi then
      t * c (ρ - (-yFormE j)) else 0) = yQc c := by
    fin_cases j
    · exact yForm_shift_neg_e0 t c
    · exact yForm_shift_neg_e1 t c
    · exact yForm_shift_neg_e2 t c
    · exact yForm_shift_neg_e3 t c
    · exact yForm_shift_neg_e4 t c
    · exact (hj rfl).elim
    · exact yForm_shift_neg_e6 t c
  exact (yQc_congr fun ρ hρ => yForm_conjCoeff_apply hα0 t c hρ).trans hshift
def yFormPres (g : ModGL .E7 K) : Prop :=
  ∃ μ : K, μ ≠ 0 ∧ ∀ c c' : (Fin Tag.E7.rank → ℤ) → K,
    g * rootProd .E7 K yPsi c * g⁻¹ = rootProd .E7 K yPsi c' → yQc c' = μ * yQc c

noncomputable def yFormSubgroup : Subgroup (ModGL .E7 K) where
  carrier := {g | g ∈ linConjSubgroup K yPsi ∧ yFormPres (K := K) g}
  mul_mem' := by
    rintro g h ⟨hgL, μg, hμg, hgQ⟩ ⟨hhL, μh, hμh, hhQ⟩
    refine ⟨mul_mem hgL hhL, μg * μh, mul_ne_zero hμg hμh, ?_⟩
    intro c c' hconj
    obtain ⟨c1, hc1, -⟩ := hhL.1 c
    have hg1 : g * rootProd .E7 K yPsi c1 * g⁻¹ = rootProd .E7 K yPsi c' := by
      calc g * rootProd .E7 K yPsi c1 * g⁻¹
          = g * (h * rootProd .E7 K yPsi c * h⁻¹) * g⁻¹ := by rw [hc1]
        _ = (g * h) * rootProd .E7 K yPsi c * (g * h)⁻¹ := by group
        _ = rootProd .E7 K yPsi c' := hconj
    rw [hgQ c1 c' hg1, hhQ c c1 hc1]
    ring
  one_mem' := by
    refine ⟨one_mem _, 1, one_ne_zero, ?_⟩
    intro c c' hconj
    have hcc : ∀ β ∈ yPsi, c' β = c β := by
      refine rootProd_injective yPsi_nodup (fun β hβ => pos_of_mem_yPsi hβ) ?_
      simpa using hconj.symm
    simpa using yQc_congr hcc
  inv_mem' := by
    rintro g ⟨hgL, μ, hμ, hgQ⟩
    refine ⟨inv_mem hgL, μ⁻¹, inv_ne_zero hμ, ?_⟩
    intro c c' hconj
    have hconj' : g * rootProd .E7 K yPsi c' * g⁻¹ = rootProd .E7 K yPsi c := by
      have := congrArg (fun z => g * z * g⁻¹) hconj
      simpa [mul_assoc] using this.symm
    have h := hgQ c' c hconj'
    rw [h, inv_mul_cancel_left₀ hμ]

theorem yForm_mem_parabolicRadical {α : Fin Tag.E7.rank → ℤ}
    (hα : α ∈ parabolicRadicalRoots .E7 yNodes) (t : K) :
    pinnedX .E7 K α t ∈ parabolicRadical .E7 K yNodes :=
  Subgroup.mem_iSup_of_mem α (Subgroup.mem_iSup_of_mem hα (Subgroup.subset_closure ⟨t, rfl⟩))

theorem yForm_pinnedX_mem {α : Fin Tag.E7.rank → ℤ} (hα : IsRoot .E7 α) (hα0 : 0 ≤ yLevel α)
    (hαl : ∀ β ∈ yPsi, α ≠ -β ∧ (IsRoot .E7 (α + β) → α + β ∈ yPsi)) (t : K)
    (hshift : ∀ c : (Fin Tag.E7.rank → ℤ) → K, yQc (conjCoeff α t yPsi c) = yQc c) :
    pinnedX .E7 K α t ∈ yFormSubgroup (K := K) := by
  refine ⟨pinnedX_mem_linConjSubgroup yPsi_nodup (fun _ hβ => isRoot_of_mem_yPsi hβ)
    yPsi_comm hα hαl t, 1, one_ne_zero, ?_⟩
  intro c c' hconj
  have heq := conj_rootProd_yPsi hα hα0 t c
  have hcc : ∀ β ∈ yPsi, c' β = conjCoeff α t yPsi c β := by
    refine rootProd_injective yPsi_nodup (fun β hβ => pos_of_mem_yPsi hβ) ?_
    rw [← heq, hconj]
  rw [yQc_congr hcc, hshift c]
  ring

theorem yForm_radical_pinnedX_mem {α : Fin Tag.E7.rank → ℤ}
    (hα : α ∈ parabolicRadicalRoots .E7 yNodes) (t : K) :
    pinnedX .E7 K α t ∈ yFormSubgroup (K := K) := by
  have hroot := hα.1.1
  have hlev := yLevel_pos_of_mem_parabolicRadicalRoots hα
  have hαl : ∀ β ∈ yPsi, α ≠ -β ∧ (IsRoot .E7 (α + β) → α + β ∈ yPsi) :=
    conj_hyp_of_yLevel_nonneg (by omega)
  refine ⟨pinnedX_mem_linConjSubgroup yPsi_nodup (fun _ hβ => isRoot_of_mem_yPsi hβ)
    yPsi_comm hroot hαl t, 1, one_ne_zero, ?_⟩
  intro c c' hconj
  have hcomm := mem_centralizer_singleton_iff.1
    (parabolicRadical_le_centralizer_rootProd_yPsi c (yForm_mem_parabolicRadical hα t))
  have hx : pinnedX .E7 K α t * rootProd .E7 K yPsi c * (pinnedX .E7 K α t)⁻¹ =
      rootProd .E7 K yPsi c := by
    rw [hcomm, mul_inv_cancel_right]
  have hcc : ∀ β ∈ yPsi, c' β = c β := by
    refine rootProd_injective yPsi_nodup (fun β hβ => pos_of_mem_yPsi hβ) ?_
    rw [← hconj, hx]
  rw [yQc_congr hcc]
  ring

theorem yForm_parabolicRadical_le :
    parabolicRadical .E7 K yNodes ≤ yFormSubgroup (K := K) :=
  iSup₂_le fun α hα => (Subgroup.closure_le _).2 (by
    rintro _ ⟨t, rfl⟩
    exact yForm_radical_pinnedX_mem hα t)

theorem yForm_torus_le : torusGroup .E7 K ≤ yFormSubgroup (K := K) := by
  intro h hh
  refine ⟨torusGroup_le_linConjSubgroup (fun _ hβ => isRoot_of_mem_yPsi hβ) hh, ?_⟩
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  refine ⟨(rootChar a yOmega : K), Units.ne_zero _, ?_⟩
  intro c c' hconj
  have hconj' := yForm_rootDiag_conj hh c
  have hcc : ∀ β ∈ yPsi, c' β = (rootChar a β : K) * c β := by
    refine rootProd_injective yPsi_nodup (fun β hβ => pos_of_mem_yPsi hβ) ?_
    rw [← hconj', hconj]
  rw [yQc_congr hcc, yForm_rootChar_smul]

theorem yForm_parabolicLevi_le :
    parabolicLevi .E7 K yNodes ≤ yFormSubgroup (K := K) := by
  refine sup_le yForm_torus_le ((Subgroup.closure_le _).2 ?_)
  rintro _ ⟨j, hj, t, rfl | rfl⟩
  · rw [← pinnedX_single]
    refine yForm_pinnedX_mem (isRoot_single .E7 j) ?_ ?_ t (fun c => yForm_conjCoeff_single hj t c)
    · simpa [yFormE, Pi.single] using (yForm_yLevel_single hj).ge
    · exact conj_hyp_of_yLevel_nonneg (by
        simpa [yFormE, Pi.single] using (yForm_yLevel_single hj).ge)
  · rw [← pinnedX_neg_single]
    refine yForm_pinnedX_mem (isRoot_neg_single .E7 j) ?_ ?_ t
      (fun c => yForm_conjCoeff_neg_single hj t c)
    · simpa [yFormE, Pi.single] using (yForm_yLevel_neg_single hj).ge
    · exact conj_hyp_of_yLevel_nonneg (by
        simpa [yFormE, Pi.single] using (yForm_yLevel_neg_single hj).ge)

theorem yForm_parabolic_le :
    parabolicSubgroup .E7 K yNodes ≤ yFormSubgroup (K := K) := by
  rw [← parabolicRadical_sup_parabolicLevi yNodes]
  exact sup_le yForm_parabolicRadical_le yForm_parabolicLevi_le

theorem yQc_conj_parabolic {z : ModGL .E7 K} (hz : z ∈ parabolicSubgroup .E7 K yNodes) :
    ∃ μ : K, μ ≠ 0 ∧ ∀ c c' : (Fin Tag.E7.rank → ℤ) → K,
      z * rootProd .E7 K yPsi c * z⁻¹ = rootProd .E7 K yPsi c' → yQc c' = μ * yQc c :=
  (yForm_parabolic_le hz).2

theorem yQc_eq_one_of_conj_yAS {L : Type} [Field L] [CharP L 2] {z : ModGL .E7 L}
    (hz : z ∈ parabolicSubgroup .E7 L yNodes)
    {c : (Fin Tag.E7.rank → ℤ) → L} (hc : z * yAS L * z⁻¹ = rootProd .E7 L yPsi c)
    (hc2 : ∀ β ∈ yPsi, c β ^ 2 = c β) : yQc c = 1 := by
  have hc0 : z * rootProd .E7 L yPsi (yCoeff (K := L)) * z⁻¹ =
      rootProd .E7 L yPsi c := by
    rw [← rootProd_yPsi_yCoeff] at hc
    exact hc
  obtain ⟨μ, hμ, hQ⟩ := yQc_conj_parabolic hz
  have hQc : yQc c = μ := by
    have h := hQ (yCoeff (K := L)) c hc0
    rwa [yForm_yQc_yCoeff, mul_one] at h
  have hsq : yQc c ^ 2 = yQc c := yForm_yQc_sq hc2
  have h01 : yQc c = 0 ∨ yQc c = 1 := by
    have h : yQc c * (yQc c - 1) = 0 := by
      rw [mul_sub, mul_one, ← sq, hsq, sub_self]
    rcases mul_eq_zero.1 h with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.1 h1)
  rcases h01 with h0 | h1
  · rw [h0] at hQc
    exact absurd hQc.symm hμ
  · exact h1

end Certs

end CFSG.SeitzReduction.E7Pilot
