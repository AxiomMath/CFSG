module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic.Reduction
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic.FixedVector
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic.Siegel
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic.CycNodes
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherBorel

public noncomputable section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial CFSG.Open
open CFSG.AGLEmbedding.ParabPrime (perfectJoin perfectJoin_le perfectJoin_perfect le_perfectJoin)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (flagStabilizer borelCuts)
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic

theorem false_of_fixBarData_flagStabilizer_caseA {r : ℕ} {K : Type} [Field K] [Finite K]
    (hK : 4 ≤ Nat.card K) {p : ℕ} (hp0 : (p : K) ≠ 0) {I : Set ℕ}
    (hI : ∀ i ∈ I, 1 ≤ i ∧ i ≤ r) {i : ℕ} (hi : i ∈ I) (hi1 : i = 1 ∨ i - 1 ∈ I)
    {v : StatedSp r K} (hv : v ∈ perfectJoin (flagStabilizer r K I)) (hvp : v ^ p = 1)
    (hfix : ∀ V : Subgroup (StatedSp r K), V ≤ Subgroup.centralizer ({v} : Set (StatedSp r K)) →
      ⁅V, V⁆ = V → V ≤ flagStabilizer r K I) : False := by
  obtain ⟨a, haF, ha0, hva⟩ := exists_fixed_vector_of_mem_perfectJoin hI hi hi1 hv hvp hp0
  obtain ⟨W, b, hWC, hWp, hab, w, hwW, hwa⟩ := exists_perfect_escape hK hvp hp0 ha0 hva
  have hwJ : w ∈ flagStabilizer r K I := hfix W hWC hWp hwW
  have hws := SymplecticHigher.mem_flagStabilizer.1 hwJ i hi
  have hmem : spMat w *ᵥ a ∈ SymplecticFlag.flag r K i := by
    have := SymplecticFlag.mem_stabilizer.1 hws
    rw [← this]
    exact ⟨a, haF, rfl⟩
  rw [hwa] at hmem
  have hbF : b ∈ SymplecticFlag.flag r K i := by
    have := Submodule.sub_mem _ hmem haF
    simpa using this
  have hiso := SymplecticHigher.isCompleteIsotropicFlag_flag (r := r) (K := K)
  have h0 := hiso.2.2 i (hI i hi).2 a haF b hbF
  rw [hab] at h0
  exact one_ne_zero h0

theorem false_of_fixBarData_symplectic
    {r : ℕ} (hr : 1 ≤ r) {K : Type} [Field K] [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpK : p ∣ Nat.card K - 1)
    {J : Subgroup (CFSG.Assembly.LowTwoRank.StatedSp r K)}
    {v : CFSG.Assembly.LowTwoRank.StatedSp r K}
    (h : FixBarData J p v) : False := by
  obtain ⟨J', v', h', hB, -⟩ := exists_standard_fixBarData h
  have hp2 : ¬ 2 ∣ p := fun hd => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 hd
    omega
  have hp0 : (p : K) ≠ 0 := fun h0 => hp2 ((CharP.cast_eq_zero_iff K 2 p).1 h0)
  obtain ⟨I, hI, rfl⟩ : ∃ I : Set ℕ, (∀ i ∈ I, 1 ≤ i ∧ i ≤ r) ∧ J' = flagStabilizer r K I :=
    ⟨borelCuts K J', SymplecticHigher.borelCuts_le J', (SymplecticHigher.borel_overgroups J' hB).1⟩
  have hI0 : I.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    apply h'.ne_top
    rw [hne, SymplecticHigher.flagStabilizer_empty]
  have hv' : v' ∈ perfectJoin (flagStabilizer r K I) := h'.join
  have hfix := h'.fix
  have hcyc := h'.cyc
  by_cases hA : ∃ i ∈ I, i = 1 ∨ i - 1 ∈ I
  · obtain ⟨i, hi, hi1⟩ := hA
    exact false_of_fixBarData_flagStabilizer_caseA hK hp0 hI hi hi1 hv' h'.pow hfix
  · push Not at hA
    have hIr : ∀ i ∈ I, i ≤ r := fun i hi => (hI i hi).2
    by_cases hr3 : 3 ≤ r
    · have h1 : 1 ∉ I := fun h1 => (hA 1 h1).1 rfl
      by_cases h3 : 3 ∈ I
      · have h2 : 2 ∉ I := (hA 3 h3).2
        exact false_of_cyc_one_two hK hp hpK hr3 hIr h1 h2 hcyc
      · exact false_of_cyc_one_three hK hp hpK hr3 hIr h1 h3 hcyc
    · obtain ⟨i, hi⟩ := hI0
      have hi1 := (hI i hi)
      have hi' := hA i hi
      by_cases hr2 : r = 2
      · subst hr2
        have : I = {2} := by
          ext j
          constructor
          · intro hj
            have := hI j hj
            have := (hA j hj).1
            simp only [Set.mem_singleton_iff]
            omega
          · intro hj
            rw [Set.mem_singleton_iff] at hj
            have := hI i hi
            have := hA i hi
            subst hj
            have : i = 2 := by omega
            rw [← this]; exact hi
        subst this
        exact false_of_siegel hK hp hp5 hpK hv' h'.pow h'.ne_one hfix
      · omega

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus
