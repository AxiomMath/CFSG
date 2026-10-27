module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic.Basic
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic.PerfectKer
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherParabolicData

public noncomputable section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.AGLEmbedding.ParabPrime (perfectJoin perfectJoin_le perfectJoin_perfect le_perfectJoin)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (flagStabilizer)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (flag stabilizer mem_stabilizer mem_flag_of_le mem_isoFlag)

variable {r : ℕ} {K : Type} [Field K]

theorem spMat_mulVec_mem_of_mem_stabilizer {W : Submodule K (Fin r ⊕ Fin r → K)}
    {g : StatedSp r K} (hg : g ∈ stabilizer r K W) {u : Fin r ⊕ Fin r → K} (hu : u ∈ W) :
    spMat g *ᵥ u ∈ W := by
  have h : mulVecLin (spMat g) u ∈ W.map (mulVecLin (spMat g)) := Submodule.mem_map_of_mem hu
  rw [mem_stabilizer.mp hg] at h
  exact h

theorem single_mem_flag {i : ℕ} (hir : i ≤ r) (n : ℕ) (hn : n < r) (hni : n < i) :
    (Pi.single (Sum.inl ⟨n, hn⟩) 1 : Fin r ⊕ Fin r → K) ∈ flag r K i := by
  rw [mem_flag_of_le hir, mem_isoFlag]
  refine ⟨fun j => ?_, fun j hj => ?_⟩
  · exact Pi.single_eq_of_ne (by simp) _
  · refine Pi.single_eq_of_ne ?_ _
    intro h
    have := Sum.inl_injective h
    have h2 : (j : ℕ) = n := by simpa using congrArg Fin.val this
    omega

theorem col_support {I : Set ℕ} (hI : ∀ i ∈ I, 1 ≤ i ∧ i ≤ r) {i : ℕ} (hi : i ∈ I)
    {h : StatedSp r K} (hh : h ∈ flagStabilizer r K I) (n : ℕ) (hn : n < r) (hni : n + 1 = i)
    (x : Fin r ⊕ Fin r) (hx : spMat h x (Sum.inl ⟨n, hn⟩) ≠ 0) :
    ∃ j : Fin r, x = Sum.inl j ∧ (j : ℕ) ≤ n := by
  have hmem := spMat_mulVec_mem_of_mem_stabilizer (SymplecticHigher.mem_flagStabilizer.mp hh i hi)
    (single_mem_flag (r := r) (K := K) (hI i hi).2 n hn (by omega))
  rw [mem_flag_of_le (hI i hi).2, mem_isoFlag] at hmem
  rw [Matrix.mulVec_single_one] at hmem
  cases x with
  | inr j => exact absurd (hmem.1 j) hx
  | inl j =>
    refine ⟨j, rfl, ?_⟩
    by_contra hj
    exact hx (hmem.2 j (by omega))

theorem chi_mul {I : Set ℕ} (hI : ∀ i ∈ I, 1 ≤ i ∧ i ≤ r) {i : ℕ} (hi : i ∈ I)
    (hi1 : i = 1 ∨ i - 1 ∈ I) (n : ℕ) (hn : n < r) (hni : n + 1 = i)
    {g h : StatedSp r K} (hg : g ∈ flagStabilizer r K I) (hh : h ∈ flagStabilizer r K I) :
    spMat (g * h) (Sum.inl ⟨n, hn⟩) (Sum.inl ⟨n, hn⟩) =
      spMat g (Sum.inl ⟨n, hn⟩) (Sum.inl ⟨n, hn⟩) * spMat h (Sum.inl ⟨n, hn⟩) (Sum.inl ⟨n, hn⟩) := by
  rw [spMat_mul, Matrix.mul_apply]
  refine Finset.sum_eq_single (Sum.inl (⟨n, hn⟩ : Fin r)) (fun x _ hx => ?_) (by simp)
  by_cases h0 : spMat h x (Sum.inl ⟨n, hn⟩) = 0
  · rw [h0, mul_zero]
  obtain ⟨j, rfl, hjn⟩ := col_support hI hi hh n hn hni x h0
  have hjn' : (j : ℕ) < n := by
    refine lt_of_le_of_ne hjn fun hjn2 => hx ?_
    congr 2
    exact Fin.ext hjn2
  have hn' : n ∈ I := by
    rcases hi1 with h1 | h1
    · omega
    · have : i - 1 = n := by omega
      rwa [this] at h1
  have hmem := spMat_mulVec_mem_of_mem_stabilizer (SymplecticHigher.mem_flagStabilizer.mp hg n hn')
    (single_mem_flag (r := r) (K := K) hn.le (j : ℕ) j.2 hjn')
  rw [mem_flag_of_le hn.le, mem_isoFlag] at hmem
  rw [Matrix.mulVec_single_one] at hmem
  have := hmem.2 ⟨n, hn⟩ le_rfl
  simp only [Matrix.col_apply] at this
  rw [this, zero_mul]

theorem exists_fixed_vector_of_mem_perfectJoin [Finite K] {I : Set ℕ}
    (hI : ∀ i ∈ I, 1 ≤ i ∧ i ≤ r) {i : ℕ} (hi : i ∈ I) (hi1 : i = 1 ∨ i - 1 ∈ I) {p : ℕ}
    {v : StatedSp r K} (hv : v ∈ perfectJoin (flagStabilizer r K I)) (hvp : v ^ p = 1)
    (hp : (p : K) ≠ 0) :
    ∃ a ∈ flag r K i, a ≠ 0 ∧ spMat v *ᵥ a = a := by
  obtain ⟨hir1, hir2⟩ := hI i hi
  obtain ⟨n, hni⟩ : ∃ n, n + 1 = i := ⟨i - 1, by omega⟩
  have hn : n < r := by omega
  set J := flagStabilizer r K I with hJ
  set x0 : Fin r ⊕ Fin r := Sum.inl ⟨n, hn⟩ with hx0
  let f : ↥J →* K :=
    { toFun := fun g => spMat (g : StatedSp r K) x0 x0
      map_one' := by simp [spMat_one]
      map_mul' := fun g h => chi_mul hI hi hi1 n hn hni g.2 h.2 }
  obtain ⟨hvJ, hv1⟩ := exists_mem_ker_of_mem_perfectJoin J f.toHomUnits hv
  have hf1 : f ⟨v, hvJ⟩ = 1 := by
    have := congrArg Units.val hv1
    simpa using this
  have hpow : ∀ j : ℕ, v ^ j ∈ J := fun j => J.pow_mem hvJ j
  have hchi : ∀ j : ℕ, spMat (v ^ j) x0 x0 = 1 := by
    intro j
    have := map_pow f ⟨v, hvJ⟩ j
    rw [hf1, one_pow] at this
    exact this
  set E : Fin r ⊕ Fin r → K := Pi.single x0 1 with hE
  have hEF : E ∈ flag r K i := single_mem_flag hir2 n hn (by omega)
  refine ⟨∑ j ∈ Finset.range p, spMat (v ^ j) *ᵥ E, ?_, ?_, ?_⟩
  · exact Submodule.sum_mem _ fun j _ =>
      spMat_mulVec_mem_of_mem_stabilizer (SymplecticHigher.mem_flagStabilizer.mp (hpow j) i hi) hEF
  · intro h0
    have := congrFun h0 x0
    rw [Finset.sum_apply] at this
    have hcol : ∀ j : ℕ, (spMat (v ^ j) *ᵥ E) x0 = 1 := fun j => by
      rw [hE, Matrix.mulVec_single_one]
      exact hchi j
    simp only [hcol, Pi.zero_apply, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one] at this
    exact hp this
  · rw [Matrix.mulVec_sum]
    simp only [Matrix.mulVec_mulVec, ← spMat_mul, ← pow_succ']
    have h1 := Finset.sum_range_succ (fun j => spMat (v ^ j) *ᵥ E) p
    have h2 := Finset.sum_range_succ' (fun j => spMat (v ^ j) *ᵥ E) p
    rw [hvp] at h1
    simp only [pow_zero] at h1 h2
    have h3 := h1.symm.trans h2
    simpa using (add_right_cancel h3).symm

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic
