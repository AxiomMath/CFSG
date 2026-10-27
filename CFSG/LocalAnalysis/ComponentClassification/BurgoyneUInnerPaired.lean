module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUPairSlice
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUInnerSplit
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUPairNormal

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.U

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
open CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.Burgoyne.Proj

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

theorem innerPaired_propAConclusion (hp2 : p ≠ 2) (hn : 3 ≤ n)
    (hinj : Function.Injective (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
      MulAut (StatedProj (StatedSU n (p ^ f) K))))
    {X : Type} [Group X] [Finite X] {ψ : X →* MulAut (StatedProj (StatedSU n (p ^ f) K))}
    (hψ : Function.Injective ψ)
    (hInn : (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
      MulAut (StatedProj (StatedSU n (p ^ f) K))).range ≤ ψ.range)
    {t : X} {A : uU h n} (htA : ψ t = uConjAut h (by omega) A) {l : K} (hl0 : l ≠ 0)
    (hlN : h.norm l = -1)
    (hAA : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (l ^ 2) • 1)
    {Y : Subgroup X} (hY : Y ≠ ⊥) (hYO : Y ≤ oddCentralizerCore t) : PropAConclusion X t Y := by
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.charP
  have h2 : (2 : K) ≠ 0 := by
    intro e
    have e' : ((2 : ℕ) : K) = 0 := by exact_mod_cast e
    rw [CharP.cast_eq_zero_iff K p] at e'
    have := Nat.le_of_dvd (by norm_num) e'
    have := h.prime.two_le
    exact hp2 (by omega)
  set M := ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hM
  have hU : (M.map h.bar)ᵀ * M = 1 := (mem_uU h).1 A.2
  have hNi : h.bar l⁻¹ * l⁻¹ = -1 := by
    rw [map_inv₀, ← mul_inv, mul_comm, ← UnitaryFieldData.norm, hlN, inv_neg, inv_one]
  have hU' : ((l⁻¹ • M).map h.bar)ᵀ * (l⁻¹ • M) = -1 := by
    rw [show (l⁻¹ • M).map h.bar = h.bar l⁻¹ • M.map h.bar by
      ext i j; simp [map_mul]]
    rw [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hU, smul_smul, hNi, neg_one_smul]
  have hA'2 : (l⁻¹ • M) * (l⁻¹ • M) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hAA, smul_smul, smul_smul]
    rw [show l⁻¹ * l⁻¹ * l ^ 2 = 1 by field_simp, one_smul]
  obtain ⟨m, rfl⟩ := exists_half_of_antiunitary h h2 hU' hA'2
  have hm : 2 ≤ m := by omega
  obtain ⟨Hm, hHU, hHA⟩ := exists_paired_unitary_normal_form h h2 hU' hA'2 hl0 hlN
  set HG := uGL h Hm hHU with hHG
  have hHi : (((HG : GL (Fin (m + m)) K)⁻¹ : GL (Fin (m + m)) K) :
      Matrix (Fin (m + m)) (Fin (m + m)) K) = (Hm.map h.bar)ᵀ := rfl
  have hconj : (((HG : GL (Fin (m + m)) K)⁻¹ : GL (Fin (m + m)) K) :
      Matrix (Fin (m + m)) (Fin (m + m)) K) * M *
      ((HG : GL (Fin (m + m)) K) : Matrix (Fin (m + m)) (Fin (m + m)) K) =
        (1 : K) • ((uPairA (m := m) h h2 hl0 hlN : GL (Fin (m + m)) K) :
          Matrix (Fin (m + m)) (Fin (m + m)) K) := by
    rw [hHi, coe_uGL, coe_uPairA, one_smul]
    have e : M = l • (l⁻¹ • M) := by rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]
    rw [e, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hHA, ← Matrix.mul_assoc, hHU,
      Matrix.one_mul, prA, ← map_smul, fromBlocks_smul]
    congr 2
    · rw [smul_zero]
    · rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]
    · rw [smul_smul, ← sq]
    · rw [smul_zero]
  obtain ⟨ψ', hinj', hInn', hψ't⟩ := exists_conj_transfer h hn hψ hInn htA ⟨HG, uGL_mem h _ _⟩
    one_ne_zero hconj
  refine propAConclusion_of_transfer hinj' hY hYO fun Y' hY' hY'O => ?_
  rw [hψ't] at hY'O ⊢
  exact paired_propAConclusionIn h hp2 h2 hm hinj hInn' hl0 hlN hY' hY'O

end CFSG.ComponentClassification.Burgoyne.U
