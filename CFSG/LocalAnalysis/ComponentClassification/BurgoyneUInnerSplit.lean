module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUNormal
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUSlice

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.U

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
open CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (signMat conj_embedding eq_bot_of_oddCoreIn
  mul_conj_mul_inv)

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

theorem uConjAut_eq_of_eq_smul (hn : 3 ≤ n) {A A' : uU h n} {c : K} (hc : c ≠ 0)
    (hAA : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      c • ((A' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    uConjAut h (by omega) A = uConjAut h (by omega) A' := by
  have h1 : uConjAut h (by omega) (A'⁻¹ * A) = 1 := by
    refine (uConjAut_eq_one_iff h hn _).2 ⟨Units.mk0 c hc, Units.ext ?_⟩
    rw [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_inv, hAA, Matrix.mul_smul,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, GeneralLinearGroup.coe_scalar,
      Matrix.smul_one_eq_diagonal]
    rfl
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1.symm

theorem exists_conj_transfer (hn : 3 ≤ n) {X : Type} [Group X]
    {ψ : X →* MulAut (StatedProj (StatedSU n (p ^ f) K))} (hψ : Function.Injective ψ)
    (hInn : (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
      MulAut (StatedProj (StatedSU n (p ^ f) K))).range ≤ ψ.range)
    {t : X} {A A' : uU h n} (htA : ψ t = uConjAut h (by omega) A) (H : uU h n) {c : K}
    (hc : c ≠ 0)
    (hH : ((((H : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((H : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) =
        c • ((A' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    ∃ ψ' : X →* MulAut (StatedProj (StatedSU n (p ^ f) K)), Function.Injective ψ' ∧
      (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
        MulAut (StatedProj (StatedSU n (p ^ f) K))).range ≤ ψ'.range ∧
      ψ' t = uConjAut h (by omega) A' := by
  obtain ⟨hinj', hInn'⟩ := conj_embedding hψ hInn (uConjAut h (by omega) H⁻¹)
  refine ⟨_, hinj', hInn', ?_⟩
  change uConjAut h (by omega) H⁻¹ * ψ t * (uConjAut h (by omega) H⁻¹)⁻¹ = _
  rw [htA, ← map_inv, inv_inv, ← map_mul, ← map_mul]
  refine uConjAut_eq_of_eq_smul h hn hc ?_
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_mul]
  exact hH

theorem propAConclusion_of_transfer {X T : Type} [Group X] [Finite X] [Group T]
    {ψ' : X →* MulAut T} (hinj' : Function.Injective ψ') {t : X}
    {Y : Subgroup X} (hY : Y ≠ ⊥) (hYO : Y ≤ oddCentralizerCore t)
    (hA : ∀ Y' : Subgroup (MulAut T), Y' ≠ ⊥ →
      Y' ≤ oddCoreIn ψ'.range (ψ' t) → PropAConclusionIn ψ'.range (ψ' t) Y') :
    PropAConclusion X t Y := by
  apply PropAConclusion.of_injective hinj'
  refine hA _ (fun hmap => hY ((map_eq_bot_iff_of_injective _ hinj').1 hmap)) ?_
  rw [← map_oddCentralizerCore_of_injective hinj']
  exact map_mono hYO

theorem innerSplit_propAConclusion (hp2 : p ≠ 2) (hn : 3 ≤ n)
    (hinj : Function.Injective (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
      MulAut (StatedProj (StatedSU n (p ^ f) K))))
    {X : Type} [Group X] [Finite X] {ψ : X →* MulAut (StatedProj (StatedSU n (p ^ f) K))}
    (hψ : Function.Injective ψ)
    (hInn : (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
      MulAut (StatedProj (StatedSU n (p ^ f) K))).range ≤ ψ.range)
    {t : X} {A : uU h n} (htA : ψ t = uConjAut h (by omega) A) {l : K} (hl0 : l ≠ 0)
    (hlN : h.norm l = 1)
    (hAA : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (l ^ 2) • 1)
    (hns : ∀ c : Kˣ, (A : GL (Fin n) K) ≠ GeneralLinearGroup.scalar (Fin n) c)
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
  have hNi : h.bar l⁻¹ * l⁻¹ = 1 := by
    rw [map_inv₀, ← mul_inv, mul_comm, ← UnitaryFieldData.norm, hlN, inv_one]
  have hU' : ((l⁻¹ • M).map h.bar)ᵀ * (l⁻¹ • M) = 1 := by
    rw [show (l⁻¹ • M).map h.bar = h.bar l⁻¹ • M.map h.bar by
      ext i j; simp [map_mul]]
    rw [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hU, smul_smul, hNi, one_smul]
  have hA'2 : (l⁻¹ • M) * (l⁻¹ • M) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hAA, smul_smul, smul_smul]
    rw [show l⁻¹ * l⁻¹ * l ^ 2 = 1 by field_simp, one_smul]
  obtain ⟨Hm, J, hHU, hHA⟩ := exists_split_unitary_normal_form h h2 hU' hA'2
  set HG := uGL h Hm hHU with hHG
  have hHi : (((HG : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (Hm.map h.bar)ᵀ := rfl
  have hconj : (((HG : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M *
      ((HG : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = l • signMat K J := by
    rw [hHi, coe_uGL]
    have e : M = l • (l⁻¹ • M) := by rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]
    rw [e, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hHA, ← Matrix.mul_assoc, hHU,
      Matrix.one_mul]
  have hHH : Hm * (Hm.map h.bar)ᵀ = 1 := mul_eq_one_comm.1 hHU
  have hJ : ∃ a ∈ J, ∃ b, b ∉ J := by
    by_contra hcon
    push Not at hcon
    obtain ⟨s, hs, hsJ⟩ : ∃ s : K, s ≠ 0 ∧ signMat K J = s • 1 := by
      by_cases hne : J.Nonempty
      · obtain ⟨a, ha⟩ := hne
        refine ⟨-1, neg_ne_zero.2 one_ne_zero, ?_⟩
        ext i j
        simp [signMat, diagonal_apply, one_apply, hcon a ha i]
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        refine ⟨1, one_ne_zero, ?_⟩
        ext i j
        simp [signMat, diagonal_apply, one_apply, hne]
    have e : l⁻¹ • M = s • 1 := by
      calc l⁻¹ • M = (l⁻¹ • M) * (Hm * (Hm.map h.bar)ᵀ) := by rw [hHH, Matrix.mul_one]
        _ = (Hm * signMat K J) * (Hm.map h.bar)ᵀ := by rw [← Matrix.mul_assoc, hHA]
        _ = s • 1 := by
            rw [hsJ, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hHH]
    apply hns (Units.mk0 (l * s) (mul_ne_zero hl0 hs))
    apply Units.ext
    rw [GeneralLinearGroup.coe_scalar]
    change M = _
    have e2 : M = l • (l⁻¹ • M) := by rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]
    rw [e2, e, smul_smul, Matrix.smul_one_eq_diagonal]
    rfl
  obtain ⟨a, ha, b, hb⟩ := hJ
  obtain ⟨ψ', hinj', hInn', hψ't⟩ := exists_conj_transfer h hn hψ hInn htA ⟨HG, uGL_mem h _ _⟩
    hl0 (A' := uSign h J) (by rw [coe_uSign]; exact hconj)
  refine propAConclusion_of_transfer hinj' hY hYO fun Y' hY' hY'O => ?_
  rw [hψ't] at hY'O ⊢
  exact split_propAConclusionIn h hp2 hn hinj hInn' ha hb hY' hY'O

end CFSG.ComponentClassification.Burgoyne.U
