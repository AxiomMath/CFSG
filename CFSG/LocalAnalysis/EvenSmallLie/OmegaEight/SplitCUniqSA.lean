module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SplitCUniqW
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SplitCUniqSADefs
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeSylow
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEightMinus.NativeSylow

public section

namespace CFSG.EvenSmallLie.OmegaEight.SplitC

open CFSG.EvenSmallLie.OmegaEight (matMulM idCode matMulM_lt)

section Plus

open OmegaEight


theorem saElt_mul_eq_iff {a b c d : ℕ} (ha : a < 8192) (hb : b < 8192) (hc : c < 8192)
    (hd : d < 8192) : saElt a * saElt b = saElt c * saElt d ↔
      matMulM (saMat a) (saMat b) = matMulM (saMat c) (saMat d) := by
  have hs := sa_facts
  have h1 := acts_mul (saElt_spec hs a ha).2 (saElt_spec hs b hb).2
  have h2 := acts_mul (saElt_spec hs c hc).2 (saElt_spec hs d hd).2
  have m1 := sylowT.mul_mem (saElt_spec hs a ha).1 (saElt_spec hs b hb).1
  have m2 := sylowT.mul_mem (saElt_spec hs c hc).1 (saElt_spec hs d hd).1
  constructor
  · intro h
    rw [h] at h1
    exact acts_unique hs (matMulM_lt _ _) (matMulM_lt _ _) h1 h2
  · intro h
    rw [h] at h1
    exact eq_of_acts hs m1 m2 (matMulM_lt _ _) h1 h2

theorem saElt_zero : saElt 0 = 1 := by
  rw [saElt]
  simp

theorem sq_eq_one_iff {i : ℕ} (hi : i < 8192) :
    saElt i * saElt i = 1 ↔ matMulM (saMat i) (saMat i) = idCode := by
  have hs := sa_facts
  have h1 := acts_mul (saElt_spec hs i hi).2 (saElt_spec hs i hi).2
  constructor
  · intro h
    rw [h] at h1
    exact acts_unique hs (matMulM_lt _ _) (by rw [← hs.id0]; exact saMat_lt 0) h1 acts_one
  · intro h
    rw [h] at h1
    exact eq_of_acts hs (sylowT.mul_mem (saElt_spec hs i hi).1 (saElt_spec hs i hi).1)
      sylowT.one_mem (by rw [← hs.id0]; exact saMat_lt 0) h1 acts_one

theorem sylowT_plus_uniqueW {W : UniqWit} (hJ : W.J = 38) (hy : W.y = yIdx)
    (hcl : W.cl = fun i => (invW i).1) (h : uniqCheckW 8192 commP conjP invP W = true)
    (F₁ F₂ : Subgroup (Equiv.Perm (Fin 360))) (h₁ : IsNSC sylowT F₁ 64)
    (h₂ : IsNSC sylowT F₂ 64) : F₁ = F₂ := by
  have hs := sa_facts
  refine eq_of_uniqCheckW (e := saElt) (fun i hi => (saElt_spec hs i hi).1)
    (fun g hg => exists_saElt hs hg) (fun i hi k hk => saElt_inj hs hi hk) ?_ ?_ ?_ ?_ h h₁ h₂
  · intro i hi k hk
    rw [commP, beq_iff_eq]
    exact (saElt_mul_eq_iff hi hk hk hi).symm
  · intro c hc a ha w hw hcw
    rw [conjP, beq_iff_eq] at hcw
    exact (saElt_mul_eq_iff hc ha hw hc).2 hcw
  · intro i hi hsq h1
    have hi0 : i ≠ 0 := by
      rintro rfl
      exact h1 saElt_zero
    simp only [invP, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
    exact ⟨hi0, (sq_eq_one_iff hi).1 hsq⟩
  · intro i hi hinv
    simp only [invP, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hinv
    obtain ⟨hj, hc, hci, hcci, hcyc⟩ := hs.invol i hi hinv.1 hinv.2
    rw [hJ, hy, hcl]
    refine ⟨hj, (invW i).2.1, hc, ?_⟩
    have e1 : saElt (invW i).2.1 * saElt (invW i).2.2 = 1 := by
      have a1 := acts_mul (saElt_spec hs _ hc).2 (saElt_spec hs _ hci).2
      rw [hcci] at a1
      exact eq_of_acts hs (sylowT.mul_mem (saElt_spec hs _ hc).1 (saElt_spec hs _ hci).1)
        sylowT.one_mem (by rw [← hs.id0]; exact saMat_lt 0) a1 acts_one
    have e2 : saElt (invW i).2.1 * saElt (yIdx (invW i).1) * saElt (invW i).2.2 = saElt i := by
      have hyl := (hs.reps _ hj).1
      have a1 := acts_mul (acts_mul (saElt_spec hs _ hc).2 (saElt_spec hs _ hyl).2)
        (saElt_spec hs _ hci).2
      rw [hcyc] at a1
      exact eq_of_acts hs (sylowT.mul_mem (sylowT.mul_mem (saElt_spec hs _ hc).1
        (saElt_spec hs _ hyl).1) (saElt_spec hs _ hci).1) (saElt_spec hs i hi).1 (saMat_lt i)
        a1 (saElt_spec hs i hi).2
    have e3 : saElt (invW i).2.2 = (saElt (invW i).2.1)⁻¹ := eq_inv_of_mul_eq_one_right e1
    rw [e3] at e2
    rw [← e2]
    group

end Plus

end CFSG.EvenSmallLie.OmegaEight.SplitC

namespace CFSG.EvenSmallLie.OmegaEightMinus

open CFSG.EvenSmallLie.OmegaEight (matMulM idCode matMulM_lt)
open CFSG.EvenSmallLie.OmegaEight.SplitC (UniqWit uniqCheckW eq_of_uniqCheckW IsNSC)

section Minus


theorem saElt_mul_eq_iffW {a b c d : ℕ} (ha : a < 8192) (hb : b < 8192) (hc : c < 8192)
    (hd : d < 8192) : saElt a * saElt b = saElt c * saElt d ↔
      matMulM (saMat a) (saMat b) = matMulM (saMat c) (saMat d) := by
  have hs := sa_facts
  have h1 := acts_mul (saElt_spec hs a ha).2 (saElt_spec hs b hb).2
  have h2 := acts_mul (saElt_spec hs c hc).2 (saElt_spec hs d hd).2
  have m1 := sylowT.mul_mem (saElt_spec hs a ha).1 (saElt_spec hs b hb).1
  have m2 := sylowT.mul_mem (saElt_spec hs c hc).1 (saElt_spec hs d hd).1
  constructor
  · intro h
    rw [h] at h1
    exact acts_unique hs (matMulM_lt _ _) (matMulM_lt _ _) h1 h2
  · intro h
    rw [h] at h1
    exact eq_of_acts hs m1 m2 (matMulM_lt _ _) h1 h2

theorem saElt_zeroW : saElt 0 = 1 := by
  rw [saElt]
  simp

theorem sq_eq_one_iffW {i : ℕ} (hi : i < 8192) :
    saElt i * saElt i = 1 ↔ matMulM (saMat i) (saMat i) = idCode := by
  have hs := sa_facts
  have h1 := acts_mul (saElt_spec hs i hi).2 (saElt_spec hs i hi).2
  constructor
  · intro h
    rw [h] at h1
    exact acts_unique hs (matMulM_lt _ _) (by rw [← hs.id0]; exact saMat_lt 0) h1 acts_one
  · intro h
    rw [h] at h1
    exact eq_of_acts hs (sylowT.mul_mem (saElt_spec hs i hi).1 (saElt_spec hs i hi).1)
      sylowT.one_mem (by rw [← hs.id0]; exact saMat_lt 0) h1 acts_one

theorem sylowT_minus_uniqueW {W : UniqWit} (hJ : W.J = 36) (hy : W.y = yIdx)
    (hcl : W.cl = fun i => (invW i).1) (h : uniqCheckW 8192 commM conjM invM W = true)
    (F₁ F₂ : Subgroup (Equiv.Perm (Fin 136))) (h₁ : IsNSC sylowT F₁ 64)
    (h₂ : IsNSC sylowT F₂ 64) : F₁ = F₂ := by
  have hs := sa_facts
  refine eq_of_uniqCheckW (e := saElt) (fun i hi => (saElt_spec hs i hi).1)
    (fun g hg => exists_saElt hs hg) (fun i hi k hk => saElt_inj hs hi hk) ?_ ?_ ?_ ?_ h h₁ h₂
  · intro i hi k hk
    rw [commM, beq_iff_eq]
    exact (saElt_mul_eq_iffW hi hk hk hi).symm
  · intro c hc a ha w hw hcw
    rw [conjM, beq_iff_eq] at hcw
    exact (saElt_mul_eq_iffW hc ha hw hc).2 hcw
  · intro i hi hsq h1
    have hi0 : i ≠ 0 := by
      rintro rfl
      exact h1 saElt_zeroW
    simp only [invM, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
    exact ⟨hi0, (sq_eq_one_iffW hi).1 hsq⟩
  · intro i hi hinv
    simp only [invM, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hinv
    obtain ⟨hj, hc, hci, hcci, hcyc⟩ := hs.invol i hi hinv.1 hinv.2
    rw [hJ, hy, hcl]
    refine ⟨hj, (invW i).2.1, hc, ?_⟩
    have e1 : saElt (invW i).2.1 * saElt (invW i).2.2 = 1 := by
      have a1 := acts_mul (saElt_spec hs _ hc).2 (saElt_spec hs _ hci).2
      rw [hcci] at a1
      exact eq_of_acts hs (sylowT.mul_mem (saElt_spec hs _ hc).1 (saElt_spec hs _ hci).1)
        sylowT.one_mem (by rw [← hs.id0]; exact saMat_lt 0) a1 acts_one
    have e2 : saElt (invW i).2.1 * saElt (yIdx (invW i).1) * saElt (invW i).2.2 = saElt i := by
      have hyl := (hs.reps _ hj).1
      have a1 := acts_mul (acts_mul (saElt_spec hs _ hc).2 (saElt_spec hs _ hyl).2)
        (saElt_spec hs _ hci).2
      rw [hcyc] at a1
      exact eq_of_acts hs (sylowT.mul_mem (sylowT.mul_mem (saElt_spec hs _ hc).1
        (saElt_spec hs _ hyl).1) (saElt_spec hs _ hci).1) (saElt_spec hs i hi).1 (saMat_lt i)
        a1 (saElt_spec hs i hi).2
    have e3 : saElt (invW i).2.2 = (saElt (invW i).2.1)⁻¹ := eq_inv_of_mul_eq_one_right e1
    rw [e3] at e2
    rw [← e2]
    group

end Minus

end CFSG.EvenSmallLie.OmegaEightMinus
