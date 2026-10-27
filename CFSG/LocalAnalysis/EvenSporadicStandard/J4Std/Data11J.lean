module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.Data11Mask
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.Local
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot
public import Certificates.Certificate25130

public section

namespace CFSG.EvenSporadicStandard.J4Std.Data11

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.Native
open CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs (duadMasks starMasks star_facts starOK_closure
  mem_star_lt)

@[expose] noncomputable def pJ : J := wordProd xJ pWord

@[expose] noncomputable def qJ : J := eta uJ 11 qMask * wordProd xJ qWord

@[expose] noncomputable def u0J : J := eta uJ 11 u0Mask

theorem pWord_letters : ∀ ℓ ∈ pWord, ℓ ∈ letters := by decide

theorem qWord_letters : ∀ ℓ ∈ qWord, ℓ ∈ letters := by decide

theorem pJ_mem : pJ ∈ Hj := wordProd_mem_Hj pWord_letters

theorem qJ_mem : qJ ∈ Hj :=
  Hj.mul_mem (Eg_le_Hj (eta_mem_Eg 11 le_rfl qMask)) (wordProd_mem_Hj qWord_letters)

theorem u0J_mem : u0J ∈ Eg uJ 11 := eta_mem_Eg 11 le_rfl u0Mask

theorem u0J_ne (hM : MatFacts) : u0J ≠ 1 := by
  intro h
  have h0 : eta uJ 11 u0Mask = eta uJ 11 0 := by rw [eta_zero]; exact h
  have := eta_inj hM u0Mask (by norm_num [u0Mask]) 0 (by norm_num) h0
  norm_num [u0Mask] at this

theorem mem_Hloc_top_iff {j : J} :
    j ∈ Hloc (⊤ : Subgroup J) (Eg uJ 11) ↔ j ∈ Hj := by
  rw [← normalizer_Eg_eq_Hj j4Facts]
  simp [Hloc]

section Matrix

variable (hM : MatFacts)
include hM

theorem pJ_pow : pJ ^ 11 = 1 := by
  have h := Certificates.certificate25130
  unfold chkPQ at h
  simp only [Bool.and_eq_true] at h
  apply Mx_injective
  have e := congrArg rowsMatrix (eqRows_iff.1 h.1)
  rw [rowsMatrix_powRows, rowsMatrix_idRows, ← Mx_wordProd hM pWord] at e
  rw [map_pow, map_one]
  exact e

theorem qJ_mul_pJ : qJ * pJ = pJ ^ 2 * qJ := by
  have h := Certificates.certificate25130
  unfold chkPQ at h
  simp only [Bool.and_eq_true] at h
  have e := congrArg rowsMatrix (eqRows_iff.1 h.2)
  simp only [rowsMatrix_mulRows] at e
  rw [← Mx_eta hM 11 le_rfl qMask, ← Mx_wordProd hM qWord, ← Mx_wordProd hM pWord] at e
  apply Mx_injective
  simpa only [qJ, pJ, map_mul, map_pow, pow_two] using e

end Matrix

section Mask

variable (hM : MatFacts) (hm : MaskData)
include hM hm

theorem conj_pJ (c : ℕ) : pJ * eta uJ 11 c * pJ⁻¹ = eta uJ 11 (pMap c) := by
  have hx : ∀ j < 11, pJ * uJ j * pJ⁻¹ = eta uJ 11 (pRow j) := by
    intro j hj
    have := word_conj XJ act pWord (fun ℓ hℓ c => hX_all hM (pWord_letters ℓ hℓ) c) (2 ^ j)
    rw [eta_two_pow hj, hm.word j hj] at this
    exact this
  exact conj_eta (elem_uJ hM) pJ pRow hx le_rfl c

theorem pJ_ne_one : pJ ≠ 1 := by
  intro h
  have h1 := conj_pJ hM hm 2
  rw [h, one_mul, inv_one, mul_one] at h1
  exact hm.ne (eta_inj hM _ (by norm_num) _ (pMap_lt hm 2) h1).symm

theorem maskSetup_J :
    MaskSetup (fun c => eta uJ 11 c) pJ where
  zero := eta_zero uJ 11
  xor := fun a b => eta_xor (elem_uJ hM) le_rfl a b
  inj := eta_inj hM
  conj := conj_pJ hM hm
  pow_eleven := pJ_pow hM

theorem pJ_comm_u0J : pJ * u0J = u0J * pJ := by
  have h := conj_pJ hM hm u0Mask
  rw [hm.fix_u0] at h
  rw [mul_inv_eq_iff_eq_mul] at h
  exact h

theorem fix_J {x : J} (hx : x ∈ Eg uJ 11) (hc : pJ * x = x * pJ) : x = 1 ∨ x = u0J := by
  obtain ⟨c, hc11, rfl⟩ := (mem_Eg_iff (elem_uJ hM)).1 hx
  have h1 := conj_pJ hM hm c
  rw [hc, mul_inv_cancel_right] at h1
  have h2 := eta_inj hM _ hc11 _ (pMap_lt hm c) h1
  rcases hm.fix c hc11 h2.symm with rfl | rfl
  · exact Or.inl (eta_zero uJ 11)
  · exact Or.inr rfl

end Mask

section Cent


theorem hj_duad {j : J} (hj : j ∈ Hj) :
    ∀ d ∈ duadMasks, d < 2 ^ 11 → ∃ d' ∈ duadMasks, d' < 2 ^ 11 ∧
      j * eta uJ 11 d * j⁻¹ = eta uJ 11 d' := by
  intro d hd _
  obtain ⟨-, hlen, hst, -, -, hcov, -⟩ := star_facts
  obtain ⟨i, hi, -, -, -, hdi, -⟩ := hcov d hd
  obtain ⟨i', hi', hOK⟩ := starOK_closure j hj i hi
  obtain ⟨c', hc', e⟩ := hOK d hdi
  have hmem : starMasks.getD i' [] ∈ starMasks := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  exact ⟨c', (hst _ hmem).2 c' hc', mem_star_lt hi' hc', e⟩

variable (hm : MaskData)
include hm

theorem cent_J {j : J} (hj : j ∈ Hj) (hc : pJ * j = j * pJ) :
    ∃ k : ℕ, ∃ e ∈ Eg uJ 11, j = pJ ^ k * e := by
  have hM := j4Facts.mat
  have hs := maskSetup_J hM hm
  obtain ⟨y, hy_lt, hy⟩ := (mem_Eg_iff (elem_uJ hM)).1
    (Hj_normalizes_Eg hM j hj _ (eta_mem_Eg 11 le_rfl 1))
  obtain ⟨m, -, hmy⟩ := conj_cent_pow hs hm hc.symm hy hy_lt (hj_duad hj)
  have key := fun c (hc' : c < 2 ^ 11) => conj_eq_of_pPow hs hm hc.symm hmy hc'
  have hxH : (pJ ^ m)⁻¹ * j ∈ Hj := Hj.mul_mem (Hj.inv_mem (Hj.pow_mem pJ_mem m)) hj
  have hxc : ∀ e ∈ Eg uJ 11, ((pJ ^ m)⁻¹ * j) * e = e * ((pJ ^ m)⁻¹ * j) := by
    intro e he
    obtain ⟨c, hc', rfl⟩ := (mem_Eg_iff (elem_uJ hM)).1 he
    have h1 := key c hc'
    calc ((pJ ^ m)⁻¹ * j) * eta uJ 11 c
        = (pJ ^ m)⁻¹ * (j * eta uJ 11 c * j⁻¹) * j := by group
      _ = (pJ ^ m)⁻¹ * (pJ ^ m * eta uJ 11 c * (pJ ^ m)⁻¹) * j := by rw [h1]
      _ = eta uJ 11 c * ((pJ ^ m)⁻¹ * j) := by group
  exact ⟨m, _, centralizer_Hj hM j4Facts _ hxH hxc, by group⟩

end Cent

end CFSG.EvenSporadicStandard.J4Std.Data11
