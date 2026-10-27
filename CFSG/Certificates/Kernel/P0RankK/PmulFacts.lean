
module

public import CFSG.Certificates.Kernel.P0RankK.Collector
public import CFSG.Certificates.Kernel.P0RankK.Conj
public import CFSG.Certificates.Kernel.P0RankK.PmulBd
public import CFSG.Certificates.Kernel.P0RankK.VisFark

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8.WordRel

open CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.TwoA
  CFSG.ComponentClassification.RankTwoSporadic.B.TwoDFix CFSG.Open
open MonsterB.P0Rank CFSG.Monster.B.TwoA.Sp8.P0Rank
open CFSG.KC.BvecLoop CFSG.KC.P0Col CFSG.KC.P0Vis

theorem pcElt_uK (κ : ℕ) : pcElt (uK κ) = uE κ := by
  simp only [pcElt, pcL, uK, pc_lD_zero, pc_tD_zero, one_mul]

theorem pcElt_mem (g : (ℕ × ℕ) × ℕ) : pcElt g ∈ P0 :=
  P0.mul_mem (Lgrp_le_P0 (pcL_mem g.1)) (uE_mem_P0 g.2)

theorem uCoord_pcElt (g : (ℕ × ℕ) × ℕ) :
    uCoord ⟨pcElt g, pcElt_mem g⟩ = Multiplicative.ofAdd (bvec 10 g.2) := by
  have e : (⟨pcElt g, pcElt_mem g⟩ : P0) =
      ⟨pcL g.1, Lgrp_le_P0 (pcL_mem g.1)⟩ * ⟨uE g.2, uE_mem_P0 g.2⟩ := Subtype.ext rfl
  rw [e, map_mul, (uCoord_eq_one_iff _).2 (pcL_mem g.1), one_mul, uCoord_uE]

theorem snd_eq_of_pcElt {g g' : (ℕ × ℕ) × ℕ} (hg : g.2 < 2 ^ 10) (hg' : g'.2 < 2 ^ 10)
    (h : pcElt g = pcElt g') : g.2 = g'.2 := by
  have e : (⟨pcElt g, pcElt_mem g⟩ : P0) = ⟨pcElt g', pcElt_mem g'⟩ := Subtype.ext h
  have hc := congrArg uCoord e
  rw [uCoord_pcElt, uCoord_pcElt] at hc
  exact bvec_inj hg hg' (Multiplicative.ofAdd.injective hc)

theorem uE_zero : uE 0 = (1 : Dfull) := by
  rw [pc_uE_eq_prod]
  simp [Nat.zero_testBit]

theorem pcL_zero : pcL (0, 0) = 1 := by
  simp only [pcL, pc_lD_zero, pc_tD_zero, one_mul]

theorem pcL_linv (x : ℕ × ℕ) : pcL (linv p0Data.beta x) = (pcL x)⁻¹ := by
  have h := pcL_lmul x (linv p0Data.beta x)
  have e : lmul p0Data.beta x (linv p0Data.beta x) = (0, 0) := by
    simp only [lmul, linv, Nat.xor_self, ← Nat.xor_assoc, Nat.zero_xor]
  rw [e, pcL_zero] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem uK_bd (κ : ℕ) : Bd (uK κ).1 := bd_zero

variable (hbd : bdOK p0Data = true)
include hbd

theorem pm_sq {κ : ℕ} (hκ : κ < 2 ^ 10) :
    ∃ t, uE κ * uE κ = lD (fval p0Data (4 * κ)) * tD t ∧ fval p0Data (4 * κ) < 2 ^ 16 := by
  obtain ⟨p, hp1⟩ : ∃ p, p = pmul p0Data (uK κ) (uK κ) := ⟨_, rfl⟩
  have hb := pmul_bd hbd (uK_bd κ) (uK_bd κ) hκ
  rw [← hp1] at hb
  have hp : pcElt p = uE κ * uE κ := by rw [hp1, pcElt_pmul, pcElt_uK]
  have e : (⟨uE κ * uE κ, P0.mul_mem (uE_mem_P0 κ) (uE_mem_P0 κ)⟩ : P0) =
      ⟨uE κ, uE_mem_P0 κ⟩ * ⟨uE κ, uE_mem_P0 κ⟩ := rfl
  have h1 : uCoord (⟨uE κ * uE κ, P0.mul_mem (uE_mem_P0 κ) (uE_mem_P0 κ)⟩ : P0) = 1 := by
    rw [e, map_mul, uCoord_uE, ← ofAdd_add]
    have : bvec 10 κ + bvec 10 κ = 0 := by
      funext i
      exact CharTwo.add_self_eq_zero _
    rw [this, ofAdd_zero]
  obtain ⟨σ, -, τ, -, hst'⟩ := exists_lD_mul_tD ((uCoord_eq_one_iff _).1 h1)
  have hst : uE κ * uE κ = lD σ * tD τ := hst'
  have h0 : p.2 = 0 := snd_eq_of_pcElt (g' := ((σ, τ), 0)) hb.2 (Nat.two_pow_pos 10) (by
    rw [hp, hst]
    simp only [pcElt, pcL, uE_zero, mul_one])
  have hκ' : κ < 1024 := by simpa using hκ
  refine ⟨p.1.2, ?_, ?_⟩
  · rw [fval_sq p0Data hκ', ← hp1, ← hp]
    simp only [pcElt, pcL, h0, uE_zero, mul_one]
  · rw [fval_sq p0Data hκ', ← hp1]
    exact hb.1.1

theorem pm_comm {κ x : ℕ} (hκ : κ < 2 ^ 10) (hx : x < 2 ^ 10) :
    ∃ t, uE κ * uE x = lD (fval p0Data (1 + 4 * κ + 4096 * x)) * tD t * uE x * uE κ ∧
      fval p0Data (1 + 4 * κ + 4096 * x) < 2 ^ 16 := by
  obtain ⟨p, hp1⟩ : ∃ p, p = pmul p0Data (uK κ) (uK x) := ⟨_, rfl⟩
  obtain ⟨q, hq1⟩ : ∃ q, q = pmul p0Data (uK x) (uK κ) := ⟨_, rfl⟩
  have hbp := pmul_bd hbd (uK_bd κ) (uK_bd x) hκ
  have hbq := pmul_bd hbd (uK_bd x) (uK_bd κ) hx
  rw [← hp1] at hbp
  rw [← hq1] at hbq
  have hp : pcElt p = uE κ * uE x := by rw [hp1, pcElt_pmul, pcElt_uK, pcElt_uK]
  have hq : pcElt q = uE x * uE κ := by rw [hq1, pcElt_pmul, pcElt_uK, pcElt_uK]
  have hpq : p.2 = q.2 := by
    have ep : (⟨pcElt p, pcElt_mem p⟩ : P0) = ⟨uE κ, uE_mem_P0 κ⟩ * ⟨uE x, uE_mem_P0 x⟩ :=
      Subtype.ext hp
    have eq : (⟨pcElt q, pcElt_mem q⟩ : P0) = ⟨uE x, uE_mem_P0 x⟩ * ⟨uE κ, uE_mem_P0 κ⟩ :=
      Subtype.ext hq
    have hu : uCoord ⟨pcElt p, pcElt_mem p⟩ = uCoord ⟨pcElt q, pcElt_mem q⟩ := by
      rw [ep, eq, map_mul, map_mul, mul_comm]
    rw [uCoord_pcElt, uCoord_pcElt] at hu
    exact bvec_inj hbp.2 hbq.2 (Multiplicative.ofAdd.injective hu)
  have hκ' : κ < 1024 := by simpa using hκ
  refine ⟨(lmul p0Data.beta p.1 (linv p0Data.beta q.1)).2, ?_, ?_⟩
  · rw [fval_comm p0Data hκ' x, ← hp1, ← hq1]
    have h3 : lD (lmul p0Data.beta p.1 (linv p0Data.beta q.1)).1 *
        tD (lmul p0Data.beta p.1 (linv p0Data.beta q.1)).2 = pcL p.1 * (pcL q.1)⁻¹ := by
      have h2 := pcL_lmul p.1 (linv p0Data.beta q.1)
      rw [pcL_linv] at h2
      exact h2
    rw [h3, mul_assoc (pcL p.1 * (pcL q.1)⁻¹) (uE x) (uE κ), ← hq]
    simp only [pcElt] at hp ⊢
    rw [← hp, hpq]
    group
  · rw [fval_comm p0Data hκ' x, ← hp1, ← hq1]
    exact (lmul_bd hbd hbp.1 (linv_bd hbd hbq.1)).1

theorem pm_conj {κ δ : ℕ} (hκ : κ < 2 ^ 10) (hδ : δ < 2 ^ 16)
    (hfix : actK p0Data.aCols κ δ = δ) :
    uE κ * lD δ = lD δ * tD (fval p0Data (2 + 4 * κ + 4096 * δ)) * uE κ ∧
      fval p0Data (2 + 4 * κ + 4096 * δ) < 2 ^ 9 := by
  obtain ⟨q, hq1⟩ : ∃ q, q = conjkap p0Data κ (δ, 0) := ⟨_, rfl⟩
  have hbq : Bd q := by
    rw [hq1]
    exact conjkap_bd hbd κ ⟨hδ, Nat.two_pow_pos 9⟩
  have hq : pcL q = uE κ * lD δ * (uE κ)⁻¹ := by
    rw [hq1, pcL_conjkap]
    simp only [pcL, pc_tD_zero, mul_one]
  let X : Lgrp := ⟨lD δ, lD_mem_Lgrp δ⟩
  have hX : sCoord X = Multiplicative.ofAdd (bvec 16 δ) := by
    have hmem : lD δ * (1 : Dfull) ∈ Lgrp := by
      rw [mul_one]
      exact lD_mem_Lgrp δ
    have h := sCoord_lD_mul hδ T9.one_mem hmem
    rwa [show (⟨lD δ * 1, hmem⟩ : Lgrp) = X from Subtype.ext (mul_one _)] at h
  have h1 := sCoord_conj_uE_bvec κ X hδ hX
  rw [hfix] at h1
  have hmemq : lD q.1 * tD q.2 ∈ Lgrp := pcL_mem q
  have h2 : sCoord ⟨lD q.1 * tD q.2, hmemq⟩ = Multiplicative.ofAdd (bvec 16 q.1) :=
    sCoord_lD_mul hbq.1 (tD_mem_T9 q.2) hmemq
  have e : (⟨lD q.1 * tD q.2, hmemq⟩ : Lgrp) =
      ⟨uE κ * X * (uE κ)⁻¹, conj_mem_Lgrp (uE_mem_P0 κ) X.2⟩ := Subtype.ext hq
  rw [e, h1] at h2
  have hq1' : q.1 = δ := bvec_inj hbq.1 hδ (Multiplicative.ofAdd.injective h2).symm
  have hκ' : κ < 1024 := by simpa using hκ
  rw [fval_conj p0Data hκ' δ, ← hq1]
  refine ⟨?_, hbq.2⟩
  have h4 : lD δ * tD q.2 = pcL q := by simp only [pcL, hq1']
  rw [h4, hq]
  group

end CFSG.Monster.B.TwoA.Sp8.WordRel
