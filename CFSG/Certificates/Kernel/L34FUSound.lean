module

public import Certificates.Data.Kernel.L34FU
public import CFSG.Certificates.Kernel.L34W.RealBSound
public import Certificates.Data.FooteLitL34FUCheck

public section

namespace CFSG.KC.L34FU.Snd

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.L34W CFSG.KC.L34W.OCS CFSG.KC.L34W.RBS
open CFSG.KC.L34KSnd CFSG.KC.L34FU
open CFSG.PSL3Four.Native CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.ComponentClassification.GrSLit.L34Facts.Real CFSG.ComponentClassification.TBLit.L34FU
open CFSG.ComponentClassification.PSL3Four

theorem mem_penumRec {n w cnt : ℕ} {T PL : ℕ → ℕ} {t : Tab}
    (h : t ∈ (CFSG.KS.PEnum.penumRec n w cnt T PL).tabs.toList) :
    ∃ q < cnt, t = unpack n w (T q) := by
  rw [CFSG.KS.PEnum.penumRec_eq, Array.mem_toList_iff, Array.mem_ofFn] at h
  obtain ⟨⟨q, hq⟩, e⟩ := h
  exact ⟨q, hq, e.symm⟩

theorem ex8_of {x : ℕ} {g : Equiv.Perm (Fin 42)} (hx : Cn x) (hg : TabRep (unpack 42 6 x) g)
    (h : ex8K x = true) : g ^ 8 = 1 := by
  unfold ex8K at h
  rw [strictB_eq', strictB_eq'] at h
  have h2 := hg.comp hg
  rw [comp_eq hx hx] at h2
  have h4 := h2.comp h2
  rw [comp_eq (cn_pc hx hx) (cn_pc hx hx)] at h4
  have h8 := h4.comp h4
  rw [comp_eq (cn_pc (cn_pc hx hx) (cn_pc hx hx)) (cn_pc (cn_pc hx hx) (cn_pc hx hx)),
    Nat.eq_of_beq_eq_true h, ← idTab42] at h8
  have e : g ^ 8 = g * g * (g * g) * (g * g * (g * g)) := by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [e]
  exact (h8.beq_iff TabRep.idTab).1 (beq_self_eq_true _)

theorem candK_of {R2 y : ℕ} {OT : ℕ → ℕ} (hy : Cn y) (hR : Cn R2)
    (hc : comp 42 (unpack 42 6 y) (unpack 42 6 R2) = comp 42 (unpack 42 6 R2) (unpack 42 6 y))
    (hi : comp 42 (unpack 42 6 y) (unpack 42 6 y) = idTab 42) (hOT : ∀ q < 280, Cn (OT q))
    (hm : ∃ q < 280, unpack 42 6 (OT q) = unpack 42 6 y) : candK R2 OT y = true := by
  unfold candK
  rw [bAnd_iff, bAnd_iff]
  refine ⟨?_, ?_, ?_⟩
  · rw [comp_eq hy hR, comp_eq hR hy] at hc
    rw [← beq_unpack (cn_pc hy hR) (cn_pc hR hy), hc, beq_self_eq_true]
  · rw [comp_eq hy hy, idTab42] at hi
    rw [← beq_unpack (cn_pc hy hy) cn_pidn, hi, beq_self_eq_true]
  · obtain ⟨q, hq, e⟩ := hm
    refine memL_iff.2 ⟨q, hq, ?_⟩
    have := beq_unpack (hOT q hq) hy
    rw [e, beq_self_eq_true] at this
    exact Nat.eq_of_beq_eq_true this.symm

theorem sixK_spec {T A Y OT W : ℕ → ℕ} {R2 : ℕ} (h : sixK T A Y OT W R2 = true) {t i : ℕ}
    (ht : t < 64) (hi : i < 36) (hc : candK R2 OT (Y (64 * i + t)) = true) :
    witK T A t i (pg 11 (mask 11) (W i) t) = true := by
  unfold sixK at h
  have h1 := allN_spec h i hi
  rw [strictB_eq'] at h1
  exact bIf_true hc (allN_spec h1 t ht)

variable {T A : ℕ → ℕ}

theorem witness_of (hT : T1Of T) (hA : AlOf A) (hb : boundsOK T A = true) {t i f : ℕ}
    (ht : t < 64) (hi : i < 36) (h : witK T A t i f = true) :
    ∃ x ∈ allM, betaRepM 1 x = x ∧ pow4X (mulM x (betaYM t i x)) = (0, 2, 0) := by
  unfold witK at h
  simp only [bAnd_iff, strictB_eq'] at h
  obtain ⟨hx, h1, h2⟩ := h
  generalize f = x at hx h1 h2
  have hx' : x < 1024 := by simpa using hx
  have hβ : betaC T A t i x < 1024 := betaC_lt hb ht hi hx'
  have hu : mulC T x (betaC T A t i x) < 1024 := mulC_lt hb hx' hβ
  have hu2 := mulC_lt hb hu hu
  refine ⟨dec x, mem_allM (dec_lt hx'), ?_, ?_⟩
  · rw [← dec_betaRepC hA (by norm_num) hx', Nat.eq_of_beq_eq_true h1]
  · rw [← dec_betaC hT hA hb ht hi hx', ← dec_mulC hT hx' hβ, pow4X, ← dec_mulC hT hu hu,
      ← dec_mulC hT hu2 hu2, Nat.eq_of_beq_eq_true h2]
    rfl

end CFSG.KC.L34FU.Snd

end
