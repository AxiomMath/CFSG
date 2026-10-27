module

public import Certificates.Data.Kernel.L34W.InvFix
public import CFSG.Certificates.Kernel.L34W.HjFixSound

public section

namespace CFSG.KC.L34W

open CFSG.KC.Enum CFSG.KS CFSG.KC.L34K CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit.L34Facts.Real
open CFSG.ComponentClassification.GrSLit.L34Facts.Real.WIso

theorem inKB_one : ∀ a b : ZMod 4, inKB (kbOfMask 1) a b = (a == 0 && b == 0) := by
  decide

theorem eqC_one (x y : ℕ) : eqC 1 x y = (dec x == dec y) := by
  rw [eqC_eq]
  unfold eqKB
  rw [inKB_one]
  generalize dec x = p
  generalize dec y = q
  obtain ⟨p1, p2, p3⟩ := p
  obtain ⟨q1, q2, q3⟩ := q
  apply Bool.eq_iff_iff.2
  simp only [Bool.and_eq_true, beq_iff_eq, sub_eq_zero, Prod.mk.injEq]

variable {T A G Y : ℕ → ℕ}

theorem cf22Any_spec {t i : ℕ} : ∀ {m : ℕ}, cf22Any T A Y t i m = true →
    ∃ c < m, cf22Lab T A Y t i c = true
  | 0, h => Bool.noConfusion h
  | m + 1, h => by
    unfold cf22Any at h
    rcases bIf_iff.1 h with ⟨hc, -⟩ | ⟨-, h'⟩
    · exact ⟨m, by omega, hc⟩
    · obtain ⟨c, hc, hl⟩ := cf22Any_spec (m := m) h'
      exact ⟨c, by omega, hl⟩

theorem cf22Lab_spec (hT : T1Of T) (hA : AlOf A) (hb : boundsOK T A = true) (hG : GensG G)
    (hy : yOK G Y = true) {t i c : ℕ} (ht : t < 64) (hi : i < 36) (hc : c < 1024)
    (h : cf22Lab T A Y t i c = true) :
    (!(wordTab (tg (dec c).1) == idTab 42) && mulM (dec c) (dec c) == oneM &&
      betaYM t i (dec c) == dec c) = true := by
  unfold cf22Lab at h
  simp only [bAnd_iff] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hw := tg_ne hG hy (k := c / 16) (by omega) h1
  have e1 : (dec c).1 = c / 16 := rfl
  rw [eqC_one, dec_mulC hT hc hc, dec_zero] at h2
  rw [eqC_one, dec_betaC hT hA hb ht hi hc] at h3
  rw [e1, hw, h2, h3]
  rfl

theorem invFixOK_of (hT : T1Of T) (hA : AlOf A) (hb : boundsOK T A = true) (hG : GensG G)
    (hy : yOK G Y = true) (h : cf22K T A Y = true) : invFixOK = true := by
  unfold invFixOK
  simp only [List.all_eq_true, List.mem_range]
  intro i hi t ht
  have hn : 64 * i + t < 2304 := by omega
  have h1 := allN_spec h (64 * i + t) hn
  unfold cf22One at h1
  have e1 : (64 * i + t) % 64 = t := by omega
  have e2 : (64 * i + t) / 64 = i := by omega
  rw [sq1M_eq hG hy ht hi]
  rcases bIf_iff.1 h1 with ⟨hq, h⟩ | ⟨hq, -⟩
  · change cf22Any T A Y ((64 * i + t) % 64) ((64 * i + t) / 64) 1024 = true at h
    rw [e1, e2] at h
    obtain ⟨c, hc, hl⟩ := cf22Any_spec h
    rw [hq]
    have key : invFixM t i = true := by
      unfold invFixM
      rw [List.any_eq_true]
      exact ⟨dec c, dec_mem_allM hc, cf22Lab_spec hT hA hb hG hy ht hi hc hl⟩
    rw [key]
    rfl
  · rw [hq]
    rfl

end CFSG.KC.L34W

end
