
module

public import Certificates.Data.Kernel.L34W.Types
public import CFSG.Certificates.Kernel.L34W.FixSound
import CFSG.Certificates.Kernel.Spor.PK.Basic

public section

namespace CFSG.KC.L34W

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.PSL3Four CFSG.PSL3Four.Native
open CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit.L34Facts.Real
open CFSG.ComponentClassification.GrSLit.L34Facts.Real.WIso

@[expose] def eltIx (n : ℕ) : ZMod 4 × ZMod 4 := (((n / 4 : ℕ) : ZMod 4), ((n % 4 : ℕ) : ZMod 4))

theorem eltIx_addIx : ∀ a < 16, ∀ b < 16, eltIx (addIx a b) = eltIx a + eltIx b := by
  decide +kernel

theorem addIx_lt : ∀ a < 16, ∀ b < 16, addIx a b < 16 := by decide +kernel

theorem eltIx_kIdx : ∀ i j : ZMod 4, eltIx (kIdx i j) = (i, j) := by decide +kernel

theorem kIdx_lt (i j : ZMod 4) : kIdx i j < 16 := by
  have hi := ZMod.val_lt i
  have hj := ZMod.val_lt j
  unfold kIdx
  omega

theorem testBit_foldr_bit : ∀ (l : List Bool) (n : ℕ), (l.foldr Nat.bit 0).testBit n = l.getD n false
  | [], n => by simp
  | b :: l, 0 => by simp [Nat.testBit_bit_zero]
  | b :: l, n + 1 => by simp [Nat.testBit_bit_succ, testBit_foldr_bit l n]

theorem foldr_bit_lt : ∀ l : List Bool, l.foldr Nat.bit 0 < 2 ^ l.length
  | [] => by simp
  | b :: l => by
    have h := foldr_bit_lt l
    simp only [List.foldr_cons, List.length_cons, pow_succ]
    cases b <;> simp only [Nat.bit, cond] <;> omega

theorem inL_mem : ∀ {L : List ℕ} {m : ℕ}, inL L m = true → m ∈ L
  | [], _, h => absurd h Bool.false_ne_true
  | x :: L, m, h => by
    change bIf(Nat.beq m x, true, inL L m) = true at h
    rcases bIf_iff.1 h with ⟨h1, -⟩ | ⟨-, h2⟩
    · rw [Nat.eq_of_beq_eq_true h1]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem x (inL_mem h2)

theorem kClass_of (h : ∀ m < 65536, isSubM m = true → inL kbMasks m = true)
    (K : AddSubgroup (ZMod 4 × ZMod 4)) :
    ∃ kb ∈ kbList, ∀ i j : ZMod 4, inKB kb i j = true ↔ (i, j) ∈ K := by
  classical
  let l : List Bool := (List.range 16).map fun n => decide (eltIx n ∈ K)
  let m := l.foldr Nat.bit 0
  have hlen : l.length = 16 := by simp [l]
  have hm : m < 65536 := by
    have := foldr_bit_lt l
    rw [hlen] at this
    exact this
  have hbit : ∀ n < 16, hasBit m n = decide (eltIx n ∈ K) := by
    intro n hn
    rw [CFSG.KS.PK.hasBit_eq, testBit_foldr_bit]
    simp only [l, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hn,
      Option.map_some, Option.getD_some]
  have hsub : isSubM m = true := by
    unfold isSubM
    rw [bAnd_iff]
    refine ⟨?_, CFSG.KS.PK.allN_iff.2 fun a ha => ?_⟩
    · change hasBit m 0 = true
      rw [hbit 0 (by norm_num), decide_eq_true_eq]
      have e : eltIx 0 = 0 := by decide
      rw [e]
      exact K.zero_mem
    · cases hA : hasBit m a
      · rfl
      · refine CFSG.KS.PK.allN_iff.2 fun b hb => ?_
        cases hB : hasBit m b
        · rfl
        · change hasBit m (addIx a b) = true
          rw [hbit a ha, decide_eq_true_eq] at hA
          rw [hbit b hb, decide_eq_true_eq] at hB
          rw [hbit _ (addIx_lt a ha b hb), decide_eq_true_eq, eltIx_addIx a ha b hb]
          exact K.add_mem hA hB
  refine ⟨kbOfMask m, List.mem_map_of_mem (inL_mem (h m hm hsub)), fun i j => ?_⟩
  unfold inKB
  rw [getD_mask m (kIdx_lt i j), ← CFSG.KS.PK.hasBit_eq, hbit _ (kIdx_lt i j), decide_eq_true_eq,
    eltIx_kIdx]

variable {G Y : ℕ → ℕ}

theorem tabRep_rhoK (hG : GensG G) {lab : ℕ} (hlab : lab < 3) :
    Cn (rhoK G lab) ∧ TabRep (unpack 42 6 (rhoK G lab)) (rhoPerm lab) := by
  obtain ⟨e4, c4⟩ := hG 4 (by norm_num)
  obtain ⟨e5, c5⟩ := hG 5 (by norm_num)
  have r4 : TabRep (unpack 42 6 (G 4)) g₅ := by
    rw [← e4]
    exact tabRep_g₅
  have r5 : TabRep (unpack 42 6 (G 5)) g₆ := by
    rw [← e5]
    exact tabRep_g₆
  interval_cases lab
  · exact ⟨c4, r4⟩
  · exact ⟨c5, r5⟩
  · refine ⟨CFSG.KC.BfsPin.canonK_pcomp c4 c5, ?_⟩
    change TabRep (unpack 42 6 (pcomp 42 6 (mask 6) (G 4) (G 5))) (g₅ * g₆)
    rw [← CFSG.KC.L34KSnd.comp_unpack' c4 c5]
    exact r4.comp r5

theorem cjE_spec (hG : GensG G) (hy : yOK G Y = true) {t i lab t' j : ℕ}
    (h : cjE G Y t i lab t' j = true) :
    t < 64 ∧ i < 36 ∧ lab < 3 ∧ t' < 64 ∧ j < 36 ∧
      yPerm t' j * yPerm t i * (yPerm t' j)⁻¹ = rhoPerm lab := by
  unfold cjE at h
  rw [strictB_eq] at h
  simp only [bAnd_iff] at h
  obtain ⟨⟨hl, ht', hj⟩, ⟨ht, hi⟩, he⟩ := h
  have ht := Nat.blt_eq.mp ht
  have hi := Nat.blt_eq.mp hi
  have hl := Nat.blt_eq.mp hl
  have ht' := Nat.blt_eq.mp ht'
  have hj := Nat.blt_eq.mp hj
  refine ⟨ht, hi, hl, ht', hj, ?_⟩
  obtain ⟨cc, rc⟩ := tabRep_Y hG hy ht' hj
  obtain ⟨cy, ry⟩ := tabRep_Y hG hy ht hi
  obtain ⟨cr, rr⟩ := tabRep_rhoK hG hl
  have e := congrArg (unpack 42 6) (Nat.eq_of_beq_eq_true he)
  change unpack 42 6 (pcomp 42 6 (mask 6) (Y (64 * j + t')) (Y (64 * i + t))) =
    unpack 42 6 (pcomp 42 6 (mask 6) (rhoK G lab) (Y (64 * j + t'))) at e
  rw [← CFSG.KC.L34KSnd.comp_unpack' cc cy, ← CFSG.KC.L34KSnd.comp_unpack' cr cc] at e
  rw [(rc.comp ry).eq_iff (rr.comp rc)] at e
  rw [e, mul_inv_cancel_right]

theorem cj_spec (hG : GensG G) (hy : yOK G Y = true) :
    ∀ {L : List ((ℕ × ℕ) × ℕ × ℕ × ℕ)}, cjOK G Y L = true → ∀ e ∈ L,
      e.1.1 < 64 ∧ e.1.2 < 36 ∧ e.2.1 < 3 ∧ e.2.2.1 < 64 ∧ e.2.2.2 < 36 ∧
        yPerm e.2.2.1 e.2.2.2 * yPerm e.1.1 e.1.2 * (yPerm e.2.2.1 e.2.2.2)⁻¹ = rhoPerm e.2.1
  | [], _, e, he => absurd he List.not_mem_nil
  | x :: L, h, e, he => by
    change bAnd(cjE G Y x.1.1 x.1.2 x.2.1 x.2.2.1 x.2.2.2, cjOK G Y L) = true at h
    rw [bAnd_iff] at h
    rcases List.mem_cons.1 he with rfl | he
    · exact cjE_spec hG hy h.1
    · exact cj_spec hG hy h.2 e he

theorem entry_of_typeOf {t i : ℕ} (h : typeOf t i < 3) :
    ∃ e ∈ outerTypes, e.1 = (t, i) ∧ e.2.1 = typeOf t i := by
  unfold typeOf at h ⊢
  cases hf : outerTypes.find? (fun e => e.1 == (t, i)) with
  | none =>
    rw [hf] at h
    simp at h
  | some e =>
    have hei := List.find?_some hf
    simp only [beq_iff_eq] at hei
    exact ⟨e, List.mem_of_find?_eq_some hf, hei, by simp⟩

theorem mul_mem_S {t t' i : ℕ} (h2 : yPerm t i * yPerm t i = 1) :
    yPerm t i * yPerm t' i ∈ CFSG.ComponentClassification.PSL3Four.S := by
  have hs := wordPerm_mem (tg t)
  have hs' := wordPerm_mem (tg t')
  have hρ := repPerm_mem i
  have h1 := conj_mem_S hρ hs
  have h3 := conj_mem_S hρ hs'
  have hsq : repPerm i * repPerm i =
      (repPerm i * wordPerm (tg t) * (repPerm i)⁻¹)⁻¹ * (wordPerm (tg t))⁻¹ := by
    calc repPerm i * repPerm i = (repPerm i * wordPerm (tg t) * (repPerm i)⁻¹)⁻¹ *
          (wordPerm (tg t))⁻¹ * (yPerm t i * yPerm t i) := by
          simp only [yPerm]
          group
      _ = _ := by rw [h2, mul_one]
  have e : yPerm t i * yPerm t' i =
      wordPerm (tg t) * (repPerm i * wordPerm (tg t') * (repPerm i)⁻¹) * (repPerm i * repPerm i) := by
    simp only [yPerm]
    group
  rw [e, hsq]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hs h3)
    (Subgroup.mul_mem _ (Subgroup.inv_mem _ h1) (Subgroup.inv_mem _ hs))

variable {T A : ℕ → ℕ}

theorem someN_spec {n : ℕ} {f : ℕ → Bool} (h : someN n f = true) : ∃ x < n, f x = true := by
  by_contra hne
  push Not at hne
  have ha : allN n (fun x => bNot (f x)) = true :=
    CFSG.KS.PK.allN_iff.2 fun x hx => by
      rw [bNot_iff]
      simpa using hne x hx
  unfold someN at h
  rw [ha] at h
  exact absurd h (by decide)

theorem fsZ_spec (hT : T1Of T) (hA : AlOf A) {b t i z : ℕ} (hb : BRow b t i) (hi : i < 36)
    (hz : z < 1024) (h : fsZ T A b i z = true) (hf : fixKB (kbOfMask 1) t i (dec z) = true) :
    ∃ x ∈ allM, fixKB (kbOfMask 1) t i x = true ∧ eqKB (kbOfMask 1) (mulM x x) (dec z) = true := by
  change bIf(fixC A b i 1 z, someN 1024 (fun x => bAnd(fixC A b i 1 x, eqC 1 (mulC T x x) z)),
    true) = true at h
  rw [fixC_eq hA hb hi 1 hz, hf] at h
  obtain ⟨x, hx, h1⟩ := someN_spec h
  rw [bAnd_iff] at h1
  obtain ⟨f1, e1⟩ := h1
  rw [fixC_eq hA hb hi 1 hx] at f1
  rw [eqC_eq, dec_mulC hT hx hx] at e1
  exact ⟨dec x, dec_mem_allM hx, f1, e1⟩

end CFSG.KC.L34W

end
