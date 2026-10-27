module

public import Certificates.Data.Kernel.O8.SARoots
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeClasses

public section

namespace CFSG.KC.O8

open CFSG.KC.Enum CFSG.EvenSmallLie.OmegaEight

private theorem fldE (q o r : Nat) :
    Nat.land (Nat.shiftRight q o) (2 ^ r - 1) = q / 2 ^ o % 2 ^ r := by
  change (q >>> o) &&& (2 ^ r - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

private theorem ix13_eq (T i : Nat) : ix13 T i = T / 2 ^ (13 * i) % 8192 := fldE T (13 * i) 13

private theorem labK_eq (i : Nat) : labK saLabT i = saLab i := fldE saLabT (3 * i) 3

private theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

private theorem nIf_eq (c : Bool) (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t c = if c = true then t else e := by cases c <;> rfl

theorem parF_succ (PT LT f i : Nat) : parF PT LT (f + 1) i =
    if i = 0 then 0 else parF PT LT f (ix13 PT i) ^^^ (if labK LT i = 4 then 1 else 0) := by
  change Bool.rec (motive := fun _ => Nat) (Nat.xor (strictN (ix13 PT i) (parF PT LT f))
    (Bool.rec (motive := fun _ => Nat) 0 1 (Nat.beq (labK LT i) 4))) 0 (Nat.beq i 0) = _
  rw [nIf_eq, nIf_eq, strictN_eq]
  by_cases h : i = 0
  · rw [if_pos (Nat.beq_eq.mpr h), if_pos h]
  · rw [if_neg (fun e => h (Nat.beq_eq.mp e)), if_neg h]
    by_cases h4 : labK LT i = 4
    · rw [if_pos (Nat.beq_eq.mpr h4), if_pos h4]
      rfl
    · rw [if_neg (fun e => h4 (Nat.beq_eq.mp e)), if_neg h4]
      rfl

theorem parF_le (PT LT : Nat) : ∀ f i, parF PT LT f i ≤ 1
  | 0, _ => Nat.zero_le _
  | f + 1, i => by
    rw [parF_succ]
    split
    · exact Nat.zero_le _
    · have h := parF_le PT LT f (ix13 PT i)
      split <;> rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h with h' | h' <;> rw [h'] <;> decide

section Sound


private theorem gen9_sq (hs : SAFacts) : gen 9 * gen 9 = 1 := by
  have m9 : gen 9 ∈ sylowT := gen_mem_sylowT (l := 4) (by norm_num)
  have a9 : Acts (gen 9) (saMat (saGen 4)) := acts_gen hs (l := 4) (by norm_num)
  have a := acts_mul a9 a9
  rw [hs.closed _ (hs.gens 4 (by norm_num)).1 4 (by norm_num),
    show saMul (saGen 4) 4 = 0 by decide +kernel, hs.id0] at a
  exact eq_of_acts hs (mul_mem m9 m9) (one_mem _) idCode_lt a acts_one

private theorem saElt_zero : saElt 0 = 1 := by
  rw [saElt, dif_neg fun h => absurd h.1 (Nat.lt_irrefl 0)]

theorem parF_spec (hs : SAFacts) : ∀ f, ∀ i < 8192, i < f →
    (parF saParT saLabT f i = 0 → saElt i ∈ omegaT) ∧
      (parF saParT saLabT f i = 1 → gen 9 * saElt i ∈ omegaT)
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | f + 1, i, hi, hif => by
    have g9 := gen9_sq hs
    have g9A : gen 9 ∈ autT := gen_mem_autT (by norm_num)
    rw [parF_succ]
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [if_pos rfl, saElt_zero]
      exact ⟨fun _ => one_mem _, fun h => absurd h (by decide)⟩
    · rw [if_neg (Nat.pos_iff_ne_zero.1 hpos), ix13_eq, labK_eq]
      obtain ⟨hp, hl, -⟩ := hs.tree i hi hpos
      have e : saElt i = gen (sylowIdx.getD (saLab i) 0) * saElt (saPar i) := by
        rw [saElt, dif_pos ⟨hpos, hp⟩]
      change (parF saParT saLabT f (saPar i) ^^^ _ = 0 → _) ∧ (parF saParT saLabT f (saPar i) ^^^ _ = 1 → _)
      obtain ⟨ih0, ih1⟩ := parF_spec hs f (saPar i) (hp.trans hi) (by omega)
      have hpb := parF_le saParT saLabT f (saPar i)
      rw [e]
      by_cases h4 : saLab i = 4
      · rw [if_pos h4]
        have hg : gen (sylowIdx.getD (saLab i) 0) = gen 9 := by rw [h4]; rfl
        rw [hg]
        rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hpb with hb | hb <;> rw [hb] at ih0 ih1 ⊢
        · refine ⟨fun h => absurd h (by decide), fun _ => ?_⟩
          rw [← mul_assoc, g9, one_mul]
          exact ih0 rfl
        · exact ⟨fun _ => ih1 rfl, fun h => absurd h (by decide)⟩
      · rw [if_neg h4]
        have hl8 : sylowIdx.getD (saLab i) 0 < 8 := by
          have : saLab i < 4 := by omega
          interval_cases (saLab i) <;> decide
        have hgm := gen_mem_omegaT hl8
        rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hpb with hb | hb <;> rw [hb] at ih0 ih1 ⊢
        · exact ⟨fun _ => mul_mem hgm (ih0 rfl), fun h => absurd h (by decide)⟩
        · refine ⟨fun h => absurd h (by decide), fun _ => ?_⟩
          have hconj := (conj_mem_omegaT g9A).1 hgm
          have e2 : gen 9 * (gen (sylowIdx.getD (saLab i) 0) * saElt (saPar i)) =
              gen 9 * gen (sylowIdx.getD (saLab i) 0) * (gen 9)⁻¹ * (gen 9 * saElt (saPar i)) := by
            group
          rw [e2]
          exact mul_mem hconj (ih1 rfl)

theorem gen9_not_mem_omegaT : gen 9 ∉ omegaT := by
  intro h9
  have hs := sa_facts
  obtain ⟨hr, hrS⟩ := repPerm_spec (j := 5) (by norm_num)
  obtain ⟨i, hi, he⟩ := exists_saElt hs hrS
  have hmem : saElt i ∈ omegaT := by
    obtain ⟨h0, h1⟩ := parF_spec hs 8192 i hi hi
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (parF_le saParT saLabT 8192 i) with hb | hb
    · exact h0 hb
    · have := mul_mem (inv_mem h9) (h1 hb)
      rwa [inv_mul_cancel_left] at this
  have := (repPerm_mem_omegaT_iff (j := 5) (by norm_num)).1 (he ▸ hmem)
  exact absurd this (by decide)

theorem parK_spec : ∀ i < 8192, saElt i ∈ omegaT ↔ parK saParT saLabT i = 0 := by
  intro i hi
  have hs := sa_facts
  obtain ⟨h0, h1⟩ := parF_spec hs 8192 i hi hi
  refine ⟨fun hm => ?_, h0⟩
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (parF_le saParT saLabT 8192 i) with hb | hb
  · exact hb
  · refine absurd ?_ gen9_not_mem_omegaT
    have := mul_mem (h1 hb) (inv_mem hm)
    rwa [mul_inv_cancel_right] at this

theorem parK_le (i : Nat) : parK saParT saLabT i ≤ 1 := parF_le _ _ _ _

end Sound

end CFSG.KC.O8

end
