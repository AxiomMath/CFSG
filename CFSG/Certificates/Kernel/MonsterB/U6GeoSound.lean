
module

public import Certificates.Data.Kernel.MonsterB.U6Geo
public import CFSG.Certificates.Kernel.MonsterB.F4CodeSound
public import CFSG.Certificates.Kernel.F4MatSound
import all CFSG.Fischer.F4

public section

namespace CFSG.KC.U6G

open CFSG.Fischer CFSG.Monster.B.TwoA.Unitary CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.F4M CFSG.KC.F4M.Aux
open CFSG.KC.Orb14 CFSG.KC.U6Orb Matrix
open CFSG.Monster.B.Classical.UnitarySix (bar)

theorem cv_lt (x t : ℕ) : cv x t < 4 := fget2_lt x t

theorem cF4_code : ∀ a : F4, cF4 a.code.val = a := by decide

theorem vec6_cv (x : ℕ) (t : Fin 6) : vec6 x t = cF4 (cv x t) := by
  unfold cv
  rw [fget2_eq x t, cF4_code]

theorem sqC_lt (c : ℕ) : sqC c < 4 := fm_lt c c

theorem cF4_sqC {c : ℕ} (hc : c < 4) : cF4 (sqC c) = bar (cF4 c) := (cF4_sq hc).symm

theorem testBit_term (c t i : ℕ) :
    (Nat.shiftLeft (Nat.land c 3) (Nat.mul 2 t)).testBit i =
      (decide (2 * t ≤ i) && decide (i < 2 * t + 2) && c.testBit (i - 2 * t)) := by
  change ((c &&& 3) <<< (2 * t)).testBit i = _
  rw [Nat.testBit_shiftLeft, show (3 : ℕ) = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.testBit_mod_two_pow]
  by_cases h1 : 2 * t ≤ i
  · simp only [ge_iff_le, h1, decide_true, Bool.true_and]
    congr 1
    exact decide_eq_decide.2 (by omega)
  · simp [h1]

theorem testBit_mkV (f : ℕ → ℕ) (i : ℕ) :
    (mkV f).testBit i = (decide (i < 12) && (f (i / 2)).testBit (i % 2)) := by
  unfold mkV
  apply Bool.eq_iff_iff.2
  rw [testBit_orN']
  constructor
  · rintro ⟨t, ht, h⟩
    have ht' : t < 6 := ht
    rw [testBit_term] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    have e1 : i / 2 = t := by omega
    have e2 : i - 2 * t = i % 2 := by omega
    rw [e2] at h3
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨by omega, by rw [e1]; exact h3⟩
  · intro h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    refine ⟨i / 2, (by omega : i / 2 < 6), ?_⟩
    rw [testBit_term]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    have e2 : i - 2 * (i / 2) = i % 2 := by omega
    rw [e2]
    exact h.2

theorem mkV_lt (f : ℕ → ℕ) : mkV f < 4096 := by
  have h : mkV f < 2 ^ 12 := Nat.lt_pow_two_of_testBit _ fun i hi => by
    rw [testBit_mkV, decide_eq_false (by omega), Bool.false_and]
  exact h

theorem vec6_mkV (f : ℕ → ℕ) (t : Fin 6) : vec6 (mkV f) t = cF4 (f t) := by
  rw [vec6_cv]
  unfold cF4
  congr 2
  rw [Nat.mod_eq_of_lt (cv_lt _ _)]
  apply Nat.eq_of_testBit_eq
  intro n
  unfold cv
  rw [testBit_fget2, testBit_mkV, testBit_mod4]
  by_cases hn : n < 2
  · have ht := t.2
    rw [decide_eq_true hn, Bool.true_and, Bool.true_and, decide_eq_true (by omega : 2 * (t : ℕ) + n < 12),
      Bool.true_and]
    have e1 : (2 * (t : ℕ) + n) / 2 = t := by omega
    have e2 : (2 * (t : ℕ) + n) % 2 = n := by omega
    rw [e1, e2]
  · rw [decide_eq_false hn, Bool.false_and, Bool.false_and]

theorem hUK_eq (x y : ℕ) : hU (vec6 x) (vec6 y) = cF4 (hUK x y) := by
  have hf : ∀ i, Nat.xor (fm (cv x i) (sqC (cv y (Nat.add i 3)))) (fm (cv x (Nat.add i 3)) (sqC (cv y i)))
      < 4 := fun i => xor_lt4 (fm_lt _ _) (fm_lt _ _)
  unfold hUK
  rw [(xorN_spec _ hf 3).2, ← Fin.sum_univ_eq_sum_range
    (fun i => cF4 (Nat.xor (fm (cv x i) (sqC (cv y (Nat.add i 3)))) (fm (cv x (Nat.add i 3))
      (sqC (cv y i))))) 3]
  unfold hU
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [cF4_xor (fm_lt _ _) (fm_lt _ _), fm_spec (cv_lt _ _) (sqC_lt _),
    fm_spec (cv_lt _ _) (sqC_lt _), cF4_sqC (cv_lt _ _), cF4_sqC (cv_lt _ _)]
  have hl : vec6 x (lo i) = cF4 (cv x i) := vec6_cv x (lo i)
  have hh : vec6 x (hi i) = cF4 (cv x (Nat.add i 3)) := vec6_cv x (hi i)
  have hl' : vec6 y (lo i) = cF4 (cv y i) := vec6_cv y (lo i)
  have hh' : vec6 y (hi i) = cF4 (cv y (Nat.add i 3)) := vec6_cv y (hi i)
  rw [hl, hh, hl', hh']

theorem barc_lt (f : Bool) {c : ℕ} (hc : c < 4) : barc f c < 4 := by
  cases f
  · exact hc
  · exact fm_lt _ _

theorem cF4_barc (f : Bool) (x : ℕ) (r : Fin 6) : cF4 (barc f (cv x r)) = barB f (vec6 x) r := by
  cases f
  · exact (vec6_cv x r).symm
  · change cF4 (sqC (cv x r)) = bar (vec6 x r)
    rw [cF4_sqC (cv_lt _ _), vec6_cv]

theorem imK_eq (f : Bool) (M : ℕ → ℕ) (x : ℕ) : vec6 (imK f M x) = imV f M (vec6 x) := by
  funext t
  unfold imK
  rw [Aux.strictN_eq, vec6_mkV]
  unfold imV
  rw [vecMul_apply6, (xorN_spec _ (fun r => fm_lt _ _) 6).2]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hr' : r < 6 := Finset.mem_range.1 hr
  rw [fm_spec (barc_lt f (cv_lt _ _)) (cv_lt _ _)]
  have e : vN (barB f (vec6 x)) r = cF4 (barc f (cv x r)) := by
    unfold vN
    rw [dif_pos hr']
    exact (cF4_barc f x ⟨r, hr'⟩).symm
  rw [e, vec6_cv (M r) t]

theorem expK_eq (R : ℕ → ℕ) (x : ℕ) : vec6 (expK R x) = fun t : Fin 6 =>
    ∑ b ∈ Finset.range 3, vec6 x (piv (vec6 (R b))) * vec6 (R b) t := by
  funext t
  unfold expK
  rw [Aux.strictN_eq, vec6_mkV, (xorN_spec _ (fun b => fm_lt _ _) 3).2]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [fm_spec (cv_lt _ _) (cv_lt _ _), vec6_cv (R b) t, vec6_cv x (piv (vec6 (R b))), pivK_eq]

theorem expK_lt (R : ℕ → ℕ) (x : ℕ) : expK R x < 4096 := by
  unfold expK
  rw [Aux.strictN_eq]
  exact mkV_lt _

theorem imK_lt (f : Bool) (M : ℕ → ℕ) (x : ℕ) : imK f M x < 4096 := by
  unfold imK
  rw [Aux.strictN_eq]
  exact mkV_lt _

theorem hGram_mul_apply (A : Matrix (Fin 6) (Fin 6) F4) (i l : Fin 6) :
    (A * hGram) i l = A i (partner l) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (partner l)]
  · rw [hGram, of_apply, if_pos (partner_partner l).symm, mul_one]
  · intro k _ hk
    rw [hGram, of_apply, if_neg (fun h => hk (by rw [h, partner_partner])), mul_zero]
  · simp

theorem gram_eq (A : Matrix (Fin 6) (Fin 6) F4) (i j : Fin 6) :
    (A * hGram * (barM A)ᵀ) i j = hU (A i) (A j) := by
  rw [Matrix.mul_apply, hU_eq_sum]
  simp only [hGram_mul_apply, transpose_apply, CFSG.Monster.B.TwoA.Unitary.barM, map_apply]
  exact Fintype.sum_equiv (Equiv.mk partner partner partner_partner partner_partner) _ _
    (fun l => by simp [partner_partner])

theorem allN_iff' (n : ℕ) (f : ℕ → Bool) : allN n f = true ↔ ∀ i < n, f i = true := allN_iff n f

theorem gram_of_gramOK {M : ℕ → ℕ} (h : gramOK M = true) :
    (Matrix.of fun i : Fin 6 => vec6 (M i)) * hGram *
      (barM (Matrix.of fun i : Fin 6 => vec6 (M i)))ᵀ = hGram := by
  ext i j
  rw [gram_eq]
  change hU (vec6 (M i)) (vec6 (M j)) = hGram i j
  unfold gramOK at h
  rw [allN_iff] at h
  have h' := h i i.2
  rw [allN_iff] at h'
  have h'' := Nat.eq_of_beq_eq_true (h' j j.2)
  rw [hUK_eq, h'', hGram, of_apply]
  by_cases hj : j = partner i
  · rw [if_pos hj]
    have : Nat.beq (j : ℕ) (Nat.mod (Nat.add i 3) 6) = true := by
      rw [Nat.beq_eq, hj]
      rfl
    rw [this]
    rfl
  · rw [if_neg hj]
    have : Nat.beq (j : ℕ) (Nat.mod (Nat.add i 3) 6) = false := by
      rw [Bool.eq_false_iff]
      intro e
      exact hj (Fin.ext (Nat.eq_of_beq_eq_true e))
    rw [this]
    rfl

end CFSG.KC.U6G

end
