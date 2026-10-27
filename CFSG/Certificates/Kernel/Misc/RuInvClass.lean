module

import CFSG.Certificates.Kernel.SporSch.LyLoop
public import CFSG.Certificates.Kernel.Misc.RuInvPack
public import CFSG.Certificates.Kernel.SporSch.ConjClosureSpec

public section

namespace CFSG.KC.Misc.RuInv.P

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb

theorem strictB_eq' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem testBit_one_iff (k : Nat) : (1 : Nat).testBit k = true ↔ k = 0 := by
  rw [show (1 : Nat) = 2 ^ 0 from rfl, Nat.testBit_two_pow, decide_eq_true_eq]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem testBit_one_shift (k b : Nat) : (1 <<< k).testBit b = true ↔ b = k := by
  rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq, testBit_one_iff]
  omega

theorem keysK_inj {Hs : Nat → Nat} {P n : Nat} (h : keysK Hs P n = true) :
    ∀ a < n, ∀ b < n, Hs a = Hs b → a = b := by
  unfold keysK at h
  rw [bAnd_iff, bAnd_iff] at h
  obtain ⟨hinc, -, hall⟩ := h
  rw [allN_iff] at hinc
  have hinc' : ∀ i < n - 1, Nat.blt (Hs (at11 P i)) (Hs (at11 P (Nat.succ i))) = true := hinc
  have hall' := Nat.eq_of_beq_eq_true hall
  rw [CFSG.KS.SporSch.LyLoop.foldN_eqP] at hall'
  have hsurj : ∀ b < n, ∃ i < n, at11 P i = b := by
    intro b hb
    have ht : (Nat.sub (Nat.shiftLeft 1 n) 1).testBit b = true := by
      change (1 <<< n - 1).testBit b = true
      rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
      exact hb
    rw [← hall'] at ht
    obtain ⟨i, hi, h1, h2⟩ := (testBit_foldr_shift (fun _ => 1) (at11 P) b (List.range n)).1 ht
    rw [List.mem_range] at hi
    rw [testBit_one_iff] at h2
    exact ⟨i, hi, by omega⟩
  have hmono : ∀ i j, i < j → j < n → Hs (at11 P i) < Hs (at11 P j) := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      have hstep : Hs (at11 P j) < Hs (at11 P (j + 1)) := Nat.blt_eq.mp (hinc' j (by omega))
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | h
      · exact lt_trans (ih h (by omega)) hstep
      · subst h
        exact hstep
  intro a ha b hb e
  obtain ⟨i, hi, rfl⟩ := hsurj a ha
  obtain ⟨j, hj, rfl⟩ := hsurj b hb
  rcases lt_trichotomy i j with h | rfl | h
  · exact absurd e (ne_of_lt (hmono i j h hj))
  · rfl
  · exact absurd e.symm (ne_of_lt (hmono j i h hi))

theorem foldr_inv (F : Nat → Nat → Nat) (Q : Nat → Prop) (h1 : ∀ b, (1 : Nat).testBit b = true → Q b)
    (hF : ∀ d seen, (∀ b, seen.testBit b = true → Q b) → ∀ b, (F d seen).testBit b = true → Q b) :
    ∀ l : List Nat, ∀ b, (l.foldr F 1).testBit b = true → Q b
  | [] => h1
  | d :: l => by
    rw [List.foldr_cons]
    exact hF d _ (foldr_inv F Q h1 hF l)

theorem testBit_of_land {seen i : Nat} (h : Nat.beq (Nat.land (Nat.shiftRight seen i) 1) 1 = true) :
    seen.testBit i = true := by
  have e := Nat.eq_of_beq_eq_true h
  change (seen >>> i) &&& 1 = 1 at e
  have h2 : (seen >>> i).testBit 0 = true := by
    rw [Nat.testBit_zero, decide_eq_true_eq, ← Nat.and_one_is_mod]
    exact e
  rw [Nat.testBit_shiftRight, Nat.add_zero] at h2
  exact h2

theorem reach_gen {N : Nat} {F : Nat → Nat → Nat}
    (hr : Nat.beq ((List.range N).foldr F 1) (Nat.sub (Nat.shiftLeft 1 N) 1) = true)
    (Q : Nat → Prop) (h0 : Q 0)
    (hF : ∀ d seen, (∀ b, seen.testBit b = true → Q b) → ∀ b, (F d seen).testBit b = true → Q b) :
    ∀ b < N, Q b := by
  intro b hb
  have key := foldr_inv F Q (fun b hb => by
    rw [testBit_one_iff] at hb
    rw [hb]
    exact h0) hF (List.range N) b
  apply key
  rw [Nat.eq_of_beq_eq_true hr]
  change (1 <<< N - 1).testBit b = true
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
  exact hb

theorem reach_all {nx s N : Nat} (Q : Nat → Prop) (h0 : Q 0)
    (hstep : ∀ i < N, Q i → Q (at11 nx (2 * (s + i)) - s) ∧ Q (at11 nx (2 * (s + i) + 1) - s))
    (hr : reachK nx s N = true) : ∀ b < N, Q b := by
  unfold reachK at hr
  rw [CFSG.KS.SporSch.LyLoop.foldN_eqP] at hr
  suffices key : ∀ b < N, b < N → Q b from fun b hb => key b hb hb
  refine reach_gen hr (fun b => b < N → Q b) (fun _ => h0) ?_
  intro d seen hI b hb
  simp only [strictN_eq] at hb
  generalize hi : Nat.sub (Nat.sub N 1) d = i at hb
  cases hc : Nat.beq (Nat.land (Nat.shiftRight seen i) 1) 1
  · rw [hc] at hb
    simp at hb
  · rw [hc] at hb
    change (seen ||| ((1 <<< (at11 nx (2 * (s + i)) - s)) |||
      (1 <<< (at11 nx (2 * (s + i) + 1) - s)))).testBit b = true at hb
    rw [Nat.testBit_or, Nat.testBit_or, Bool.or_eq_true, Bool.or_eq_true] at hb
    have hQi := hI i (testBit_of_land hc)
    intro hbN
    have hi' : N - 1 - d = i := hi
    have hiN : i < N := by omega
    obtain ⟨hA, hB⟩ := hstep i hiN (hQi hiN)
    rcases hb with h | h | h
    · exact hI b h hbN
    · rw [(testBit_one_shift _ _).1 h]
      exact hA
    · rw [(testBit_one_shift _ _).1 h]
      exact hB

theorem nIf_eq' (c : Bool) (a b : Nat) :
    Bool.rec (motive := fun _ => Nat) b a c = if c = true then a else b := by
  cases c <;> rfl

theorem clsLo_eq (j : Nat) : clsLo j =
    if j < 1 then 0 else if j < 31 then 1 else if j < 271 then 31 else if j < 751 then 271 else 751 := by
  unfold clsLo
  simp only [nIf_eq', blt_dec, decide_eq_true_eq]

theorem clsHi_eq (j : Nat) : clsHi j =
    if j < 1 then 1 else if j < 31 then 31 else if j < 271 then 271 else if j < 751 then 751 else 1391 := by
  unfold clsHi
  simp only [nIf_eq', blt_dec, decide_eq_true_eq]

theorem conjE_spec {E G GI : Nat → Nat} {nx j : Nat} (hj : j < 1391)
    (h : conjE E G GI nx j = true) : ∀ l < 2, clsLo j ≤ at11 nx (2 * j + l) ∧
      at11 nx (2 * j + l) < clsLo j + (clsHi j - clsLo j) ∧
      conjP (G l) (GI l) (E j) = E (at11 nx (2 * j + l)) := by
  unfold conjE at h
  rw [Nat.blt_eq.mpr hj] at h
  change conjK E G GI nx (clsLo j) (Nat.sub (clsHi j) (clsLo j)) j 1 = true at h
  unfold conjK at h
  rw [allN_iff] at h
  have h0 := h 0 (by norm_num)
  simp only [strictB_eq'] at h0
  rw [allN_iff] at h0
  intro l hl
  have h1 := h0 l hl
  rw [bAnd_iff, bAnd_iff] at h1
  obtain ⟨a1, a2, a3⟩ := h1
  have e : Nat.add j 0 = j := rfl
  rw [e] at a1 a2 a3
  exact ⟨Nat.le_of_ble_eq_true a1, Nat.blt_eq.mp a2, Nat.eq_of_beq_eq_true a3⟩

@[expose] def cl (x0 x1 y : G) : Set G :=
  {z | ∃ c ∈ Subgroup.closure ({x0, x1} : Set G), z = c * y * c⁻¹}

@[expose] def gam (x0 x1 : G) (l : Nat) : G := if l = 0 then x0 else x1

theorem gam_mem (x0 x1 : G) (l : Nat) : gam x0 x1 l ∈ Subgroup.closure ({x0, x1} : Set G) := by
  unfold gam
  split
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem cl_conj {x0 x1 y z : G} (l : Nat) (hz : z ∈ cl x0 x1 y) :
    gam x0 x1 l * z * (gam x0 x1 l)⁻¹ ∈ cl x0 x1 y := by
  obtain ⟨c, hc, rfl⟩ := hz
  exact ⟨gam x0 x1 l * c, Subgroup.mul_mem _ (gam_mem x0 x1 l) hc, by group⟩

theorem self_mem_cl (x0 x1 y : G) : y ∈ cl x0 x1 y :=
  ⟨1, Subgroup.one_mem _, by group⟩

theorem cl_sub {x0 x1 y g : G} {D : Set G} (hg : g ∈ cl x0 x1 y) (hgD : g ∈ D)
    (hD : ∀ l < 2, ∀ z ∈ D, gam x0 x1 l * z * (gam x0 x1 l)⁻¹ ∈ D) : cl x0 x1 y ⊆ D := by
  have hcl := CFSG.KS.SporSch.ClsSpec.conj_closed (gs := ({x0, x1} : Set G)) (S := D) (by
    intro a ha z hz
    rcases ha with rfl | ha
    · exact hD 0 (by norm_num) z hz
    · rw [Set.mem_singleton_iff.1 ha]
      exact hD 1 (by norm_num) z hz)
  obtain ⟨c, hc, rfl⟩ := hg
  have hy : y ∈ D := by
    have := hcl c⁻¹ (Subgroup.inv_mem _ hc) _ hgD
    simpa [mul_assoc] using this
  rintro _ ⟨c', hc', rfl⟩
  exact hcl c' hc' y hy

theorem prep_gen2 {C0 C1 : Nat} {x0 x1 : G} (h0 : PRep 4060 12 C0 x0) (h1 : PRep 4060 12 C1 x1)
    (l : Nat) : PRep 4060 12 (gen2 C0 C1 l) (gam x0 x1 l) := by
  unfold gen2 gam
  by_cases hl : l = 0
  · subst hl
    exact h0
  · rw [if_neg hl, show Nat.beq l 0 = false from beq_false_of_ne hl]
    exact h1

theorem prep_gen2_inv {CI0 CI1 : Nat} {x0 x1 : G} (h0 : PRep 4060 12 CI0 x0⁻¹)
    (h1 : PRep 4060 12 CI1 x1⁻¹) (l : Nat) : PRep 4060 12 (gen2 CI0 CI1 l) (gam x0 x1 l)⁻¹ := by
  unfold gen2 gam
  by_cases hl : l = 0
  · subst hl
    exact h0
  · rw [if_neg hl, show Nat.beq l 0 = false from beq_false_of_ne hl]
    exact h1

section Class

variable {E Hs : Nat → Nat} {C0 C1 CI0 CI1 nx : Nat} {x0 x1 : G}
  (h0 : PRep 4060 12 C0 x0) (h1 : PRep 4060 12 C1 x1) (hi0 : PRep 4060 12 CI0 x0⁻¹)
  (hi1 : PRep 4060 12 CI1 x1⁻¹)
  (hconj : ∀ j < 1391, conjE E (gen2 C0 C1) (gen2 CI0 CI1) nx j = true)
  {lo N : Nat} (hcls : ∀ j, lo ≤ j → j < lo + N → clsLo j = lo ∧ clsHi j = lo + N)
  (hloN : lo + N ≤ 1391)

include h0 h1 hi0 hi1 hconj hcls hloN

theorem class_step {b : Nat} (hb : b < N) {z : G} (hz : PRep 4060 12 (E (lo + b)) z) (l : Nat)
    (hl : l < 2) : at11 nx (2 * (lo + b) + l) - lo < N ∧
      PRep 4060 12 (E (lo + (at11 nx (2 * (lo + b) + l) - lo))) (gam x0 x1 l * z * (gam x0 x1 l)⁻¹) := by
  have hj : lo + b < 1391 := by omega
  obtain ⟨hcl, hch⟩ := hcls (lo + b) (by omega) (by omega)
  obtain ⟨a1, a2, a3⟩ := conjE_spec hj (hconj _ hj) l hl
  rw [hcl] at a1
  rw [hcl, hch] at a2
  refine ⟨by omega, ?_⟩
  rw [show lo + (at11 nx (2 * (lo + b) + l) - lo) = at11 nx (2 * (lo + b) + l) by omega, ← a3]
  exact prep_conjP (prep_gen2 h0 h1 l) (prep_gen2_inv hi0 hi1 l) hz

theorem class_reach (hreach : reachK nx lo N = true) {y : G} (hy : PRep 4060 12 (E lo) y) :
    ∀ b < N, ∃ z ∈ cl x0 x1 y, PRep 4060 12 (E (lo + b)) z := by
  refine reach_all (fun b => b < N → ∃ z ∈ cl x0 x1 y, PRep 4060 12 (E (lo + b)) z)
    (fun _ => ⟨y, self_mem_cl x0 x1 y, by simpa using hy⟩) ?_ hreach |> fun h b hb => h b hb hb
  intro i hi hQ
  obtain ⟨z, hzc, hz⟩ := hQ hi
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · obtain ⟨-, h⟩ := class_step h0 h1 hi0 hi1 hconj hcls hloN hi hz 0 (by norm_num)
    exact ⟨_, cl_conj 0 hzc, by simpa using h⟩
  · obtain ⟨-, h⟩ := class_step h0 h1 hi0 hi1 hconj hcls hloN hi hz 1 (by norm_num)
    exact ⟨_, cl_conj 1 hzc, h⟩

theorem class_cover {y : G} (hy : PRep 4060 12 (E lo) y) (hN : 0 < N) :
    cl x0 x1 y ⊆ {z | ∃ b < N, PRep 4060 12 (E (lo + b)) z} := by
  refine cl_sub (self_mem_cl x0 x1 y) ⟨0, hN, by simpa using hy⟩ ?_
  rintro l hl z ⟨b, hb, hz⟩
  obtain ⟨h1', h2'⟩ := class_step h0 h1 hi0 hi1 hconj hcls hloN hb hz l hl
  exact ⟨_, h1', h2'⟩

end Class

end CFSG.KC.Misc.RuInv.P

end
