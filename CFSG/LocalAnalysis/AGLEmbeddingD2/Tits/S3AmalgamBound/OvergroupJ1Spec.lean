module

public import CFSG.Sporadic.J1.Simple
public import Certificates.Certificate310101
public import CFSG.Assembly.Defs

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupJ1

open CFSG.Sporadic.J1 CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
  CFSG.Sporadic.J1.Native CFSG.Sporadic.J1.Sylow.Native

theorem sylow_check : sylowCheck orb = true := Certificates.certificate310101

theorem genG_invLetter (z : ℤ) : genG (invLetter z) = (genG z)⁻¹ := by
  by_cases h1 : z = 1
  · subst h1
    simp [invLetter, genG]
  by_cases h2 : z = -1
  · subst h2
    simp [invLetter, genG]
  by_cases h3 : z = 2
  · subst h3
    simp [invLetter, genG]
  · have e : invLetter z = 2 := by simp [invLetter, h1, h2, h3]
    have e2 : genG z = b⁻¹ := by simp [genG, h1, h2, h3]
    rw [e, e2, inv_inv]
    simp [genG]

theorem wordG_append (w v : List ℤ) : wordG genG (w ++ v) = wordG genG w * wordG genG v := by
  simp [wordG, List.map_append, List.prod_append]

theorem wordG_invWord (w : List ℤ) : wordG genG (invWord w) = (wordG genG w)⁻¹ := by
  induction w with
  | nil => simp [wordG, invWord]
  | cons l w ih =>
    have e : invWord (l :: w) = invWord w ++ [invLetter l] := by simp [invWord, List.reverse_cons]
    rw [e, wordG_append, ih]
    simp [wordG, genG_invLetter, mul_inv_rev]

theorem rep_word (w : List ℤ) : Rep 1540 (wordT 1540 (genTables orb) w) (wordG genG w) :=
  Rep.wordT (by norm_num) w (fun l _ => rep_gen l)

theorem rep_b : Rep 1540 (genTables orb 2) b := by simpa [genG] using rep_gen 2

theorem rep_conj (w : List ℤ) :
    Rep 1540 (conjT 1540 (genTables orb) (genTables orb 2) w)
      (wordG genG w * b * (wordG genG w)⁻¹) := by
  have := Rep.compT (rep_word w) (Rep.compT rep_b (rep_word (invWord w)))
  rw [wordG_invWord] at this
  simpa [conjT, mul_assoc] using this

theorem tabEq_iff {n : ℕ} {P Q : Table} : tabEq n P Q = true ↔ ∀ i < n, ap P i = ap Q i := by
  unfold tabEq
  rw [allIn_eq_true]
  constructor
  · intro h i hi
    have := h i (Nat.zero_le _) hi
    simpa using this
  · intro h i _ hi
    simpa using h i hi

theorem eq_of_tabEq {g h : J} {P Q : Table} (hP : Rep 1540 P g) (hQ : Rep 1540 Q h)
    (e : tabEq 1540 P Q = true) : g = h := by
  have key := tabEq_iff.1 e
  refine eq_of_smul_eq_smul (α := Fin 1540) fun x => ?_
  apply Fin.ext
  rw [smul_val_eq_idx, smul_val_eq_idx, ← hP _ x.isLt, ← hQ _ x.isLt]
  exact key _ x.isLt

theorem ne_of_tabEq_false {g h : J} {P Q : Table} (hP : Rep 1540 P g) (hQ : Rep 1540 Q h)
    (e : tabEq 1540 P Q = false) : g ≠ h := by
  intro hgh
  subst hgh
  have : tabEq 1540 P Q = true :=
    tabEq_iff.2 fun i hi => (hP i hi).trans (hQ i hi).symm
  rw [e] at this
  exact absurd this (by decide)

theorem map_getElem! {α β : Type*} [Inhabited α] [Inhabited β] (f : α → β) (a : Array α) {p : ℕ}
    (hp : p < a.size) : (a.map f)[p]! = f a[p]! := by
  rw [getElem!_pos _ p (by simpa using hp), Array.getElem_map, getElem!_pos a p hp]

@[expose] abbrev tw : Array (List ℤ) := parseWords (tWordsStr ())

@[expose] abbrev nw : Array (List ℤ) := parseWords (nWordsStr ())

@[expose] noncomputable def tg (p : ℕ) : J := wordG genG tw[p]!

@[expose] noncomputable def xg (p : ℕ) : J := tg p * b * (tg p)⁻¹

@[expose] noncomputable def vg (i : ℕ) : J := wordG genG nw[i]!

@[expose] noncomputable def fg : J := vg (fIdx ())

theorem false_of_not {b : Bool} (h : (!b) = true) : b = false := by simpa using h

theorem false_of_not_and {b c : Bool} (h : (!b && !c) = true) : b = false ∧ c = false := by
  simpa using h

theorem sylow_parts :
    tw.size = 2926 ∧ nw.size = 60 ∧ fIdx () < 60 ∧ tg 0 = 1 ∧
    (∀ p q, p < q → q < 2926 → xg p ≠ xg q ∧ xg p ≠ xg q * xg q) ∧
    (∀ i, i < 60 → vg i * b * (vg i)⁻¹ = b ∨ vg i * b * (vg i)⁻¹ = b * b) ∧
    (∀ i j, i < j → j < 60 → vg i ≠ vg j) ∧ fg ^ 5 = 1 ∧ fg ≠ 1 ∧
    (∀ p, 1 ≤ p → p < 2926 → fg * xg p * fg⁻¹ ≠ xg p ∧ fg * xg p * fg⁻¹ ≠ xg p * xg p) ∧
    (∀ p, 1 ≤ p → p < 2926 → b * xg p * b⁻¹ ≠ xg p ∧ b * xg p * b⁻¹ ≠ xg p * xg p) := by
  have h := sylow_check
  simp only [sylowCheck, share, pairCheck, normCheck, fCheck, bCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, orb_size] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, h2⟩, h3⟩, h4⟩, h0⟩, h5⟩, ⟨h6, h7⟩⟩, ⟨⟨h8, h9⟩, h10⟩⟩, h11⟩ := h
  have hsz : tw.size = 2926 := h2
  have hsz' : nw.size = 60 := h3
  have rep_x : ∀ p, p < 2926 →
      Rep 1540 ((tw.map (conjT 1540 (genTables orb) (genTables orb 2)))[p]!) (xg p) := by
    intro p hp
    rw [map_getElem! _ _ (by omega)]
    exact rep_conj _
  have rep_x2 : ∀ p, p < 2926 →
      Rep 1540 ((Array.map (fun t => compT 1540 t t)
        (tw.map (conjT 1540 (genTables orb) (genTables orb 2))))[p]!) (xg p * xg p) := by
    intro p hp
    rw [map_getElem! _ _ (by simpa using (by omega : p < tw.size))]
    exact Rep.compT (rep_x p hp) (rep_x p hp)
  have rep_v : ∀ i, i < 60 → Rep 1540 ((nw.map (wordT 1540 (genTables orb)))[i]!) (vg i) := by
    intro i hi
    rw [map_getElem! _ _ (by omega)]
    exact rep_word _
  have rep_vi : ∀ i, i < 60 →
      Rep 1540 ((nw.map fun w => wordT 1540 (genTables orb) (invWord w))[i]!) (vg i)⁻¹ := by
    intro i hi
    rw [map_getElem! _ _ (by omega)]
    have := rep_word (invWord nw[i]!)
    rw [wordG_invWord] at this
    exact this
  have hb2 : Rep 1540 (compT 1540 (genTables orb 2) (genTables orb 2)) (b * b) :=
    Rep.compT rep_b rep_b
  have hbinv : b⁻¹ = b * b := by
    have := b_cube
    rw [pow_succ, pow_two] at this
    exact inv_eq_of_mul_eq_one_right (by rw [← mul_assoc]; exact this)
  have hf : fIdx () < 60 := h4
  have rep_f : Rep 1540 ((nw.map (wordT 1540 (genTables orb)))[fIdx ()]!) fg := rep_v _ hf
  have rep_fi : Rep 1540 ((nw.map fun w => wordT 1540 (genTables orb) (invWord w))[fIdx ()]!)
      fg⁻¹ := rep_vi _ hf
  refine ⟨hsz, hsz', hf, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : tw[0]! = [] := h0
    simp [tg, this, wordG]
  · intro p q hpq hq
    have h5' := (allIn_eq_true.1 h5) p (Nat.zero_le _) (by omega)
    have h5'' := (allIn_eq_true.1 h5') q (by omega) hq
    obtain ⟨e1, e2⟩ := false_of_not_and h5''
    exact ⟨ne_of_tabEq_false (rep_x p (by omega)) (rep_x q hq) e1,
      ne_of_tabEq_false (rep_x p (by omega)) (rep_x2 q hq) e2⟩
  · intro i hi
    have h6' := (allIn_eq_true.1 h6) i (Nat.zero_le _) hi
    have rc := Rep.compT (rep_v i hi) (Rep.compT rep_b (rep_vi i hi))
    rw [Bool.or_eq_true] at h6'
    rcases h6' with e | e
    · left
      simpa [mul_assoc] using eq_of_tabEq rc rep_b e
    · right
      simpa [mul_assoc] using eq_of_tabEq rc hb2 e
  · intro i j hij hj
    have h7' := (allIn_eq_true.1 h7) i (Nat.zero_le _) (by omega)
    have h7'' := (allIn_eq_true.1 h7') j (by omega) hj
    exact ne_of_tabEq_false (rep_v i (by omega)) (rep_v j hj) (false_of_not h7'')
  · have e := tabEq_iff.1 h8
    have rp := Rep.powT (by norm_num : 1540 < 2 ^ 32) rep_f 5
    exact eq_of_tabEq rp (Rep.idT (by norm_num)) h8
  · exact ne_of_tabEq_false rep_f (Rep.idT (by norm_num)) (false_of_not h9)
  · intro p hp hp'
    have h10' := (allIn_eq_true.1 h10) p hp hp'
    obtain ⟨e1, e2⟩ := false_of_not_and h10'
    have rc := Rep.compT rep_f (Rep.compT (rep_x p hp') rep_fi)
    refine ⟨ne_of_tabEq_false (by simpa [mul_assoc] using rc) (rep_x p hp') e1,
      ne_of_tabEq_false (by simpa [mul_assoc] using rc) (rep_x2 p hp') e2⟩
  · intro p hp hp'
    have h11' := (allIn_eq_true.1 h11) p hp hp'
    obtain ⟨e1, e2⟩ := false_of_not_and h11'
    have rc := Rep.compT rep_b (Rep.compT (rep_x p hp') hb2)
    rw [← hbinv] at rc
    refine ⟨ne_of_tabEq_false (by simpa [mul_assoc] using rc) (rep_x p hp') e1,
      ne_of_tabEq_false (by simpa [mul_assoc] using rc) (rep_x2 p hp') e2⟩

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupJ1
