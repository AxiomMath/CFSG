module

public import CFSG.CGT.T75JM.M22PresInputs
public import CFSG.Sporadic.Mathieu.M22

public section

namespace CFSG.CGT.T75JM

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Mathieu CFSG.Blueprint
open CFSG.Sporadic.Mathieu.Native (m22Data)

@[expose] def m22GensG (z : ℤ) : NativeSporadic.M22 := if z = 1 then m22a else m22b

theorem m22GenWord_letters (k : ℕ) : ∀ l ∈ m22GenWord k, l = 1 ∨ l = 2 := by
  match k with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | 4 => decide
  | 5 => decide
  | 6 => decide
  | _ + 7 => simp [m22GenWord]

@[expose] noncomputable def m22GenE (k : ℕ) : NativeSporadic.M22 :=
  wordG m22GensG (m22GenWord k)

@[expose] noncomputable def m22Gen (i : Fin 7) : NativeSporadic.M22 := m22GenE i.val

@[expose] noncomputable def m22ImgG (z : ℤ) : NativeSporadic.M22 :=
  if 0 < z then m22GenE (z - 1).toNat else (m22GenE (-z - 1).toNat)⁻¹

theorem m22ImgG_letterZ (l : Fin 7 × Bool) :
    m22ImgG (m22LetterZ l) = if l.2 then m22Gen l.1 else (m22Gen l.1)⁻¹ := by
  obtain ⟨i, b⟩ := l
  have hi : (i.val : ℤ) + 1 - 1 = (i.val : ℤ) := by omega
  cases b
  · simp [m22ImgG, m22LetterZ, m22Gen]
  · have h0 : (0 : ℤ) < (i.val : ℤ) + 1 := by omega
    simp [m22ImgG, m22LetterZ, h0, hi, m22Gen]

theorem wordG_m22ImgG_map_letterZ (w : List (Fin 7 × Bool)) :
    wordG m22ImgG (w.map m22LetterZ) = FreeGroup.lift m22Gen (FreeGroup.mk w) := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    simp only [wordG, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih, show FreeGroup.mk (l :: w) = FreeGroup.mk [l] * FreeGroup.mk w from rfl, map_mul,
      m22ImgG_letterZ]
    obtain ⟨i, b⟩ := l
    cases b
    · rw [show FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ from rfl, map_inv,
        FreeGroup.lift_apply_of]
      simp
    · rw [show FreeGroup.mk [(i, true)] = FreeGroup.of i from rfl, FreeGroup.lift_apply_of]
      simp

abbrev m22T (k : ℕ) : Table := m22Img k

abbrev m22V (k : ℕ) : Table := invT 22 (m22T k)

abbrev m22L : ℤ → Table :=
  m22ImgLetter (m22T 0) (m22T 1) (m22T 2) (m22T 3) (m22T 4) (m22T 5) (m22T 6)
    (m22V 0) (m22V 1) (m22V 2) (m22V 3) (m22V 4) (m22V 5) (m22V 6)

theorem rep_m22T (k : ℕ) : Rep 22 (m22T k) (m22GenE k) := by
  refine Rep.wordT (by norm_num) _ fun l hl => ?_
  rcases m22GenWord_letters k l hl with rfl | rfl
  · simpa [m22AB, m22GensG] using rep_m22a
  · simpa [m22AB, m22GensG] using rep_m22b

theorem tab_facts (h : m22TabCheck = true) :
    (∀ k, k < 7 → invOK 22 (m22T k) (m22V k) = true) ∧
    (∀ r ∈ m22Rels, wordT 22 m22L (r.map m22LetterZ) = idT 22) ∧
    wordT 22 m22L m22SurjA = m22Data.tA ∧
    wordT 22 m22L m22SurjB = m22Data.tB := by
  unfold m22TabCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  refine ⟨fun k hk => ?_, h7, h8, h9⟩
  interval_cases k
  exacts [h0, h1, h2, h3, h4, h5, h6]

theorem rep_m22L (h : m22TabCheck = true) {z : ℤ} (hz0 : z ≠ 0) (hz : z.natAbs ≤ 7) :
    Rep 22 (m22L z) (m22ImgG z) := by
  have hinv := (tab_facts h).1
  have hz' : z = 1 ∨ z = 2 ∨ z = 3 ∨ z = 4 ∨ z = 5 ∨ z = 6 ∨ z = 7 ∨ z = -1 ∨ z = -2 ∨ z = -3 ∨
      z = -4 ∨ z = -5 ∨ z = -6 ∨ z = -7 := by omega
  rcases hz' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rep_m22T 0
  · exact rep_m22T 1
  · exact rep_m22T 2
  · exact rep_m22T 3
  · exact rep_m22T 4
  · exact rep_m22T 5
  · exact rep_m22T 6
  · exact Rep.inv_of_invOK (rep_m22T 0) (hinv 0 (by norm_num))
  · exact Rep.inv_of_invOK (rep_m22T 1) (hinv 1 (by norm_num))
  · exact Rep.inv_of_invOK (rep_m22T 2) (hinv 2 (by norm_num))
  · exact Rep.inv_of_invOK (rep_m22T 3) (hinv 3 (by norm_num))
  · exact Rep.inv_of_invOK (rep_m22T 4) (hinv 4 (by norm_num))
  · exact Rep.inv_of_invOK (rep_m22T 5) (hinv 5 (by norm_num))
  · exact Rep.inv_of_invOK (rep_m22T 6) (hinv 6 (by norm_num))

theorem eq_of_rep_eq {g h : NativeSporadic.M22} {X : Table} (hg : Rep 22 X g) (hh : Rep 22 X h) :
    g = h := by
  refine Subtype.ext (Equiv.ext fun i => ?_)
  apply Fin.ext
  have e := (hg i.val i.isLt).symm.trans (hh i.val i.isLt)
  rwa [idx_of_lt g i.isLt, idx_of_lt h i.isLt] at e

theorem rep_wordG_m22ImgG (h : m22TabCheck = true) (w : List (Fin 7 × Bool)) :
    Rep 22 (wordT 22 m22L (w.map m22LetterZ)) (wordG m22ImgG (w.map m22LetterZ)) := by
  refine Rep.wordT (by norm_num) _ fun z hz => ?_
  obtain ⟨l, -, rfl⟩ := List.mem_map.1 hz
  obtain ⟨i, b⟩ := l
  have hi := i.isLt
  refine rep_m22L h ?_ ?_
  · cases b <;> simp [m22LetterZ] <;> omega
  · cases b <;> simp [m22LetterZ] <;> omega

theorem lift_m22Gen_eq_one (h : m22TabCheck = true) {w : List (Fin 7 × Bool)}
    (hw : w ∈ m22Rels) : FreeGroup.lift m22Gen (FreeGroup.mk w) = 1 := by
  have h1 := (tab_facts h).2.1 w hw
  have hr := rep_wordG_m22ImgG h w
  rw [h1] at hr
  rw [← wordG_m22ImgG_map_letterZ]
  exact eq_of_rep_eq hr (Rep.idT (by norm_num))

theorem lift_m22Gen_mem_closure (v : FreeGroup (Fin 7)) :
    FreeGroup.lift m22Gen v ∈ Subgroup.closure (Set.range m22Gen) := by
  induction v using FreeGroup.induction_on with
  | one => simp
  | of i =>
    rw [FreeGroup.lift_apply_of]
    exact Subgroup.subset_closure (Set.mem_range_self i)
  | inv_of i =>
    rw [map_inv, FreeGroup.lift_apply_of]
    exact Subgroup.inv_mem _ (Subgroup.subset_closure (Set.mem_range_self i))
  | mul _ _ h₁ h₂ => rw [map_mul]; exact Subgroup.mul_mem _ h₁ h₂

theorem closure_m22Gen (h : m22TabCheck = true) :
    Subgroup.closure (Set.range m22Gen) = ⊤ := by
  have hab : Subgroup.closure ({m22a, m22b} : Set NativeSporadic.M22) = ⊤ :=
    closure_pair_eq_top m22_eq _ _
  rw [eq_top_iff, ← hab, Subgroup.closure_le]
  have hA : m22a = FreeGroup.lift m22Gen (FreeGroup.mk (m22OfCodes m22SurjACodes)) := by
    rw [← wordG_m22ImgG_map_letterZ]
    have hr := rep_wordG_m22ImgG h (m22OfCodes m22SurjACodes)
    rw [show (m22OfCodes m22SurjACodes).map m22LetterZ = m22SurjA from rfl,
      (tab_facts h).2.2.1] at hr
    exact eq_of_rep_eq rep_m22a hr
  have hB : m22b = FreeGroup.lift m22Gen (FreeGroup.mk (m22OfCodes m22SurjBCodes)) := by
    rw [← wordG_m22ImgG_map_letterZ]
    have hr := rep_wordG_m22ImgG h (m22OfCodes m22SurjBCodes)
    rw [show (m22OfCodes m22SurjBCodes).map m22LetterZ = m22SurjB from rfl,
      (tab_facts h).2.2.2] at hr
    exact eq_of_rep_eq rep_m22b hr
  rintro _ (rfl | rfl)
  · rw [hA]; exact lift_m22Gen_mem_closure _
  · rw [hB]; exact lift_m22Gen_mem_closure _

end CFSG.CGT.T75JM
