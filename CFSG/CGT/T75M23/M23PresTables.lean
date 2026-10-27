module

public import CFSG.CGT.T75M23.M23PresInputs
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Sporadic.Mathieu.Simple

public section

namespace CFSG.CGT.T75M23

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Mathieu CFSG.Blueprint


abbrev m23gA : Equiv.Perm (Fin 23) :=
  List.formPerm [0, 1] * List.formPerm [2, 3] * List.formPerm [6, 7] * List.formPerm [8, 9] *
    List.formPerm [12, 13] * List.formPerm [14, 15] * List.formPerm [18, 19] *
    List.formPerm [20, 21]

abbrev m23gB : Equiv.Perm (Fin 23) :=
  List.formPerm [0, 15, 10, 2] * List.formPerm [1, 8, 20, 11] * List.formPerm [3, 4, 7, 22] *
    List.formPerm [5, 21, 13, 17] * List.formPerm [12, 19] * List.formPerm [14, 16]

theorem m23_eq : NativeSporadic.M23 = Subgroup.closure {m23gA, m23gB} := rfl

abbrev m23a : NativeSporadic.M23 :=
  ⟨m23gA, by rw [m23_eq]; exact Subgroup.subset_closure (Set.mem_insert _ _)⟩

abbrev m23b : NativeSporadic.M23 :=
  ⟨m23gB, by rw [m23_eq]; exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

theorem rep_m23a : Rep 23 m23tA m23a := by
  unfold CFSG.Sporadic.Th.Rep
  decide +kernel

theorem rep_m23b : Rep 23 m23tB m23b := by
  unfold CFSG.Sporadic.Th.Rep
  decide +kernel

@[expose] def m23GensG (z : ℤ) : NativeSporadic.M23 := if z = 1 then m23a else m23b

theorem m23GenWord_letters (k : ℕ) : ∀ l ∈ m23GenWord k, l = 1 ∨ l = 2 := by
  match k with
  | 0 => decide +kernel
  | 1 => decide +kernel
  | 2 => decide +kernel
  | 3 => decide +kernel
  | 4 => decide +kernel
  | 5 => decide +kernel
  | 6 => decide +kernel
  | _ + 7 => simp [m23GenWord]

@[expose] noncomputable def m23GenE (k : ℕ) : NativeSporadic.M23 :=
  wordG m23GensG (m23GenWord k)

@[expose] noncomputable def m23Gen (i : Fin 7) : NativeSporadic.M23 := m23GenE i.val

@[expose] noncomputable def m23ImgG (z : ℤ) : NativeSporadic.M23 :=
  if 0 < z then m23GenE (z - 1).toNat else (m23GenE (-z - 1).toNat)⁻¹

theorem m23ImgG_letterZ (l : Fin 7 × Bool) :
    m23ImgG (m23LetterZ l) = if l.2 then m23Gen l.1 else (m23Gen l.1)⁻¹ := by
  obtain ⟨i, b⟩ := l
  have hi : (i.val : ℤ) + 1 - 1 = (i.val : ℤ) := by omega
  cases b
  · simp [m23ImgG, m23LetterZ, m23Gen]
  · have h0 : (0 : ℤ) < (i.val : ℤ) + 1 := by omega
    simp [m23ImgG, m23LetterZ, h0, hi, m23Gen]

theorem wordG_m23ImgG_map_letterZ (w : List (Fin 7 × Bool)) :
    wordG m23ImgG (w.map m23LetterZ) = FreeGroup.lift m23Gen (FreeGroup.mk w) := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    simp only [wordG, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih, show FreeGroup.mk (l :: w) = FreeGroup.mk [l] * FreeGroup.mk w from rfl, map_mul,
      m23ImgG_letterZ]
    obtain ⟨i, b⟩ := l
    cases b
    · rw [show FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ from rfl, map_inv,
        FreeGroup.lift_apply_of]
      simp
    · rw [show FreeGroup.mk [(i, true)] = FreeGroup.of i from rfl, FreeGroup.lift_apply_of]
      simp

abbrev m23T (k : ℕ) : Table := m23Img k

abbrev m23V (k : ℕ) : Table := invT 23 (m23T k)

abbrev m23L : ℤ → Table :=
  m23ImgLetter (m23T 0) (m23T 1) (m23T 2) (m23T 3) (m23T 4) (m23T 5) (m23T 6)
    (m23V 0) (m23V 1) (m23V 2) (m23V 3) (m23V 4) (m23V 5) (m23V 6)

theorem rep_m23T (k : ℕ) : Rep 23 (m23T k) (m23GenE k) := by
  refine Rep.wordT (by norm_num) _ fun l hl => ?_
  rcases m23GenWord_letters k l hl with rfl | rfl
  · simpa [m23AB, m23GensG] using rep_m23a
  · simpa [m23AB, m23GensG] using rep_m23b

theorem tab_facts (h : m23TabCheck = true) :
    (∀ k, k < 7 → invOK 23 (m23T k) (m23V k) = true) ∧
    (∀ r ∈ m23Rels, wordT 23 m23L (r.map m23LetterZ) = idT 23) ∧
    wordT 23 m23L m23SurjA = m23tA ∧
    wordT 23 m23L m23SurjB = m23tB := by
  unfold m23TabCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  refine ⟨fun k hk => ?_, h7, h8, h9⟩
  interval_cases k
  exacts [h0, h1, h2, h3, h4, h5, h6]

theorem rep_m23L (h : m23TabCheck = true) {z : ℤ} (hz0 : z ≠ 0) (hz : z.natAbs ≤ 7) :
    Rep 23 (m23L z) (m23ImgG z) := by
  have hinv := (tab_facts h).1
  have hz' : z = 1 ∨ z = 2 ∨ z = 3 ∨ z = 4 ∨ z = 5 ∨ z = 6 ∨ z = 7 ∨ z = -1 ∨ z = -2 ∨ z = -3 ∨
      z = -4 ∨ z = -5 ∨ z = -6 ∨ z = -7 := by omega
  rcases hz' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rep_m23T 0
  · exact rep_m23T 1
  · exact rep_m23T 2
  · exact rep_m23T 3
  · exact rep_m23T 4
  · exact rep_m23T 5
  · exact rep_m23T 6
  · exact Rep.inv_of_invOK (rep_m23T 0) (hinv 0 (by norm_num))
  · exact Rep.inv_of_invOK (rep_m23T 1) (hinv 1 (by norm_num))
  · exact Rep.inv_of_invOK (rep_m23T 2) (hinv 2 (by norm_num))
  · exact Rep.inv_of_invOK (rep_m23T 3) (hinv 3 (by norm_num))
  · exact Rep.inv_of_invOK (rep_m23T 4) (hinv 4 (by norm_num))
  · exact Rep.inv_of_invOK (rep_m23T 5) (hinv 5 (by norm_num))
  · exact Rep.inv_of_invOK (rep_m23T 6) (hinv 6 (by norm_num))

theorem eq_of_rep_eq {g h : NativeSporadic.M23} {X : Table} (hg : Rep 23 X g) (hh : Rep 23 X h) :
    g = h := by
  refine Subtype.ext (Equiv.ext fun i => ?_)
  apply Fin.ext
  have e := (hg i.val i.isLt).symm.trans (hh i.val i.isLt)
  rwa [idx_of_lt g i.isLt, idx_of_lt h i.isLt] at e

theorem rep_wordG_m23ImgG (h : m23TabCheck = true) (w : List (Fin 7 × Bool)) :
    Rep 23 (wordT 23 m23L (w.map m23LetterZ)) (wordG m23ImgG (w.map m23LetterZ)) := by
  refine Rep.wordT (by norm_num) _ fun z hz => ?_
  obtain ⟨l, -, rfl⟩ := List.mem_map.1 hz
  obtain ⟨i, b⟩ := l
  have hi := i.isLt
  refine rep_m23L h ?_ ?_
  · cases b <;> simp [m23LetterZ] <;> omega
  · cases b <;> simp [m23LetterZ] <;> omega

theorem lift_m23Gen_eq_one (h : m23TabCheck = true) {w : List (Fin 7 × Bool)}
    (hw : w ∈ m23Rels) : FreeGroup.lift m23Gen (FreeGroup.mk w) = 1 := by
  have h1 := (tab_facts h).2.1 w hw
  have hr := rep_wordG_m23ImgG h w
  rw [h1] at hr
  rw [← wordG_m23ImgG_map_letterZ]
  exact eq_of_rep_eq hr (Rep.idT (by norm_num))

theorem lift_m23Gen_mem_closure (v : FreeGroup (Fin 7)) :
    FreeGroup.lift m23Gen v ∈ Subgroup.closure (Set.range m23Gen) := by
  induction v using FreeGroup.induction_on with
  | one => simp
  | of i =>
    rw [FreeGroup.lift_apply_of]
    exact Subgroup.subset_closure (Set.mem_range_self i)
  | inv_of i =>
    rw [map_inv, FreeGroup.lift_apply_of]
    exact Subgroup.inv_mem _ (Subgroup.subset_closure (Set.mem_range_self i))
  | mul _ _ h₁ h₂ => rw [map_mul]; exact Subgroup.mul_mem _ h₁ h₂

theorem closure_m23Gen (h : m23TabCheck = true) :
    Subgroup.closure (Set.range m23Gen) = ⊤ := by
  have hab : Subgroup.closure ({m23a, m23b} : Set NativeSporadic.M23) = ⊤ :=
    closure_pair_eq_top m23_eq _ _
  rw [eq_top_iff, ← hab, Subgroup.closure_le]
  have hA : m23a = FreeGroup.lift m23Gen (FreeGroup.mk (m23OfCodes m23SurjACodes)) := by
    rw [← wordG_m23ImgG_map_letterZ]
    have hr := rep_wordG_m23ImgG h (m23OfCodes m23SurjACodes)
    rw [show (m23OfCodes m23SurjACodes).map m23LetterZ = m23SurjA from rfl,
      (tab_facts h).2.2.1] at hr
    exact eq_of_rep_eq rep_m23a hr
  have hB : m23b = FreeGroup.lift m23Gen (FreeGroup.mk (m23OfCodes m23SurjBCodes)) := by
    rw [← wordG_m23ImgG_map_letterZ]
    have hr := rep_wordG_m23ImgG h (m23OfCodes m23SurjBCodes)
    rw [show (m23OfCodes m23SurjBCodes).map m23LetterZ = m23SurjB from rfl,
      (tab_facts h).2.2.2] at hr
    exact eq_of_rep_eq rep_m23b hr
  rintro _ (rfl | rfl)
  · rw [hA]; exact lift_m23Gen_mem_closure _
  · rw [hB]; exact lift_m23Gen_mem_closure _

end CFSG.CGT.T75M23
