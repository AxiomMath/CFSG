module

public import CFSG.CGT.M24R.M24NativeInputs
public import CFSG.Sporadic.Mathieu.M24

public section

namespace CFSG.CGT.M24R

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Mathieu CFSG.Blueprint
open CFSG.Sporadic.Mathieu.Native (m24Data)

@[expose] def m24GensG (z : ℤ) : NativeSporadic.M24 := if z = 1 then m24a else m24b

theorem m24GenWord_letters (k : ℕ) : ∀ l ∈ m24GenWord k, l = 1 ∨ l = 2 := by
  match k with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | 4 => decide
  | 5 => decide
  | 6 => decide
  | 7 => decide
  | 8 => decide
  | 9 => decide
  | 10 => decide
  | _ + 11 => simp [m24GenWord]

@[expose] noncomputable def m24GenE (k : ℕ) : NativeSporadic.M24 :=
  wordG m24GensG (m24GenWord k)

@[expose] noncomputable def m24Gen (i : Fin 11) : NativeSporadic.M24 := m24GenE i.val

@[expose] noncomputable def m24ImgG (z : ℤ) : NativeSporadic.M24 :=
  if 0 < z then m24GenE (z - 1).toNat else (m24GenE (-z - 1).toNat)⁻¹

theorem m24ImgG_letterZ (l : Fin 11 × Bool) :
    m24ImgG (letterZ l) = if l.2 then m24Gen l.1 else (m24Gen l.1)⁻¹ := by
  obtain ⟨i, b⟩ := l
  have hi : (i.val : ℤ) + 1 - 1 = (i.val : ℤ) := by omega
  cases b
  · simp [m24ImgG, letterZ, m24Gen]
  · have h0 : (0 : ℤ) < (i.val : ℤ) + 1 := by omega
    simp [m24ImgG, letterZ, h0, hi, m24Gen]

theorem wordG_m24ImgG_map_letterZ (w : M24Word) :
    wordG m24ImgG (w.map letterZ) = FreeGroup.lift m24Gen (FreeGroup.mk w) := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    simp only [wordG, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih, show FreeGroup.mk (l :: w) = FreeGroup.mk [l] * FreeGroup.mk w from rfl, map_mul,
      m24ImgG_letterZ]
    obtain ⟨i, b⟩ := l
    cases b
    · rw [show FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ from rfl, map_inv,
        FreeGroup.lift_apply_of]
      simp
    · rw [show FreeGroup.mk [(i, true)] = FreeGroup.of i from rfl, FreeGroup.lift_apply_of]
      simp

theorem rep_m24Img (k : ℕ) : Rep 24 (m24Img k) (m24GenE k) := by
  refine Rep.wordT (by norm_num) _ fun l hl => ?_
  rcases m24GenWord_letters k l hl with rfl | rfl
  · simpa [m24AB, m24GensG] using rep_m24a
  · simpa [m24AB, m24GensG] using rep_m24b

theorem m24TabCheck_facts (h : m24TabCheck = true) :
    (∀ k, k < 11 → m24Img k = genTable k ∧ invOK 24 (m24Img k) (invT 24 (m24Img k)) = true) ∧
    (∀ r ∈ m24Rels, wordT 24 m24L (r.map letterZ) = idT 24) ∧
    wordT 24 m24L (surjAWord.map letterZ) = m24Data.tA ∧
    wordT 24 m24L (surjBWord.map letterZ) = m24Data.tB := by
  unfold m24TabCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

theorem rep_m24L (h : m24TabCheck = true) {z : ℤ} (hz : z.natAbs ≤ 11) :
    Rep 24 (m24L z) (m24ImgG z) := by
  by_cases hpos : 0 < z
  · simp only [m24L, m24ImgG, hpos, ite_true]
    exact rep_m24Img _
  · simp only [m24L, m24ImgG, hpos, ite_false]
    have hk : (-z - 1).toNat < 11 := by omega
    exact Rep.inv_of_invOK (rep_m24Img _) ((m24TabCheck_facts h).1 _ hk).2

theorem eq_of_rep_eq_m24 {g h : NativeSporadic.M24} {X : Table} (hg : Rep 24 X g)
    (hh : Rep 24 X h) : g = h := by
  refine Subtype.ext (Equiv.ext fun i => ?_)
  apply Fin.ext
  have e := (hg i.val i.isLt).symm.trans (hh i.val i.isLt)
  rwa [idx_of_lt g i.isLt, idx_of_lt h i.isLt] at e

theorem rep_wordG_m24ImgG (h : m24TabCheck = true) (w : M24Word) :
    Rep 24 (wordT 24 m24L (w.map letterZ)) (wordG m24ImgG (w.map letterZ)) := by
  refine Rep.wordT (by norm_num) _ fun z hz => ?_
  obtain ⟨l, -, rfl⟩ := List.mem_map.1 hz
  obtain ⟨i, b⟩ := l
  have hi := i.isLt
  refine rep_m24L h ?_
  cases b <;> simp [letterZ] <;> omega

theorem lift_m24Gen_eq_one (h : m24TabCheck = true) {w : M24Word} (hw : w ∈ m24Rels) :
    FreeGroup.lift m24Gen (FreeGroup.mk w) = 1 := by
  have h1 := (m24TabCheck_facts h).2.1 w hw
  have hr := rep_wordG_m24ImgG h w
  rw [h1] at hr
  rw [← wordG_m24ImgG_map_letterZ]
  exact eq_of_rep_eq_m24 hr (Rep.idT (by norm_num))

theorem lift_m24Gen_mem_closure (v : FreeGroup (Fin 11)) :
    FreeGroup.lift m24Gen v ∈ Subgroup.closure (Set.range m24Gen) := by
  induction v using FreeGroup.induction_on with
  | one => simp
  | of i =>
    rw [FreeGroup.lift_apply_of]
    exact Subgroup.subset_closure (Set.mem_range_self i)
  | inv_of i =>
    rw [map_inv, FreeGroup.lift_apply_of]
    exact Subgroup.inv_mem _ (Subgroup.subset_closure (Set.mem_range_self i))
  | mul _ _ h₁ h₂ => rw [map_mul]; exact Subgroup.mul_mem _ h₁ h₂

theorem closure_m24Gen (h : m24TabCheck = true) :
    Subgroup.closure (Set.range m24Gen) = ⊤ := by
  have hab : Subgroup.closure ({m24a, m24b} : Set NativeSporadic.M24) = ⊤ :=
    closure_pair_eq_top m24_eq _ _
  rw [eq_top_iff, ← hab, Subgroup.closure_le]
  have hA : m24a = FreeGroup.lift m24Gen (FreeGroup.mk surjAWord) := by
    rw [← wordG_m24ImgG_map_letterZ]
    have hr := rep_wordG_m24ImgG h surjAWord
    rw [(m24TabCheck_facts h).2.2.1] at hr
    exact eq_of_rep_eq_m24 rep_m24a hr
  have hB : m24b = FreeGroup.lift m24Gen (FreeGroup.mk surjBWord) := by
    rw [← wordG_m24ImgG_map_letterZ]
    have hr := rep_wordG_m24ImgG h surjBWord
    rw [(m24TabCheck_facts h).2.2.2] at hr
    exact eq_of_rep_eq_m24 rep_m24b hr
  rintro _ (rfl | rfl)
  · rw [hA]; exact lift_m24Gen_mem_closure _
  · rw [hB]; exact lift_m24Gen_mem_closure _

end CFSG.CGT.M24R
