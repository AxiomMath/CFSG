module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf2DataE64
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf3Aff

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

@[expose] def fanoT7 (a b : Fin 7) : Fin 7 :=
  Fin.ofNat 7 ((([[0, 3, 6, 1, 5, 4, 2], [3, 0, 4, 0, 2, 6, 5], [6, 4, 0, 5, 1, 3, 0],
    [1, 0, 5, 0, 6, 2, 4], [5, 2, 1, 6, 0, 0, 3], [4, 6, 3, 2, 0, 0, 1],
    [2, 5, 0, 4, 3, 1, 0]] : List (List ℕ)).getD a.1 []).getD b.1 0)

theorem line_fanoT7 : ∀ a b y : Fin 7, ({a, b, y} : Finset (Fin 7)) ∈ fanoLines → y = fanoT7 a b := by
  decide +kernel

@[expose] def fanoTf (q : Fin 7 × Fin 7 × Fin 7) (x : Fin 7) : Fin 7 :=
  match x.1 with
  | 0 => q.1
  | 1 => q.2.1
  | 2 => q.2.2
  | 3 => fanoT7 q.1 q.2.1
  | 4 => fanoT7 q.2.1 q.2.2
  | 5 => fanoT7 q.2.2 (fanoT7 q.1 q.2.1)
  | _ => fanoT7 q.1 q.2.2

theorem fanoTf_spec : ∀ a b c : Fin 7, fanoTf (a, b, c) 0 = a ∧ fanoTf (a, b, c) 1 = b ∧
    fanoTf (a, b, c) 2 = c ∧ fanoTf (a, b, c) 3 = fanoT7 a b ∧ fanoTf (a, b, c) 4 = fanoT7 b c ∧
    fanoTf (a, b, c) 5 = fanoT7 c (fanoT7 a b) ∧ fanoTf (a, b, c) 6 = fanoT7 a c := by decide +kernel

theorem fanoLines_mem4 : ({0, 1, 3} : Finset (Fin 7)) ∈ fanoLines ∧
    ({1, 2, 4} : Finset (Fin 7)) ∈ fanoLines ∧ ({2, 3, 5} : Finset (Fin 7)) ∈ fanoLines ∧
    ({0, 2, 6} : Finset (Fin 7)) ∈ fanoLines := by decide +kernel

theorem fano_image_line (p : Equiv.Perm (Fin 7))
    (hp : ∀ s ∈ fanoLines, s.map p.toEmbedding ∈ fanoLines ∧ s.map p⁻¹.toEmbedding ∈ fanoLines)
    {a b c : Fin 7} (h : ({a, b, c} : Finset (Fin 7)) ∈ fanoLines) :
    ({p a, p b, p c} : Finset (Fin 7)) ∈ fanoLines := by
  have := (hp _ h).1
  simpa [Finset.map_insert, Finset.map_singleton] using this

theorem perm_eq_fanoTf (p : Equiv.Perm (Fin 7))
    (hp : ∀ s ∈ fanoLines, s.map p.toEmbedding ∈ fanoLines ∧ s.map p⁻¹.toEmbedding ∈ fanoLines)
    (x : Fin 7) : p x = fanoTf (p 0, p 1, p 2) x := by
  obtain ⟨m1, m2, m3, m4⟩ := fanoLines_mem4
  have h3 : p 3 = fanoT7 (p 0) (p 1) := line_fanoT7 _ _ _ (fano_image_line p hp m1)
  have h4 : p 4 = fanoT7 (p 1) (p 2) := line_fanoT7 _ _ _ (fano_image_line p hp m2)
  have h5 : p 5 = fanoT7 (p 2) (p 3) := line_fanoT7 _ _ _ (fano_image_line p hp m3)
  have h6 : p 6 = fanoT7 (p 0) (p 2) := line_fanoT7 _ _ _ (fano_image_line p hp m4)
  obtain ⟨s0, s1, s2, s3, s4, s5, s6⟩ := fanoTf_spec (p 0) (p 1) (p 2)
  rw [← h3] at s5
  fin_cases x
  · exact s0.symm
  · exact s1.symm
  · exact s2.symm
  · exact h3.trans s3.symm
  · exact h4.trans s4.symm
  · exact h5.trans s5.symm
  · exact h6.trans s6.symm

@[expose] def fanoTrList : List (Fin 7 × Fin 7 × Fin 7) :=
  (List.finRange 7).flatMap fun a => (List.finRange 7).flatMap fun b =>
    ((List.finRange 7).filter fun c => decide (a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ c ≠ fanoT7 a b)).map
      fun c => (a, b, c)

theorem mem_fanoTrList {a b c : Fin 7} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hc : c ≠ fanoT7 a b) : (a, b, c) ∈ fanoTrList := by
  simp only [fanoTrList, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_finRange,
    true_and, decide_eq_true_eq]
  exact ⟨a, b, c, ⟨hab, hac, hbc, hc⟩, rfl⟩

theorem perm_chk_E64 :
    chk (fun q t => decide (∀ x, pc t.1 x = fanoTf q x)) fanoTrList permWords = true := by
  decide +kernel

theorem perm_cover : ∀ p : Equiv.Perm (Fin 7),
    (∀ s ∈ fanoLines, s.map p.toEmbedding ∈ fanoLines ∧ s.map p⁻¹.toEmbedding ∈ fanoLines) →
      Equiv.Perm.sign p = 1 → ∃ t ∈ permWords, pc t.1 = p := by
  intro p hp _
  have h3 : p 3 = fanoT7 (p 0) (p 1) := line_fanoT7 _ _ _ (fano_image_line p hp fanoLines_mem4.1)
  have hq : (p 0, p 1, p 2) ∈ fanoTrList := by
    refine mem_fanoTrList ?_ ?_ ?_ ?_
    · intro h; exact absurd (p.injective h) (by decide)
    · intro h; exact absurd (p.injective h) (by decide)
    · intro h; exact absurd (p.injective h) (by decide)
    · intro h
      have h' : p 2 = p 3 := h.trans h3.symm
      exact absurd (p.injective h') (by decide)
  obtain ⟨t, ht, hf⟩ := chk_spec _ _ _ perm_chk_E64 _ hq
  exact ⟨t, ht, Equiv.ext fun x => (of_decide_eq_true hf x).trans (perm_eq_fanoTf p hp x).symm⟩

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf
