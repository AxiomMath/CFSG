module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf2Basic

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf

open CFSG.ClassicalInvolution.Q3.AE

@[expose] def x8 (a b : Fin 8) : Fin 8 := ⟨(a.1 ^^^ b.1) % 8, Nat.mod_lt _ (by norm_num)⟩

@[expose] def qf (q : Fin 8 × Fin 8 × Fin 8 × Fin 8) (x : Fin 8) : Fin 8 :=
  x8 (x8 (x8 q.1 (if x.1 % 2 = 1 then x8 q.1 q.2.1 else 0))
      (if x.1 / 2 % 2 = 1 then x8 q.1 q.2.2.1 else 0))
    (if x.1 / 4 % 2 = 1 then x8 q.1 q.2.2.2 else 0)

theorem plane_xor : ∀ a b c y : Fin 8, ({a, b, c, y} : Finset (Fin 8)) ∈ affinePlanes →
    y = x8 (x8 a b) c := by decide +kernel

theorem qf_spec : ∀ a b c d : Fin 8, qf (a, b, c, d) 0 = a ∧ qf (a, b, c, d) 1 = b ∧
    qf (a, b, c, d) 2 = c ∧ qf (a, b, c, d) 4 = d ∧ qf (a, b, c, d) 3 = x8 (x8 a b) c ∧
    qf (a, b, c, d) 5 = x8 (x8 a b) d ∧ qf (a, b, c, d) 6 = x8 (x8 a c) d ∧
    qf (a, b, c, d) 7 = x8 (x8 a (x8 (x8 a b) c)) d := by decide +kernel

theorem planes_mem : ({0, 1, 2, 3} : Finset (Fin 8)) ∈ affinePlanes ∧
    ({0, 1, 4, 5} : Finset (Fin 8)) ∈ affinePlanes ∧
    ({0, 2, 4, 6} : Finset (Fin 8)) ∈ affinePlanes ∧
    ({0, 3, 4, 7} : Finset (Fin 8)) ∈ affinePlanes := by decide +kernel

theorem image_plane (p : Equiv.Perm (Fin 8)) (hp : p ∈ agl32) {a b c d : Fin 8}
    (h : ({a, b, c, d} : Finset (Fin 8)) ∈ affinePlanes) :
    ({p a, p b, p c, p d} : Finset (Fin 8)) ∈ affinePlanes := by
  have := (hp _ h).1
  simpa [Finset.map_insert, Finset.map_singleton] using this

theorem perm_eq_qf (p : Equiv.Perm (Fin 8)) (hp : p ∈ agl32) (x : Fin 8) :
    p x = qf (p 0, p 1, p 2, p 4) x := by
  obtain ⟨m1, m2, m3, m4⟩ := planes_mem
  have h3 : p 3 = x8 (x8 (p 0) (p 1)) (p 2) := plane_xor _ _ _ _ (image_plane p hp m1)
  have h5 : p 5 = x8 (x8 (p 0) (p 1)) (p 4) := plane_xor _ _ _ _ (image_plane p hp m2)
  have h6 : p 6 = x8 (x8 (p 0) (p 2)) (p 4) := plane_xor _ _ _ _ (image_plane p hp m3)
  have h7 : p 7 = x8 (x8 (p 0) (p 3)) (p 4) := plane_xor _ _ _ _ (image_plane p hp m4)
  obtain ⟨s0, s1, s2, s4, s3, s5, s6, s7⟩ := qf_spec (p 0) (p 1) (p 2) (p 4)
  fin_cases x
  · exact s0.symm
  · exact s1.symm
  · exact s2.symm
  · exact h3.trans s3.symm
  · exact s4.symm
  · exact h5.trans s5.symm
  · exact h6.trans s6.symm
  · rw [show (7 : Fin 8) = ⟨7, by norm_num⟩ from rfl] at *
    exact (h7.trans (by rw [h3])).trans s7.symm

@[expose] def quadsList : List (Fin 8 × Fin 8 × Fin 8 × Fin 8) :=
  (List.finRange 8).flatMap fun a => (List.finRange 8).flatMap fun b =>
    (List.finRange 8).flatMap fun c =>
      ((List.finRange 8).filter fun d => decide (a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ d ≠ a ∧ d ≠ b ∧ d ≠ c ∧
        d ≠ x8 (x8 a b) c)).map fun d => (a, b, c, d)

theorem mem_quadsList {a b c d : Fin 8} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hda : d ≠ a)
    (hdb : d ≠ b) (hdc : d ≠ c) (hdy : d ≠ x8 (x8 a b) c) : (a, b, c, d) ∈ quadsList := by
  simp only [quadsList, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_finRange,
    true_and, decide_eq_true_eq]
  exact ⟨a, b, c, d, ⟨hab, hac, hbc, hda, hdb, hdc, hdy⟩, rfl⟩

@[expose] def chk {α β : Type} (f : α → β → Bool) : List α → List β → Bool
  | a :: as, b :: bs => f a b && chk f as bs
  | [], [] => true
  | _, _ => false

theorem chk_spec {α β : Type} (f : α → β → Bool) :
    ∀ (as : List α) (bs : List β), chk f as bs = true → ∀ a ∈ as, ∃ b ∈ bs, f a b = true := by
  intro as
  induction as with
  | nil => intro bs _ a ha; exact absurd ha (by simp)
  | cons a0 as ih =>
    intro bs h a ha
    cases bs with
    | nil => simp [chk] at h
    | cons b0 bs =>
      simp only [chk, Bool.and_eq_true] at h
      rcases List.mem_cons.mp ha with rfl | ha'
      · exact ⟨b0, List.mem_cons_self, h.1⟩
      · obtain ⟨b, hb, hfb⟩ := ih bs h.2 a ha'
        exact ⟨b, List.mem_cons_of_mem _ hb, hfb⟩

theorem perm_cover_of_chk {T : List (List (List (Fin 8)) × List ℕ)}
    (hT : chk (fun q t => decide (∀ x, pc t.1 x = qf q x)) quadsList T = true) :
    ∀ p ∈ agl32, ∃ t ∈ T, pc t.1 = p := by
  intro p hp
  obtain ⟨m1, -, -, -⟩ := planes_mem
  have h3 : p 3 = x8 (x8 (p 0) (p 1)) (p 2) := plane_xor _ _ _ _ (image_plane p hp m1)
  have hq : (p 0, p 1, p 2, p 4) ∈ quadsList := by
    refine mem_quadsList ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro h; have := p.injective h; exact absurd this (by decide)
    · intro h; have := p.injective h; exact absurd this (by decide)
    · intro h; have := p.injective h; exact absurd this (by decide)
    · intro h; have := p.injective h; exact absurd this (by decide)
    · intro h; have := p.injective h; exact absurd this (by decide)
    · intro h; have := p.injective h; exact absurd this (by decide)
    · intro h
      have h4 : p 4 = p 3 := by rw [h3]; exact h
      have := p.injective h4; exact absurd this (by decide)
  obtain ⟨t, ht, hf⟩ := chk_spec _ _ _ hT _ hq
  refine ⟨t, ht, Equiv.ext fun x => ?_⟩
  rw [perm_eq_qf p hp x]
  exact of_decide_eq_true hf x

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf
