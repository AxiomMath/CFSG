module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BLyFix

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B.LyA11

open Equiv Equiv.Perm MulAction Subgroup

variable {X : Type*} [Fintype X] [DecidableEq X]

structure Elem27 (E : Subgroup (Perm X)) : Prop where
  comm : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e
  cube : ∀ e ∈ E, e ^ 3 = 1
  card : Nat.card E = 27

theorem exists_moved {g : Perm X} (hg : g ≠ 1) : ∃ z, g z ≠ z := by
  by_contra hcon
  exact hg (Equiv.ext fun z => by_contra fun hz => hcon ⟨z, hz⟩)

theorem mem_orbit' {E : Subgroup (Perm X)} {x z : X} : z ∈ orbit E x ↔ ∃ e ∈ E, e x = z := by
  constructor
  · intro h
    obtain ⟨⟨e, he⟩, hez⟩ := mem_orbit_iff.1 h
    exact ⟨e, he, hez⟩
  · rintro ⟨e, he, hez⟩
    exact mem_orbit_iff.2 ⟨⟨e, he⟩, hez⟩

theorem disjoint_orbit_of_notMem {E : Subgroup (Perm X)} {x z : X} (hz : z ∉ orbit E x) :
    Disjoint (orbit E x : Set X) (orbit E z) := by
  rw [Set.disjoint_left]
  intro w hw hw'
  apply hz
  have h1 : orbit E w = orbit E x := orbit_eq_iff.2 hw
  have h2 : orbit E w = orbit E z := orbit_eq_iff.2 hw'
  have : z ∈ orbit E z := mem_orbit_self z
  rwa [← h2, h1] at this

theorem ncard_le_eleven (hX : Fintype.card X = 11) (S : Set X) : S.ncard ≤ 11 := by
  have := Set.ncard_le_ncard (Set.subset_univ S) (Set.toFinite _)
  rwa [Set.ncard_univ, Nat.card_eq_fintype_card, hX] at this

namespace Elem27

variable {E : Subgroup (Perm X)}

theorem fix_orbit (h : Elem27 E) {g : Perm X} (hg : g ∈ E) {x : X} (hgx : g x = x) {z : X}
    (hz : z ∈ orbit E x) : g z = z := by
  obtain ⟨e, he, rfl⟩ := mem_orbit'.1 hz
  calc g (e x) = (g * e) x := rfl
    _ = (e * g) x := by rw [h.comm g hg e he]
    _ = e (g x) := rfl
    _ = e x := by rw [hgx]

theorem orbit_ncard_dvd (h : Elem27 E) (x : X) : (orbit E x).ncard ∣ 27 := by
  rw [← MulAction.index_stabilizer E x, ← h.card]
  exact Subgroup.index_dvd_card _

theorem ncard_cases (h : Elem27 E) (x : X) :
    (orbit E x).ncard = 1 ∨ (orbit E x).ncard = 3 ∨ (orbit E x).ncard = 9 ∨
      (orbit E x).ncard = 27 := by
  obtain ⟨m, hm, hm'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1
    (show (orbit E x).ncard ∣ 3 ^ 3 by simpa using h.orbit_ncard_dvd x)
  interval_cases m
  · exact Or.inl (by simpa using hm')
  · exact Or.inr (Or.inl (by simpa using hm'))
  · exact Or.inr (Or.inr (Or.inl (by simpa using hm')))
  · exact Or.inr (Or.inr (Or.inr (by simpa using hm')))

theorem two_le_ncard {x : X} (hx : ∃ e ∈ E, e x ≠ x) : 2 ≤ (orbit E x).ncard := by
  obtain ⟨e, he, hne⟩ := hx
  exact (Set.one_lt_ncard_iff (Set.toFinite _)).2
    ⟨x, e x, mem_orbit_self x, mem_orbit'.2 ⟨e, he, rfl⟩, hne.symm⟩

theorem three_le_ncard (h : Elem27 E) {x : X} (hx : ∃ e ∈ E, e x ≠ x) :
    3 ≤ (orbit E x).ncard := by
  have h2 := two_le_ncard hx
  rcases h.ncard_cases x with h' | h' | h' | h' <;> omega

theorem ncard_orbit_three (hX : Fintype.card X = 11) (h : Elem27 E) {x : X}
    (hx : ∃ e ∈ E, e x ≠ x) : (orbit E x).ncard = 3 := by
  have h2 := two_le_ncard hx
  have h11 := ncard_le_eleven hX (orbit E x : Set X)
  rcases h.ncard_cases x with h1 | h3 | h9 | h27
  · omega
  · exact h3
  · exfalso
    have hidx : (stabilizer E x).index = 9 := by rw [MulAction.index_stabilizer]; exact h9
    have hcm := Subgroup.card_mul_index (stabilizer E x)
    rw [h.card, hidx] at hcm
    have hgt : 1 < Nat.card (stabilizer E x) := by omega
    obtain ⟨⟨g, hgs⟩, hg1⟩ :=
      Subgroup.ne_bot_iff_exists_ne_one.1 ((Subgroup.one_lt_card_iff_ne_bot _).1 hgt)
    have hgx : (g : Perm X) x = x := MulAction.mem_stabilizer_iff.1 hgs
    have hgne : (g : Perm X) ≠ 1 := by
      intro h'
      apply hg1
      apply Subtype.ext
      apply Subtype.ext
      exact h'
    obtain ⟨z, hz⟩ := exists_moved hgne
    have hzO : z ∉ orbit E x := fun hm => hz (h.fix_orbit g.2 hgx hm)
    have h3z := h.three_le_ncard ⟨g, g.2, hz⟩
    have hu := Set.ncard_union_eq (disjoint_orbit_of_notMem hzO)
    have := ncard_le_eleven hX (orbit E x ∪ orbit E z)
    omega
  · omega

theorem exists_fix_ne_one (hX : Fintype.card X = 11) (h : Elem27 E) {u v : X}
    (hu : ∃ e ∈ E, e u ≠ u) (hv : ∃ e ∈ E, e v ≠ v) :
    ∃ a ∈ E, a ≠ 1 ∧ a u = u ∧ a v = v := by
  have hiu : (stabilizer E u).index = 3 := by
    rw [MulAction.index_stabilizer]; exact ncard_orbit_three hX h hu
  have hiv : (stabilizer E v).index = 3 := by
    rw [MulAction.index_stabilizer]; exact ncard_orbit_three hX h hv
  have hle : (stabilizer E u ⊓ stabilizer E v).index ≤ 9 := by
    have := Subgroup.index_inf_le (H := stabilizer E u) (K := stabilizer E v)
    rwa [hiu, hiv] at this
  have hcm := Subgroup.card_mul_index (stabilizer E u ⊓ stabilizer E v)
  rw [h.card] at hcm
  have hgt : 1 < Nat.card (stabilizer E u ⊓ stabilizer E v : Subgroup E) := by
    by_contra hc
    have := Nat.mul_le_mul (not_lt.1 hc) hle
    omega
  obtain ⟨⟨g, hgu, hgv⟩, hg1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.1 ((Subgroup.one_lt_card_iff_ne_bot _).1 hgt)
  have hgne : (g : Perm X) ≠ 1 := by
    intro h'
    apply hg1
    apply Subtype.ext
    apply Subtype.ext
    exact h'
  exact ⟨g, g.2, hgne, MulAction.mem_stabilizer_iff.1 hgu, MulAction.mem_stabilizer_iff.1 hgv⟩

end Elem27

structure Triple (E : Subgroup (Perm X)) where
  x : Fin 3 → X
  a : Fin 3 → Perm X
  moved : ∀ i, ∃ e ∈ E, e (x i) ≠ x i
  a_mem : ∀ i, a i ∈ E
  a_ne : ∀ i, a i ≠ 1
  a_fix : ∀ i j, i ≠ j → a i (x j) = x j
  sep : ∀ i j, i ≠ j → x j ∉ orbit E (x i)

theorem Elem27.exists_triple {E : Subgroup (Perm X)} (hX : Fintype.card X = 11) (h : Elem27 E) :
    Nonempty (Triple E) := by
  obtain ⟨x0, hx0⟩ : ∃ x0, ∃ e ∈ E, e x0 ≠ x0 := by
    have h1 : E ≠ ⊥ := (Subgroup.one_lt_card_iff_ne_bot _).1 (by rw [h.card]; norm_num)
    obtain ⟨⟨e, he⟩, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 h1
    obtain ⟨z, hz⟩ := exists_moved (g := e) fun h' => he1 (Subtype.ext h')
    exact ⟨z, e, he, hz⟩
  obtain ⟨g1, hg1E, hg1, hg1x0, -⟩ := h.exists_fix_ne_one hX hx0 hx0
  obtain ⟨x1, hx1⟩ := exists_moved hg1
  have hsep1 : x1 ∉ orbit E x0 := fun hm => hx1 (h.fix_orbit hg1E hg1x0 hm)
  have hmv1 : ∃ e ∈ E, e x1 ≠ x1 := ⟨g1, hg1E, hx1⟩
  obtain ⟨g2, hg2E, hg2, hg2x0, hg2x1⟩ := h.exists_fix_ne_one hX hx0 hmv1
  obtain ⟨x2, hx2⟩ := exists_moved hg2
  have hsep2 : x2 ∉ orbit E x0 := fun hm => hx2 (h.fix_orbit hg2E hg2x0 hm)
  have hsep2' : x2 ∉ orbit E x1 := fun hm => hx2 (h.fix_orbit hg2E hg2x1 hm)
  have hmv2 : ∃ e ∈ E, e x2 ≠ x2 := ⟨g2, hg2E, hx2⟩
  obtain ⟨a0, ha0E, ha0, ha0x1, ha0x2⟩ := h.exists_fix_ne_one hX hmv1 hmv2
  obtain ⟨a1, ha1E, ha1, ha1x0, ha1x2⟩ := h.exists_fix_ne_one hX hx0 hmv2
  refine ⟨⟨![x0, x1, x2], ![a0, a1, g2], ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro i
    fin_cases i
    exacts [hx0, hmv1, hmv2]
  · intro i
    fin_cases i
    exacts [ha0E, ha1E, hg2E]
  · intro i
    fin_cases i
    exacts [ha0, ha1, hg2]
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
        | exact absurd rfl hij
        | exact ha0x1 | exact ha0x2 | exact ha1x0 | exact ha1x2 | exact hg2x0 | exact hg2x1
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
        | exact absurd rfl hij
        | exact hsep1 | exact hsep2 | exact hsep2'
        | exact fun hm => hsep1 (mem_orbit_symm.1 hm)
        | exact fun hm => hsep2 (mem_orbit_symm.1 hm)
        | exact fun hm => hsep2' (mem_orbit_symm.1 hm)

end CFSG.LocalAnalysis.GLTheoremA.H301B.LyA11

end
