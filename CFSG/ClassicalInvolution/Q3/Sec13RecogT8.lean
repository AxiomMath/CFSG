module

import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Data.Fintype.EquivFin

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

private def prismLines {Δ : Type*} [Fintype Δ] [DecidableEq Δ] (adj : Δ → Δ → Prop)
    [DecidableRel adj] : Finset (Finset Δ) :=
  ((Finset.univ : Finset Δ).powersetCard 7).filter fun C => ∀ x ∈ C, ∀ y ∈ C, x ≠ y → adj x y

private lemma mem_prismLines {Δ : Type*} [Fintype Δ] [DecidableEq Δ] (adj : Δ → Δ → Prop)
    [DecidableRel adj] (C : Finset Δ) :
    C ∈ prismLines adj ↔ C.card = 7 ∧ ∀ x ∈ C, ∀ y ∈ C, x ≠ y → adj x y := by
  simp [prismLines, Finset.mem_powersetCard]

private lemma prism_line_eq {Δ : Type*} [DecidableEq Δ] (adj : Δ → Δ → Prop) (u : Δ)
    (A B C : Finset Δ) (hA : A.card = 6) (hB : B.card = 6) (hdisj : Disjoint A B)
    (hnbr : ∀ v, adj u v ↔ v ∈ A ∪ B)
    (hmA : ∀ a ∈ A, ∀ a' ∈ A, ∀ b ∈ B, adj a b → adj a' b → a = a')
    (hmB : ∀ b ∈ B, ∀ b' ∈ B, ∀ a ∈ A, adj a b → adj a b' → b = b')
    (hC : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → adj x y) (hcard : C.card = 7) (huC : u ∈ C) :
    C = insert u A ∨ C = insert u B := by
  have hmem : ∀ x ∈ C.erase u, x ∈ C := fun x hx => Finset.mem_of_mem_erase hx
  have hsub : ∀ x ∈ C.erase u, x ∈ A ∪ B := fun x hx =>
    (hnbr x).1 (hC u huC x (hmem x hx) (Finset.ne_of_mem_erase hx).symm)
  have hcard' : (C.erase u).card = 6 := by
    have := Finset.card_erase_of_mem huC
    omega
  have key : C.erase u = A ∨ C.erase u = B := by
    by_cases hex : ∃ a ∈ C.erase u, a ∈ A
    · obtain ⟨a, ha, haA⟩ := hex
      left
      have hnoB : ∀ x ∈ C.erase u, x ∉ B := by
        intro x hx hxB
        have hax : a ≠ x := fun h => Finset.disjoint_left.1 hdisj haA (by rw [h]; exact hxB)
        have hsub2 : C.erase u ⊆ {a, x} := by
          intro y hy
          by_contra hyn
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hyn
          obtain ⟨hya, hyx⟩ := hyn
          have hxa : adj a x := hC a (hmem a ha) x (hmem x hx) hax
          have hyx' : adj y x := hC y (hmem y hy) x (hmem x hx) hyx
          have hay : adj a y := hC a (hmem a ha) y (hmem y hy) (fun h => hya h.symm)
          rcases Finset.mem_union.1 (hsub y hy) with hyA | hyB
          · exact hya (hmA a haA y hyA x hxB hxa hyx').symm
          · exact hyx (hmB y hyB x hxB a haA hay hxa)
        have h2 : ({a, x} : Finset Δ).card ≤ 2 := Finset.card_le_two
        have h3 := Finset.card_le_card hsub2
        omega
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        rcases Finset.mem_union.1 (hsub x hx) with h | h
        · exact h
        · exact absurd h (hnoB x hx)
      · omega
    · right
      have hex' : ∀ x ∈ C.erase u, x ∉ A := fun x hx hxA => hex ⟨x, hx, hxA⟩
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        rcases Finset.mem_union.1 (hsub x hx) with h | h
        · exact absurd h (hex' x hx)
        · exact h
      · omega
  rcases key with h | h
  · left
    rw [← h, Finset.insert_erase huC]
  · right
    rw [← h, Finset.insert_erase huC]

private lemma prism_insert_mem {Δ : Type*} [DecidableEq Δ] (adj : Δ → Δ → Prop)
    (hsymm : ∀ u v, adj u v → adj v u) (hirr : ∀ u, ¬ adj u u) (u : Δ) (A : Finset Δ)
    (hA : A.card = 6) (hu : ∀ x ∈ A, adj u x) (hcl : ∀ v ∈ A, ∀ w ∈ A, v ≠ w → adj v w) :
    (insert u A).card = 7 ∧ ∀ x ∈ insert u A, ∀ y ∈ insert u A, x ≠ y → adj x y := by
  have huA : u ∉ A := fun h => hirr u (hu u h)
  refine ⟨?_, ?_⟩
  · rw [Finset.card_insert_of_notMem huA]
    omega
  · intro x hx y hy hxy
    rcases Finset.mem_insert.1 hx with hx1 | hx2 <;>
      rcases Finset.mem_insert.1 hy with hy1 | hy2
    · exact absurd (hx1.trans hy1.symm) hxy
    · rw [hx1]
      exact hu y hy2
    · rw [hy1]
      exact hsymm _ _ (hu x hx2)
    · exact hcl x hx2 y hy2 hxy

private lemma prism_insert_ne {Δ : Type*} [DecidableEq Δ] (adj : Δ → Δ → Prop)
    (hirr : ∀ u, ¬ adj u u) (u : Δ) (A B : Finset Δ) (hA : A.card = 6)
    (hdisj : Disjoint A B) (hu : ∀ x ∈ A, adj u x) : insert u A ≠ insert u B := by
  intro h
  obtain ⟨a, ha⟩ : A.Nonempty := Finset.card_pos.1 (by omega)
  have haB : a ∈ insert u B := by
    rw [← h]
    exact Finset.mem_insert_of_mem ha
  rcases Finset.mem_insert.1 haB with h1 | h1
  · have hau := hu a ha
    rw [h1] at hau
    exact hirr u hau
  · exact Finset.disjoint_left.1 hdisj ha h1

theorem exists_equiv_pairs_of_locally_prism {Δ : Type*} [Fintype Δ] [DecidableEq Δ]
    (adj : Δ → Δ → Prop) [DecidableRel adj] (hsymm : ∀ u v, adj u v → adj v u)
    (hirr : ∀ u, ¬ adj u u) (hcard : Fintype.card Δ = 28)
    (hloc : ∀ u : Δ, ∃ A B : Finset Δ, A.card = 6 ∧ B.card = 6 ∧ Disjoint A B ∧
      (∀ v, adj u v ↔ v ∈ A ∪ B) ∧ (∀ v ∈ A, ∀ w ∈ A, v ≠ w → adj v w) ∧
      (∀ v ∈ B, ∀ w ∈ B, v ≠ w → adj v w) ∧
      (∀ a ∈ A, ∀ a' ∈ A, ∀ b ∈ B, adj a b → adj a' b → a = a') ∧
      (∀ b ∈ B, ∀ b' ∈ B, ∀ a ∈ A, adj a b → adj a b' → b = b')) :
    ∃ e : Δ ≃ {s : Finset (Fin 8) // s.card = 2},
      ∀ u v, adj u v ↔ (u ≠ v ∧ ((e u : Finset (Fin 8)) ∩ (e v : Finset (Fin 8))).Nonempty) := by
  choose A B hA hB hdisj hnbr hAcl hBcl hmA hmB using hloc
  have hAnb : ∀ u x, x ∈ A u → adj u x :=
    fun u x hx => (hnbr u x).2 (Finset.mem_union_left _ hx)
  have hBnb : ∀ u x, x ∈ B u → adj u x :=
    fun u x hx => (hnbr u x).2 (Finset.mem_union_right _ hx)
  have hlineA : ∀ u, insert u (A u) ∈ prismLines adj := fun u =>
    (mem_prismLines adj _).2 (prism_insert_mem adj hsymm hirr u (A u) (hA u) (hAnb u) (hAcl u))
  have hlineB : ∀ u, insert u (B u) ∈ prismLines adj := fun u =>
    (mem_prismLines adj _).2 (prism_insert_mem adj hsymm hirr u (B u) (hB u) (hBnb u) (hBcl u))
  have hthrough : ∀ u, (prismLines adj).filter (fun C => u ∈ C) =
      {insert u (A u), insert u (B u)} := by
    intro u
    ext C
    rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hCL, huC⟩
      obtain ⟨hc7, hcl⟩ := (mem_prismLines adj C).1 hCL
      exact prism_line_eq adj u (A u) (B u) C (hA u) (hB u) (hdisj u) (hnbr u) (hmA u)
        (hmB u) hcl hc7 huC
    · rintro (rfl | rfl)
      · exact ⟨hlineA u, Finset.mem_insert_self _ _⟩
      · exact ⟨hlineB u, Finset.mem_insert_self _ _⟩
  have hdeg : ∀ u, ((prismLines adj).filter (fun C => u ∈ C)).card = 2 := by
    intro u
    rw [hthrough u]
    exact Finset.card_pair (prism_insert_ne adj hirr u (A u) (B u) (hA u) (hdisj u) (hAnb u))
  have hfilt : ∀ C ∈ prismLines adj,
      ((Finset.univ : Finset Δ).filter (fun u => u ∈ C)).card = 7 := by
    intro C hC
    have hC' : (Finset.univ : Finset Δ).filter (fun u => u ∈ C) = C := by
      ext u
      simp
    rw [hC']
    exact ((mem_prismLines adj C).1 hC).1
  have hcountL : (prismLines adj).card = 8 := by
    have hdc : ∑ u : Δ, ((prismLines adj).filter (fun C => u ∈ C)).card =
        ∑ C ∈ prismLines adj, ((Finset.univ : Finset Δ).filter (fun u => u ∈ C)).card :=
      Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (r := fun (u : Δ) (C : Finset Δ) => u ∈ C) (s := Finset.univ) (t := prismLines adj)
    have h1 : ∑ u : Δ, ((prismLines adj).filter (fun C => u ∈ C)).card = 56 := by
      simp only [hdeg, Finset.sum_const, Finset.card_univ, hcard, smul_eq_mul]
    have h2 : ∑ C ∈ prismLines adj, ((Finset.univ : Finset Δ).filter (fun u => u ∈ C)).card =
        (prismLines adj).card * 7 := by
      rw [Finset.sum_congr rfl hfilt, Finset.sum_const, smul_eq_mul]
    omega
  have hLcard : Fintype.card {C // C ∈ prismLines adj} = 8 :=
    (Fintype.card_coe _).trans hcountL
  obtain ⟨σ, -⟩ : ∃ σ : {C // C ∈ prismLines adj} ≃ Fin 8, True :=
    ⟨Fintype.equivFinOfCardEq hLcard, trivial⟩
  have hσC : ∀ C : Finset Δ, ∀ hC : C ∈ prismLines adj, ∃ i, (σ.symm i).1 = C :=
    fun C hC => ⟨σ ⟨C, hC⟩, by simp⟩
  obtain ⟨P, hPdef⟩ : ∃ P : Δ → Finset (Fin 8), ∀ u i, i ∈ P u ↔ u ∈ (σ.symm i).1 :=
    ⟨fun u => (Finset.univ : Finset (Fin 8)).filter fun i => u ∈ (σ.symm i).1,
      fun u i => by simp⟩
  have hPcard : ∀ u, (P u).card = 2 := by
    intro u
    refine Eq.trans (Finset.card_nbij (fun i => (σ.symm i).1) ?_ ?_ ?_) (hdeg u)
    · intro i hi
      have hu : u ∈ (σ.symm i).1 := (hPdef u i).1 (Finset.mem_coe.1 hi)
      exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨(σ.symm i).2, hu⟩)
    · intro i _ j _ hij
      exact σ.symm.injective (Subtype.ext hij)
    · intro C hC
      have hCf := Finset.mem_filter.1 (Finset.mem_coe.1 hC)
      refine ⟨σ ⟨C, hCf.1⟩, Finset.mem_coe.2 ((hPdef u _).2 ?_), ?_⟩
      · simpa using hCf.2
      · simp
  have hpt : ∀ u v, P u = P v → u = v := by
    intro u v huv
    have hcontain : ∀ C : Finset Δ, C ∈ prismLines adj → u ∈ C → v ∈ C := by
      intro C hC huC
      obtain ⟨i, hi⟩ := hσC C hC
      have hiu : i ∈ P u := (hPdef u i).2 (by rw [hi]; exact huC)
      have hiv : i ∈ P v := by
        rw [← huv]
        exact hiu
      have hvi := (hPdef v i).1 hiv
      rwa [hi] at hvi
    rcases Finset.mem_insert.1 (hcontain _ (hlineA u) (Finset.mem_insert_self u (A u)))
      with h1 | h1
    · exact h1.symm
    · rcases Finset.mem_insert.1 (hcontain _ (hlineB u) (Finset.mem_insert_self u (B u)))
        with h2 | h2
      · exact h2.symm
      · exact absurd h2 (Finset.disjoint_left.1 (hdisj u) h1)
  have hcardT : Fintype.card Δ = Fintype.card {s : Finset (Fin 8) // s.card = 2} := by
    rw [hcard, Fintype.card_finset_len, Fintype.card_fin]
    decide
  obtain ⟨f, hf⟩ : ∃ f : Δ → {s : Finset (Fin 8) // s.card = 2}, ∀ u, (f u).1 = P u :=
    ⟨fun u => ⟨P u, hPcard u⟩, fun u => rfl⟩
  have hinj : Function.Injective f := fun u v h =>
    hpt u v (by rw [← hf u, ← hf v]; exact congrArg Subtype.val h)
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, hcardT⟩
  have he : ∀ u, ((Equiv.ofBijective f hbij u : {s : Finset (Fin 8) // s.card = 2}) :
      Finset (Fin 8)) = P u := fun u => hf u
  refine ⟨Equiv.ofBijective f hbij, fun u v => ?_⟩
  rw [he u, he v]
  constructor
  · intro h
    have huv : u ≠ v := by
      rintro rfl
      exact hirr _ h
    have hex : ∃ C ∈ prismLines adj, u ∈ C ∧ v ∈ C := by
      rcases Finset.mem_union.1 ((hnbr u v).1 h) with hvA | hvB
      · exact ⟨insert u (A u), hlineA u, Finset.mem_insert_self _ _,
          Finset.mem_insert_of_mem hvA⟩
      · exact ⟨insert u (B u), hlineB u, Finset.mem_insert_self _ _,
          Finset.mem_insert_of_mem hvB⟩
    obtain ⟨C, hC, huC, hvC⟩ := hex
    obtain ⟨i, hi⟩ := hσC C hC
    refine ⟨huv, i, Finset.mem_inter.2 ⟨(hPdef u i).2 ?_, (hPdef v i).2 ?_⟩⟩
    · rw [hi]
      exact huC
    · rw [hi]
      exact hvC
  · rintro ⟨huv, i, hi⟩
    obtain ⟨hu, hv⟩ := Finset.mem_inter.1 hi
    exact ((mem_prismLines adj _).1 (σ.symm i).2).2 u ((hPdef u i).1 hu) v
      ((hPdef v i).1 hv) huv

end CFSG.ClassicalInvolution.Q3.Sec13
