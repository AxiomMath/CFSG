module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaData.LinearAlgebra.Defs

public section

namespace CFSG.EvenSporadicStandard.HNRecog.HaradaLA

open Finset

@[expose] def c1 (X : Finset V6) (x : V6) : ℕ := (X.filter fun y => x + y ∈ X).card

@[expose] def c2 (X : Finset V6) (x : V6) : ℕ := ∑ y ∈ X.filter fun y => x + y ∈ X, c1 X y

private lemma filter_perm (X : Finset V6) (g : Equiv.Perm V6) (hg : IsAddPerm g)
    (hX : ∀ x, g x ∈ X ↔ x ∈ X) (x : V6) :
    X.filter (fun y => g x + y ∈ X) = (X.filter fun y => x + y ∈ X).map g.toEmbedding := by
  ext y
  rw [Finset.mem_filter, Finset.mem_map]
  constructor
  · rintro ⟨hyX, hgxy⟩
    refine ⟨g.symm y, ?_, g.apply_symm_apply y⟩
    rw [Finset.mem_filter]
    refine ⟨(hX (g.symm y)).1 ?_, ?_⟩
    · rw [Equiv.apply_symm_apply]; exact hyX
    · have : g (x + g.symm y) ∈ X := by
        rw [hg x (g.symm y), Equiv.apply_symm_apply]
        exact hgxy
      exact (hX (x + g.symm y)).1 this
  · rintro ⟨z, hz, rfl⟩
    rw [Finset.mem_filter] at hz
    change g z ∈ X ∧ g x + g z ∈ X
    exact ⟨(hX z).2 hz.1, by rw [← hg x z]; exact (hX (x + z)).2 hz.2⟩

theorem c1_perm (X : Finset V6) (g : Equiv.Perm V6) (hg : IsAddPerm g)
    (hX : ∀ x, g x ∈ X ↔ x ∈ X) (x : V6) : c1 X (g x) = c1 X x := by
  simp only [c1]
  rw [filter_perm X g hg hX x, Finset.card_map]

theorem c2_perm (X : Finset V6) (g : Equiv.Perm V6) (hg : IsAddPerm g)
    (hX : ∀ x, g x ∈ X ↔ x ∈ X) (x : V6) : c2 X (g x) = c2 X x := by
  simp only [c2]
  rw [filter_perm X g hg hX x, Finset.sum_map]
  exact Finset.sum_congr rfl fun y _ => c1_perm X g hg hX y

abbrev IsolatedByC1 (X : Finset V6) : Prop :=
  tv ∈ X ∧ ∀ x ∈ X, c1 X x = c1 X tv → x = tv

abbrev IsolatedByC2 (X : Finset V6) : Prop :=
  tv ∈ X ∧ ∀ x ∈ X, c2 X x = c2 X tv → x = tv

theorem fix_tv_of_isolatedByC1 {X : Finset V6} (h : IsolatedByC1 X) (g : Equiv.Perm V6)
    (hg : IsAddPerm g) (hX : ∀ x, g x ∈ X ↔ x ∈ X) : g tv = tv :=
  h.2 (g tv) ((hX tv).2 h.1) (c1_perm X g hg hX tv)

theorem fix_tv_of_isolatedByC2 {X : Finset V6} (h : IsolatedByC2 X) (g : Equiv.Perm V6)
    (hg : IsAddPerm g) (hX : ∀ x, g x ∈ X ↔ x ∈ X) : g tv = tv :=
  h.2 (g tv) ((hX tv).2 h.1) (c2_perm X g hg hX tv)

set_option maxRecDepth 100000 in
theorem isolatedByC1_Yv2 : IsolatedByC1 Yv2 := by decide +kernel

set_option maxRecDepth 100000 in
theorem isolatedByC1_Yv1 : IsolatedByC1 Yv1 := by decide +kernel

set_option maxRecDepth 100000 in
theorem isolatedByC1_Yv12 : IsolatedByC1 Yv12 := by decide +kernel

set_option maxRecDepth 100000 in
theorem isolatedByC2_X48 : IsolatedByC2 X48 := by decide +kernel

theorem rigid_Yv2 (g : Equiv.Perm V6) (hg : IsAddPerm g) (hX : ∀ x, g x ∈ Yv2 ↔ x ∈ Yv2) :
    g tv = tv :=
  fix_tv_of_isolatedByC1 isolatedByC1_Yv2 g hg hX

theorem rigid_Yv1 (g : Equiv.Perm V6) (hg : IsAddPerm g) (hX : ∀ x, g x ∈ Yv1 ↔ x ∈ Yv1) :
    g tv = tv :=
  fix_tv_of_isolatedByC1 isolatedByC1_Yv1 g hg hX

theorem rigid_Yv12 (g : Equiv.Perm V6) (hg : IsAddPerm g) (hX : ∀ x, g x ∈ Yv12 ↔ x ∈ Yv12) :
    g tv = tv :=
  fix_tv_of_isolatedByC1 isolatedByC1_Yv12 g hg hX

theorem rigid_X48 (g : Equiv.Perm V6) (hg : IsAddPerm g) (hX : ∀ x, g x ∈ X48 ↔ x ∈ X48) :
    g tv = tv :=
  fix_tv_of_isolatedByC2 isolatedByC2_X48 g hg hX

end CFSG.EvenSporadicStandard.HNRecog.HaradaLA
