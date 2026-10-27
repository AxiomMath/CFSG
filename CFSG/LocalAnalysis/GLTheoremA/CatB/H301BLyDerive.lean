module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BLyOrb
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BLyCard

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B.LyA11

open Equiv Equiv.Perm MulAction Subgroup

variable {X : Type*} [Fintype X] [DecidableEq X] {E : Subgroup (Perm X)}

namespace Triple

def U (t : Triple E) : Set X := orbit E (t.x 0) ∪ orbit E (t.x 1) ∪ orbit E (t.x 2)

theorem mem_U (t : Triple E) {z : X} : z ∈ t.U ↔ ∃ i, z ∈ orbit E (t.x i) := by
  constructor
  · intro hz
    rcases hz with (hz | hz) | hz
    · exact ⟨0, hz⟩
    · exact ⟨1, hz⟩
    · exact ⟨2, hz⟩
  · rintro ⟨i, hi⟩
    fin_cases i
    · exact Or.inl (Or.inl hi)
    · exact Or.inl (Or.inr hi)
    · exact Or.inr hi

theorem disjoint (t : Triple E) {i j : Fin 3} (hij : i ≠ j) :
    Disjoint (orbit E (t.x i) : Set X) (orbit E (t.x j)) :=
  disjoint_orbit_of_notMem (t.sep i j hij)

theorem ncard_U (hX : Fintype.card X = 11) (h : Elem27 E) (t : Triple E) : t.U.ncard = 9 := by
  have h3 : ∀ i, (orbit E (t.x i)).ncard = 3 := fun i => h.ncard_orbit_three hX (t.moved i)
  have d01 := t.disjoint (show (0 : Fin 3) ≠ 1 by decide)
  have d02 := t.disjoint (show (0 : Fin 3) ≠ 2 by decide)
  have d12 := t.disjoint (show (1 : Fin 3) ≠ 2 by decide)
  unfold U
  rw [Set.ncard_union_eq (Set.disjoint_union_left.2 ⟨d02, d12⟩), Set.ncard_union_eq d01,
    h3, h3, h3]

theorem fixed_outside (hX : Fintype.card X = 11) (h : Elem27 E) (t : Triple E) {z : X}
    (hz : z ∉ t.U) : ∀ e ∈ E, e z = z := by
  by_contra hcon
  obtain ⟨e, he, hez⟩ : ∃ e ∈ E, e z ≠ z := by
    by_contra h'
    exact hcon fun e he => by_contra fun hne => h' ⟨e, he, hne⟩
  have hzi : ∀ i, z ∉ orbit E (t.x i) := fun i hi => hz (t.mem_U.2 ⟨i, hi⟩)
  have hd : Disjoint t.U (orbit E z) :=
    Set.disjoint_union_left.2 ⟨Set.disjoint_union_left.2
      ⟨disjoint_orbit_of_notMem (hzi 0), disjoint_orbit_of_notMem (hzi 1)⟩,
      disjoint_orbit_of_notMem (hzi 2)⟩
  have h1 := Set.ncard_union_eq hd
  have h2 := h.three_le_ncard ⟨e, he, hez⟩
  have h3 := ncard_le_eleven hX (t.U ∪ orbit E z)
  have h4 := t.ncard_U hX h
  omega

theorem support_eq (hX : Fintype.card X = 11) (h : Elem27 E) (t : Triple E) (i : Fin 3) :
    ((t.a i).support : Set X) = orbit E (t.x i) := by
  have hout : ∀ z, z ∉ orbit E (t.x i) → t.a i z = z := by
    intro z hz
    by_cases hzU : z ∈ t.U
    · obtain ⟨j, hj⟩ := t.mem_U.1 hzU
      have hji : j ≠ i := fun hji => hz (hji ▸ hj)
      exact h.fix_orbit (t.a_mem i) (t.a_fix i j hji.symm) hj
    · exact t.fixed_outside hX h hzU (t.a i) (t.a_mem i)
  ext z
  constructor
  · intro hz
    by_contra hzO
    exact (Equiv.Perm.mem_support.1 (Finset.mem_coe.1 hz)) (hout z hzO)
  · intro hz
    rw [Finset.mem_coe, Equiv.Perm.mem_support]
    intro hfix
    have hax : t.a i (t.x i) = t.x i := by
      obtain ⟨e, he, rfl⟩ := mem_orbit'.1 hz
      have hc : (t.a i * e) (t.x i) = (e * t.a i) (t.x i) := by
        rw [h.comm (t.a i) (t.a_mem i) e he]
      have h1 : (t.a i * e) (t.x i) = t.a i (e (t.x i)) := rfl
      have h2 : (e * t.a i) (t.x i) = e (t.a i (t.x i)) := rfl
      exact e.injective (h2.symm.trans (hc.symm.trans (h1.trans hfix)))
    refine t.a_ne i (Equiv.ext fun w => ?_)
    by_cases hw : w ∈ orbit E (t.x i)
    · exact h.fix_orbit (t.a_mem i) hax hw
    · exact hout w hw

end Triple

theorem Elem27.exists_config (hX : Fintype.card X = 11) (h : Elem27 E) : Nonempty (Config E) := by
  obtain ⟨t⟩ := h.exists_triple hX
  have hc : t.Uᶜ.ncard = 2 := by
    rw [Set.ncard_compl t.U, Nat.card_eq_fintype_card, hX, t.ncard_U hX h]
  obtain ⟨p, q, hpq, hU⟩ := Set.ncard_eq_two.1 hc
  have hp : p ∈ t.Uᶜ := by rw [hU]; exact Set.mem_insert _ _
  have hq : q ∈ t.Uᶜ := by rw [hU]; exact Set.mem_insert_of_mem _ rfl
  refine ⟨⟨p, q, t.a, hpq, t.a_mem, fun i => h.cube _ (t.a_mem i), fun i => ?_,
    fun i j hij => ?_, t.fixed_outside hX h hp, t.fixed_outside hX h hq,
    fun z hzp hzq => ?_⟩⟩
  · rw [← Set.ncard_coe_finset, t.support_eq hX h i]
    exact h.ncard_orbit_three hX (t.moved i)
  · rw [← Finset.disjoint_coe, t.support_eq hX h i, t.support_eq hX h j]
    exact t.disjoint hij
  · have hzU : z ∈ t.U := by
      by_contra hzU
      have hz : z ∈ t.Uᶜ := hzU
      rw [hU] at hz
      rcases hz with h1 | h1
      · exact hzp h1
      · exact hzq h1
    obtain ⟨i, hi⟩ := t.mem_U.1 hzU
    refine ⟨i, ?_⟩
    rw [← Finset.mem_coe, t.support_eq hX h i]
    exact hi

theorem Elem27.card_le_sixteen (hX : Fintype.card X = 11) (h : Elem27 E) {T : Subgroup (Perm X)}
    (hT : IsPGroup 2 T) (hET : E ≤ normalizer T) : Nat.card T ≤ 16 := by
  obtain ⟨c⟩ := h.exists_config hX
  have hE : IsPGroup 3 E := fun g => ⟨1, Subtype.ext (by simpa using h.cube g.1 g.2)⟩
  exact CFSG.LocalAnalysis.GLTheoremA.H301B.LyA11.card_le_sixteen hX c hE hT hET

end CFSG.LocalAnalysis.GLTheoremA.H301B.LyA11

end
