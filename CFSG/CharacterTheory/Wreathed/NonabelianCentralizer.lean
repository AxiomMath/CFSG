module

public import CFSG.CharacterTheory.Wreathed.Involutions

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical

theorem base_commutes_swap_iff (m : ℕ) (a b c d : ZMod m) :
    Commute (element m a b 0) (element m c d 1) ↔ a = b := by
  change element m a b 0 * element m c d 1 = element m c d 1 * element m a b 0 ↔ _
  rw [element_base_mul, element_swap_mul, add_zero, element_eq_iff]
  constructor
  · rintro ⟨h, _, _⟩
    linear_combination h
  · intro h
    subst b
    simp only [eq_self, and_true]
    constructor <;> abel

theorem swap_commutes_swap_iff (m : ℕ) (a b c d : ZMod m) :
    Commute (element m a b 1) (element m c d 1) ↔ a - b = c - d := by
  change element m a b 1 * element m c d 1 = element m c d 1 * element m a b 1 ↔ _
  rw [element_swap_mul, element_swap_mul, element_eq_iff]
  constructor
  · rintro ⟨h, _, _⟩
    linear_combination h
  · intro h
    refine ⟨?_, ?_, rfl⟩
    · linear_combination h
    · linear_combination -h

theorem outside_centralizer_is_abelian (m : ℕ) (c d : ZMod m)
    (x y : Wreath m) (hx : Commute x (element m c d 1))
    (hy : Commute y (element m c d 1)) : Commute x y := by
  obtain ⟨⟨a, b, e⟩, rfl⟩ := (coordinateEquiv m).symm.surjective x
  obtain ⟨⟨u, v, f⟩, rfl⟩ := (coordinateEquiv m).symm.surjective y
  change Commute (element m a b e) (element m c d 1) at hx
  change Commute (element m u v f) (element m c d 1) at hy
  change Commute (element m a b e) (element m u v f)
  rcases swap_exponent_cases e with rfl | rfl <;>
    rcases swap_exponent_cases f with rfl | rfl
  · change element m a b 0 * element m u v 0 = element m u v 0 * element m a b 0
    simp only [element_base_mul, add_comm]
  · exact (base_commutes_swap_iff m a b u v).mpr
      ((base_commutes_swap_iff m a b c d).mp hx)
  · exact ((base_commutes_swap_iff m u v a b).mpr
      ((base_commutes_swap_iff m u v c d).mp hy)).symm
  · exact (swap_commutes_swap_iff m a b u v).mpr
      (((swap_commutes_swap_iff m a b c d).mp hx).trans
        ((swap_commutes_swap_iff m u v c d).mp hy).symm)

theorem nonabelian_subgroup_centralizer_eq_center (m : ℕ) (hm : 1 < m)
    (P : Subgroup (Wreath m))
    (hP : ∃ x y : P, x * y ≠ y * x) :
    Subgroup.centralizer (P : Set (Wreath m)) = Subgroup.center (Wreath m) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨x, y, hxy⟩ := hP
    obtain ⟨⟨a, b, e⟩, rfl⟩ := (coordinateEquiv m).symm.surjective g
    change element m a b e ∈ Subgroup.centralizer (P : Set (Wreath m)) at hg
    change element m a b e ∈ Subgroup.center (Wreath m)
    rcases swap_exponent_cases e with rfl | rfl
    · have hout : ∃ c d : ZMod m, element m c d 1 ∈ P := by
        by_contra hnone
        have hbase (p : P) : ∃ c d : ZMod m, p.val = element m c d 0 := by
          obtain ⟨⟨c, d, f⟩, hp⟩ := (coordinateEquiv m).symm.surjective p.val
          change element m c d f = p.val at hp
          rcases swap_exponent_cases f with rfl | rfl
          · exact ⟨c, d, hp.symm⟩
          · exact False.elim (hnone ⟨c, d, hp ▸ p.property⟩)
        obtain ⟨c, d, hx⟩ := hbase x
        obtain ⟨u, v, hy⟩ := hbase y
        apply hxy
        apply Subtype.ext
        change x.val * y.val = y.val * x.val
        rw [hx, hy, element_base_mul, element_base_mul]
        simp only [add_comm]
      obtain ⟨c, d, hcd⟩ := hout
      have hcomm : Commute (element m a b 0) (element m c d 1) :=
        (Subgroup.mem_centralizer_iff.mp hg _ hcd).symm
      exact (element_mem_center_iff m hm a b 0).mpr
        ⟨rfl, (base_commutes_swap_iff m a b c d).mp hcomm⟩
    · have hx : Commute x.val (element m a b 1) :=
        Subgroup.mem_centralizer_iff.mp hg x.val x.property
      have hy : Commute y.val (element m a b 1) :=
        Subgroup.mem_centralizer_iff.mp hg y.val y.property
      have hcomm := outside_centralizer_is_abelian m a b x.val y.val hx hy
      apply False.elim
      apply hxy
      apply Subtype.ext
      exact hcomm.eq
  · exact Subgroup.center_le_centralizer _

theorem nonabelian_subgroup_center (m : ℕ) (hm : 1 < m)
    (P : Subgroup (Wreath m))
    (hP : ∃ x y : P, x * y ≠ y * x) :
    (Subgroup.center P).map P.subtype = P ⊓ Subgroup.center (Wreath m) := by
  ext g
  constructor
  · rintro ⟨p, hp, rfl⟩
    change p ∈ Subgroup.center P at hp
    refine ⟨p.property, ?_⟩
    change p.val ∈ Subgroup.center (Wreath m)
    rw [← nonabelian_subgroup_centralizer_eq_center m hm P hP]
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hp ⟨x, hx⟩)
  · rintro ⟨hgP, hgZ⟩
    change g ∈ Subgroup.center (Wreath m) at hgZ
    refine ⟨⟨g, hgP⟩, ?_, rfl⟩
    change (⟨g, hgP⟩ : P) ∈ Subgroup.center P
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp hgZ x.val

end CFSG.Wreathed
