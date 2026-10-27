module

public import CFSG.Fischer.Polar.Defs
public import CFSG.Fischer.Uniq.Xi

public section

namespace CFSG.Fischer

structure PolarFacts : Prop where
  perp_comm : ∀ p q, perp p q → perp q p
  perp_self : ∀ p, perp p p
  line_perp : ∀ L, IsLine L → ∀ x ∈ L, ∀ y ∈ L, perp x y
  isLine_lineThru : ∀ x y, x ≠ y → perp x y → IsLine (lineThru x y)
  left_mem_lineThru : ∀ x y, x ∈ lineThru x y
  right_mem_lineThru : ∀ x y, y ∈ lineThru x y
  eq_lineThru : ∀ L, IsLine L → ∀ x ∈ L, ∀ y ∈ L, x ≠ y → L = lineThru x y
  ncard_lines_through : ∀ p, {L | IsLine L ∧ p ∈ L}.ncard = 45
  twins_of_line : ∀ p x y, perp p x → perp p y → x ≠ p → y ≠ p → x ≠ y →
    (∃ L, IsLine L ∧ p ∈ L ∧ x ∈ L ∧ y ∈ L) → ∀ w, perp p w → w ≠ p → (perp w x ↔ perp w y)
  ncard_perp_perp : ∀ p q, ¬ perp p q → {w | perp w p ∧ perp w q}.ncard = 45
  twinFree : ∀ p q, ¬ perp p q → ∀ x y, (perp x p ∧ perp x q) → (perp y p ∧ perp y q) →
    x ≠ y → perp x y → ∃ w, (perp w p ∧ perp w q) ∧ ¬ (perp w x ↔ perp w y)
  eq_of_perp_perp : ∀ p q q', ¬ perp p q → ¬ perp p q' →
    (∀ w, perp w p ∧ perp w q ↔ perp w p ∧ perp w q') → q' = q ∨ q' = tvP p q
  ncard_perp_ne : ∀ p, {q | perp p q ∧ q ≠ p}.ncard = 180
  exists_mem_hypOrbit : ∀ O, IsClosedHyperoval O → O.Nonempty → ∃ i, O ∈ hypOrbit i
  ncard_of_mem_hypOrbit : ∀ i, ∀ O ∈ hypOrbit i, O.ncard = 126
  tvP_image_mem_hypOrbit : ∀ i, ∀ O ∈ hypOrbit i, ∀ p, tvP p '' O ∈ hypOrbit i
  hypOrbit_subset_of_invariant : ∀ 𝒮 : Set (Set (Fin 693)), (∀ O ∈ 𝒮, ∀ p, tvP p '' O ∈ 𝒮) →
    ∀ i, ∀ O ∈ 𝒮, O ∈ hypOrbit i → hypOrbit i ⊆ 𝒮
  ncard_hypOrbit : ∀ i, (hypOrbit i).ncard = 1408
  hypOrbit_disjoint : ∀ i j, i ≠ j → Disjoint (hypOrbit i) (hypOrbit j)
  perp_delta : ∀ p q, perp (delta p) (delta q) ↔ perp p q
  delta_tvP : ∀ p q, delta (tvP p q) = tvP (delta p) (delta q)
  image_delta_hypOrbit : ∀ i, (fun O => ⇑delta '' O) '' hypOrbit i = hypOrbit (i + 1)
  injOn_tvP_image : ∀ O ∈ hypOrbit 0, Set.InjOn (fun f => tvP f '' O) Oᶜ
  tvP_image_ne : ∀ O ∈ hypOrbit 0, ∀ f ∉ O, tvP f '' O ≠ O
  exists_not_perp : ∀ O, IsClosedHyperoval O → O.Nonempty → ∀ f ∉ O, ∃ x ∈ O, ¬ perp f x
  xi_D2 : ∀ v, v ≠ xiRoot → ¬ (xiGraph (hypOrbit 0)).Adj xiRoot v →
    ∃ x, (xiGraph (hypOrbit 0)).Adj xiRoot x ∧ (xiGraph (hypOrbit 0)).Adj x v
  xi_MU : ∀ v, v ≠ xiRoot → ¬ (xiGraph (hypOrbit 0)).Adj xiRoot v →
    ((xiGraph (hypOrbit 0)).induce
      {x | (xiGraph (hypOrbit 0)).Adj xiRoot x ∧ (xiGraph (hypOrbit 0)).Adj x v}).Connected
  xi_ED : ∀ v w, v ≠ xiRoot → ¬ (xiGraph (hypOrbit 0)).Adj xiRoot v → w ≠ xiRoot →
    ¬ (xiGraph (hypOrbit 0)).Adj xiRoot w → (xiGraph (hypOrbit 0)).Adj v w →
    ∃ x, (xiGraph (hypOrbit 0)).Adj xiRoot x ∧ (xiGraph (hypOrbit 0)).Adj x v ∧
      (xiGraph (hypOrbit 0)).Adj x w

theorem perp_iff_polarModel {p q : Fin 693} : perp p q ↔ polarModel.perp p q := Iff.rfl

end CFSG.Fischer
