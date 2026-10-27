module

public import CFSG.Sporadic.Fi22.LH.Defs
public import CFSG.Sporadic.Fi22.Graph
public import Certificates.Certificate1005
public import Certificates.Certificate1010
public import CFSG.Fischer.Polar.Lines
public import CFSG.Fischer.Uniq.HyperovalFacts
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.Fischer

open CFSG.Blueprint.Fischer CFSG.Sporadic.Fi22

structure Fi22Facts : Prop where
  exists_mem_lhOrbit : ∀ T : Set D, IsLocallyHyperoval D (Subtype.val '' T) → T.Nonempty →
    ∃ i, T ∈ lhOrbit i
  ncard_of_mem_lhOrbit : ∀ i, ∀ T ∈ lhOrbit i, T.ncard = 351
  ncard_lhOrbit : ∀ i, (lhOrbit i).ncard = 14080
  lhOrbit_disjoint : ∀ i j, i ≠ j → Disjoint (lhOrbit i) (lhOrbit j)
  lhOrbit_subset_of_invariant : ∀ 𝒮 : Set (Set D),
    (∀ T ∈ 𝒮, ∀ p, (pairModel pair_D).tv p '' T ∈ 𝒮) →
    ∀ i, ∀ T ∈ 𝒮, T ∈ lhOrbit i → lhOrbit i ⊆ 𝒮
  lhU_commute : ∀ x y : D, ((lhU x : D) : J) * lhU y = lhU y * lhU x ↔ (x : J) * y = y * x
  lhU_tv : ∀ x y : D, lhU ((pairModel pair_D).tv x y) = (pairModel pair_D).tv (lhU x) (lhU y)
  image_lhU_lhOrbit : ∀ i, (fun T => ⇑lhU '' T) '' lhOrbit i = lhOrbit (i + 1)
  injOn_tv_image : ∀ T ∈ lhOrbit 0, Set.InjOn (fun f => (pairModel pair_D).tv f '' T) Tᶜ
  tv_image_ne : ∀ T ∈ lhOrbit 0, ∀ f ∉ T, (pairModel pair_D).tv f '' T ≠ T
  exists_not_commute : ∀ i, ∀ T ∈ lhOrbit i, ∀ f ∉ T, ∃ x ∈ T, ¬ ((f : J) * x = x * f)
  xi23_D2 : ∀ v, v ≠ xi23Root → ¬ ((pairModel pair_D).xi (lhOrbit 0)).Adj xi23Root v →
    ∃ x, ((pairModel pair_D).xi (lhOrbit 0)).Adj xi23Root x ∧
      ((pairModel pair_D).xi (lhOrbit 0)).Adj x v
  xi23_MU : ∀ v, v ≠ xi23Root → ¬ ((pairModel pair_D).xi (lhOrbit 0)).Adj xi23Root v →
    (((pairModel pair_D).xi (lhOrbit 0)).induce {x | ((pairModel pair_D).xi (lhOrbit 0)).Adj
      xi23Root x ∧ ((pairModel pair_D).xi (lhOrbit 0)).Adj x v}).Connected
  xi23_ED : ∀ v w, v ≠ xi23Root → ¬ ((pairModel pair_D).xi (lhOrbit 0)).Adj xi23Root v →
    w ≠ xi23Root → ¬ ((pairModel pair_D).xi (lhOrbit 0)).Adj xi23Root w →
    ((pairModel pair_D).xi (lhOrbit 0)).Adj v w →
    ∃ x, ((pairModel pair_D).xi (lhOrbit 0)).Adj xi23Root x ∧
      ((pairModel pair_D).xi (lhOrbit 0)).Adj x v ∧ ((pairModel pair_D).xi (lhOrbit 0)).Adj x w

end CFSG.Fischer
