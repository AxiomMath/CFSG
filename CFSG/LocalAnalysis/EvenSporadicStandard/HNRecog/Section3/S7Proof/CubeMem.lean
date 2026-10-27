module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.S7Proof.CubeDDD

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

theorem s7_DD_mem {a z x t t' : G} (H : S7Hyps a z) (hx : x ∈ orb3A a a)
    (ht : t ∈ orb2A a a ∩ orb2A a x) (ht' : t' ∈ orb2A a a ∩ orb2A a x) (hne : t ≠ t')
    (hcomm : t * t' = t' * t) : t * t' ∈ orb2B a z a ∩ orb2B a z x := by
  have hxa : IsConj a x := hx.1
  have hord : orderOf (a * x) = 3 := hx.2.1
  have h1 : IsConj a (t * t') ∧ IsConj z (a * (t * t')) :=
    s7_DD H hxa hord ht ht' hne hcomm
  have h2 : IsConj x (t * t') ∧ IsConj z (x * (t * t')) :=
    s7_DD (H.of_isConj hxa (IsConj.refl z)) (IsConj.symm hxa)
      (by rw [s7_orderOf_swap]; exact hord) (s7_swap_D hxa ht) (s7_swap_D hxa ht') hne hcomm
  exact ⟨h1, ⟨h1.1, h2.2⟩⟩

theorem s7_DDD_mem {a z x t t' t'' : G} (H : S7Hyps a z) (hx : x ∈ orb3A a a)
    (ht : t ∈ orb2A a a ∩ orb2A a x) (ht' : t' ∈ orb2A a a ∩ orb2A a x)
    (ht'' : t'' ∈ orb2A a a ∩ orb2A a x) (h12 : t ≠ t') (h31 : t'' ≠ t) (h32 : t'' ≠ t')
    (h3 : t'' ≠ t * t') (c12 : t * t' = t' * t) (c13 : t * t'' = t'' * t)
    (c23 : t' * t'' = t'' * t') : t * t' * t'' ∈ orb2BB a z a ∩ orb2BB a z x := by
  have hxa : IsConj a x := hx.1
  have hord : orderOf (a * x) = 3 := hx.2.1
  have h1 : IsConj z (t * t' * t'') ∧ IsConj z (a * (t * t' * t'')) :=
    s7_DDD H hxa hord ht ht' ht'' h12 h31 h32 h3 c12 c13 c23
  have h2 : IsConj z (t * t' * t'') ∧ IsConj z (x * (t * t' * t'')) :=
    s7_DDD (H.of_isConj hxa (IsConj.refl z)) (IsConj.symm hxa)
      (by rw [s7_orderOf_swap]; exact hord) (s7_swap_D hxa ht) (s7_swap_D hxa ht')
      (s7_swap_D hxa ht'') h12 h31 h32 h3 c12 c13 c23
  exact ⟨h1, ⟨h1.1, h2.2⟩⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
