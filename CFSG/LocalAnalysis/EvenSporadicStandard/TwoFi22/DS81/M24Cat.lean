module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.M24CatLie
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.M24CatSporadic

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open CFSG.Blueprint

theorem exists_noncomm_of_card_M24 {T : Type} [Group T] [IsSimpleGroup T]
    (hord : Nat.card T = 244823040) : ∃ a b : T, a * b ≠ b * a := by
  by_contra hcomm
  push Not at hcomm
  let _ : CommGroup T := { ‹Group T› with mul_comm := hcomm }
  have : Finite T := Nat.finite_of_card_ne_zero (by omega)
  have hp := IsSimpleGroup.prime_card (α := T)
  rw [hord] at hp
  exact absurd hp (by norm_num)

theorem isSporadic_M24_of_catalog {X : Type} [Group X] (hX : Catalog X)
    (hord : Nat.card X = 244823040) : NativeSporadic.IsSporadic X .M24 := by
  by_cases hs : NativeSporadic.SporadicRep X
  · obtain ⟨s, ⟨e⟩⟩ := hs
    have hs24 := eq_M24_of_card_carrier (s := s) ((Nat.card_congr e.toEquiv).symm.trans hord)
    subst hs24
    exact ⟨e⟩
  · exact (false_of_catalog_not_sporadic hX hs hord).elim

theorem isSporadic_M24_of_kProper_section {G : Type} [Group G]
    (hK : CFSG.Assembly.KProper Catalog G) {K L : Subgroup G} (hKtop : K ≠ ⊤) (hLK : L ≤ K)
    [(L.subgroupOf K).Normal] (hsimple : IsSimpleGroup (K ⧸ L.subgroupOf K))
    (hord : Nat.card (K ⧸ L.subgroupOf K) = 244823040) :
    NativeSporadic.IsSporadic (K ⧸ L.subgroupOf K) .M24 :=
  isSporadic_M24_of_catalog
    (hK K L hKtop hLK hsimple (@exists_noncomm_of_card_M24 _ _ hsimple hord)) hord

end CFSG.EvenSporadicStandard.TwoFi22.DS81
