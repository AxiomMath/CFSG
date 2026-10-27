module

public import CFSG.GroupTheory.PRankTwoOfPGroup

public section

namespace CFSG

theorem one_lt_pRank_of_le_of_exp_p {X : Type} [Group X] [Finite X] {p : Nat} (hp : p.Prime)
    {D H : Subgroup X} (hDp : IsPGroup p D) (hDexp : ∀ x ∈ D, x ^ p = 1)
    (hDcard : p < Nat.card D) (hDH : D ≤ H) :
    1 < CFSG.Open.pRank p H := by
  have htop : 1 < CFSG.Open.pRank p (⊤ : Subgroup ↥D) :=
    one_lt_pRank_of_isPGroup (D := ↥D) hp hDp hDcard fun x => Subtype.ext (hDexp x x.2)
  have hle : CFSG.Open.pRank p (⊤ : Subgroup ↥D) ≤ CFSG.Open.pRank p H := by
    have hmap := CFSG.SectionRank.pRank_le_map (p := p) hp.one_lt D.subtype
      D.subtype_injective (⊤ : Subgroup ↥D)
    have hD : (⊤ : Subgroup ↥D).map D.subtype = D := by
      rw [Subgroup.map_top, Subgroup.range_subtype]
    rw [hD] at hmap
    exact hmap.trans (CFSG.SectionRank.pRank_mono hp.one_lt hDH)
  exact htop.trans_le hle

end CFSG
