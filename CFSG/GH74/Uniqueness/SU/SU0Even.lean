module

public import CFSG.GH74.Uniqueness.SU.SU0Bender
public import CFSG.GH74.GLS.Statements

public section

namespace CFSG.GH74.Uniqueness.SU.SU0

open Subgroup CFSG.GH74.Uniqueness.Bender

variable {G : Type} [Group G] [Finite G] {n i e : ℕ}

theorem not_isComponent_centralizerBar
    (h : BenderType G n i e) {x : G} (hx : orderOf x = 2)
    (L : Subgroup (CentralizerBar x)) : ¬ CFSG.IsComponent L := by
  have := isSolvable_centralizer h hx
  have : Group.IsSolvable (CentralizerBar x) := inferInstance
  exact not_isComponent_of_isSolvable L

theorem pRank_eq_of_benderType
    (h : BenderType G n i e) : CFSG.pRank 2 G = n := by
  rw [GLS.pRank_two_eq_twoRank, h.twoRank_eq]

theorem isEvenType_of_benderType
    (h : BenderType G n i e) (hn : 3 ≤ n) : GLS.IsEvenType G :=
  ⟨fun x hx L hL => absurd hL (not_isComponent_centralizerBar h hx L),
    fun x hx => pPrimeCore_centralizer_eq_bot h hx,
    by rw [pRank_eq_of_benderType h]; exact hn⟩

theorem isRestrictedEvenType_of_benderType
    (h : BenderType G n i e) (hn : 3 ≤ n) :
    GLS.IsRestrictedEvenType G := by
  refine ⟨isEvenType_of_benderType h hn, ?_, ?_, ?_⟩
  · intro x hx L hL
    exact absurd hL (not_isComponent_centralizerBar h hx L)
  · intro x L hTP
    have := isSolvable_centralizer h hTP.1
    exact absurd hTP.2.1.2 (not_isComponent_of_isSolvable _)
  · intro x y L hx _ _ hTP
    have := isSolvable_centralizer h hx
    exact absurd hTP.2.1.2 (not_isComponent_of_isSolvable _)

theorem not_isLB2Type_of_benderType
    (h : BenderType G n i e) (hn : 3 ≤ n) :
    ¬ GLS.IsLB2Type G :=
  fun hLB => hLB.2.2 (isRestrictedEvenType_of_benderType h hn)

end CFSG.GH74.Uniqueness.SU.SU0
