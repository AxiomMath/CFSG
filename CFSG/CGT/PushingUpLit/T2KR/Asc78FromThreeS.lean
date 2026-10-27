module

public import CFSG.CGT.PushingUpLit.T2KR.Asc78Gen
public import CFSG.CGT.PushingUpLit.A78.ThreeSNonSylow
public import CFSG.CGT.PushingUpLit.A78One.CfgAssembly
public import CFSG.CGT.PushingUpLit.A78One.Ending
public import CFSG.CGT.PushingUpLit.A78One.PhiJ

public section

namespace CFSG.CGT.PushingUpLit.T2K

open CFSG CFSG.CGT.PushingUpLit.A78 CFSG.CGT.PushingUpLit.A78One

theorem sectionalTwoRankLE_of_endData (h : Aschbacher78ThreeSNonSylow) {G : Type} [Group G]
    [Finite G] {L M : Subgroup G} {n : ℕ} {T T' : Subgroup G} {x : G}
    (c : CexCtx L M n T T' x) (e : EndData L M n T T' x) :
    CFSG.GH74.SectionalTwoRankLE G 4 := by
  obtain ⟨x', h1, h2, h3, h4⟩ := exists_x' c e
  exact h G L (cj x'⁻¹ L) T n (a78Cfg_of_endData c e h1 h2 h3 h4) (not_isSylow_top c e)

theorem aschbacher78OneGen_of_threeSNonSylow (h : Aschbacher78ThreeSNonSylow) :
    Aschbacher78OneGen := by
  intro G _ _ L M n hyp nM T T' hT hle hge
  by_cases hN : Subgroup.normalizer (T' : Set G) ≤ M
  · exact Or.inl hN
  · have hx : ∃ x, x ∈ Subgroup.normalizer (T' : Set G) ∧ x ∉ M := by
      by_contra hcon
      exact hN fun x hx => by_contra fun hxM => hcon ⟨x, hx, hxM⟩
    obtain ⟨x, hx, hxM⟩ := hx
    have c : CexCtx L M n T T' x := ⟨hyp, nM, hT, hle, hge, hx, hxM⟩
    exact Or.inr (sectionalTwoRankLE_of_endData h c c.endData)

end CFSG.CGT.PushingUpLit.T2K
