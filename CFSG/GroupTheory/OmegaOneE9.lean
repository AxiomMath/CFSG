module

public import CFSG.GroupTheory.ElemAbelianRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.GroupTheory

theorem card_omega₁_eq_pow_pRank_of_isMulCommutative {X : Type*} [Group X] [Finite X]
    [IsMulCommutative X] {p : ℕ} [hp : Fact p.Prime] :
    Nat.card (omega₁ X (p := p)) = p ^ CFSG.pRank p X := by
  let Ω : Subgroup X := omega₁ X (p := p)
  have hΩel : CFSG.Open.IsElemAbelian p Ω :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p Ω).1
      (IsElementaryAbelian.omega₁_of_isMulCommutative X)
  have hΩcard : Nat.card Ω = p ^ CFSG.Open.pRank p Ω :=
    CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian hp.out hΩel
  have htop : CFSG.Open.pRank p (⊤ : Subgroup X) = CFSG.pRank p X :=
    (CFSG.SectionRank.pRank_eq_open_pRank_top p X).symm
  have hle : CFSG.Open.pRank p Ω ≤ CFSG.Open.pRank p (⊤ : Subgroup X) :=
    CFSG.SectionRank.pRank_mono hp.out.one_lt le_top
  have hge : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ CFSG.Open.pRank p Ω := by
    refine CFSG.SectionRank.pRank_le hp.out.one_lt (H := ⊤) ?_
    intro E _ hE
    haveI : IsElementaryAbelian p E :=
      (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p E).2 hE
    have hEΩ : E ≤ Ω := CFSG.elementaryAbelian_le_omega₁
    have hEcard : Nat.card E = p ^ CFSG.Open.pRank p E :=
      CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian hp.out hE
    have hrank : CFSG.Open.pRank p E ≤ CFSG.Open.pRank p Ω :=
      CFSG.SectionRank.le_pRank hp.out.one_lt hEΩ hE (by rw [hEcard])
    calc Nat.card E = p ^ CFSG.Open.pRank p E := hEcard
      _ ≤ p ^ CFSG.Open.pRank p Ω := Nat.pow_le_pow_right hp.out.pos hrank
  rw [hΩcard]
  have hpp : CFSG.Open.pRank p Ω = CFSG.pRank p X := by
    rw [← htop]
    exact le_antisymm hle hge
  rw [hpp]

end CFSG.GroupTheory

end
