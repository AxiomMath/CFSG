module

public import CFSG.LieType.Universal.SpinOmega.Center

public section

namespace CFSG.HardMathSupport.Lang.Proving

open CFSG.Assembly.LowTwoRank

theorem nonempty_statedProj_statedOmega_quadPlus_equiv {F : Type} [Field F] {n : ℕ} (hn : 3 ≤ n)
    {G : Type*} [Group G] (hG : Subgroup.center G = ⊥)
    (θ : StatedOmega (StatedQuadPlus n F) →* G)
    (hθ : Function.Surjective θ) (hne : ∃ x, θ x ≠ 1) :
    Nonempty (StatedProj (StatedOmega (StatedQuadPlus n F)) ≃* G) := by
  have hK : IsQuasisimple (StatedOmega (StatedQuadPlus n F)) :=
    CFSG.LieType.Universal.Spin.isQuasisimple_statedOmega_quadPlus hn
  have hker : θ.ker ≤ Subgroup.center (StatedOmega (StatedQuadPlus n F)) :=
    CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hK hne
  have hc : Subgroup.center (StatedOmega (StatedQuadPlus n F)) =
      (StatedScalars _ F).subgroupOf (StatedOmega (StatedQuadPlus n F)) :=
    CFSG.LieType.Universal.Spin.center_statedOmega_quadPlus hn
  let e := CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple hK hθ hker
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hc).symm.trans
    (e.trans ((QuotientGroup.quotientMulEquivOfEq hG).trans QuotientGroup.quotientBot))⟩

end CFSG.HardMathSupport.Lang.Proving

end
