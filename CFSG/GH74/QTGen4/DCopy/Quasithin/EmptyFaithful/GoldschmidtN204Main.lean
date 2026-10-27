module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtN204Main
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152ZA

public section

namespace CFSG.Quasithin.He9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.N204
open scoped commutatorElement Pointwise

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem input15204CharTwoLc_of_F112Q_F4 (h15112 : StageLemma15112) (h15206 : StageLemma15206_F4)
    (h15207 : StageLemma15207_F4) (hQ : Input15204F112Q) : Input15204CharTwoLc_F4 := by
  intro G _ _ T Mc M H K₁ K₂ π c ho2 hS hP Lc hLc hKL hn
  by_contra hnot
  have hJ := c.thompsonJ_le_S_F4 h15112 h15206 h15207
  have hU := c.isUniqueM_YT_F4 h15206 h15207
  have hodd := c.oddCoreIn_G₀_eq_bot ho2
  have hLcG : Lc ≤ g0Of T Mc M K₁ := le_of_mem_cComp hLc
  have hq : CFSG.IsQuasisimple ↥Lc := isQuasisimple_of_not_charTwo_of_oddCore hLc hodd hnot
  have hXL : g0Of T Mc M K₁ ≤ Subgroup.normalizer (Lc : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLcG).mp hn
  have hcomm : ⁅Lc, pCoreOf 2 (g0Of T Mc M K₁)⁆ = ⊥ :=
    commutator_eq_bot_of_quasisimple hq hLcG hXL (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
      (le_normalizer_pCoreOf 2 _) (pCoreOf_isPGroup 2 _)
  have hcenL : ∀ k ∈ Lc, ∀ q ∈ pCoreOf 2 (g0Of T Mc M K₁), k * q = q * k := fun k hk q hq =>
    ((Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hk)) q hq).symm
  have hG₀ : ¬ CharTwo (g0Of T Mc M K₁) := fun h =>
    hnot (Ctx15204.charTwo_Lc_of_charTwo_G₀ hn hLcG h)
  exact hQ G T Mc M H K₁ K₂ π c ho2 hS
    (c.charTwoMod_G₁ hJ hU ho2 hG₀ fun k hk => hcenL k (hKL hk))
    (c.charTwoMod_G₂ fun k hk => hcenL k (hKL hk))

theorem input15204Dichotomy_of_F112Q_F4 (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h15112 : StageLemma15112) (h15206 : StageLemma15206_F4) (h15207 : StageLemma15207_F4)
    (hQ : Input15204F112Q) : Input15204Dichotomy_F4 :=
  input15204Dichotomy_of_charTwoLc_F4 h37 h38 h39
    (input15204CharTwoLc_of_F112Q_F4 h15112 h15206 h15207 hQ)

end CFSG.Quasithin.He9
