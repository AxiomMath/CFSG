module

public import CFSG.Quasithin.EmptyFaithful.S152He9N
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152He9J
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152He9U

public section

namespace CFSG.Quasithin.He9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

@[expose] def Input15204Dichotomy_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M H K₁ K₂ : Subgroup G) (π : ↥H →* W5),
    Ctx15204 T Mc M H K₁ K₂ π → pCoreOf 2 (g0Of T Mc M K₁) ≠ ⊥ →
    IsSylowTwoOf (sOf T K₁) (g0Of T Mc M K₁) →
    ¬ pCoreOf 2 (yOf152 T Mc M) ≤ pCoreOf 2 (g0Of T Mc M K₁) → CharTwo (g0Of T Mc M K₁)

@[expose] def Input15204BranchB_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M H K₁ K₂ : Subgroup G) (π : ↥H →* W5)
    (c : Ctx15204 T Mc M H K₁ K₂ π) (Lc : Subgroup G), Tail15204 c Lc →
    yOf152 T Mc M ≤ Lc → ¬ IsSylowTwoOf (rOf T Mc M K₁) (rOf T Mc M K₁ ⊔ Lc) → False

theorem stageLemma15204_of_named_F4 (h1515 : StageLemma1515CE) (h1519 : StageLemma1519)
    (h15112 : StageLemma15112) (h15201 : StageLemma15201_F4) (h15203 : StageLemma15203_F4)
    (h15206 : StageLemma15206_F4) (h15207 : StageLemma15207_F4)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hF : Input15204F112) (hD : Input15204Dichotomy_F4) (hA : Input15204BranchA)
    (hB : Input15204BranchB_F4) : StageLemma15204_F4 := by
  intro G _ _ T Mc M hs H hH φ
  have c1519 := h1519 G T Mc M hs.qtfe hs.mf hs.ce
  obtain ⟨π, K₁, K₂, c⟩ := exists_ctx hs hH c1519 (h1515 G T Mc M hs.qtfe hs.mf hs.ce)
    (h15201 G T Mc M hs) (h15203 G T Mc M hs) φ
  by_cases ho2 : pCoreOf 2 (g0Of T Mc M K₁) = ⊥
  · exact c.false_of_o2_eq_bot hF ho2
  · have hJ := c.thompsonJ_le_S_F4 h15112 h15206 h15207
    have hU := c.isUniqueM_YT_F4 h15206 h15207
    obtain ⟨-, hS⟩ := c.sylow_G₀ hJ hU ho2
    have hChar : CharTwo (g0Of T Mc M K₁) := by
      by_cases hP : pCoreOf 2 (yOf152 T Mc M) ≤ pCoreOf 2 (g0Of T Mc M K₁)
      · exact c.charTwo_G₀ hJ hU ho2 hP
      · exact hD G T Mc M H K₁ K₂ π c ho2 hS hP
    obtain ⟨Lc, hLc, hKL, hn⟩ := c.exists_Lc h37 h38 h39 ho2 hS
    have hLcG : Lc ≤ g0Of T Mc M K₁ := le_of_mem_cComp hLc
    have tail : Tail15204 c Lc :=
      ⟨ho2, hS, hChar, c.hypC23 hU ho2 hS, c.charTwo_M₁, hLc, hn, hKL, c.not_Lc_le_M hKL,
        c.g0_eq hKL hLcG⟩
    by_cases hsyl : IsSylowTwoOf (rOf T Mc M K₁) (rOf T Mc M K₁ ⊔ Lc)
    · exact c.false_of_commutator_le hKL hLcG hS (hA G T Mc M H K₁ K₂ π c Lc tail hsyl)
    · exact hB G T Mc M H K₁ K₂ π c Lc tail (c.Y_le_of_not_sylow hLcG hn hS hsyl) hsyl

end CFSG.Quasithin.He9
