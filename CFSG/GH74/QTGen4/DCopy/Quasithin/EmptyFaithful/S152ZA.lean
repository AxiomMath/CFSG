module

public import CFSG.Quasithin.EmptyFaithful.S152ZA
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152He9N

public section

namespace CFSG.Quasithin.He9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

@[expose] def Input15204CharTwoLc_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M H K₁ K₂ : Subgroup G) (π : ↥H →* W5),
    Ctx15204 T Mc M H K₁ K₂ π → pCoreOf 2 (g0Of T Mc M K₁) ≠ ⊥ →
    IsSylowTwoOf (sOf T K₁) (g0Of T Mc M K₁) →
    ¬ pCoreOf 2 (yOf152 T Mc M) ≤ pCoreOf 2 (g0Of T Mc M K₁) →
    ∀ Lc : Subgroup G, Lc ∈ cComp (g0Of T Mc M K₁) → K₁ ≤ Lc →
      (Lc.subgroupOf (g0Of T Mc M K₁)).Normal → CharTwo Lc

theorem input15204Dichotomy_of_charTwoLc_F4 (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hL : Input15204CharTwoLc_F4) : Input15204Dichotomy_F4 := by
  intro G _ _ T Mc M H K₁ K₂ π c ho2 hS hP
  obtain ⟨Lc, hLc, hKL, hn⟩ := c.exists_Lc h37 h38 h39 ho2 hS
  exact c.charTwo_G₀_of_charTwo_Lc hn hKL (le_of_mem_cComp hLc) hS
    (hL G T Mc M H K₁ K₂ π c ho2 hS hP Lc hLc hKL hn)

end CFSG.Quasithin.He9
