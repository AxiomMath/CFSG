module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S151XD
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.T1515cE
public import CFSG.Quasithin.EmptyFaithful.S151ZE

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

@[expose] def Input15122ThreeD'_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15122 T Mc M Z₁ Z₂ V₁ V₂ L → IsComponentOf L (g1_1516 Z₁) → Case15120ThreeD T Mc Z₁ L →
    Lemma15118Extra T Mc M Z₁ → Case15122Five T M Mc Z₁ L ∨ Case15122Six T Mc Z₁ L

@[expose] def Input15122ThreeDHSRu_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15122 T Mc M Z₁ Z₂ V₁ V₂ L → IsComponentOf L (g1_1516 Z₁) → Case15120ThreeD T Mc Z₁ L →
    Lemma15118Extra T Mc M Z₁ →
    ¬ (IsSporadic .HS (↥L ⧸ CFSG.pCore 2 ↥L) ∨ IsSporadic .Ru (↥L ⧸ CFSG.pCore 2 ↥L))

theorem lemma15122InputU_of_corrected_inputs_F4 (nDich : Input15122Dichotomy) (nNoB : Input15122NoBorel)
    (nA7 : Input15122A7) (nR2 : Input15122Rank2Block) (nL45 : Input15122L45Block')
    (nC : Input15122ThreeC) (nD : Input15122ThreeD'_F4) (nE : Input15122ThreeE_F4) : Lemma15122InputU_F4 := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 h19 hL h20 h21 hx
  have hc : Ctx15122 T Mc M Z₁ Z₂ V₁ V₂ L := ⟨hC, h17, h18, h19, hL, h20, h21⟩
  rcases nDich G T Mc M Z₁ Z₂ V₁ V₂ L hc with hchar | hcomp
  · obtain ⟨-, hcases⟩ := h20.two hchar
    rcases hcases with h | h | h
    · exact (not_caseTwoA_15122 hL h21 hchar h).elim
    · rcases h.2.1 hL.comp with h7 | h3 | h6 | hg
      · exact Or.inl (nA7 G T Mc M Z₁ Z₂ V₁ V₂ L hc h h7)
      · exact Or.inr (Or.inl (nR2 G T Mc M Z₁ Z₂ V₁ V₂ L hc h (Or.inl h3)))
      · exact Or.inr (Or.inl (nR2 G T Mc M Z₁ Z₂ V₁ V₂ L hc h (Or.inr (Or.inl h6))))
      · exact Or.inr (Or.inl (nR2 G T Mc M Z₁ Z₂ V₁ V₂ L hc h (Or.inr (Or.inr hg))))
    · exact Or.inr (Or.inr (Or.inl (nL45 G T Mc M Z₁ Z₂ V₁ V₂ L hc hchar h)))
  · obtain ⟨-, hcases⟩ := h20.three hcomp
    rcases hcases with h | h | h | h | h
    · exact ((nNoB G T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp).1 h).elim
    · exact ((nNoB G T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp).2 h).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inl (nC G T Mc M Z₁ Z₂ V₁ V₂ L hc h))))
    · rcases nD G T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp h hx with h5 | h6
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h6)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (nE G T Mc M Z₁ Z₂ V₁ V₂ L hc h))))))

end CFSG.Quasithin
