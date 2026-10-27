module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsPair
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.ChevThree
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.GNQuotient
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.QuasithinUnique
  CFSG.AGLEmbeddingD2.GN KFactsPair

@[expose] def KFactChevGenQOn (R : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L S₀ : Subgroup Y), CFSG.Open.IsQuasisimple ↥L →
    IsSylowTwoOf S₀ L → ∀ d : TauCeti.ValidLieTypeIndex, IsRankTwoPlus d.1 → R d.1 →
      Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∃ Ps : Set (Subgroup Y), (∀ P ∈ Ps, IsMinOverBorel L S₀ P) ∧
        L = (⨆ P ∈ Ps, pElementSubgroup 2 P) ∧
        ∀ P ∈ Ps, ∀ p : ℕ, p.Prime → p ∣ indexQ d.1 ^ 2 - 1 →
          ∃ x ∈ pElementSubgroup 2 P, orderOf x = p

@[expose] def KFactChevGenQ : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L S₀ : Subgroup Y), CFSG.Open.IsQuasisimple ↥L →
    IsSylowTwoOf S₀ L → ∀ d : TauCeti.ValidLieTypeIndex, IsRankTwoPlus d.1 →
      Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∃ Ps : Set (Subgroup Y), (∀ P ∈ Ps, IsMinOverBorel L S₀ P) ∧
        L = (⨆ P ∈ Ps, pElementSubgroup 2 P) ∧
        ∀ P ∈ Ps, ∀ p : ℕ, p.Prime → p ∣ indexQ d.1 ^ 2 - 1 →
          ∃ x ∈ pElementSubgroup 2 P, orderOf x = p

namespace K517ChevGenQ

theorem kFactChevGenQ_of_cases {R₁ R₂ : TauCeti.LieTypeIndex → Prop}
    (h₁ : KFactChevGenQOn R₁) (h₂ : KFactChevGenQOn R₂)
    (hR : ∀ d : TauCeti.LieTypeIndex, IsRankTwoPlus d → R₁ d ∨ R₂ d) : KFactChevGenQ := by
  intro Y _ _ L S₀ hL hS d hd e
  rcases hR d.1 hd with h | h
  · exact h₁ Y L S₀ hL hS d hd h e
  · exact h₂ Y L S₀ hL hS d hd h e

theorem classical_of_rankTwoPlus {d : TauCeti.LieTypeIndex} (h : IsRankTwoPlus d) :
    IsClassicalOrG2Index d := by
  cases d <;> first | exact h.1 | exact h | exact h.elim

end K517ChevGenQ

theorem k517_4a_of_genQ (hG : KFactChevGenQ) : K517_4a := by
  intro X _ _ T T₁ T₂ hX hgood Ls hY d hd e p hp hpQ
  have hS : IsSylowTwoOf (gnImg T T ⊓ Ls) Ls :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.GNQuotient.isSylowTwoOf_gnImg_inf hX.sylow
      hY.1.2.1
  have hchev : IsChevTwo (↥Ls ⧸ Subgroup.center ↥Ls) :=
    Or.inl ⟨d, isChevIndexTwo_of_classical (K517ChevGenQ.classical_of_rankTwoPlus hd), e⟩
  have hcov : ParabolicCover T T₁ T₂ Ls := fun P hP => hgood.parabolic Ls hY.1 hchev P hP
  obtain ⟨Ps, hPs, hgen, hK⟩ := hG _ Ls (gnImg T T ⊓ Ls) hY.1.2.2 hS d hd e
  obtain ⟨⟨P₁, hP₁, h₁⟩, ⟨P₂, hP₂, h₂⟩⟩ := exists_parabolic_le_gnA hY hcov hPs hgen
  have key : ∀ (A P : Subgroup (X ⧸ gnC T)), P ∈ Ps → pElementSubgroup 2 P ≤ A →
      p ∣ Nat.card A := by
    intro A P hP hPA
    obtain ⟨x, hx, ho⟩ := hK P hP p hp hpQ
    rw [← ho]
    exact Subgroup.orderOf_dvd_natCard A (hPA hx)
  exact ⟨key _ P₁ hP₁ h₁, key _ P₂ hP₂ h₂⟩

end CFSG.LocalAnalysis.RankThreeUC.S15
