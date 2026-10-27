module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1KlingenIdentDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.LocalAnalysis.RankThreeTheoremC

@[expose] def KlingenIdentLie : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (Y : Type) [Group Y] [Finite Y] (Rb : Sylow p Y) (Y₀ : Subgroup Y),
    ReducedNongeneration p Y Rb Y₀ → CatalogSimpleSections Y →
    Open.pRank p (Rb : Subgroup Y) = 3 →
    ∀ K : Subgroup Y, IsComponentOf K ⊤ → (∀ L : Subgroup Y, IsComponentOf L ⊤ → L = K) →
      ¬ IsCyclic ((Rb : Subgroup Y) ⊓ K : Subgroup Y) →
      (∀ c ∈ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y), orderOf c = p →
        c ∈ (Subgroup.center K).map K.subtype) →
      HasKlingenData p Rb Y₀ → ∀ d : TauCeti.ValidLieTypeIndex, P1ThreeLieList p d →
        Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) → IsKlingenIndex p d

@[expose] def KlingenIdentAlt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (Y : Type) [Group Y] [Finite Y] (Rb : Sylow p Y) (Y₀ : Subgroup Y),
    ReducedNongeneration p Y Rb Y₀ → CatalogSimpleSections Y →
    Open.pRank p (Rb : Subgroup Y) = 3 →
    ∀ K : Subgroup Y, IsComponentOf K ⊤ → (∀ L : Subgroup Y, IsComponentOf L ⊤ → L = K) →
      ¬ IsCyclic ((Rb : Subgroup Y) ⊓ K : Subgroup Y) →
      (∀ c ∈ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y), orderOf c = p →
        c ∈ (Subgroup.center K).map K.subtype) →
      HasKlingenData p Rb Y₀ →
        ¬ Nonempty (K ⧸ Subgroup.center K ≃* alternatingGroup (Fin (3 * p)))

@[expose] def KlingenIdentSpor : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (Y : Type) [Group Y] [Finite Y] (Rb : Sylow p Y) (Y₀ : Subgroup Y),
    ReducedNongeneration p Y Rb Y₀ → CatalogSimpleSections Y →
    Open.pRank p (Rb : Subgroup Y) = 3 →
    ∀ K : Subgroup Y, IsComponentOf K ⊤ → (∀ L : Subgroup Y, IsComponentOf L ⊤ → L = K) →
      ¬ IsCyclic ((Rb : Subgroup Y) ⊓ K : Subgroup Y) →
      (∀ c ∈ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y), orderOf c = p →
        c ∈ (Subgroup.center K).map K.subtype) →
      HasKlingenData p Rb Y₀ → ∀ s : TauCeti.SporadicName, P1ThreeSporList p s →
        ¬ Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic s).Group)

theorem kFactKlingenIdent_of_rows (hP1L : KFactP1ThreeLie) (hP1A : KFactP1ThreeAlt)
    (hP1S : KFactP1ThreeSpor) (hL : KlingenIdentLie) (hA : KlingenIdentAlt)
    (hS : KlingenIdentSpor) : KFactKlingenIdent := by
  intro p _ Y _ _ Rb Y₀ hred hcat hrank K hK huniq hnc hcent hkl
  have hnab :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hK.2.2
  obtain ⟨i, ⟨e⟩⟩ := hcat.isCatalogGroup_center_quotient hK
  cases i with
  | cyclic q hq => exact (not_nonempty_mulEquiv_zmod hnab ⟨e⟩).elim
  | alternating m hm =>
    obtain rfl := hP1A p Y Rb Y₀ hred hcat K hK huniq hnc hcent m hm ⟨e⟩
    exact (hA p Y Rb Y₀ hred hcat hrank K hK huniq hnc hcent hkl ⟨e⟩).elim
  | lie d =>
    exact ⟨d, hL p Y Rb Y₀ hred hcat hrank K hK huniq hnc hcent hkl d
      (hP1L p Y Rb Y₀ hred hcat K hK huniq hnc hcent d ⟨e⟩) ⟨e⟩, ⟨e⟩⟩
  | sporadic s =>
    exact (hS p Y Rb Y₀ hred hcat hrank K hK huniq hnc hcent hkl s
      (hP1S p Y Rb Y₀ hred hcat K hK huniq hnc hcent s ⟨e⟩) ⟨e⟩).elim

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
