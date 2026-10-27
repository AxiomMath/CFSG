module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatLat
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporCert
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporHash
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2RootGroups
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
public import Certificates.Certificate43

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm

theorem localPair_of_ctx {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)] {Lab : Type}
    [DecidableEq Lab] [Hashable Lab] [Inhabited Lab] (C : LatCtx Γ n Lab)
    (hS : IsSylowTwoOf C.S ⊤) (j₁ j₂ : ℕ) (h₁ : j₁ < C.J) (h₂ : j₂ < C.J)
    (huniq₁ : ∀ j < C.J, Nat.card (C.Y j) = Nat.card (C.Y j₁) → j = j₁)
    (huniq₂ : ∀ j < C.J, Nat.card (C.Y j) = Nat.card (C.Y j₂) → j = j₂)
    (hne₁ : Nat.card (C.Y j₁) ≠ Nat.card Γ) (hne₂ : Nat.card (C.Y j₂) ≠ Nat.card Γ)
    (hjoin : ∀ j < C.J, ¬ (C.Y j₁ ≤ C.Y j ∧ C.Y j₂ ≤ C.Y j))
    (g₁ : GoodLocal (C.Y j₁)) (g₂ : GoodLocal (C.Y j₂)) : LocalPair Γ := by
  obtain ⟨hS2, hSi⟩ := K1.isSylowTwoOf_top_iff.1 hS
  have hinv : ∀ (j : ℕ), j < C.J → (∀ j' < C.J, Nat.card (C.Y j') = Nat.card (C.Y j) → j' = j) →
      Nat.card (C.Y j) ≠ Nat.card Γ →
      ∀ α : MulAut Γ, C.S.map α.toMonoidHom = C.S → (C.Y j).map α.toMonoidHom = C.Y j := by
    intro j hj huniq hne α hα
    have hle : C.S ≤ (C.Y j).map α.toMonoidHom := by
      rw [← hα]
      exact Subgroup.map_mono (C.S_le_Y j)
    obtain ⟨j', hj', hZ⟩ := C.complete _ hle
    have hcard : Nat.card ((C.Y j).map α.toMonoidHom) = Nat.card (C.Y j) :=
      Subgroup.card_map_of_injective α.injective
    by_cases hjJ : j' < C.J
    · have hY : (C.Y j).map α.toMonoidHom = C.Y j' := by
        rw [hZ]
        simp [memberOrTop, hjJ]
      rw [hY] at hcard
      have := huniq j' hjJ hcard
      rw [hY, this]
    · exfalso
      have hY : (C.Y j).map α.toMonoidHom = ⊤ := by
        rw [hZ]
        simp [memberOrTop, hjJ]
      rw [hY, Subgroup.card_top] at hcard
      exact hne hcard.symm
  have hne : ∀ (j : ℕ), Nat.card (C.Y j) ≠ Nat.card Γ → C.Y j ≠ ⊤ := by
    intro j h hj
    exact h (by rw [hj, Subgroup.card_top])
  refine ⟨C.S, C.Y j₁, C.Y j₂, hS2, hSi, hinv j₁ h₁ huniq₁ hne₁, hinv j₂ h₂ huniq₂ hne₂,
    hne j₁ hne₁, hne j₂ hne₂, ?_, g₁, g₂⟩
  have hle : C.S ≤ C.Y j₁ ⊔ C.Y j₂ := (C.S_le_Y j₁).trans le_sup_left
  obtain ⟨j, hj, hZ⟩ := C.complete _ hle
  by_cases hjJ : j < C.J
  · exfalso
    have hY : C.Y j₁ ⊔ C.Y j₂ = C.Y j := by
      rw [hZ]
      simp [memberOrTop, hjJ]
    exact hjoin j hjJ ⟨hY ▸ le_sup_left, hY ▸ le_sup_right⟩
  · rw [hZ]
    simp [memberOrTop, hjJ]

end CFSG.QuasithinUnique.Vol2Native.L239
