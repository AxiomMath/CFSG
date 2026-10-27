module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParSuzuki
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParTwoAssembly
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParTwoMap

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar

open CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.Quasithin
  CFSG.Open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen

@[expose] def KFactConcl {Y : Type} [Group Y] (L R P : Subgroup Y) : Prop :=
  (∃ M : Subgroup Y, MinParabolic (pElementSubgroup 2 (conjClosure P R) ⊔ R) R M) ∧
    (conjClosure P R ≠ L →
      ⁅pCoreOf 2 (twoResidual (pElementSubgroup 2 (conjClosure P R))),
        twoResidual (pElementSubgroup 2 (conjClosure P R))⁆ ≠ ⊥)

theorem kFact_of_twoPar_cat {Y : Type} [Group Y] [Finite Y] {L R P : Subgroup Y}
    (hR : R ≤ Subgroup.normalizer (L : Set Y)) (hR2 : IsPGroup 2 R)
    (hS : IsSylowTwoOf (R ⊓ L) L) (hP : IsMinOverBorel L (R ⊓ L) P)
    {G₀ : Type} [Group G₀] (e : (↥L ⧸ Subgroup.center ↥L) ≃* G₀)
    (h : ∃ T₀ P₁ P₂ : Subgroup G₀, TwoPar G₀ T₀ P₁ P₂) : KFactConcl L R P := by
  obtain ⟨T₀, P₁, P₂, h0⟩ := h
  have hT : IsSylowTwoOf (((R ⊓ L).subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))) ⊤ :=
    isSylowTwoOf_top_map_center hS
  obtain ⟨P₁', P₂', h1⟩ := TwoPar.exists_of_equiv e.symm h0 hT
  exact kFact_of_twoPar hR hR2 hS hP h1

theorem kFact_of_suzuki {Y : Type} [Group Y] [Finite Y] {L R P : Subgroup Y}
    (hL : Open.IsQuasisimple ↥L) (hR : R ≤ Subgroup.normalizer (L : Set Y)) (hR2 : IsPGroup 2 R)
    (hS : IsSylowTwoOf (R ⊓ L) L) (hP : IsMinOverBorel L (R ⊓ L) P) (m : ℕ)
    (hv : (TauCeti.LieTypeIndex.suzuki m).Valid)
    (e : (↥L ⧸ Subgroup.center ↥L) ≃* (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.suzuki m, hv⟩).Group) :
    KFactConcl L R P := by
  obtain ⟨-, hOne⟩ := suzuki_cat m hv e (isSylowTwoOf_top_map_center hS)
  exact kFact_of_oneNode hL hR hR2 hS hP hOne

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar
