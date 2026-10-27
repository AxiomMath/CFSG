module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.Defs
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Basic
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Transport
import CFSG.LocalAnalysis.ComponentInitial.LocalBMaximalPropagation
import CFSG.Foundations.GilmanSolomonGrammar
public import CFSG.Blueprint.OddStandardExact
public import CFSG.Blueprint.RecognitionDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Defs
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalKGroup
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.SectionRank.SQT
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint

private theorem oddCore_eq_pPrimeCore' (X : Type) [Group X] :
    oddCore X = pPrimeCore 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.oddCore_eq_piCore, CFSG.pPrimeCore_eq_piCore]

private theorem smallF3StarQuotient_of_mulEquiv {Q Q' : Type} [Group Q] [Group Q']
    (e : Q ≃* Q') (h : Omega.SmallF3StarQuotient Q) : Omega.SmallF3StarQuotient Q' := by
  rcases h with h | h | h | h
  · exact Or.inl (LieModel.of_mulEquiv e h)
  · exact Or.inr (Or.inl (LieModel.of_mulEquiv e h))
  · exact Or.inr (Or.inr (Or.inl (LieModel.of_mulEquiv e h)))
  · exact Or.inr (Or.inr (Or.inr (LieModel.of_mulEquiv e h)))

private theorem isFStar_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsFStar X) : IsFStar Y := by
  let e' : X ⧸ pPrimeCore 2 X ≃* Y ⧸ pPrimeCore 2 Y :=
    QuotientGroup.congr _ _ e (CFSG.pPrimeCore_map_iso 2 e)
  unfold IsFStar at h
  rcases h with h | h | h | h | h | h
  · exact Or.inl (LieModel.of_mulEquiv e' h)
  · exact Or.inr (Or.inl (LieModel.of_mulEquiv e' h))
  · exact Or.inr (Or.inr (Or.inl (LieModel.of_mulEquiv e' h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (LieModel.of_mulEquiv e' h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (Omega.smallF3OmegaQuotient_of_mulEquiv e' h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Omega.isTwoU43_of_mulEquiv e' h)))))

private theorem isFStarGroup_of_isFStar {X : Type} [Group X] (hX : IsQuasisimple X)
    (h : IsFStar X) : Omega.IsFStarGroup X := by
  let e : X ⧸ oddCore X ≃* X ⧸ pPrimeCore 2 X :=
    QuotientGroup.quotientMulEquivOfEq (oddCore_eq_pPrimeCore' X)
  unfold IsFStar at h
  rcases h with h | h | h | h | h | h
  · exact Or.inr ⟨hX, Or.inl (LieModel.of_mulEquiv e.symm h)⟩
  · exact Or.inr ⟨hX, Or.inr (Or.inl (LieModel.of_mulEquiv e.symm h))⟩
  · exact Or.inr ⟨hX, Or.inr (Or.inr (Or.inl (LieModel.of_mulEquiv e.symm h)))⟩
  · exact Or.inr ⟨hX, Or.inr (Or.inr (Or.inr (LieModel.of_mulEquiv e.symm h)))⟩
  · exact Or.inl ⟨hX, Or.inl (Omega.smallF3OmegaQuotient_of_mulEquiv e.symm h)⟩
  · exact Or.inl ⟨hX, Or.inr (Omega.isTwoU43_of_mulEquiv e.symm h)⟩

private theorem isFStar_of_isFStarGroup {X : Type} [Group X] (hX : IsQuasisimple X)
    (h : Omega.IsFStarGroup X) : IsFStar X := by
  let e : X ⧸ oddCore X ≃* X ⧸ pPrimeCore 2 X :=
    QuotientGroup.quotientMulEquivOfEq (oddCore_eq_pPrimeCore' X)
  unfold Omega.IsFStarGroup Omega.IsFGroup at h
  rcases h with ⟨-, hQ⟩ | ⟨-, hQ⟩
  · rcases hQ with hQ | hQ
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (Omega.smallF3OmegaQuotient_of_mulEquiv e hQ)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Omega.isTwoU43_of_mulEquiv e hQ)))))
  · have hQ' := smallF3StarQuotient_of_mulEquiv e hQ
    rcases hQ' with hQ' | hQ' | hQ' | hQ'
    · exact Or.inl hQ'
    · exact Or.inr (Or.inl hQ')
    · exact Or.inr (Or.inr (Or.inl hQ'))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hQ')))

theorem isFStar_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) :
    IsFStar X ↔ IsFStar Y :=
  ⟨isFStar_of_mulEquiv e, isFStar_of_mulEquiv e.symm⟩

theorem isFStarGroup_iff_isFStar {X : Type} [Group X] (hX : IsQuasisimple X) :
    Omega.IsFStarGroup X ↔ IsFStar X :=
  ⟨isFStar_of_isFStarGroup hX, isFStarGroup_of_isFStar hX⟩

theorem aschA2_of_hypA2 {G : Type} [Group G] [Finite G] (h : HypA2 G) : Omega.AschA2 G := by
  intro x y hx hy hcomm L K hL hK hLK hLstar
  have hLq : IsQuasisimple ↥L := hL.isQuasisimple
  have hKq : IsQuasisimple ↥K := hK.isQuasisimple
  have hLc : IsPComponent 2 (L.subgroupOf (centralizer ({x, y} : Set G))) :=
    CFSG.LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hL.2
  have hKc : IsPComponent 2 (K.subgroupOf (centralizer ({y} : Set G))) :=
    CFSG.LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hK.2
  have hLK' : L ≤ K ⊔ K.map (MulAut.conj x).toMonoidHom := by
    rw [← CFSG.GSGrammar.conjugate_eq_map_conj hx K]
    exact hLK
  have hcfg : A2Config G x y L K :=
    { ox := hx, oy := hy, comm := hcomm, X_le := hL.le, X_comp := hLc,
      K_le := hK.le, K_comp := hKc, X_le_KK := hLK' }
  have hFL : IsFStar ↥L := (isFStarGroup_iff_isFStar hLq).1 hLstar
  have hFK : IsFStar ↥K := h x y L K hcfg hFL
  exact (isFStarGroup_iff_isFStar hKq).2 hFK

theorem smallF3OmegaV_of_hypA2
    (h : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SmallF3Cyclic G L →
      ¬ Catalog G → HypA2 G) :
    Omega.SmallF3OmegaV := by
  intro G _ _ L hL hcat hQ hnot
  exact hnot (aschA2_of_hypA2 (h G L hL hcat))

end CFSG.OddStandard.SmallF3.HypA2
