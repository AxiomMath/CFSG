module

public import CFSG.LocalAnalysis.ComponentClassification.CTUMaxTwoAt

public section

namespace CFSG.ComponentClassification.Sol76

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem maximalTwoComponentSimple_held
    (hCI : GSLit.ClassicalInvolutionInput) (hGA : TBLit.GriessMultipliersAllModels)
    (h13 : Sol76T13.SolomonThm13Simple) (hS : SchreierFor Blueprint.Catalog)
    (hHN : GrSLit.HeldNotProperFixedInput) :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
      IsSimpleGroup (GeneralizedFitting.subgroup G) →
      (∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a) →
      ¬ Blueprint.OddLieType (GeneralizedFitting.subgroup G) →
      Assembly.KProper Blueprint.Catalog G →
      ∀ J : Subgroup G, GrSLit.GSWeakMaximalComponent J → 2 ≤ pRank 2 ↥J →
      (¬ ∃ (K : Type) (_ : Field K) (_ : Finite K), Odd (Nat.card K) ∧
          Nonempty (J ⧸ Open.fusionZStar J ≃*
            Assembly.LowTwoRank.StatedProj (Assembly.LowTwoRank.StatedSp 2 K))) →
      GrSLit.IsHeldType (J ⧸ Open.fusionZStar J) →
      ∀ t : G, orderOf t = 2 → J ≤ centralizer ({t} : Set G) →
        (⨆ (g : G) (_ : conjugate J g ≤ centralizer ({t} : Set G)), conjugate J g) ≤
            (pPrimeCore 2 (centralizer ({t} : Set G))).map (centralizer ({t} : Set G)).subtype ⊔
              J ∧
          (3 ≤ pRank 2 ↥J → ∀ g : G, ¬ ⁅J, conjugate J g⁆ ≤
            (pPrimeCore 2 J).map J.subtype ⊓
              (pPrimeCore 2 (conjugate J g)).map (conjugate J g).subtype) := by
  intro G _ _ _ hsF hnF hoF hK J hJ hm hSp hHe t ht hJt
  obtain ⟨a, ha, hJa, hJp⟩ := hJ.1
  have hnab : ∃ x y : G, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hnF
    exact ⟨x, y, fun h => hxy (Subtype.ext h)⟩
  exact maximalTwoComponentSimple_at_of_solomonMaximal hCI hGA hsF hnF hoF h13 hK hJ hm hSp
    (Foote5.SolMax.isSolomonMaximal_of_held hS hHN hnab hsF hnF hK ha ⟨hJa, hJp⟩ hHe) ht hJt

end CFSG.ComponentClassification.Sol76
