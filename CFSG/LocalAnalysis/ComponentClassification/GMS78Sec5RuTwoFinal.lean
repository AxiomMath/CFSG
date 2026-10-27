module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5Ru217
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuB1Main
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuNotSylow

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.Quasithin CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G] {L T R R₂ : Subgroup G} {y d : G}

namespace SzMinCounter

theorem dempwolff217_of_min
    (hF : Foundation) (hS3 : B1Stage3)
    (hM : SzMinCounter G L 1) (hS : Sec3.SzR G L T R 1 y d) (hR₂ : Sec3.IsR₂ L T R R₂ d)
    (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4)
    (h216 : ∀ F₁ : Subgroup G, F₁ ≤ gmsA L T → Nat.card F₁ = 4 →
      normalizer (F₁ : Set G) ≤ normalizer (R : Set G))
    (hkinds : ∀ (μ : G → ℕ) (ν : G → Fin 8), Sec3.SzR.MaskCoords L T R μ ν → ∀ f ∈ gmsA L T,
      f ≠ 1 → ∀ X : Subgroup G, (∀ x, x ∈ X ↔ x ∈ R ∧ μ x ∈ 0 :: RuQCode.ppOf (ν f)) →
      ∃ S : Subgroup G, IsSylowOf 2 S ⊤ ∧ R ≤ S ∧ S ≤ normalizer (R : Set G) ∧
        S ≤ centralizer ({f} : Set G) ∧ X ≤ S ∧
        ∀ f₁ ∈ gmsA L T, f₁ ≠ 1 → f₁ ≠ f →
          ∀ h ∈ centralizer ({f} : Set G), h * f₁ * h⁻¹ ∈ S → h * f₁ * h⁻¹ ∈ X) :
    ∀ (μ : G → ℕ) (ν : G → Fin 8), Sec3.SzR.MaskCoords L T R μ ν → ∀ S : Subgroup G,
      IsSylowOf 2 S (normalizer (R : Set G)) → ∀ f ∈ gmsA L T, f ≠ 1 →
      S ⊓ centralizer (S : Set G) = zpowers f → ∀ X : Subgroup G,
      (∀ x, x ∈ X ↔ x ∈ R ∧ μ x ∈ 0 :: RuQCode.ppOf (ν f)) →
      centralizer ({f} : Set G) ≤ normalizer (gmsA L T : Set G) ∨
        centralizer ({f} : Set G) ≤ normalizer (X : Set G) := by
  have h3 := hS.sec3
  have hZ : Odd (Nat.card (center L)) := hS.oddCenter
  have hO := dempwolffOddCore_of hF hS3 G L hM _ h3.isSylowOf_T₀ h4
  have h34 : NoStronglyClosedAbelian G := fun S _ hAS hAab hA1 hcl =>
    hM.hyp.lemma34 S hAS hAab hA1 hcl
  exact hS.dempwolff217 h34 hR₂ h4 (hM.centralizer_gmsV_eq h3 hS.foundation hZ h4 hO)
    (fun e he he1 => hM.centralizer_eq_sup h3 hS.foundation hZ h4 hO he he1)
    (fun a haL ha1 ha2 => hM.isPGroup_inf_centralizer h3 hS.foundation hZ h4 hO haL ha1 ha2)
    (hS.not_isSylowOf_normalizer hM hR₂) h216 hkinds

end SzMinCounter

end CFSG.ComponentClassification.GMS78
