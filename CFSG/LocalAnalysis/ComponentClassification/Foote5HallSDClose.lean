module

public import CFSG.LocalAnalysis.ComponentClassification.HallQ8Main

public section

namespace CFSG.ComponentClassification.Foote5.HallGen

open CFSG Subgroup CFSG.ABGLocalTools

theorem hallWeak
    (G : Type) [Group G] [Finite G] (D : Subgroup G)
    (hD : AschbacherTheorem3.IsDihedralTwoGroup D) (h16 : 16 ≤ Nat.card D)
    (hcl : ∀ x ∈ normalizer (D : Set G), x ∉ D → orderOf x = 2 →
      ∀ d ∈ D, orderOf d = 2 → ∀ g : G, g⁻¹ * x * g ≠ d) :
    HallWeakConclusion D :=
  hallWeak_of_residual hallQ8Residual G D hD h16 hcl

theorem goldschmidtCorB4 :
    GoldschmidtCorB4 :=
  goldschmidtCorB4_of_residual hallQ8Residual

end CFSG.ComponentClassification.Foote5.HallGen
