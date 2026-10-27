module

public import CFSG.ClassicalInvolution.Phan.PhanS7Def
public import CFSG.ClassicalInvolution.Asc77.AscB3C1
public import CFSG.ClassicalInvolution.Phan.PhanS7Ctx

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open CFSG.LieType.Universal.Spin QuadraticMap CFSG.ClassicalInvolution.PhanB3.H
  CFSG.ClassicalInvolution.Models.OrthogonalPairs
open scoped MatrixGroups

variable {F K : Type} [Field F] [Field K] [Algebra F K]

structure Node0Facts (D : KDat F K) (h2 : (2 : F) ≠ 0) : Prop where
  fix_vE3 : ∀ A : SL(2, F), extK (La0 h2 A).toLinearMap (vE3 D) = vE3 D
  mem_l0 : ∀ A : SL(2, F), ∃ a b c d : K,
    extK (La0 h2 A).toLinearMap (vXi D) = a • vXi D + b • vE2 D ∧
    extK (La0 h2 A).toLinearMap (vE2 D) = c • vXi D + d • vE2 D
  rot_vXi : ∀ (a b : F) (h : a ^ 2 + b ^ 2 = 1),
    extK (La0 h2 (rotSL0 a b h)).toLinearMap (vXi D) =
      (algebraMap F K a + algebraMap F K b * D.θ) • vXi D
  rot_vE2 : ∀ (a b : F) (h : a ^ 2 + b ^ 2 = 1),
    extK (La0 h2 (rotSL0 a b h)).toLinearMap (vE2 D) =
      (algebraMap F K a - algebraMap F K b * D.θ) • vE2 D
  rot_of_fix : ∀ (A : SL(2, F)) {c : K}, c ≠ 0 →
    extK (La0 h2 A).toLinearMap (vXi D) = c • vXi D →
      ∃ (a b : F) (hab : a ^ 2 + b ^ 2 = 1), A = rotSL0 a b hab
  rot_of_mapsTo : ∀ A : SL(2, F),
    (∀ s z : F, ∃ s' z' : F, La0 h2 A (mk7 s 0 0 s 0 0 z) = mk7 s' 0 0 s' 0 0 z') →
      ∃ (a b : F) (hab : a ^ 2 + b ^ 2 = 1), A = rotSL0 a b hab
  move : ∀ α β : K, IsFF7 D (α • vXi D + β • vE2 D) →
    ∃ A : SL(2, F), ∃ c : K, c ≠ 0 ∧
      extK (La0 h2 A).toLinearMap (vXi D) = c • (α • vXi D + β • vE2 D)

structure Node1Facts (D : KDat F K) (h2 : (2 : F) ≠ 0) : Prop where
  fix_vXi : ∀ A : SL(2, F), extK (La1 h2 A).toLinearMap (vXi D) = vXi D
  mem_l23 : ∀ A : SL(2, F), ∃ a b c d : K,
    extK (La1 h2 A).toLinearMap (vE2 D) = a • vE2 D + b • vE3 D ∧
    extK (La1 h2 A).toLinearMap (vE3 D) = c • vE2 D + d • vE3 D
  rot_vE2 : ∀ (a b : F) (h : a ^ 2 + 4 * b ^ 2 = 1),
    extK (La1 h2 (rotSL1 a b h)).toLinearMap (vE2 D) =
      (algebraMap F K a - 2 * algebraMap F K b * D.θ) • vE2 D
  rot_vE3 : ∀ (a b : F) (h : a ^ 2 + 4 * b ^ 2 = 1),
    extK (La1 h2 (rotSL1 a b h)).toLinearMap (vE3 D) =
      (algebraMap F K a + 2 * algebraMap F K b * D.θ) • vE3 D
  rot_of_fix : ∀ (A : SL(2, F)) {c : K}, c ≠ 0 →
    extK (La1 h2 A).toLinearMap (vE2 D) = c • vE2 D →
      ∃ (a b : F) (hab : a ^ 2 + 4 * b ^ 2 = 1), A = rotSL1 a b hab
  rot_of_mapsTo : ∀ A : SL(2, F),
    (∀ a b : F, ∃ a' b' : F,
      La1 h2 A (mk7 0 a b 0 (-a) (-b) 0) = mk7 0 a' b' 0 (-a') (-b') 0) →
      ∃ (a b : F) (hab : a ^ 2 + 4 * b ^ 2 = 1), A = rotSL1 a b hab
  move : ∀ α β : K, IsFF7 D (α • vE2 D + β • vE3 D) →
    ∃ A : SL(2, F), ∃ c : K, c ≠ 0 ∧
      extK (La1 h2 A).toLinearMap (vE2 D) = c • (α • vE2 D + β • vE3 D)

structure WittFact [Finite F] (D : KDat F K) : Prop where
  move : Odd (Nat.card F) → (2 : K) ≠ 0 → ¬ IsSquare (-1 : F) →
    ∀ {R : Submodule F (W7 F)}, ((quadOdd 3 F).restrict R).Nondegenerate →
      Module.finrank F R ≤ 4 → ∀ {x y : W7 K}, IsFF7 D x → IsFF7 D y →
        (∀ r ∈ R, polar (quadOdd 3 K) x (emb r) = 0) →
        (∀ r ∈ R, polar (quadOdd 3 K) y (emb r) = 0) →
          ∃ g : spinGroup (quadOdd 3 F), (∀ r ∈ R, spinAction (quadOdd 3 F) g r = r) ∧
            ∃ c : K, c ≠ 0 ∧ actK g x = c • y

structure OrderFacts [Finite F] (h2 : (2 : F) ≠ 0) (Dθ : ThetaData F h2) : Prop where
  fixP : ∀ g : spinGroup (quadOdd 3 F),
    (∀ s z : F, spinAction (quadOdd 3 F) g (mk7 s 0 0 s 0 0 z) = mk7 s 0 0 s 0 0 z) →
      g ∈ Dθ.θ.range
  fixW0 : ∀ g : spinGroup (quadOdd 3 F),
    (∀ x ∈ (fr0 h2).span, spinAction (quadOdd 3 F) g x = x) →
      g ∈ (CFSG.ClassicalInvolution.Asc77.B3C.twShort h2).range.map Dθ.θ

end CFSG.ClassicalInvolution.PhanB3.S
