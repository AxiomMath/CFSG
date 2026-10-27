module

public import CFSG.ClassicalInvolution.Q3.TL4Conn26Z2U
public import CFSG.ClassicalInvolution.Q3.TL4Conn26Z2E
public import CFSG.ClassicalInvolution.Q3.TL4Conn26Z2G
public import CFSG.ClassicalInvolution.Q3.TL4OddFrGen

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)

section Cit3b


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem alphaOf_eq_bot_of_z2 (h4 : Thm4RBelow 3 n)
    (htw : PhilipHall.Frame.Thm1RTwinLiftSetEBelow n) (hOm : OmegaAutOddFreeR)
    (hfree : TightZ2TFreeR 3 n) (hL : TightLargeHypR 3 n Y R S t)
    (hc : DConnected (CoreAssembly.conjClass (tightCore R))) (hA : ¬ TriNbrAll R t)
    (hcase : LinkZ2 R t) (hsimp : IsSimpleGroup ↥(genFittingFStar ↥(linkGrp R t)))
    (hnab : ∃ a b : ↥(genFittingFStar ↥(linkGrp R t)), a * b ≠ b * a)
    (hinv : ∀ a : ↥(linkGrp R t), a * a = 1 → a ∈ genFittingFStar ↥(linkGrp R t))
    (hα : ∀ (𝒳 : Subgroup (MulAut ↥(genFittingFStar ↥(linkGrp R t))))
      (hinn : ∀ g : ↥(genFittingFStar ↥(linkGrp R t)), MulAut.conj g ∈ 𝒳)
      (a a' : ↥(genFittingFStar ↥(linkGrp R t))), a * a = 1 → a ≠ 1 → a' ≠ a → a * a' = a' * a →
        (∃ g : ↥(genFittingFStar ↥(linkGrp R t)), g * a * g⁻¹ = a') →
        alphaOf (Subgroup.closure
          ({⟨MulAut.conj a, hinn a⟩, ⟨MulAut.conj a', hinn a'⟩} : Set ↥𝒳)) = ⊥)
    (hconj : ∀ a a' : ↥(genFittingFStar ↥(linkGrp R t)), a * a = 1 → a ≠ 1 → a' * a' = 1 → a' ≠ 1 →
      ∃ g : ↥(genFittingFStar ↥(linkGrp R t)), g * a * g⁻¹ = a')
    (hgen : ∀ a a' : ↥(linkGrp R t), a * a = 1 → a ≠ 1 → a' * a' = 1 → a' ≠ 1 → a' ≠ a →
      a * a' = a' * a →
        Subgroup.centralizer ({a} : Set ↥(linkGrp R t)) ⊔
          Subgroup.centralizer ({a'} : Set ↥(linkGrp R t)) = ⊤)
    (hD : ∀ M ∈ linkFam R t, ∀ a : ↥(linkGrp R t), IsUniqueInvolution M a →
      ∀ P : Subgroup ↥(linkGrp R t), IsSylow2In P M →
        ∀ β : MulAut ↥(linkGrp R t), β * β = 1 → (∀ x ∈ P, β x = x) →
          β = 1 ∨ β = MulAut.conj a) :
    ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R), ∀ u : Y,
      IsUniqueInvolution J u → alphaOf (Subgroup.closure ({t, u} : Set Y)) = ⊥ := by
  refine alphaOf_eq_bot_of_framesP (P := fun J u w => ∃ J₂ J₃, Z2FrameAt R t J J₂ J₃ u w)
    hL hc ?_ ?_ ?_ ?_
  · rintro J u w ⟨J₂, J₃, hF⟩
    exact ⟨hF.memJ, hF.invJ⟩
  · rintro J u w ⟨J₂, J₃, hF⟩
    exact hF.hyp51 h4 htw hOm hL
      (fun _ _ _ _ _ hF' => hF'.hyp51At_t hL hsimp hnab hinv hconj hα)
      (fun _ _ _ _ _ hF' => hF'.hyp51At_u h4 htw hOm hfree hL hc hA hcase hD)
  · intro J hJ u hu
    obtain ⟨J₂, J₃, v, hF⟩ := exists_z2FrameAt hL hsimp hnab hinv hconj hJ hu
    exact ⟨v, J₂, J₃, hF⟩
  · intro J hJ J' hJ'
    obtain ⟨u, hu⟩ := Sec6Gen.exists_uniqueInvolution hL.datum.hypOmegaGen hJ.1
    obtain ⟨J₂, J₃, v, hF⟩ := exists_z2FrameAt hL hsimp hnab hinv hconj hJ hu
    obtain ⟨g, hgC, hgB, hJeq⟩ := hF.exists_linkStep hL hcase.1 hgen hJ'
    exact Relation.ReflTransGen.single ⟨u, v, ⟨J₂, J₃, hF⟩, g, hgC, hgB, hJeq⟩

theorem tightLinkZ2Alpha_of (h4 : Thm4RBelow 3 n)
    (htw : PhilipHall.Frame.Thm1RTwinLiftSetEBelow n) (hOm : OmegaAutOddFreeR)
    (hfree : TightZ2TFreeR 3 n) :
    ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
      TightLargeHypR 3 n Y R S t → DConnected (CoreAssembly.conjClass (tightCore R)) →
        ¬ TriNbrAll R t → LinkZ2 R t → IsSimpleGroup ↥(genFittingFStar ↥(linkGrp R t)) →
        (∃ a b : ↥(genFittingFStar ↥(linkGrp R t)), a * b ≠ b * a) →
        (∀ a : ↥(linkGrp R t), a * a = 1 → a ∈ genFittingFStar ↥(linkGrp R t)) →
        (∀ (𝒳 : Subgroup (MulAut ↥(genFittingFStar ↥(linkGrp R t))))
          (hinn : ∀ g : ↥(genFittingFStar ↥(linkGrp R t)), MulAut.conj g ∈ 𝒳)
          (a a' : ↥(genFittingFStar ↥(linkGrp R t))), a * a = 1 → a ≠ 1 → a' ≠ a → a * a' = a' * a →
            (∃ g : ↥(genFittingFStar ↥(linkGrp R t)), g * a * g⁻¹ = a') →
              alphaOf (Subgroup.closure
                ({⟨MulAut.conj a, hinn a⟩, ⟨MulAut.conj a', hinn a'⟩} : Set ↥𝒳)) = ⊥) →
        (∀ a a' : ↥(genFittingFStar ↥(linkGrp R t)), a * a = 1 → a ≠ 1 → a' * a' = 1 → a' ≠ 1 →
          ∃ g : ↥(genFittingFStar ↥(linkGrp R t)), g * a * g⁻¹ = a') →
        (∀ a a' : ↥(linkGrp R t), a * a = 1 → a ≠ 1 → a' * a' = 1 → a' ≠ 1 → a' ≠ a →
          a * a' = a' * a →
            Subgroup.centralizer ({a} : Set ↥(linkGrp R t)) ⊔
              Subgroup.centralizer ({a'} : Set ↥(linkGrp R t)) = ⊤) →
        (∀ M ∈ linkFam R t, ∀ a : ↥(linkGrp R t), IsUniqueInvolution M a →
          ∀ P : Subgroup ↥(linkGrp R t), IsSylow2In P M →
            ∀ β : MulAut ↥(linkGrp R t), β * β = 1 → (∀ x ∈ P, β x = x) →
              β = 1 ∨ β = MulAut.conj a) →
          ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R), ∀ u : Y,
            IsUniqueInvolution J u → alphaOf (Subgroup.closure ({t, u} : Set Y)) = ⊥ :=
  fun _ _ _ _ _ _ hL hc hA hcase hsimp hnab hinv hα hconj hgen hD =>
    alphaOf_eq_bot_of_z2 h4 htw hOm hfree hL hc hA hcase hsimp hnab hinv hα hconj hgen hD

end Cit3b

end CFSG.ClassicalInvolution.Q3.TL4
