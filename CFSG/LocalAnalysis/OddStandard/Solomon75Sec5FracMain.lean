module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5FracFive
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5FracSwap

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

@[expose] def Solomon75Frac53Four : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ) (z : X) (Z : Subgroup X)
    (S : Sylow 2 ↥(normalizer (Z : Set X))), Sec5Data X n z Z S → ∀ s, IsSec5Inv X Z s →
      ∀ A, Sec5Comp X n (normalizer (Z : Set X)) A → ∀ hs : s ∈ normalizer (A : Set X),
        ∀ M : AhatModel X n A, fixCount (M.perm s hs) = 4 → False

@[expose] def Solomon75Frac53Three : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ) (z : X) (Z : Subgroup X)
    (S : Sylow 2 ↥(normalizer (Z : Set X))), Sec5Data X n z Z S → ∀ s, IsSec5Inv X Z s →
      ∀ A, Sec5Comp X n (normalizer (Z : Set X)) A → ∀ hs : s ∈ normalizer (A : Set X),
        ∀ M : AhatModel X n A,
          transCount (M.perm s hs) = 3 → fixCount (M.perm s hs) ≤ 3 → False

theorem frac53_printed (h4 : Solomon75Frac53Four) :
    ∀ (X : Type) [Group X] [Finite X] (n : ℕ) (z : X) (Z : Subgroup X)
      (S : Sylow 2 ↥(normalizer (Z : Set X))), Sec5Data X n z Z S → ∀ s, IsSec5Inv X Z s →
        (∀ A, Sec5Comp X n (normalizer (Z : Set X)) A → ∀ hs : s ∈ normalizer (A : Set X),
            ∀ M : AhatModel X n A, fixCount (M.perm s hs) ≤ 3) ∧
        (∀ A A', Sec5Comp X n (normalizer (Z : Set X)) A → Sec5Comp X n (normalizer (Z : Set X)) A' →
          A ≠ A' → A.map (MulAut.conj s).toMonoidHom = A' →
            zStar A ⊔ oddCoreOf (K0 X n (normalizer (Z : Set X))) =
              zStar A' ⊔ oddCoreOf (K0 X n (normalizer (Z : Set X)))) := by
  intro X _ _ n z Z S h s hs
  refine ⟨fun A hA hsA M => ?_, fun A A' hA hA' hne hAs =>
    zStar_sup_eq_of_swap h hs hA hA' hne hAs⟩
  by_contra hcon
  by_cases h5 : 5 ≤ fixCount (M.perm s hsA)
  · exact false_of_fixCount_ge_five h hs hA hsA M h5
  · exact h4 X n z Z S h s hs A hA hsA M (by omega)

theorem frac53 (hres : Solomon75Frac53Four ∧ Solomon75Frac53Three) : Solomon75Frac53 := by
  intro X _ _ n z Z S h s hs
  obtain ⟨hfix, hswap⟩ := frac53_printed hres.1 X n z Z S h s hs
  refine ⟨fun A hA hsA M => ⟨hfix A hA hsA M, fun h3 => ?_⟩, hswap⟩
  exact hres.2 X n z Z S h s hs A hA hsA M h3 (hfix A hA hsA M)

end CFSG.OddStandard.Solomon75
