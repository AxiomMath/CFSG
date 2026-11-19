module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.Chev

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Parts

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531 (FFChevConclusion)

section Vocab
variable {G : Type} [Group G] [Finite G]

abbrev Mt (M : Subgroup G) : Type := ↥M ⧸ CFSG.pCore 2 ↥M

@[expose] def tl (M X : Subgroup G) : Subgroup (Mt M) :=
  (X.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M))

end Vocab

@[expose] def Lemma96 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ), GLStanding G m p →
    ∀ M D : Subgroup G, Prop95Hyp p M D →
      ∀ K : Subgroup (Mt M), IsComponentOf K ⊤ → ⁅tl M (gammaD D), K⁆ = K →
        (∀ T₀ : Subgroup G, T₀ ≠ ⊥ → (IsCharIn T₀ (gammaD D) ∨ IsCharIn T₀ (sigmaOf D)) →
          ¬ K ≤ tl M (Subgroup.normalizer (T₀ : Set G))) ∧
        FFChevConclusion (↥K ⧸ Subgroup.center ↥K)

section L97
variable {G : Type} [Group G] [Finite G]

structure Lemma97Chief (p : ℕ) (M D X W : Subgroup G) : Prop where
  two_le : pCoreOf 2 M ≤ X
  lt : X < W
  le_core : W ≤ GLAPPrimeCoreOf p M
  normalX : (X.subgroupOf M).Normal
  normalW : (W.subgroupOf M).Normal
  commX : ⁅gammaD D, X⁆ ≤ pCoreOf 2 M
  chief : ∀ V : Subgroup G, V ≤ M → (V.subgroupOf M).Normal → X ≤ V → V ≤ W → V = X ∨ V = W
  comm_ne : ¬ ⁅gammaD D, W⁆ ≤ pCoreOf 2 M

end L97

@[expose] def Lemma97Ab : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ), GLStanding G m p →
    ∀ M D : Subgroup G, Prop95Hyp p M D → ∀ X W : Subgroup G,
      Lemma97Chief p M D X W → ⁅W, W⁆ ≤ X → False

@[expose] def Lemma97NonAb : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ), GLStanding G m p →
    ∀ M D : Subgroup G, Prop95Hyp p M D → ∀ X W : Subgroup G,
      Lemma97Chief p M D X W → ¬ ⁅W, W⁆ ≤ X → False

@[expose] def Lemma97 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ), GLStanding G m p →
    ∀ M D : Subgroup G, Prop95Hyp p M D →
      ⁅gammaD D, GLAPPrimeCoreOf p M⁆ ≤ pCoreOf 2 M

@[expose] def Prop95i : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ), GLStanding G m p →
    ∀ M D : Subgroup G, Prop95Hyp p M D → gammaD D ⊓ GLAPPrimeCoreOf p M = pCoreOf 2 M

@[expose] def Prop95ii : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ), GLStanding G m p →
    ∀ M D : Subgroup G, Prop95Hyp p M D →
      barX p M (gammaD D) ≤ Subgroup.centralizer
        ((CFSG.Open.pCore p (↥M ⧸ GLAPPrimeCore p ↥M) : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
          Set (↥M ⧸ GLAPPrimeCore p ↥M))

@[expose] def Prop95iii : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ), GLStanding G m p →
    ∀ M D : Subgroup G, Prop95Hyp p M D → ∀ L : Subgroup G, GLAPComponent p M L →
      barX p M (gammaD D) ≤ Subgroup.normalizer ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
        Set (↥M ⧸ GLAPPrimeCore p ↥M))

@[expose] def Prop95IvChev : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ), GLStanding G m p →
    ∀ M D : Subgroup G, Prop95Hyp p M D →
      ⁅gammaD D, GLAPPrimeCoreOf p M⁆ ≤ pCoreOf 2 M →
      ∀ L : Subgroup G, GLAPComponent p M L →
        barX p M (gammaD D) ≤ Subgroup.normalizer ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
          Set (↥M ⧸ GLAPPrimeCore p ↥M)) →
        ¬ barX p M (gammaD D) ≤ Subgroup.centralizer ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
          Set (↥M ⧸ GLAPPrimeCore p ↥M)) →
        FFChevConclusion (↥(tl M L) ⧸ Subgroup.center ↥(tl M L)) →
        (¬ ∃ n : ℕ, 5 ≤ n ∧ Nonempty ((↥(tl M L) ⧸ Subgroup.center ↥(tl M L)) ≃* alternatingGroup (Fin n))) →
        IsGLBlock M L ∧ Prop95Beta p M D L

@[expose] def Prop95IvAlt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ), GLStanding G m p →
    ∀ M D : Subgroup G, Prop95Hyp p M D →
      ⁅gammaD D, GLAPPrimeCoreOf p M⁆ ≤ pCoreOf 2 M →
      ∀ L : Subgroup G, GLAPComponent p M L →
        barX p M (gammaD D) ≤ Subgroup.normalizer ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
          Set (↥M ⧸ GLAPPrimeCore p ↥M)) →
        ¬ barX p M (gammaD D) ≤ Subgroup.centralizer ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
          Set (↥M ⧸ GLAPPrimeCore p ↥M)) →
        (∃ n : ℕ, 5 ≤ n ∧ Nonempty ((↥(tl M L) ⧸ Subgroup.center ↥(tl M L)) ≃* alternatingGroup (Fin n))) →
        IsGLBlock M L ∧ (Prop95Alpha p M D L ∨ Prop95Gamma p M D L)

section Sub
variable {G : Type} [Group G] [Finite G]

end Sub

@[expose] def NearSolvableTwoFacts : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (p : ℕ), p.Prime → p ≠ 2 → IsSimpleGroup S →
    ¬ p ∣ Nat.card S → signalizerNearSimpleModel p S →
    (¬ Nonempty (S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 p))) →
    ∀ f : MulAut S, orderOf f = p →
      CFSG.pCore 2 ↥(signalizerFixedSubgroup f) = ⊥ ∧
        ∀ g : MulAut S, IsPGroup 2 (Subgroup.zpowers g) → (∀ x ∈ signalizerFixedSubgroup f, g x = x) → g = 1

@[expose] def L2ThreeNotChevTwoOrAlt : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 →
    ¬ FFChevConclusion (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 p))

end CFSG.LocalAnalysis.GLTheoremB.Prop95Parts
