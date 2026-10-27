module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ThetaShapes
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0.Layers
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0.Shape
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.C4Defs
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0Sub

open Equiv Equiv.Perm CFSG.AGLEmbedding CFSG.Open CFSG.Quasithin CFSG.RankThree.PartTwo
  CFSG.QuasithinUnique CFSG.Quasithin.ASInputs
open CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure
open CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
open scoped Pointwise

@[expose] def E0SubConfigStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), Asc81bHyp X S → IsWeakSBlock X S L →
    S ≤ Subgroup.normalizer (L : Set G) → ∀ N : ℕ, 6 ≤ N →
    ∀ θ : ↥(L ⊔ S) →* Perm (Fin N), NaturalSectionTheta S L N θ →
    (∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ S) →
    ∀ Δ₀ : Finset (Fin N), Δ₀.card = 4 →
    ∀ P : Subgroup (Perm (Fin N)), Nat.card P = 4 → (∀ p ∈ P, p * p = 1) →
    (∀ p ∈ P, ∀ i, i ∉ Δ₀ → p i = i) → (∀ i ∈ Δ₀, ∀ j ∈ Δ₀, ∃ p ∈ P, p i = j) →
    ∀ ω : Perm (Fin N), (∀ x, ω (ω x) = x) → (∀ x ∈ Δ₀, ω x = x) → (∀ x, x ∉ Δ₀ → ω x ≠ x) →
    (S.subgroupOf (L ⊔ S)).map θ = P ⊔ Subgroup.closure {τ | ∃ x, x ∉ Δ₀ ∧ τ = swap x (ω x)} →
    ¬ ⁅pCoreOf 2 (L ⊔ S), L⁆ ≤ blockV S L →
    ∃ L₁ : Subgroup G, L₁ ≤ L ∧ ⁅L₁, L₁⁆ = L₁ ∧ S ≤ Subgroup.normalizer (L₁ : Set G) ∧
      IsMSPair (L₁ ⊔ S) S ∧ L₁ ∈ cComp (L₁ ⊔ S) ∧
      ((L₁ ⊔ S : Subgroup G) : Set G) = (L₁ : Set G) * (S : Set G) ∧
      Nat.card (↥L₁ ⧸ CFSG.pCore 2 ↥L₁) = 360 ∧ ¬ IsShort2 L₁

theorem notSL3Statement_holds :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 360 →
        ¬ ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F)
            (α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)),
            Fintype.card F = 2 ^ n ∧ IsModO2Surj L α := by
  intro G _ _ L hcard ⟨n, F, _, _, α, hF, hsurj, hker⟩
  have e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hsurj)
  have h1 : Nat.card (CFSG.Assembly.LowTwoRank.StatedSL 3 F) = 360 := by
    rw [← hcard]; exact (Nat.card_congr e.toEquiv).symm
  rw [CFSG.Open.StatedAPI.card_statedSL_three] at h1
  set q := Nat.card F with hqdef
  have hq : 2 ≤ q := Finite.one_lt_card
  have h3 : q ^ 3 ≤ 360 := Nat.le_of_dvd (by norm_num) ⟨_, h1.symm⟩
  have h7 : q ≤ 7 := by
    by_contra h
    push Not at h
    have : 8 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left h 3
    omega
  interval_cases q <;> omega

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0Sub
