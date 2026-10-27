module

public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs2
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DHeis
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6EInputs

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance

@[expose] def Lemma62Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), GLStanding G m 3 → GLCaseFour G 3 →
    ∀ B : Subgroup G, IsExtremal B → ∀ x ∈ B, x ≠ 1 → ∀ K : Subgroup G,
      GLAPComponent 3 (Subgroup.centralizer ({x} : Set G)) K →
        B ≤ Subgroup.normalizer (K : Set G) ∨ IsLTwoOddPow (barOf 3 K)

@[expose] def barCenterX {G : Type*} [Group G] (p : ℕ) (X K : Subgroup G) :
    Subgroup (↥X ⧸ GLAPPrimeCore p ↥X) :=
  (Subgroup.center ↥(barX p X K)).map (barX p X K).subtype

theorem IsExtremalType.isLThreeEps {Y : Type*} [Group Y] (h : IsExtremalType Y) : IsLThreeEps Y := by
  rcases h with ⟨K, hK, hf, h1, he⟩ | ⟨K, hK, hf, q, h1, h2, -, he⟩
  · exact Or.inl ⟨K, hK, hf, h1, he⟩
  · exact Or.inr ⟨K, hK, hf, q, h1, h2, he⟩

@[expose] def Input11_2Ext : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ), GLStanding G m p →
    ∀ (X B L : Subgroup G), X ≠ ⊤ → IsElemAbelian p B → B ≤ X →
      GLATwoLocalRank p ↥X ≤ CFSG.Open.pRank p B → GLAPComponent p X L →
      ¬ B ≤ Subgroup.normalizer (L : Set G) →
      p = 3 ∧ (Subgroup.normalizer (L : Set G)).relIndex B = 3 ∧
        (∀ y ∈ B, y ∉ Subgroup.normalizer (L : Set G) →
          GLAPComponent 3 (bClosure B L ⊓ Subgroup.centralizer ({y} : Set G))
              (GLAPLayer 3 (bClosure B L ⊓ Subgroup.centralizer ({y} : Set G))) ∧
            Nonempty (↥(GLAPLayer 3 (bClosure B L ⊓ Subgroup.centralizer ({y} : Set G))) ⧸
              GLAPPrimeCore 3 ↥(GLAPLayer 3 (bClosure B L ⊓ Subgroup.centralizer ({y} : Set G))) ≃*
              (↥(barX 3 X L) ⧸ Subgroup.center ↥(barX 3 X L)))) ∧
        (IsLTwoOddPow (barOf 3 L) ∨
          (IsElemAbelian 3 (barCenterX 3 X (bClosure B L)) ∧
            (Nat.card (barCenterX 3 X (bClosure B L)) = 3 ∨
              (Nat.card (barCenterX 3 X (bClosure B L)) = 9 ∧
                Nat.card ↥(barCenterX 3 X (bClosure B L) ⊓
                  Subgroup.centralizer (barX 3 X B : Set (↥X ⧸ GLAPPrimeCore 3 ↥X))) = 3)) ∧
            ∀ R : Subgroup G, R ≤ L → IsPGroup 3 ↥R →
              (∀ S : Subgroup G, S ≤ L → IsPGroup 3 ↥S → R ≤ S → S = R) →
                IsThreeOnePlusTwo R ∧ barCenterX 3 X R = barCenterX 3 X L))

@[expose] def InputL3U3Facts : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsLThreeEps Y →
    (commutator Y = ⊤ → IsSimpleGroup Y) ∧ (∃ E : Subgroup Y, IsElemAbelian 3 E ∧ Nat.card E = 9) ∧
      (∀ α : MulAut Y, α ∈ innerAut Y → IsFieldAutThree α → α = 1) ∧
      (∀ P : Subgroup (MulAut Y), IsPGroup 3 ↥P → ¬ HasElemSection3 P 4)

@[expose] def InputFieldRecog : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ky K₀ : Subgroup G) (g : G),
    IsLThreeEps (barOf 3 Ky) → g ∈ Subgroup.normalizer (Ky : Set G) → g ^ 3 = 1 →
    GLAPComponent 3 (Ky ⊓ Subgroup.centralizer ({g} : Set G)) K₀ →
    (∃ E : Subgroup G, E ≤ K₀ ∧ IsElemAbelian 3 E ∧ Nat.card E = 9) → InducesFieldAut 3 Ky g

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
