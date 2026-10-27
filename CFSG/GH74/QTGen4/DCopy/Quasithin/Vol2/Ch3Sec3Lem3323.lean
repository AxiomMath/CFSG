module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3StatementsB
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem335

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)

@[expose] def Step3_3_23_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L D : Subgroup G), Hyp331 G T M L D →
    IsPSL 3 2 1 ↥(autOn L (vPlus L T)) →
    (IsLnBlock L 3 ∧ ∃ X₁ X₂ : Subgroup G,
      (oTwoUpper X₁ = X₁ ∧ T ≤ Subgroup.normalizer (X₁ : Set G) ∧
        Nonempty (↥(X₁ ⊔ T) ⧸ CFSG.pCore 2 ↥(X₁ ⊔ T) ≃* Equiv.Perm (Fin 3)) ∧
        ¬ HasNoncentralTwoChief X₁ 3) ∧
      (oTwoUpper X₂ = X₂ ∧ T ≤ Subgroup.normalizer (X₂ : Set G) ∧
        Nonempty (↥(X₂ ⊔ T) ⧸ CFSG.pCore 2 ↥(X₂ ⊔ T) ≃* Equiv.Perm (Fin 3)) ∧
        ¬ HasNoncentralTwoChief X₂ 3) ∧
      pCoreOf 2 (X₁ ⊔ T) ⊓ pCoreOf 2 (X₂ ⊔ T) = preCenterAut T (vPlus L T)) ∨
    ((HasNoncentralTwoChief L 2 ∧ ¬ HasNoncentralTwoChief L 4) ∧
      ∃ C : Subgroup G, C ≠ ⊥ ∧
        C ≤ pCoreOf 2 (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ⊔ T) ∧
        L ⊔ T ≤ Subgroup.normalizer (C : Set G) ∧
        Subgroup.normalizer ((pCoreOf 2
          (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ⊔ T) : Subgroup G) :
            Set G) ≤ Subgroup.normalizer (C : Set G))

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem stmt3_3_23_of_F4
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h20 : Stmt3_3_20) (hS : Step3_3_23_F4) :
    Stmt3_3_23_F4 := by
  intro G _ _ T M L D h hP
  rcases hS G T M L D h hP with
    ⟨hLn, X₁, X₂, ⟨hX₁, hTX₁, hS₁, hγ₁⟩, ⟨hX₂, hTX₂, hS₂, hγ₂⟩, hT₀⟩ |
      ⟨hk, C, hC, hCR, hLTC, hNC⟩
  · left
    refine ⟨hLn, ?_⟩
    have hR₁ : D ≤ Subgroup.normalizer (pCoreOf 2 (X₁ ⊔ T) : Set G) := by
      by_contra hD
      exact hγ₁ (h20 G T M L D X₁ h hX₁ hTX₁ hS₁ hD).2.2.2.1
    have hR₂ : D ≤ Subgroup.normalizer (pCoreOf 2 (X₂ ⊔ T) : Set G) := by
      by_contra hD
      exact hγ₂ (h20 G T M L D X₂ h hX₂ hTX₂ hS₂ hD).2.2.2.1
    rw [← hT₀]
    intro d hd
    have h1 := hR₁ hd
    have h2 := hR₂ hd
    rw [Subgroup.mem_normalizer_iff] at h1 h2 ⊢
    intro x
    simp only [SetLike.mem_coe, Subgroup.mem_inf] at h1 h2 ⊢
    exact and_congr (h1 x) (h2 x)
  · right
    refine ⟨hk, fun hDR => ?_⟩
    have hCLT : C ≤ L ⊔ T :=
      hCR.trans ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (sup_le_sup_right inf_le_left T))
    exact h.not_le_normalizer h38 h39 hC hCLT hLTC (hDR.trans hNC)

end CFSG.Quasithin.H13
