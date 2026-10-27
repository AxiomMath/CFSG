module

public import CFSG.LocalAnalysis.ComponentClassification.FiveCatEvenPSL
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatEvenPSU
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatEvenPSp
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatEvenOmega
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatEvenExc
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatEvenE6
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatEvenSuz
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatEvenInner
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatEvenTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder

public section

namespace CFSG.ComponentClassification.SolMax.FiveCat

open CFSG Subgroup CatLeaf Equiv
open CFSG.ComponentClassification.SolMax.FiveCat.Even

private theorem card_L2_16 {S : Type} [Group S] (h : Blueprint.LieModel S .PSL 2 2 4) :
    Nat.card S = 4080 :=
  (CFSG.GH74.card_of_lieModel_PSL (by norm_num) h).trans (by decide)

private theorem card_L3_4 {S : Type} [Group S] (h : Blueprint.LieModel S .PSL 3 2 2) :
    Nat.card S = 20160 :=
  (CFSG.GH74.card_of_lieModel_PSL (by norm_num) h).trans (by decide)

private theorem card_U3_4 {S : Type} [Group S] (h : Blueprint.LieModel S .PSU 3 2 2) :
    Nat.card S = 62400 :=
  ((CFSG.Timmesfeld.card_statedClassicalModel_two
    (CFSG.GH74.statedClassicalModel_of_lieModel (by norm_num) h)).2.1 rfl).trans (by decide)

theorem fivePump_even_PSL
    : FivePumpEvenClause .PSL :=
  fivePumpEven_of_inner_outer (evenFiveInner .PSL)
    (evenFiveOuter_PSL CatLeafProof.lieOrderFormulasInput)

theorem fivePump_even_PSU
    : FivePumpEvenClause .PSU :=
  fivePumpEven_of_inner_outer (evenFiveInner .PSU)
    (evenFiveOuter_PSU CatLeafProof.lieOrderFormulasInput)

theorem fivePump_even_PSp
    : FivePumpEvenClause .PSp :=
  fivePumpEven_of_inner_outer (evenFiveInner .PSp)
    (evenFiveOuter_PSp CatLeafProof.lieOrderFormulasInput)

theorem fivePump_even_POmegaPlus
    : FivePumpEvenClause .POmegaPlus :=
  fivePumpEven_of_inner_outer (evenFiveInner .POmegaPlus)
    (evenFiveOuter_POmegaPlus CatLeafProof.lieOrderFormulasInput)

theorem fivePump_even_POmegaMinus
    : FivePumpEvenClause .POmegaMinus :=
  fivePumpEven_of_inner_outer (evenFiveInner .POmegaMinus)
    (evenFiveOuter_POmegaMinus CatLeafProof.lieOrderFormulasInput)

theorem fivePump_even_exceptional
    (τ : Open.StatedLieTag)
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .twistedE6 ∨ τ = .trialityD4 ∨
      τ = .twistedB2 ∨ τ = .twistedF4 ∨ τ = .Tits) : FivePumpEvenClause τ := by
  have hO : LieOrderFormulasInput := CatLeafProof.lieOrderFormulasInput
  rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fivePumpEven_of_inner_outer (evenFiveInner _) (evenFiveOuter_G2 hO)
  · exact fivePumpEven_of_inner_outer (evenFiveInner _) (evenFiveOuter_F4 hO)
  · exact fivePumpEven_of_inner_outer (evenFiveInner _) (evenFiveOuter_E6 hO)
  · exact fivePumpEven_of_inner_outer (evenFiveInner _) (evenFiveOuter_E7 hO)
  · exact fivePumpEven_of_inner_outer (evenFiveInner _) (evenFiveOuter_E8 hO)
  · exact fivePumpEven_of_inner_outer (evenFiveInner _) (evenFiveOuter_twistedE6 hO)
  · exact fivePumpEven_of_inner_outer (evenFiveInner _) (evenFiveOuter_trialityD4 hO)
  · exact fivePumpEven_of_inner_outer (evenFiveInner _) (evenFiveOuter_twistedB2 hO)
  · exact fivePumpEven_of_inner_outer (evenFiveInner _) (evenFiveOuter_twistedF4 hO)
  · exact fivePumpEven_of_inner_outer (evenFiveInner _) (evenFiveOuter_Tits hO)

theorem fivePump_even_vacuous (τ : Open.StatedLieTag) (hτ : τ = .POmegaOdd ∨ τ = .twistedG2) :
    FivePumpEvenClause τ := by
  intro S _ _ _ _ ⟨n, f, hL⟩
  have hadm := hL.admissible
  rcases hτ with rfl | rfl
  · exact absurd rfl hadm.2.2.2
  · exact absurd hadm.2.2.2.1 (by norm_num)

theorem Even.evenFiveOuter_all
    (hO : LieOrderFormulasInput) (τ : Open.StatedLieTag) : EvenFiveOuter τ := by
  cases τ
  · exact evenFiveOuter_PSL hO
  · exact evenFiveOuter_PSU hO
  · exact evenFiveOuter_PSp hO
  · exact fun _ _ n f hadm => absurd rfl hadm.2.2.2
  · exact evenFiveOuter_POmegaPlus hO
  · exact evenFiveOuter_POmegaMinus hO
  · exact evenFiveOuter_G2 hO
  · exact evenFiveOuter_F4 hO
  · exact evenFiveOuter_E6 hO
  · exact evenFiveOuter_E7 hO
  · exact evenFiveOuter_E8 hO
  · exact evenFiveOuter_twistedE6 hO
  · exact evenFiveOuter_trialityD4 hO
  · exact evenFiveOuter_twistedB2 hO
  · exact fun _ _ n f hadm => absurd hadm.2.2.2.1 (by norm_num)
  · exact evenFiveOuter_twistedF4 hO
  · exact evenFiveOuter_Tits hO

theorem fiveTwoLayer_even
    (τ : Open.StatedLieTag) : FiveTwoLayerEvenClause τ := by
  have hO : LieOrderFormulasInput := CatLeafProof.lieOrderFormulasInput
  intro S _ _ hs hna ⟨n, f, hL⟩ σ P₁ P₂ h₁ h₂ hne hZ₁ hZ₂ e₁ e₂ _
  exfalso
  have hlist := evenFiveList_of_inner_outer (evenFiveInner τ) (evenFiveOuter_all hO τ) hs hna hL
    h₁ e₁
  have eA : Nonempty (↥P₁ ⧸ pPrimeCore 2 ↥P₁ ≃* alternatingGroup (Fin 5)) := by
    obtain ⟨e⟩ := e₁
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hZ₁.symm).trans e⟩
  have eB : Nonempty (↥P₂ ⧸ pPrimeCore 2 ↥P₂ ≃* alternatingGroup (Fin 5)) := by
    obtain ⟨e⟩ := e₂
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hZ₂.symm).trans e⟩
  have h3600 : 3600 ∣ Nat.card S :=
    (dvd_card_of_two_layers h₁.2.1 h₁.2.2.1 h₂.2.1 h₂.2.2.1 hne eA eB).trans
      (Subgroup.card_subgroup_dvd_card _)
  rcases hlist with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · rw [card_L2_16 hL] at h3600
    exact absurd h3600 (by decide)
  · rw [card_L3_4 hL] at h3600
    exact absurd h3600 (by decide)
  · rw [card_U3_4 hL] at h3600
    exact absurd h3600 (by decide)

end CFSG.ComponentClassification.SolMax.FiveCat
