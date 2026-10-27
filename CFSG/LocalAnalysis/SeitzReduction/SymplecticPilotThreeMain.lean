module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeCTField
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeMainSwap
public import CFSG.LocalAnalysis.SeitzReduction.SeitzFamiliesXCharCat

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput MonsterInnerInput
  MonsterLocalComponentsInput)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp)

@[expose] def SpThreeGraphRowsInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f → 2 ≤ f →
    ∀ (e : L ≃* StatedSp 3 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
    ∀ κ : Sp2mKind, κ ≠ .field → κ ≠ .swap → (∀ k : Fin 3, RootKindSp e t f k κ) → False

section Clauses


theorem false_of_working_three_of_clauses (hcat2 : Sp2mCatalogueClausesAt 2)
    (hcat3 : LinearPilot.SLmCatalogueClausesAt 3) (hdet3 : LinearPilot.SLmEvenTypeDetAt 3)
    (hGraph : SpThreeGraphRowsInput) {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hset : SeitzSetting G L) {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp 3 K) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) : False := by
  have hK4 : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hsplit : UnitaryPilot.OddCentralSplit (siegelLevi K 3) :=
    oddCentralSplit_siegelLevi (by norm_num)
  obtain ⟨κ, hκ, hfield, hswap⟩ := exists_rootKindSp_param (m := 2) hcat2 hset hKc hf le_rfl e
    htC ht
  by_cases hκf : κ = .field
  ·
    obtain ⟨F, _, _, ι, σ, hσ, hfix⟩ := exists_quadraticExtension K
    obtain ⟨ψ, hinj, hrange, -, hσψ⟩ := exists_injective_fieldRow_three hcat3 hdet3 hsplit hset
      hKc hf e ht hKt ι hσ hfix (hfield hκf F ι σ hσ hfix)
    exact false_of_spFieldRow (ι := ι) hset hK4 le_rfl e ht hKt hσ hinj hrange hσψ
      (unique_of_spFieldRow hset le_rfl hKc hf e ht hKt ι hσ hfix hinj hrange)
  by_cases hκs : κ = .swap
  ·
    exact false_of_swapRow_three hcat3 hdet3 hsplit hset hKc hf e ht hKt (hswap hκs)
  ·
    exact hGraph G L hset f K hKc hf e t ht hKt κ hκf hκs hκ

theorem spThreeInput_of_clauses (hcat2 : Sp2mCatalogueClausesAt 2)
    (hcat3 : LinearPilot.SLmCatalogueClausesAt 3) (hdet3 : LinearPilot.SLmEvenTypeDetAt 3)
    (hGraph : SpThreeGraphRowsInput) : SpThreeInput := by
  intro G _ _ L hset f K _ _ _ hKc hf e t ht hKt
  exact false_of_working_three_of_clauses hcat2 hcat3 hdet3 hGraph hset hKc hf e ht hKt

end Clauses

section XChar


theorem spThreeInput_of_xchar (hGLS : GLS3OddLieAutComponentsInput) (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) (hres2 : CatSp2mSporadicResidual 2)
    (hSL3 : LinearPilot.CatSLmSporadicAt 3) (hGraph : SpThreeGraphRowsInput) : SpThreeInput :=
  spThreeInput_of_clauses
    (sp2mCatalogueClausesAt_of_inputs hGLS (CrossChar.sp2mNotOddLieInput 2) hMinn hMcomp hres2)
    (slmCatalogueClausesAt_of_xchar (by norm_num) (LinearPilot.slmEvenTypeDetAt (by norm_num))
      hGLS hSL3)
    (LinearPilot.slmEvenTypeDetAt (by norm_num)) hGraph

end XChar

end CFSG.SeitzReduction.SymplecticPilot
