module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotMainInputs
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotEndField
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCatAssembly
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotEndSwap
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotParamMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizeFieldFour

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput MonsterInnerInput
  MonsterLocalComponentsInput)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp)

section Main

theorem false_of_working_four_le_of_inputs (hGLS : GLS3OddLieAutComponentsInput)
    (hX : ∀ m : ℕ, 3 ≤ m → Sp2mNotOddLieInput m) (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) (hres : ∀ m : ℕ, 3 ≤ m → CatSp2mSporadicResidual m)
    (hField : SpFieldRowUniqueInput) (hFour : SpFourOrthInput)
    (hSwapU : SpSwapRowUniqueInput) (hGraph : SpGraphRowsInput) {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (hset : SeitzSetting G L) {m f : ℕ} (hm : 3 ≤ m) {K : Type} [Field K]
    [Finite K] [CharP K 2] (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* StatedSp (m + 1) K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) : False := by
  have hK4 : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hcat : Sp2mCatalogueClausesAt m :=
    sp2mCatalogueClausesAt_of_inputs hGLS (hX m hm) hMinn hMcomp (hres m hm)
  obtain ⟨κ, hκ, hfield, hswap⟩ := exists_rootKindSp_param hcat hset hKc hf (by omega) e htC ht
  by_cases hκf : κ = .field
  ·
    obtain ⟨F, _, _, ι, σ, hσ, hfix⟩ := exists_quadraticExtension K
    have hP := hfield hκf F ι σ hσ hfix
    obtain ⟨ψ, hinj, hrange, hι, hσψ⟩ : ∃ ψ : StatedSp (m + 1) F →* G, Function.Injective ψ ∧
        ψ.range = spGlobal e ∧
        (∀ x : StatedSp (m + 1) K, ψ (spFieldMap (m + 1) ι x) = ((e.symm x : L) : G)) ∧
        ∀ x : StatedSp (m + 1) F, t * ψ x * t⁻¹ = ψ (fieldSp (m + 1) F σ x) := by
      rcases Nat.lt_or_ge m 4 with hm4 | hm4
      · obtain rfl : m = 3 := by omega
        exact exists_injective_fieldRow_four hK4 e hσ hfix hP
          (hFour G L hset f K hKc hf e t ht hKt F ι σ hσ hfix hP)
      · exact exists_injective_fieldRow hK4 (by omega) e hσ hfix hP
    exact false_of_spFieldRow (ι := ι) hset hK4 (by omega) e ht hKt hσ hinj hrange hσψ
      (hField G L hset (m + 1) f K (by omega) hKc hf e t ht hKt F ι σ hσ hfix ψ hinj hrange hι
        hσψ)
  by_cases hκs : κ = .swap
  ·
    have hP := hswap hκs
    obtain ⟨G₁, hq, h₁₂, hsup, hδ, hsurj⟩ := exists_swapFactors_neighbourCore hK4 (by omega) e hP
    have : IsSimpleGroup G := hset.1
    exact LinearPilot.false_of_simple_of_swapFactors ht hq h₁₂ hsup
      (hSwapU G L hset (m + 1) f K (by omega) hKc hf e t ht hKt hP G₁ hq h₁₂ hsup hδ hsurj)
  ·
    exact hGraph G L hset (m + 1) f K (by omega) hKc hf e t ht hKt κ hκf hκs hκ

theorem false_of_working_of_inputs (hGLS : GLS3OddLieAutComponentsInput)
    (hX : ∀ m : ℕ, 3 ≤ m → Sp2mNotOddLieInput m) (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) (hres : ∀ m : ℕ, 3 ≤ m → CatSp2mSporadicResidual m)
    (hField : SpFieldRowUniqueInput) (hFour : SpFourOrthInput)
    (hSwapU : SpSwapRowUniqueInput) (hGraph : SpGraphRowsInput) (hThree : SpThreeInput)
    (hTwo : SpTwoInput) {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hset : SeitzSetting G L) {n f : ℕ} (hn : 3 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2]
    (hKc : Nat.card K = 2 ^ f) (hnf : (n, f) ≠ (3, 1)) (e : L ≃* StatedSp n K) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) : False := by
  rcases LinearPilot.card_eq_two_or_four_le hKc with ⟨rfl, hK2⟩ | ⟨hf, -⟩
  · refine hTwo G L hset n K hK2 ?_ e t ht hKt
    by_contra hn4
    exact hnf (by rw [show n = 3 by omega])
  · rcases Nat.lt_or_ge n 4 with hn4 | hn4
    · obtain rfl : n = 3 := by omega
      exact hThree G L hset f K hKc hf e t ht hKt
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      exact false_of_working_four_le_of_inputs hGLS hX hMinn hMcomp hres hField hFour
        hSwapU hGraph hset (by omega) hKc hf e ht hKt

theorem seitzExclusion_highPSp_of_inputs (hGLS : GLS3OddLieAutComponentsInput)
    (hX : ∀ m : ℕ, 3 ≤ m → Sp2mNotOddLieInput m) (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) (hres : ∀ m : ℕ, 3 ≤ m → CatSp2mSporadicResidual m)
    (hField : SpFieldRowUniqueInput) (hFour : SpFourOrthInput)
    (hSwapU : SpSwapRowUniqueInput) (hGraph : SpGraphRowsInput) (hThree : SpThreeInput)
    (hTwo : SpTwoInput) : SeitzExclusion HighPSp :=
  seitzExclusion_highPSp_of_forall fun _ _ _ _ hset _ _ _ _ _ _ hK hn hnf e _ ht hKt =>
    false_of_working_of_inputs hGLS hX hMinn hMcomp hres hField hFour hSwapU hGraph
      hThree hTwo hset hn hK hnf e ht hKt

end Main

end CFSG.SeitzReduction.SymplecticPilot
