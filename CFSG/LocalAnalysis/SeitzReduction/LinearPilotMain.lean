module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotMainInputs
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatAssembly
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatTypeDet
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotEndSwap
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotGlobalNormalModel
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwap
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotWeakCTGlobal

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)

section Main

theorem false_of_working_five_le_of_inputs (hGLS : GLS3OddLieAutComponentsInput)
    (hX : SLmNotOddLieInput) (hSpor : CatSLmSporadic) (hFR : LinearFRInput) (hTP : LinearTPInput)
    (hField : LinearFieldRowInput) (hLift : LinearSwapLiftInput)
    (hUniq : LinearSwapRowUniqueInput) (hOrth : LinearOrthFiveInput) {G : Type} [Group G]
    [Finite G] {L : Subgroup G} (hset : SeitzSetting G L) {m f : ℕ} (hm : 4 ≤ m) {K : Type}
    [Field K] [Finite K] [CharP K 2] (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* LinearFlag.projectiveSL (m + 1) K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) : False := by
  have hK4 : 4 ≤ Nat.card K := (four_le_card_iff_two_le hKc).2 hf
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq_zpowers hKt
  have : IsSimpleGroup G := hset.1
  have hR5 := exists_conj_eq_mul_transvection_of_rigid_std hset (n := m + 1) (by omega) hKc e ht
    hKt (hFR (m + 1) _ (by omega) K f hKc hf) (hTP (m + 1) (by omega) K f hKc hf)
  have hcat : SLmCatalogueClausesAt (m + 1 - 2) :=
    slmCatalogueClausesAt_of_inputs (by omega) (slmEvenTypeDetAt (by omega)) hGLS
      (hX _ (by omega)) (hSpor _ (by omega))
  have hdet : SLmEvenTypeDetAt (m + 1 - 2) := slmEvenTypeDetAt (by omega)
  obtain ⟨ι, σ, hσ1, hσσ, hfix⟩ := exists_subfield_involution (F := GaloisField 2 (2 * f))
    (by omega) hKc (GaloisField.card 2 (2 * f) (by omega))
  have hD2c : ∀ (a b : Fin (m + 1)) (hab : a ≠ b),
      Nonempty (FieldNeighbourParam e t ι σ (modelToG e (rootTorus (K := K) hab))
        (({a, b} : Finset (Fin (m + 1)))ᶜ)) ∨ RootTorusSwapRow e t hab := fun a b hab =>
    nonempty_fieldNeighbourParam_rootTorus_or_swap_of_transvection hset hcat hdet hKc hf e
      (by omega) htC ht hR5 hab ι hσ1 hσσ hfix
  by_cases hone : ∃ (a b : Fin (m + 1)) (hab : a ≠ b),
      Nonempty (FieldNeighbourParam e t ι σ (modelToG e (rootTorus (K := K) hab))
        (({a, b} : Finset (Fin (m + 1)))ᶜ))
  ·
    obtain ⟨a, b, hab, hP⟩ := hone
    rcases Nat.lt_or_ge m 5 with hm5 | hm5
    · obtain rfl : m = 4 := by omega
      have h02 := hOrth G L hset f K hKc hf e t ht hKt hR5
        (Or.inl ⟨GaloisField 2 (2 * f), inferInstance, inferInstance, ι, σ, hσ1, hσσ, hfix, a, b,
          hab, hP⟩)
      exact hField G L hset 4 f K le_rfl hKc hf e t ht hKt _ ι σ hσ1 hσσ hfix _ rfl
        (exists_globalField_rootTorus_five hset hKc hf e htC ht ι hσ1 hσσ hfix hab hP h02 rfl)
    · exact hField G L hset m f K hm hKc hf e t ht hKt _ ι σ hσ1 hσσ hfix _ rfl
        (exists_globalField_rootTorus_of_one hset hm5 hKc hf e htC ht ι hσ1 hσσ hfix hab hP rfl)
  ·
    have hparam : ∀ (a b : Fin (m + 1)) (hab : a ≠ b),
        Nonempty (SwapNeighbourParam e t (modelToG e (rootTorus (K := K) hab))
          (({a, b} : Finset (Fin (m + 1)))ᶜ)) := fun a b hab =>
      hLift G L hset (m + 1) f K (by omega) hKc hf e t ht hKt hR5 a b hab
        ((hD2c a b hab).resolve_left fun hP => hone ⟨a, b, hab, hP⟩)
    rcases Nat.lt_or_ge m 5 with hm5 | hm5
    · obtain rfl : m = 4 := by omega
      have h02 := hOrth G L hset f K hKc hf e t ht hKt hR5 (Or.inr hparam)
      obtain ⟨G₁, hq, h₁₂, hsup, hδ, hsurj⟩ := exists_swapFactors_of_param le_rfl hK4 e hparam
        (forall_pieceCore_nodePair_le_centralizer e (a := 0) (b := 1) (c := 2) (d := 3)
          (by decide) h02)
      exact false_of_simple_of_swapFactors ht hq h₁₂ hsup
        (hUniq G L hset 4 f K le_rfl hKc hf e t ht hKt hparam G₁ hq h₁₂ hsup hδ hsurj)
    · obtain ⟨G₁, hq, h₁₂, hsup, hδ, hsurj⟩ := exists_swapFactors_rootTorus hm5 hK4 e hparam
      exact false_of_simple_of_swapFactors ht hq h₁₂ hsup
        (hUniq G L hset m f K hm hKc hf e t ht hKt hparam G₁ hq h₁₂ hsup hδ hsurj)

theorem false_of_working_of_inputs (hGLS : GLS3OddLieAutComponentsInput)
    (hX : SLmNotOddLieInput) (hSpor : CatSLmSporadic) (hFR : LinearFRInput) (hTP : LinearTPInput)
    (hField : LinearFieldRowInput) (hLift : LinearSwapLiftInput)
    (hUniq : LinearSwapRowUniqueInput) (hOrth : LinearOrthFiveInput) (hFour : LinearFourInput)
    (hTwo : LinearTwoInput) {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hset : SeitzSetting G L) {n f : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2]
    (hKc : Nat.card K = 2 ^ f) (hnf : (n, f) ≠ (4, 1)) (e : L ≃* LinearFlag.projectiveSL n K)
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) : False := by
  rcases card_eq_two_or_four_le hKc with ⟨rfl, hK2⟩ | ⟨hf, -⟩
  · refine hTwo G L hset n K hK2 ?_ e t ht hKt
    by_contra hn5
    exact hnf (by rw [show n = 4 by omega])
  · rcases Nat.lt_or_ge n 5 with hn5 | hn5
    · obtain rfl : n = 4 := by omega
      exact hFour G L hset f K hKc hf e t ht hKt
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      exact false_of_working_five_le_of_inputs hGLS hX hSpor hFR hTP hField hLift hUniq hOrth hset
        (by omega) hKc hf e ht hKt

theorem seitzExclusion_highPSL_of_inputs (hGLS : GLS3OddLieAutComponentsInput)
    (hX : SLmNotOddLieInput) (hSpor : CatSLmSporadic) (hFR : LinearFRInput) (hTP : LinearTPInput)
    (hField : LinearFieldRowInput) (hLift : LinearSwapLiftInput)
    (hUniq : LinearSwapRowUniqueInput) (hOrth : LinearOrthFiveInput) (hFour : LinearFourInput)
    (hTwo : LinearTwoInput) : SeitzExclusion HighPSL :=
  seitzExclusion_highPSL_of_forall fun _ _ _ _ hset _ _ _ _ _ _ hK hn hnf e _ ht hKt =>
    false_of_working_of_inputs hGLS hX hSpor hFR hTP hField hLift hUniq hOrth hFour hTwo hset hn hK
      hnf e ht hKt

end Main

end CFSG.SeitzReduction.LinearPilot
