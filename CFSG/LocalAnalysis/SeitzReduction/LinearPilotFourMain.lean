module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFourSwapLift
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotOrthFive
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotUniqueGraphEnd
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotEndSwap
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatAssembly
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatTypeDet
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFRNonalt
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTPGraphFieldStd
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotGlobalNormalModel
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwap

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)

@[expose] def LinearSwapRowUniqueFourInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f → 2 ≤ f →
    ∀ (e : L ≃* LinearFlag.projectiveSL 4 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ a : Fin 4,
        Nonempty (SwapNeighbourParam e t (modelToG e (levTorus (K := K) a)) ({a}ᶜ))) →
    ∀ G₁ : Subgroup G, CFSG.Open.IsQuasisimple G₁ →
      G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G) →
      G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom =
        ⨆ i : Fin 3, pieceCore e ({i.castSucc, i.succ} : Finset (Fin 4)) →
      (∀ x ∈ G₁, x * (t * x * t⁻¹) ∈ L) → (∀ y ∈ L, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y) →
      ∀ g : G, g⁻¹ * t * g ∈ normalizer ((⨆ i : Fin 3,
          pieceCore e ({i.castSucc, i.succ} : Finset (Fin 4)) : Subgroup G) : Set G) →
        g ∈ normalizer ((⨆ i : Fin 3,
          pieceCore e ({i.castSucc, i.succ} : Finset (Fin 4)) : Subgroup G) : Set G)

section FieldRow

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_conj_eq_mul_transvection_four (hset : SeitzSetting G L) {f : ℕ} {K : Type}
    [Field K] (hKc : Nat.card K = 2 ^ f) (e : L ≃* LinearFlag.projectiveSL 4 K) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    ∃ (g : G) (z : L), IsInvolutionClass 1 (e z) ∧ g⁻¹ * t * g = t * (z : G) := by
  have : Finite K := finite_of_card_eq_two_pow hKc
  exact exists_conj_eq_mul_transvection_of_rigid_std hset le_rfl hKc e ht hKt
    (innerGraphFieldRigid_four hKc) (transvectionIntrinsicStd hKc le_rfl)

theorem not_nonempty_fieldNeighbourParam_levTorus_four (hset : SeitzSetting G L) {f : ℕ}
    {K : Type} [Field K] (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* LinearFlag.projectiveSL 4 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {F : Type} [Field F]
    [Finite F] (ι : K →+* F) {σ : F ≃+* F} (hσ1 : σ ≠ 1) (hσσ : σ * σ = 1)
    (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) (a : Fin 4) :
    ¬ Nonempty (FieldNeighbourParam e t ι σ (modelToG e (levTorus (K := K) a)) ({a}ᶜ)) := by
  intro hP
  have : Finite K := finite_of_card_eq_two_pow hKc
  have : CharP K 2 := charP_two_of_card_eq_two_pow hKc
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq_zpowers hKt
  exact false_of_fieldNeighbourParam_levTorus_four_of_card hset hKc hf e ht hKt ι hσ1 hσσ hfix hP
    (pieceCore_le_centralizer_four_levTorus_field hset hKc hf e htC ht
      (exists_conj_eq_mul_transvection_four hset hKc e ht hKt) ι hσ1 hσσ hfix hP)

theorem forall_neighbourSwapRow_levTorus_four (hset : SeitzSetting G L)
    (hcat : SLmCatalogueClausesAt 3) (hdet : SLmEvenTypeDetAt 3) {f : ℕ} {K : Type} [Field K]
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* LinearFlag.projectiveSL 4 K) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (a : Fin 4) :
    NeighbourSwapRow e t (.levi a) := by
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq_zpowers hKt
  obtain ⟨ι, σ, hσ1, hσσ, hfix⟩ := exists_subfield_involution (F := GaloisField 2 (2 * f))
    (by omega) hKc (GaloisField.card 2 (2 * f) (by omega))
  exact (nonempty_fieldNeighbourParam_levTorus_or_swapRow hset hcat hdet hKc hf e htC ht
    (exists_conj_eq_mul_transvection_four hset hKc e ht hKt) a ι hσ1 hσσ hfix).resolve_left
    (not_nonempty_fieldNeighbourParam_levTorus_four hset hKc hf e ht hKt ι hσ1 hσσ hfix a)

end FieldRow

section SwapRow

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_swapFactors_levTorus_four (hset : SeitzSetting G L) {f : ℕ} {K : Type} [Field K]
    [Finite K] [CharP K 2] (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* LinearFlag.projectiveSL 4 K) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2)
    (hR5 : ∃ (g : G) (z : L), IsInvolutionClass 1 (e z) ∧ g⁻¹ * t * g = t * (z : G))
    (hparam : ∀ a : Fin 4,
      Nonempty (SwapNeighbourParam e t (modelToG e (levTorus (K := K) a)) ({a}ᶜ))) :
    ∃ G₁ : Subgroup G, CFSG.Open.IsQuasisimple G₁ ∧
      G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G) ∧
      G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom =
        ⨆ i : Fin 3, pieceCore e ({i.castSucc, i.succ} : Finset (Fin 4)) ∧
      (∀ x ∈ G₁, x * (t * x * t⁻¹) ∈ L) ∧ ∀ y ∈ L, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y := by
  have hK4 : 4 ≤ Nat.card K := (four_le_card_iff_two_le hKc).2 hf
  have h02 := pieceCore_le_centralizer_four_levTorus_swap hset hKc hf e htC ht hR5 (hparam 3)
    (hparam 0)
  exact exists_swapFactors_of_cover (m := 3) (by norm_num) hK4 e
    (swapNeighbourCover_levTorus le_rfl hparam (by norm_num))
    (forall_pieceCore_nodePair_le_centralizer e (a := 0) (b := 1) (c := 2) (d := 3) (by decide)
      h02)

theorem false_of_swapParam_levTorus_four (hset : SeitzSetting G L) {f : ℕ} {K : Type} [Field K]
    [Finite K] [CharP K 2] (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* LinearFlag.projectiveSL 4 K) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2)
    (hR5 : ∃ (g : G) (z : L), IsInvolutionClass 1 (e z) ∧ g⁻¹ * t * g = t * (z : G))
    (hparam : ∀ a : Fin 4,
      Nonempty (SwapNeighbourParam e t (modelToG e (levTorus (K := K) a)) ({a}ᶜ)))
    (huniq : ∀ G₁ : Subgroup G, CFSG.Open.IsQuasisimple G₁ →
      G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G) →
      G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom =
        ⨆ i : Fin 3, pieceCore e ({i.castSucc, i.succ} : Finset (Fin 4)) →
      (∀ x ∈ G₁, x * (t * x * t⁻¹) ∈ L) → (∀ y ∈ L, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y) →
      ∀ g : G, g⁻¹ * t * g ∈ normalizer ((⨆ i : Fin 3,
          pieceCore e ({i.castSucc, i.succ} : Finset (Fin 4)) : Subgroup G) : Set G) →
        g ∈ normalizer ((⨆ i : Fin 3,
          pieceCore e ({i.castSucc, i.succ} : Finset (Fin 4)) : Subgroup G) : Set G)) :
    False := by
  have : IsSimpleGroup G := hset.1
  obtain ⟨G₁, hq, h₁₂, hsup, hδ, hsurj⟩ :=
    exists_swapFactors_levTorus_four hset hKc hf e htC ht hR5 hparam
  exact false_of_simple_of_swapFactors ht hq h₁₂ hsup (huniq G₁ hq h₁₂ hsup hδ hsurj)

end SwapRow

section Main


theorem forall_nonempty_swapNeighbourParam_levTorus_four {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (hset : SeitzSetting G L) (hcat : SLmCatalogueClausesAt 3)
    (hdet : SLmEvenTypeDetAt 3) {f : ℕ} {K : Type} [Field K] (hKc : Nat.card K = 2 ^ f)
    (hf : 2 ≤ f) (e : L ≃* LinearFlag.projectiveSL 4 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) (a : Fin 4) :
    Nonempty (SwapNeighbourParam e t (modelToG e (levTorus (K := K) a)) ({a}ᶜ)) :=
  nonempty_swapNeighbourParam_levTorus_of_swapRow hset hKc hf e
    (mem_centralizer_of_inf_eq_zpowers hKt) ht a
    (forall_neighbourSwapRow_levTorus_four hset hcat hdet hKc hf e ht hKt a)

theorem false_of_four_of_clauses (hcat : SLmCatalogueClausesAt 3) (hdet : SLmEvenTypeDetAt 3)
    (hUniq : LinearSwapRowUniqueFourInput) {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hset : SeitzSetting G L) {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* LinearFlag.projectiveSL 4 K) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    False := by
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq_zpowers hKt
  have hparam := forall_nonempty_swapNeighbourParam_levTorus_four hset hcat hdet hKc hf e ht hKt
  exact false_of_swapParam_levTorus_four hset hKc hf e htC ht
    (exists_conj_eq_mul_transvection_four hset hKc e ht hKt) hparam
    (hUniq G L hset f K hKc hf e t ht hKt hparam)

theorem linearFourInput_of_clauses (hcat : SLmCatalogueClausesAt 3) (hdet : SLmEvenTypeDetAt 3)
    (hUniq : LinearSwapRowUniqueFourInput) : LinearFourInput :=
  fun _ _ _ _ hset _ _ _ _ _ hKc hf e _ ht hKt =>
    false_of_four_of_clauses hcat hdet hUniq hset hKc hf e ht hKt

end Main

section Inputs


theorem linearFourInput_of_inputs (hGLS : GLS3OddLieAutComponentsInput)
    (hX : SLmNotOddLieInputAt 3) (hSpor : CatSLmSporadicAt 3)
    (hUniq : LinearSwapRowUniqueFourInput) : LinearFourInput :=
  linearFourInput_of_clauses
    (slmCatalogueClausesAt_of_inputs le_rfl (slmEvenTypeDetAt le_rfl) hGLS hX hSpor)
    (slmEvenTypeDetAt le_rfl) hUniq

end Inputs

end CFSG.SeitzReduction.LinearPilot
