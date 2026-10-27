module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotUniqueGraphField
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotUniqueGraphFour
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotEndFieldMain

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag

theorem nonFieldInvolutionExclusion_holds {n f : ℕ} (hf : 1 ≤ f) (hn : 3 ≤ n) {K F : Type}
    [Field K] [Finite K] [Field F] [Finite F] [CharP F 2] (hK : Nat.card K = 2 ^ f)
    (hF : Nat.card F = 2 ^ (2 * f)) {σ : F ≃+* F} (hσ1 : σ ≠ 1) (hσσ : σ * σ = 1) :
    NonFieldInvolutionExclusion n K F σ :=
  nonFieldInvolutionExclusion_of_graph hf hn hK hF hσ1 hσσ
    (graphInvolutionExclusion hf hn hK hF) (graphFieldInvolutionExclusion hf hn hK hF)

theorem fieldCoreTypeDet_holds {n f : ℕ} (hf : 1 ≤ f) (hn : 3 ≤ n) {K F : Type} [Field K]
    [Finite K] [Field F] [Finite F] (hK : Nat.card K = 2 ^ f) (ι : K →+* F) {σ : F ≃+* F}
    (hσ1 : σ ≠ 1) (hσσ : σ * σ = 1) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) :
    FieldCoreTypeDet n K F := by
  have hF : Nat.card F = 2 ^ (2 * f) := natCard_eq_two_pow_of_fixedField hK ι hσ1 hσσ hfix
  exact fieldCoreTypeDet_of_graph hf hn hK ι hσ1 hσσ hfix
    (graphInvolutionExclusion hf hn hK hF) (graphFieldInvolutionExclusion hf hn hK hF)

theorem exists_card_eq_two_pow_of_ringHom {K F : Type} [Field K] [Finite K] [Field F]
    [CharP F 2] (ι : K →+* F) : ∃ f, 1 ≤ f ∧ Nat.card K = 2 ^ f := by
  have : CharP K 2 := ι.charP ι.injective 2
  have := Fintype.ofFinite K
  obtain ⟨f, -, hf⟩ := FiniteField.card K 2
  exact ⟨f, f.pos, by rw [Nat.card_eq_fintype_card, hf]⟩

theorem fieldCoreTypeDet_of_card {m : ℕ} (hm : 2 ≤ m) {K F : Type} [Field K] [Finite K]
    [Field F] [Finite F] [CharP F 2] (ι : K →+* F) {σ : F ≃+* F} (hσ1 : σ ≠ 1)
    (hσσ : σ * σ = 1) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) :
    FieldCoreTypeDet (m + 1) K F := by
  obtain ⟨f, hf, hK⟩ := exists_card_eq_two_pow_of_ringHom ι
  exact fieldCoreTypeDet_holds hf (by omega) hK ι hσ1 hσσ hfix

section Global

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.EvenSmallLie (StandardSetting)

theorem false_of_globalField_of_card (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {m : ℕ} (hm : 2 ≤ m) {K F : Type} [Field K] [Finite K]
    [Field F] [Finite F] [CharP F 2] (ι : K →+* F) {σ : F ≃+* F} (hσ1 : σ ≠ 1)
    (hσσ : σ * σ = 1) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    (e : L ≃* LinearFlag.projectiveSL (m + 1) K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {G₀ : Subgroup G}
    (hG₀ : G₀ = ⨆ i : Fin m, pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1))))
    (hLG₀ : L ≤ G₀) (htG₀ : t ∈ normalizer (G₀ : Set G)) (hq : CFSG.IsQuasisimple G₀)
    (ψ : G₀ ⧸ center G₀ ≃* LinearFlag.projectiveSL (m + 1) F)
    (hψt : ∀ x : G₀, ψ ((G₀.normalizerMonoidHom ⟨t, htG₀⟩ x : G₀) : G₀ ⧸ center G₀) =
      fieldAut (m + 1) F σ (ψ (x : G₀ ⧸ center G₀))) :
    False :=
  false_of_globalField hset hOut hm ι hσ1 hσσ hfix e ht hKt
    (fieldCoreTypeDet_of_card hm ι hσ1 hσσ hfix) hG₀ hLG₀ htG₀ hq ψ hψt

end Global

section FieldRow

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem nonFieldInvolutionExclusion_of_fixedField {n f : ℕ} (hn : 3 ≤ n) {K : Type} [Field K]
    (hKc : Nat.card K = 2 ^ f) (hf : 1 ≤ f) {F : Type} [Field F] [Finite F] (ι : K →+* F)
    {σ : F ≃+* F} (hσ1 : σ ≠ 1) (hσσ : σ * σ = 1) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) :
    NonFieldInvolutionExclusion n K F σ := by
  have : Finite K := finite_of_card_eq_two_pow hKc
  have hF : Nat.card F = 2 ^ (2 * f) := natCard_eq_two_pow_of_fixedField hKc ι hσ1 hσσ hfix
  have : CharP F 2 := charP_two_of_card_eq_two_pow hF
  exact nonFieldInvolutionExclusion_holds hf hn hKc hF hσ1 hσσ

theorem false_of_fieldNeighbourParam_levTorus_four_of_card
    (hset : CFSG.SeitzReduction.SeitzSetting G L) {f : ℕ} {K : Type} [Field K]
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* LinearFlag.projectiveSL 4 K) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {F : Type} [Field F] [Finite F] (ι : K →+* F) {σ : F ≃+* F} (hσ1 : σ ≠ 1)
    (hσσ : σ * σ = 1) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) {a : Fin 4}
    (hP : Nonempty (FieldNeighbourParam e t ι σ (modelToG e (levTorus (K := K) a)) ({a}ᶜ)))
    (h02 : pieceCore e ({0, 1} : Finset (Fin 4)) ≤
      centralizer (pieceCore e ({2, 3} : Finset (Fin 4)) : Set G)) : False :=
  false_of_fieldNeighbourParam_levTorus_four hset hKc hf e ht hKt ι hσ1 hσσ hfix hP h02
    (nonFieldInvolutionExclusion_of_fixedField (by omega) hKc (by omega) ι hσ1 hσσ hfix)

end FieldRow

end CFSG.SeitzReduction.LinearPilot
