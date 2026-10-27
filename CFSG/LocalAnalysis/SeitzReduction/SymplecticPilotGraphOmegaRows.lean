module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphOmegaSplit
public import CFSG.LocalAnalysis.SeitzReduction.EPilotEndOddBasic
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphOmegaNormal

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeafProof (fixedSubgroupCongrEquiv)
open CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.OmegaRadical
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.SeitzReduction.F4Pilot (normalizerMulAut)

section Inputs

@[expose] def SpOmegaRowGlobal {G : Type} [Group G] {L : Subgroup G} {n : ℕ} {K : Type} [Field K]
    (e : L ≃* StatedSp n K) (t : G) (f : ℕ) (κ : Sp2mKind) : Prop :=
  Sp2mKindType (spGlobal e) n f κ ∧
    ∀ hN : t ∈ normalizer (spGlobal e : Set G),
      (spGlobal e).normalizerMonoidHom ⟨t, hN⟩ ∉
          (MulAut.conj : spGlobal e →* MulAut (spGlobal e)).range ∧
        LieModel (fixedSubgroup ((spGlobal e).normalizerMonoidHom ⟨t, hN⟩)) .PSp n 2 f

@[expose] def SpOmegaRecognitionInput (κ : Sp2mKind) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ n → Nat.card K = 2 ^ f →
    2 ≤ f → ∀ (e : L ≃* StatedSp n K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin n, RootKindSp e t f k κ) → SpOmegaRowGlobal e t f κ

@[expose] def SpOmegaRowUniqueInput (κ : Sp2mKind) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ n → Nat.card K = 2 ^ f →
    2 ≤ f → ∀ (e : L ≃* StatedSp n K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin n, RootKindSp e t f k κ) → SpOmegaRowGlobal e t f κ →
      ∀ g : G, g⁻¹ * t * g ∈ normalizer (spGlobal e : Set G) →
        g ∈ normalizer (spGlobal e : Set G)

@[expose] def OmegaPlusDicksonInput : Prop :=
  ∀ (K' : Type) [Field K'] [Finite K'] [CharP K' 2] (N : ℕ), 5 ≤ N →
    ∃ v : Fin (2 * N) → K', coordinateQuadPlus N K' v = 1 ∧
      ∃ χ : MulAut (matrixProjectiveDerived (coordinateQuadPlus N K')) →* Multiplicative (ZMod 2),
        (∀ x, χ (MulAut.conj x) = 1) ∧ χ (symmetryAut (coordinateQuadPlus N K') v) ≠ 1

@[expose] def OmegaMinusOutInput : Prop :=
  ∀ (K' : Type) [Field K'] [Finite K'] [CharP K' 2] (N : ℕ) (hN : 4 ≤ N) (b c : K'),
    (∀ s : K', s ^ 2 + b * s + c ≠ 0) →
    ∃ v : Fin (2 * N) → K', coordinateQuadMinus N K' (by omega) b c v = 1 ∧
      ∃ C : Subgroup (MulAut (matrixProjectiveDerived (coordinateQuadMinus N K' (by omega) b c))),
        IsCyclic C ∧
        (∀ β ∈ C, β ∈ (MulAut.conj : matrixProjectiveDerived (coordinateQuadMinus N K' (by omega) b c)
          →* MulAut _).range → β = 1) ∧
        (∀ α, ∃ g, ∃ β ∈ C, α = MulAut.conj g * β) ∧
        symmetryAut (coordinateQuadMinus N K' (by omega) b c) v ∈ C

end Inputs

section Endgame


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem false_of_spOmegaPlusRow_of_global (hD : OmegaPlusDicksonInput)
    (hset : SeitzSetting G L) {n f : ℕ} (hn : 4 ≤ n) (e : L ≃* StatedSp n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hglob : SpOmegaRowGlobal e t f .omegaPlus)
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer (spGlobal e : Set G) →
      g ∈ normalizer (spGlobal e : Set G)) : False := by
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have htN := mem_normalizer_spGlobal e htC
  have htt : t * t = 1 := by rw [← _root_.sq, ← ht, pow_orderOf_eq_one]
  obtain ⟨hty, hact⟩ := hglob
  obtain ⟨hout, hfix⟩ := hact htN
  have hty' : LieModel (spGlobal e) .POmegaPlus (n + 1) 2 f := hty
  have hC := CFSG.ComponentClassification.EvenOrthSelector.statedModel_of_lieModel
    (by decide) hty'
  have hI := (even_orthogonal_involutions_conjugate_into_semilinear_image (spGlobal e)
    .POmegaPlus (Or.inl rfl) (n + 1) f hC).1
  obtain ⟨⟨-, hf1, hn4'⟩, K', _, _, hK', ⟨eE⟩⟩ := hC
  have hn4 : 4 ≤ n + 1 := hn4'
  have : CharP K' 2 := LinearPilot.charP_two_of_card_eq_two_pow hK'
  have hconj := (hI K' hK' eE).1
  have hreg := regular_coordinateQuadPlus (K := K') (n := n + 1) (by omega)
  have hE := commutator_coordinateQuadPlus (K := K') (n := n + 1) (by omega)
  obtain ⟨v, hv, χ, hχInn, hχv⟩ := hD K' (n + 1) (by omega)
  set ε := coordinatePlusWitnessEquiv K' eE with hεdef
  set θ := (spGlobal e).normalizerMonoidHom ⟨t, htN⟩ with hθdef
  have hθθ : θ * θ = 1 := by
    rw [hθdef, ← map_mul, show (⟨t, htN⟩ : normalizer (spGlobal e : Set G)) * ⟨t, htN⟩ = 1 from
      Subtype.ext htt, map_one]
  have hαα : MulAut.congr ε θ * MulAut.congr ε θ = 1 := by rw [← map_mul, hθθ, map_one]
  have hαo : MulAut.congr ε θ ∉ inner (matrixProjectiveDerived (coordinateQuadPlus (n + 1) K')) := by
    rw [LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hout
  have hαfix : LieModel (fixedSubgroup (MulAut.congr ε θ)) .PSp n 2 f :=
    LieType.CurtisTits.lieModel_of_mulEquiv (fixedSubgroupCongrEquiv ε θ) hfix
  obtain ⟨Ψ, hΨ⟩ := exists_conj_eq_symmetryAut_of_lieModel_PSp hf1 hK' hn4 hreg.1 hreg.2 hE hconj
    hv _ hαα hαo hαfix
  have : IsSimpleGroup G := hset.1
  refine EPilot.false_of_simple_of_mulAut_hom ε htN ht huniq χ (by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]; decide) hχInn ?_
  have h1 : χ (MulAut.congr ε θ) = χ (symmetryAut (coordinateQuadPlus (n + 1) K') v) := by
    rw [hΨ, map_mul, map_mul, map_inv]
    exact mul_inv_cancel_comm _ _
  change χ (MulAut.congr ε θ) ≠ 1
  rw [h1]
  exact hχv

omit [Finite K] [CharP K 2] in
theorem false_of_spOmegaMinusRow_of_global (hO : OmegaMinusOutInput)
    (hset : SeitzSetting G L) {n f : ℕ} (hn : 4 ≤ n) (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* StatedSp n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hglob : SpOmegaRowGlobal e t f .omegaMinus)
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer (spGlobal e : Set G) →
      g ∈ normalizer (spGlobal e : Set G)) : False := by
  have hK4 : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have htN := mem_normalizer_spGlobal e htC
  have htt : t * t = 1 := by rw [← _root_.sq, ← ht, pow_orderOf_eq_one]
  obtain ⟨hty, hact⟩ := hglob
  obtain ⟨hout, hfix⟩ := hact htN
  have hty' : LieModel (spGlobal e) .POmegaMinus (n + 1) 2 f := hty
  have hC := CFSG.ComponentClassification.EvenOrthSelector.statedModel_of_lieModel
    (by decide) hty'
  have hI := (even_orthogonal_involutions_conjugate_into_semilinear_image (spGlobal e)
    .POmegaMinus (Or.inr rfl) (n + 1) f hC).1
  obtain ⟨⟨-, hf1, hn4'⟩, K', _, _, hK', b, c, hirr, ⟨eE⟩⟩ := hC
  have hn4 : 4 ≤ n + 1 := hn4'
  have h1n : 1 ≤ n + 1 := by omega
  have : CharP K' 2 := LinearPilot.charP_two_of_card_eq_two_pow hK'
  have hconj := hI h1n K' hK' b c hirr eE
  have hreg := regular_coordinateQuadMinus (n + 1) K' b c hn4 hirr
  have hE := commutator_coordinateQuadMinus (n + 1) K' b c hn4 hirr
  obtain ⟨v, hv, C, hCcyc, hCInn, hNF, hvC⟩ := hO K' (n + 1) hn4 b c hirr
  set ε := coordinateMinusWitnessEquiv K' h1n b c eE with hεdef
  set θ := (spGlobal e).normalizerMonoidHom ⟨t, htN⟩ with hθdef
  have hθθ : θ * θ = 1 := by
    rw [hθdef, ← map_mul, show (⟨t, htN⟩ : normalizer (spGlobal e : Set G)) * ⟨t, htN⟩ = 1 from
      Subtype.ext htt, map_one]
  have hαα : MulAut.congr ε θ * MulAut.congr ε θ = 1 := by rw [← map_mul, hθθ, map_one]
  have hαo : MulAut.congr ε θ ∉
      inner (matrixProjectiveDerived (coordinateQuadMinus (n + 1) K' h1n b c)) := by
    rw [LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hout
  have hαfix : LieModel (fixedSubgroup (MulAut.congr ε θ)) .PSp n 2 f :=
    LieType.CurtisTits.lieModel_of_mulEquiv (fixedSubgroupCongrEquiv ε θ) hfix
  obtain ⟨Ψ, hΨ⟩ := exists_conj_eq_symmetryAut_of_lieModel_PSp hf1 hK' hn4 hreg.1 hreg.2 hE hconj
    hv _ hαα hαo hαfix
  have htZ : t ∉ centralizer (spGlobal e : Set G) := by
    intro htZ
    apply hout
    refine ⟨1, MulEquiv.ext fun y => Subtype.ext ?_⟩
    rw [map_one, MulAut.one_apply, hθdef, Subgroup.normalizerMonoidHom_apply_apply_coe,
      ← mem_centralizer_iff.1 htZ y y.2, mul_inv_cancel_right]
  have hZ := EPilot.odd_card_centralizer_of_inf_eq_zpowers hKt (le_spGlobal hK4 (by omega) e) ht
    htN htZ
  have hker : Odd (Nat.card (normalizerMulAut ε).ker) := by
    rw [EPilot.card_ker_normalizerMulAut]
    exact hZ
  have : IsCyclic C := hCcyc
  have hout' : normalizerMulAut ε ⟨t, htN⟩ ∉
      (MulAut.conj : matrixProjectiveDerived (coordinateQuadMinus (n + 1) K' h1n b c) →*
        MulAut _).range := hαo
  have hidx := EPilot.exists_normal_index_two_of_action_complement_of_isConj (normalizerMulAut ε)
    hker hCInn hNF (EPilot.exists_normalizerMulAut_eq_conj ε) htN ht hout' huniq ⟨Ψ⁻¹, by
      change Ψ⁻¹ * MulAut.congr ε θ * Ψ⁻¹⁻¹ ∈ C
      have h1 : Ψ⁻¹ * MulAut.congr ε θ * Ψ⁻¹⁻¹ =
          symmetryAut (coordinateQuadMinus (n + 1) K' h1n b c) v := by
        rw [hΨ]
        group
      rw [h1]
      exact hvC⟩
  have : IsSimpleGroup G := hset.1
  have htG : t ∉ spGlobal e := EPilot.not_mem_of_normalizerMulAut_not_mem_range ε htN hout'
  exact CFSG.SeitzReduction.not_exists_normal_index_two_of_simple
    (EPilot.two_lt_card_of_odd_centralizer hZ ht htG) hidx

end Endgame

section Rows


theorem false_of_spOmegaPlusRow (hrec : SpOmegaRecognitionInput .omegaPlus)
    (huniq : SpOmegaRowUniqueInput .omegaPlus) (hD : OmegaPlusDicksonInput) :
    SpOmegaPlusRowInput := by
  intro G _ _ L hset n f K _ _ _ hn hKc hf e t ht hKt hκ
  have hglob := hrec G L hset n f K hn hKc hf e t ht hKt hκ
  exact false_of_spOmegaPlusRow_of_global hD hset hn e ht hKt hglob
    (huniq G L hset n f K hn hKc hf e t ht hKt hκ hglob)

theorem false_of_spOmegaMinusRow (hrec : SpOmegaRecognitionInput .omegaMinus)
    (huniq : SpOmegaRowUniqueInput .omegaMinus) (hO : OmegaMinusOutInput) :
    SpOmegaMinusRowInput := by
  intro G _ _ L hset n f K _ _ _ hn hKc hf e t ht hKt hκ
  have hglob := hrec G L hset n f K hn hKc hf e t ht hKt hκ
  exact false_of_spOmegaMinusRow_of_global hO hset hn hKc hf e ht hKt hglob
    (huniq G L hset n f K hn hKc hf e t ht hKt hκ hglob)

theorem spGraphRowsInput_of_omegaInputs (hLE : SpLinearEvenRowInput)
    (hUE : SpUnitaryEvenRowInput) (hLO : SpLinearOddRowInput) (hUO : SpUnitaryOddRowInput)
    (hrecP : SpOmegaRecognitionInput .omegaPlus) (huniqP : SpOmegaRowUniqueInput .omegaPlus)
    (hD : OmegaPlusDicksonInput) (hrecM : SpOmegaRecognitionInput .omegaMinus)
    (huniqM : SpOmegaRowUniqueInput .omegaMinus) (hO : OmegaMinusOutInput) :
    SpGraphRowsInput :=
  spGraphRowsInput_of_rows hLE hUE hLO hUO (false_of_spOmegaPlusRow hrecP huniqP hD)
    (false_of_spOmegaMinusRow hrecM huniqM hO)

end Rows

end CFSG.SeitzReduction.SymplecticPilot
