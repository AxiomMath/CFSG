module

public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Representations.RealBridgeOddFamilyBound
import CFSG.FeitThompson.Representations.TypeIIIIVTwoCoherentLayers
import CFSG.FeitThompson.Representations.TypeThreeFourInnerComplementCyclic
import CFSG.FeitThompson.Representations.RealBridgeLowFamilySupport

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

universe u

open Subgroup
open scoped ComplexConjugate

open scoped Classical in
noncomputable def typeIIILayerOne {G : Type u} [Group G] [Fintype G] (T V : Subgroup G) :
    Set (↥T → ℂ) :=
  CFSG.FeitThompson.Prep06.indFamKer T (CFSG.FeitThompson.Prep06.derivedOf T)
    ((CFSG.FeitThompson.Prep06.hallCoreIn T ⊔
      (V ⊓ centralizer ((CFSG.FeitThompson.Prep06.hallCoreIn T : Subgroup G) : Set G)) :
        Subgroup G).subgroupOf T)

open scoped Classical in
theorem typeIIILayerOne_eq {G : Type u} [Group G] [Fintype G] (T V : Subgroup G) :
    typeIIILayerOne T V =
      CFSG.FeitThompson.Prep06.indFamKer T (CFSG.FeitThompson.Prep06.derivedOf T)
        ((CFSG.FeitThompson.Prep06.hallCoreIn T ⊔
          (V ⊓ centralizer ((CFSG.FeitThompson.Prep06.hallCoreIn T : Subgroup G) : Set G)) :
            Subgroup G).subgroupOf T) := (rfl)

theorem natCard_typeIIILayerOne_mul_eq
    (h₅ : _root_.CFSG.FeitThompson.Statements.FPF_type_iii_iv_core_elementary_chief_kernel_trivial.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FPF_type_iii_iv_second_derived_fitting.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FPF_type_iii_v_extended_dade_support.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FPF_type_iii_v_induced_family_noncoherence.{u})
    (h₉ : _root_.CFSG.FeitThompson.Statements.FPF_type_iii_v_second_factor_prime.{u})
    {G : Type u} [Group G] [Fintype G] (hG : CFSG.FeitThompson.Prep06.IsMinimalOddSimple G)
    {T V W₁ W₂ : Subgroup G} (hT : IsCoatom T) (hIII : IsTypeIII T)
    (hcT : IsWitnessedPConfiguration T V W₂ W₁) :
    Nat.card (typeIIILayerOne T V) * Nat.card W₂ = Nat.card V - 1 := by
  have hcyc := (_root_.CFSG.FeitThompson.Proofs.FPF_type_iii_iv_inner_complement_cyclic
    h₅ h₆ h₇ h₈ h₉ G hG T V W₂ W₁ hT (Or.inl hIII) hcT).1
  obtain ⟨-, hCeq, -, -, -, -, -, -, -, -, -, -, n, hn, -, -, hnp⟩ :=
    _root_.CFSG.FeitThompson.Proofs.FPF_type_iii_iv_two_coherent_layers h₅ h₆ h₇ h₈ h₉ G hG T V W₂ W₁
      hT (Or.inl hIII) hcT _ rfl _ _ rfl rfl
  have hcomm : ⁅V, V⁆ = (⊥ : Subgroup G) := by
    have : IsMulCommutative V := hcyc.isMulCommutative
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer).2 (Subgroup.le_centralizer V)
  rw [hCeq, hcomm, Subgroup.relIndex_bot_left] at hnp
  rw [typeIIILayerOne, hn]
  exact hnp

theorem div_le_div_of_mul_eq_sub_one {n p q u v : ℕ} (hp : 0 < p) (hv : 1 ≤ v)
    (hnp : n * p = v - 1) (hle : (n : ℝ) ≤ ((u : ℝ) - 1) / (q : ℝ)) :
    ((v : ℚ) - 1) / (p : ℚ) ≤ ((u : ℚ) - 1) / (q : ℚ) := by
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  have hv' : ((v : ℚ) - 1) = (n : ℚ) * p := by
    have : ((v - 1 : ℕ) : ℚ) = ((n * p : ℕ) : ℚ) := by rw [hnp]
    push_cast [Nat.cast_sub hv] at this
    linarith
  rw [hv', mul_div_cancel_right₀ _ hpq]
  have : ((n : ℚ) : ℝ) ≤ (((((u : ℚ) - 1) / (q : ℚ)) : ℚ) : ℝ) := by push_cast; exact hle
  exact_mod_cast this

private theorem exists_real_bridge_low_family
    (_h₁ : _root_.CFSG.FeitThompson.Statements.FCH_type_p_actual_bridge_remainder.{u})
    (_h₂ : _root_.CFSG.FeitThompson.Statements.FNI_type_p_elementary_core_structure.{u})
    (_h₃ : _root_.CFSG.FeitThompson.Statements.FNI_type_p_prime_factors.{u})
    (_h₄ : _root_.CFSG.FeitThompson.Statements.FPF_type_iii_full_support_ti_induction.{u})
    (_h₅ : _root_.CFSG.FeitThompson.Statements.FPF_type_iii_iv_core_elementary_chief_kernel_trivial.{u})
    (_h₆ : _root_.CFSG.FeitThompson.Statements.FPF_type_iii_iv_second_derived_fitting.{u})
    (_h₇ : _root_.CFSG.FeitThompson.Statements.FPF_type_iii_v_extended_dade_support.{u})
    (_h₈ : _root_.CFSG.FeitThompson.Statements.FPF_type_iii_v_induced_family_noncoherence.{u})
    (_h₉ : _root_.CFSG.FeitThompson.Statements.FPF_type_iii_v_second_factor_prime.{u})
    {G : Type u} [Group G] [Fintype G] (_hG : CFSG.FeitThompson.Prep06.IsMinimalOddSimple G)
    {S T U V W₁ W₂ : Subgroup G} (_hS : IsCoatom S) (_hT : IsCoatom T)
    (_hcS : IsWitnessedPConfiguration S U W₁ W₂) (_hcT : IsWitnessedPConfiguration T V W₂ W₁)
    (_hqp : Nat.card W₁ < Nat.card W₂) (_hIII : IsTypeIII T) :
    ∃ θ Γ : G → ℂ, ∃ v : Fin (Nat.card (typeIIILayerOne T V)) → G → ℂ,
      θ ∈ signedIrr G ∧ (θ ≠ fun x => conj (θ x)) ∧ IsOrthogonal θ (1 : G → ℂ) ∧
      Γ ∈ Submodule.span ℤ (Irr G) ∧ (∀ g, (Γ g).im = 0) ∧ IsOrthogonal Γ (1 : G → ℂ) ∧
      cfInner ((1 : G → ℂ) - θ + Γ) ((1 : G → ℂ) - θ + Γ) =
        ((((Nat.card U : ℝ) - 1) / (Nat.card W₁ : ℝ) : ℝ) : ℂ) + 2 ∧
      IsOrthonormalFamily v ∧ (∀ i, v i ∈ signedIrr G) ∧
      (∀ i, IsOrthogonal (v i) (1 : G → ℂ)) ∧ (∀ i, IsOrthogonal (v i) θ) ∧
      (∀ i, IsOrthogonal (v i) fun x => conj (θ x)) ∧
      ∀ i, ∃ Δ : G → ℂ, Δ ∈ Submodule.span ℤ (Irr G) ∧ (∀ g, (Δ g).im = 0) ∧
        IsOrthogonal Δ (1 : G → ℂ) ∧
        IsOrthogonal ((1 : G → ℂ) - v i + Δ) ((1 : G → ℂ) - θ + Γ) ∧
        IsOrthogonal ((1 : G → ℂ) - v i + Δ) θ := by
  classical
  have hodd := _hG.odd
  have hfin : Finite G := Finite.of_fintype G
  have hW' : IsCyclicTIPair (W₂ ⊔ W₁) W₂ W₁ := CrossedRowData.isCyclicTIPair_sup hodd _hcT
  obtain ⟨τ', hτ'⟩ := hW'.exists_isCyclicTIIsometry
  obtain ⟨j₀, hj₀, Γ, hΓspan, hΓreal, hΓ1, hBnorm, hBsupp⟩ :=
    RealBridgeLowFamily.exists_bridge_of_actualBridgeRemainder _h₁ _hG _hS _hcS hW' hτ'
  set θ := hW'.prodCharEta τ' j₀ (principalIrr ↥W₁) with hθdef
  obtain ⟨v, hvon, hvsigned, hvη, hbr⟩ :=
    RealBridgeLowFamily.exists_low_family_of_typeIII _h₄ _h₅ _h₆ _h₇ _h₈ _h₉ _hG _hT _hIII _hcT
      hW' hτ'
  rw [typeIIILayerOne_eq]
  have h1η : (1 : G → ℂ) = hW'.prodCharEta τ' (principalIrr ↥W₂) (principalIrr ↥W₁) :=
    (hW'.prodCharEta_principal hτ').symm
  obtain ⟨k, hk, -, -⟩ := hW'.exists_conj_index_left hj₀
  have hθbar : (fun x => conj (θ x)) = hW'.prodCharEta τ' k (principalIrr ↥W₁) :=
    hW'.conj_prodCharEta_row hτ' hk
  have hG5 := isMinimalSimpleOdd_of_isMinimalOddSimple _hG
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hHcard, -⟩ :=
    _h₂ G hG5 S U W₁ W₂ _hS _hcS (Nat.card W₂) (Nat.card W₁) rfl rfl
  have hcop : (Nat.card W₂).Coprime (Nat.card (⁅T, T⁆ : Subgroup G)) :=
    _hcT.coprime_natCard_W₁_natCard_commutator
  refine ⟨θ, Γ, v, hW'.prodCharEta_mem_signedIrr hτ' _ _,
    Ne.symm (hW'.conj_prodCharEta_row_ne hτ' hj₀), ?_, hΓspan, hΓreal,
    isOrthogonal_iff.2 hΓ1, hBnorm, hvon, hvsigned,
    fun i => by rw [h1η]; exact hvη i _ _, fun i => hvη i _ _,
    fun i => by rw [hθbar]; exact hvη i _ _, fun i => ?_⟩
  · rw [isOrthogonal_iff, h1η, hθdef, hW'.cfInner_prodCharEta hτ']
    simp [hj₀]
  obtain ⟨Δ, hΔspan, hΔreal, hΔ1, hβη, hβsupp⟩ := hbr i
  refine ⟨Δ, hΔspan, hΔreal, hΔ1, ?_, ?_⟩
  ·
    rw [isOrthogonal_iff, cfInner_def]
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun x _ => ?_)
    by_cases hx : ((1 : G → ℂ) - v i + Δ) x = 0
    · rw [hx, zero_mul]
    · obtain ⟨c, hc, hxc⟩ := hβsupp x hx
      have hBx : ((1 : G → ℂ) - θ + Γ) x = 0 := by
        refine hBsupp x fun a ha hxa => ?_
        exact RealBridgeLowFamily.not_isConj_of_mem_mixedSupport _hcS hHcard hcop ha hc
          (hxa.symm.trans hxc)
      rw [hBx, map_zero, mul_zero]
  ·
    rw [isOrthogonal_iff, hβη, if_neg hj₀]

private theorem reciprocalTypeThreeLowFamilyBound_residual
    (_h₁ : _root_.CFSG.FeitThompson.Statements.FCH_type_p_actual_bridge_remainder.{u})
    (_h₂ : _root_.CFSG.FeitThompson.Statements.FNI_type_p_elementary_core_structure.{u})
    (_h₃ : _root_.CFSG.FeitThompson.Statements.FNI_type_p_prime_factors.{u})
    (_h₄ : _root_.CFSG.FeitThompson.Statements.FPF_type_iii_full_support_ti_induction.{u})
    (_h₅ : _root_.CFSG.FeitThompson.Statements.FPF_type_iii_iv_core_elementary_chief_kernel_trivial.{u})
    (_h₆ : _root_.CFSG.FeitThompson.Statements.FPF_type_iii_iv_second_derived_fitting.{u})
    (_h₇ : _root_.CFSG.FeitThompson.Statements.FPF_type_iii_v_extended_dade_support.{u})
    (_h₈ : _root_.CFSG.FeitThompson.Statements.FPF_type_iii_v_induced_family_noncoherence.{u})
    (_h₉ : _root_.CFSG.FeitThompson.Statements.FPF_type_iii_v_second_factor_prime.{u}) :
    _root_.CFSG.FeitThompson.Statements.FPF_reciprocal_type_three_low_family_bound.{u} := by
  classical
  intro G _ _ hG S T U V W₁ W₂ hS hT hcS hcT p q u v hp hq hu hv hqp hIII
  have _ : Fintype G := Fintype.ofFinite G
  have hG6 : CFSG.FeitThompson.Prep06.IsMinimalOddSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  subst hp hq hu hv
  obtain ⟨θ, Γ, w, hθ, hθnr, hθ1, hΓ, hΓreal, hΓ1, hB, hw, hwmem, hw1, hwθ, hwθbar, hbr⟩ :=
    exists_real_bridge_low_family _h₁ _h₂ _h₃ _h₄ _h₅ _h₆ _h₇ _h₈ _h₉ hG6 hS hT hcS hcT hqp hIII
  have hr : (0 : ℝ) ≤ ((Nat.card U : ℝ) - 1) / (Nat.card W₁ : ℝ) := by
    have : (1 : ℝ) ≤ Nat.card U := by exact_mod_cast Nat.card_pos
    exact div_nonneg (by linarith) (Nat.cast_nonneg _)
  have hbound := (real_bridge_odd_family_bound hG.odd_natCard hθ hθnr hθ1 hΓ hΓreal hΓ1 hr hB
    hw hwmem hw1 hwθ hwθbar hbr).2
  rw [Fintype.card_fin] at hbound
  exact div_le_div_of_mul_eq_sub_one Nat.card_pos Nat.card_pos
    (natCard_typeIIILayerOne_mul_eq _h₅ _h₆ _h₇ _h₈ _h₉ hG6 hT hIII hcT) hbound

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

universe u

theorem FPF_reciprocal_type_three_low_family_bound
    (h₁ : Statements.FCH_type_p_actual_bridge_remainder.{u})
    (h₂ : Statements.FNI_type_p_elementary_core_structure.{u})
    (h₃ : Statements.FNI_type_p_prime_factors.{u})
    (h₄ : Statements.FPF_type_iii_full_support_ti_induction.{u})
    (h₅ : Statements.FPF_type_iii_iv_core_elementary_chief_kernel_trivial.{u})
    (h₆ : Statements.FPF_type_iii_iv_second_derived_fitting.{u})
    (h₇ : Statements.FPF_type_iii_v_extended_dade_support.{u})
    (h₈ : Statements.FPF_type_iii_v_induced_family_noncoherence.{u})
    (h₉ : Statements.FPF_type_iii_v_second_factor_prime.{u}) :
    Statements.FPF_reciprocal_type_three_low_family_bound.{u} :=
  CFSG.FeitThompson.reciprocalTypeThreeLowFamilyBound_residual
    h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉

end CFSG.FeitThompson.Proofs

end
