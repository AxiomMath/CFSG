module

public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
import CFSG.FeitThompson.Local.OrderedOuterPrimeForcesTypeII
import CFSG.FeitThompson.Representations.PairedSupportingKernelCollapse
import CFSG.FeitThompson.OddOrder.TypeIIntersectionInSupportingKernel

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson.Proofs

open Subgroup CFSG.FeitThompson

universe u

namespace OrderedPairFullComplement

variable {G : Type*} [Group G]

theorem conjSubgroup_eq_self_of_forall_commute {Y : Subgroup G} {y : G}
    (h : ∀ w ∈ Y, y * w = w * y) : _root_.CFSG.FeitThompson.conjSubgroup Y y = Y := by
  ext x
  rw [_root_.CFSG.FeitThompson.mem_conjSubgroup']
  constructor
  · intro hx
    have hc := h _ hx
    have : x = y * x * y⁻¹ := by
      calc x = y⁻¹ * (y * x * y⁻¹) * y := by group
        _ = y⁻¹ * ((y * x * y⁻¹) * y) := by group
        _ = y⁻¹ * (y * (y * x * y⁻¹)) := by rw [hc]
        _ = y * x * y⁻¹ := by group
    rw [this]; exact hx
  · intro hx
    have : y * x * y⁻¹ = x := by
      calc y * x * y⁻¹ = (x * y) * y⁻¹ := by rw [h x hx]
        _ = x := by group
    rw [this]; exact hx

theorem conjSubgroup_sup (Y Z : Subgroup G) (g : G) :
    _root_.CFSG.FeitThompson.conjSubgroup (Y ⊔ Z) g =
      _root_.CFSG.FeitThompson.conjSubgroup Y g ⊔ _root_.CFSG.FeitThompson.conjSubgroup Z g := by
  rw [_root_.CFSG.FeitThompson.conjSubgroup_eq, _root_.CFSG.FeitThompson.conjSubgroup_eq,
    _root_.CFSG.FeitThompson.conjSubgroup_eq, Subgroup.map_sup]

end OrderedPairFullComplement

open OrderedPairFullComplement

theorem FNI_ordered_pair_full_supporting_complement
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_type_II_supporting_maximal_configuration.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FCH_type_I_P_packet_separation.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FCH_type_I_frobenius_coherent_family.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FCH_type_p_actual_bridge_remainder.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FNI_type_p_elementary_core_structure.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FPF_type_iii_iv_core_elementary_chief_kernel_trivial.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FPF_type_iii_iv_second_derived_fitting.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FPF_type_iii_v_extended_dade_support.{u})
    (h₉ : _root_.CFSG.FeitThompson.Statements.FPF_type_iii_v_induced_family_noncoherence.{u})
    (h₁₀ : _root_.CFSG.FeitThompson.Statements.FPF_type_iii_v_second_factor_prime.{u}) :
    _root_.CFSG.FeitThompson.Statements.FNI_ordered_pair_full_supporting_complement.{u} := by
  intro G _ _ hG S T U V W₁ W₂ L hS hT hST hcS hcT hcyc hinf hcov hlt hL hNL
  classical
  have _iF : Fintype G := Fintype.ofFinite G
  have hG2 : CFSG.FeitThompson.IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hG5 : CFSG.FeitThompson.Prep05.IsMinimalSimpleOdd G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hII : IsTypeII S :=
    FNI_ordered_outer_prime_forces_type_II h₅ h₆ h₇ h₈ h₉ h₁₀ G hG S U W₁ W₂ hS hcS hlt
  obtain ⟨hLI, ⟨E, -, hsdE, hfreeE⟩, hUH, hcompl⟩ :=
    h₁ G hG2 S T U V W₁ W₂ hS hT hST hcS hcT hII hcyc hinf
      (fun N hN hNI => (hcov N hN hNI).imp (fun ⟨g, hg⟩ => ⟨g, hg.symm⟩)
        (fun ⟨g, hg⟩ => ⟨g, hg.symm⟩))
      L hL hNL _ _ _ rfl rfl rfl _ _ rfl rfl
  set H := _root_.CFSG.FeitThompson.hallCoreIn L with hHdef
  replace hsdE : FreeCore.IsInternalSemidirectProduct L H E := hsdE
  replace hfreeE : ∀ e ∈ E, e ≠ 1 → H ⊓ centralizer ({e} : Set G) = ⊥ := hfreeE
  replace hUH : U ≤ H := hUH
  replace hcompl : FreeCore.IsInternalSemidirectProduct L H W₁ ∨
      ∃ y ∈ _root_.CFSG.FeitThompson.hallCoreIn T,
        FreeCore.IsInternalSemidirectProduct L H (W₁ ⊔ _root_.CFSG.FeitThompson.conjSubgroup W₂ y) :=
    hcompl
  refine ⟨hII, hLI, hUH, ?_⟩
  obtain ⟨-, hpp, -⟩ :=
    h₅ G hG5 S U W₁ W₂ hS hcS (Nat.card ↥W₂) (Nat.card ↥W₁) rfl rfl
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hcW₂, -, -, -, -, hdpT, habT, -⟩ :=
    h₅ G hG5 T V W₂ W₁ hT hcT (Nat.card ↥W₁) (Nat.card ↥W₂) rfl rfl
  rcases hcompl with hc1 | ⟨y, hyQ, hc2⟩
  ·
    exfalso
    have he : H.relIndex L = Nat.card ↥W₁ :=
      relIndex_eq_natCard_of_isInternalSemidirectProduct hc1
    obtain ⟨I, J, _, _, α, β, i₀, j₀, w, σ, ω, η, δ, μ, γ, bfam, hdata⟩ :=
      PairedSupportingKernel.exists_isPBridgeData hG.odd_natCard hS hcS hL hLI
    have hJ : 1 < Fintype.card J := by
      have h1 := hdata.isIrrIndexing_W₂
      have := hcS.isCyclic_W₂
      rw [Fintype.card_eq_nat_card, ← Nat.card_range_of_injective h1.1, h1.2.1,
        card_Irr_eq_card_of_isMulCommutative]
      exact hpp.one_lt
    obtain ⟨j₁, hj₁⟩ := Fintype.exists_ne_of_one_lt_card hJ j₀
    obtain ⟨⟨ν, hν⟩, ⟨φ, hφ, hφ1⟩, hmain⟩ :=
      FCH_type_I_P_bridge_parity h₂ h₃ h₄ G hG2 S L U W₁ W₂ I J inferInstance inferInstance
        α β i₀ j₀ w σ ω η δ μ γ bfam hdata _ _ _ _ _ rfl rfl rfl rfl rfl
    obtain ⟨-, -, -, -, -, halt, -⟩ := hmain ν hν φ hφ hφ1 _ rfl j₁ hj₁ _ _ rfl rfl
    have he' : CFSG.FeitThompson.hallCoreIndex L = Nat.card ↥W₁ := he
    rw [he'] at halt
    rcases halt with ⟨-, hle⟩ | ⟨-, hle⟩
    ·
      have hle : ((Nat.card ↥H : ℚ) - 1) / (Nat.card ↥W₁ : ℚ) ≤
          ((Nat.card ↥U : ℚ) - 1) / (Nat.card ↥W₁ : ℚ) := hle
      have hq0 : (0 : ℚ) < (Nat.card ↥W₁ : ℚ) := by exact_mod_cast Nat.card_pos
      have hle' : (Nat.card ↥H : ℚ) ≤ (Nat.card ↥U : ℚ) := by
        have := (div_le_div_iff_of_pos_right hq0).1 hle
        linarith
      have hle'' : Nat.card ↥H ≤ Nat.card ↥U := by exact_mod_cast hle'
      have hHU : U = H := Subgroup.eq_of_le_of_card_ge hUH hle''
      have hLS : L ≤ S := by
        rw [← hc1.sup_eq, ← hHU]
        exact sup_le hcS.le_M_E hcS.le_M_W₁
      have hLS' : L = S := ((hL.le_iff.1 hLS).resolve_left hS.1).symm
      obtain ⟨-, -, -, hnot, -⟩ :=
        hII.clauses_of_isWitnessedPConfiguration_of_minimalSimple hG.isSimpleGroup
          hG.not_isMulCommutative hG.odd_natCard hG.isSolvable_of_ne_top hS hcS
      exact hnot (hLS' ▸ hNL)
    ·
      omega
  · refine ⟨y, hyQ, hc2, ?_, ?_⟩
    ·
      intro e he he1
      have heH : e ∉ H := by
        intro heH
        have hmem : e ∈ H ⊓ (W₁ ⊔ _root_.CFSG.FeitThompson.conjSubgroup W₂ y) := ⟨heH, he⟩
        rw [hc2.inf_eq_bot, Subgroup.mem_bot] at hmem
        exact he1 hmem
      have : (H.subgroupOf L).Normal := hsdE.normal_subgroupOf
      exact inf_centralizer_singleton_eq_bot_of_mem_of_notMem (E := E)
        hsdE.coe_eq_mul.symm hsdE.inf_eq_bot hfreeE (hc2.right_le he) heH
    ·
      rw [relIndex_eq_natCard_of_isInternalSemidirectProduct hc2]
      have hW₁Q : W₁ ≤ CFSG.FeitThompson.Prep05.hallCoreOf T := by
        rw [← hcW₂]; exact inf_le_left
      have habF := isMulCommutative_iff_of_setLike.1 habT
      have hPF := hdpT.left_le
      have hyc : ∀ x ∈ W₁, y * x = x * y := fun x hx => habF y (hPF hyQ) x (hPF (hW₁Q hx))
      have heq : W₁ ⊔ _root_.CFSG.FeitThompson.conjSubgroup W₂ y =
          _root_.CFSG.FeitThompson.conjSubgroup (W₁ ⊔ W₂) y := by
        rw [conjSubgroup_sup, conjSubgroup_eq_self_of_forall_commute hyc]
      rw [heq, _root_.CFSG.FeitThompson.natCard_conjSubgroup,
        hcS.isInternalDirectProduct_sup.card_eq_mul, Nat.mul_comm]

end CFSG.FeitThompson.Proofs
