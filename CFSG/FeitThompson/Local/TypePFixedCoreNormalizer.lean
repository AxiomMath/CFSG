module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
import CFSG.FeitThompson.Local.FaithfulAbelianComplementNormalizerFixedCore
import CFSG.FeitThompson.Local.TypePInnerActionFaithful

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type*} [Group G]

theorem pow_eq_one_multiplicative (p : ℕ) {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (x : Multiplicative V) : x ^ p = 1 := by
  have h : p • Multiplicative.toAdd x = 0 := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod p) p, ZMod.natCast_self, zero_smul]
  apply Multiplicative.toAdd.injective
  simpa using h

theorem isElementaryAbelian_of_mulEquiv_multiplicative {p : ℕ} {A : Subgroup G} {V : Type*}
    [AddCommGroup V] [Module (ZMod p) V] (e : ↥A ≃* Multiplicative V) :
    IsElementaryAbelian p A := by
  refine isElementaryAbelian_iff.2 ⟨IsMulCommutative.of_comm fun x y => e.injective ?_,
    fun x hx => ?_⟩
  · rw [map_mul, map_mul, mul_comm]
  · have h : (⟨x, hx⟩ : ↥A) ^ p = 1 :=
      e.injective (by rw [map_pow, map_one, pow_eq_one_multiplicative])
    simpa using congrArg Subtype.val h

end

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

public section

open Subgroup CFSG.FeitThompson
open CFSG.FeitThompson.Prep05

universe u

theorem FBG_type_p_fixed_core_normalizer
    (h₁ : Statements.FCH_type_p_action_kernel_ratio.{u})
    (h₂ : Statements.FNI_type_p_elementary_core_structure.{u}) :
    Statements.FBG_type_p_fixed_core_normalizer.{u} := by
  intro G _ _ hG M U W₁ W₂ hM hc
  have hG' : CFSG.FeitThompson.Prep05.IsMinimalSimpleOdd G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  obtain ⟨-, hpp, -, -, -, -, hUne, hUcomm, hsemi₁, hsemi₂, hcop, hfree,
    hVex, -, -, hcW₁, hHne, -, -, -, -, -, hTIH, -⟩ :=
    h₂ G hG' M U W₁ W₂ hM hc (Nat.card ↥W₂) (Nat.card ↥W₁) rfl rfl
  obtain ⟨hCU, -⟩ := FNI_type_p_inner_action_faithful.{u} h₁ h₂ G hG' M U W₁ W₂ hM hc
  obtain ⟨V, _, _, -, ⟨e⟩⟩ := hVex
  have hnormH : M ≤ normalizer ((hallCoreOf M : Subgroup G) : Set G) :=
    le_normalizer_map_subtype_hallCore M
  have hZ : (hallCoreOf M ⊓ centralizer (W₁ : Set G) : Subgroup G) = W₂ := hcW₁
  have hfix : IsFixedCoreConfig (Nat.card ↥W₂) M (hallCoreOf M) U W₁ := by
    refine
      { prime_p := hpp
        isElementaryAbelian_P := isElementaryAbelian_of_mulEquiv_multiplicative e
        P_ne_bot := hHne
        U_ne_bot := hUne
        isMulCommutative_U := hUcomm
        B_ne_bot := hc.ne_bot_W₁
        isCyclic_B := hc.isCyclic_W₁
        coprime_P := hcop
        coprime_U_B := ?_
        S_le_normalizer_P := hnormH
        sup_eq_S := hsemi₁.sup_eq
        inf_eq_bot := hsemi₁.inf_eq_bot
        B_le_normalizer_U := hc.le_normalizer_E
        U_inf_B_eq_bot := hsemi₂.inf_eq_bot
        inf_centralizer_singleton_eq_bot := ?_
        inf_centralizer_P_eq_bot := hCU
        inf_centralizer_B_ne_bot := ?_
        isTIWithNormalizer_P := hTIH }
    ·
      exact (Nat.Coprime.coprime_dvd_right
        (Subgroup.card_dvd_of_le hc.le_commutator_E)
        hc.coprime_natCard_W₁_natCard_commutator).symm
    ·
      intro b hb hb1
      have h := hfree b hb hb1
      rwa [centralizerIn_eq, centralizer_coe_zpowers] at h
    · rw [hZ]; exact hc.ne_bot_W₂
  refine ⟨?_, ?_, ?_⟩
  ·
    have h := hfix.normalizer_core_eq_centralizer_core
    rwa [hZ] at h
  ·
    have h := hfix.centralizer_core_eq_sup
    rw [hZ] at h
    rw [h]
    exact hfix.coe_sup_P_B
  ·
    exact ⟨rfl, sup_le Subgroup.le_normalizer (hc.le_M_W₁.trans hnormH), hfix.disjoint_P_B⟩

end

end CFSG.FeitThompson.Proofs
