module

public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
import CFSG.FeitThompson.Local.TypeIIIIVChiefData
import CFSG.FeitThompson.Representations.TypeThreeFourChiefKernelCentralized
import CFSG.FeitThompson.Local.SigmaCoreComplementFixedInDerived
import CFSG.FeitThompson.Local.SolvableDerivedKernelCommutators
import CFSG.FeitThompson.OddOrder.PConfigCoprimeFrobeniusAction
public import Mathlib.Tactic.ENatToNat

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup CFSG.FeitThompson.Prep05

variable {G : Type*} [Group G] [Finite G] {M U W₁ W₂ : Subgroup G}

theorem centralizerIn_hallCore_le_commutator
    (hc : IsWitnessedPConfiguration M U W₁ W₂) (hsolvM : Group.IsSolvable ↥M)
    (hcop : (Nat.card ↥U).Coprime (Nat.card ↥(hallCoreOf M)))
    (hHle : hallCoreOf M ≤ ⁅(⁅M, M⁆ : Subgroup G), (⁅M, M⁆ : Subgroup G)⁆) :
    centralizerIn (hallCoreOf M) U ≤ ⁅hallCoreOf M, hallCoreOf M⁆ := by
  set K : Subgroup G := ⁅M, M⁆ with hK
  have hKM : K ≤ M := Subgroup.commutator_le_self M
  have hHK : hallCoreOf M ≤ K := by
    rw [hallCoreOf_eq]; exact hc.hallCore_le_commutator
  have hUK : U ≤ K := hc.le_commutator_E
  have hsolvK : Group.IsSolvable ↥K := by
    have := hsolvM; exact isSolvable_of_le hKM
  have hHnormal : ((hallCoreOf M).subgroupOf K).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hHK).2 (hKM.trans ?_)
    rw [hallCoreOf_eq]; exact le_normalizer_map_subtype_hallCore M
  have hsolvH : Group.IsSolvable ↥((hallCoreOf M).subgroupOf K) := isSolvable_of_le le_top
  have hsup : (hallCoreOf M).subgroupOf K ⊔ U.subgroupOf K = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hHK hUK, hallCoreOf_eq, hc.sup_hallCore_E, hK,
      Subgroup.subgroupOf_self]
  have hinf : (hallCoreOf M).subgroupOf K ⊓ U.subgroupOf K = ⊥ := by
    rw [← subgroupOf_inf,
      show hallCoreOf M ⊓ U = ⊥ from (hallCoreOf_eq M ▸ hc.disjoint_hallCore_E).eq_bot,
      Subgroup.bot_subgroupOf]
  have hcommK : (⁅K, K⁆ : Subgroup G).subgroupOf K = _root_.commutator ↥K := by
    rw [← Subgroup.map_subtype_commutator, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
  have hHcomm : (hallCoreOf M).subgroupOf K ≤ _root_.commutator ↥K := by
    rw [← hcommK]; exact Subgroup.subgroupOf_mono K hHle
  have hHKU := eq_commutator_of_isSolvable_of_le_commutator
    ((hallCoreOf M).subgroupOf K) (U.subgroupOf K) hsup hinf hHcomm
  have hcop' : (Nat.card ↥(U.subgroupOf K)).Coprime
      (Nat.card ↥((hallCoreOf M).subgroupOf K)) := by
    rw [natCard_subgroupOf hUK, natCard_subgroupOf hHK]; exact hcop
  have hres := CFSG.FeitThompson.Proofs.inf_centralizer_le_commutator_self_of_eq_commutator hcop' hHKU
  intro x hx
  rw [centralizerIn_eq] at hx
  obtain ⟨hxH, hxc⟩ := Subgroup.mem_inf.1 hx
  have hxK : x ∈ K := hHK hxH
  have hmem : (⟨x, hxK⟩ : ↥K) ∈ (hallCoreOf M).subgroupOf K
      ⊓ centralizer ((U.subgroupOf K : Subgroup ↥K) : Set ↥K) :=
    Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.2 hxH,
      Subgroup.mem_centralizer_iff.2 fun k hk => Subtype.ext
        (Subgroup.mem_centralizer_iff.1 hxc (k : G) (Subgroup.mem_subgroupOf.1 hk))⟩
  have h2 := hres hmem
  rw [commutator_subgroupOf hHK hHK, Subgroup.mem_subgroupOf] at h2
  exact h2

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

open Subgroup CFSG.FeitThompson
open CFSG.FeitThompson.Prep05

universe u

theorem FPF_type_iii_iv_chief_kernel_is_derived
    (hfitting : Statements.FPF_type_iii_iv_second_derived_fitting.{u})
    (hprime : Statements.FPF_type_iii_v_second_factor_prime.{u}) :
    Statements.FPF_type_iii_iv_chief_kernel_is_derived.{u} := by
  intro G _ _ hG M U W₁ W₂ hM htype hc H₀ hH₀ hlayer
  have : Fintype G := Fintype.ofFinite G
  have hG6 : CFSG.FeitThompson.Prep06.IsMinimalOddSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  obtain ⟨-, -, -, -, -, -, -, -, hcopH, -, -, -, -, -, -, hlayers⟩ :=
    FPF_type_iii_iv_chief_data hprime G hG M U W₁ W₂ hM htype hc _ _ rfl rfl
  obtain ⟨⟨-, hcommle, -, -⟩, -⟩ := hlayers H₀ hH₀ hlayer
  have hUH₀ : ⁅U, H₀⁆ = ⊥ :=
    FPF_type_iii_iv_chief_kernel_centralized hprime G hG M U W₁ W₂ hM htype hc H₀ hH₀ hlayer
  obtain ⟨hK'', hsupF, -, -⟩ := hfitting G hG6 M U W₁ W₂ hM htype hc
  have hHleK'' : hallCoreOf M ≤ ⁅(⁅M, M⁆ : Subgroup G), (⁅M, M⁆ : Subgroup G)⁆ := by
    rw [hK'', ← hsupF, CFSG.FeitThompson.Prep06.hallCoreIn_eq, ← hallCoreOf_eq]
    exact le_sup_left
  have hcop : (Nat.card ↥U).Coprime (Nat.card ↥(hallCoreOf M)) :=
    Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le (le_sup_left : U ≤ U ⊔ W₁)) hcopH.symm
  have hsolvM : Group.IsSolvable ↥M := hG.isSolvable_of_ne_top M hM.1
  refine le_antisymm (le_trans ?_ (centralizerIn_hallCore_le_commutator hc hsolvM hcop hHleK''))
    hcommle
  rw [centralizerIn_eq]
  refine le_inf hlayer.2.1.le ?_
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
  exact hUH₀

end CFSG.FeitThompson.Proofs

end
