module

public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.PairedSupportingCrossedAlternatives
import CFSG.FeitThompson.Local.PairedFullSupportForcesFieldAction
import CFSG.FeitThompson.Local.TypePFieldInnerComplementOrder
import CFSG.FeitThompson.Local.TypePInnerActionFaithful
import CFSG.FeitThompson.Local.PCoreLinearAlternativePConfiguration
import CFSG.FeitThompson.Local.AllTypeIKernelPartition
import CFSG.FeitThompson.Representations.FixedPointFreeComplementOrderBounds
import CFSG.FeitThompson.OddOrder.GeometricSumCongruences
import CFSG.FeitThompson.OddOrder.FinalAlternativeFullNormQuotient
import CFSG.FeitThompson.OddOrder.MobiusNormIteration

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace PairedSupportingInnerNorm

open Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
open CFSG.FeitThompson.Prep05

variable {G : Type*} [Group G]

theorem isIrreducibleLinear_map_of_conj_minimal {S U H : Subgroup G}
    (hHS : S ≤ normalizer (H : Set G)) {p : ℕ} {Vm : Type*} [AddCommGroup Vm]
    [Module (ZMod p) Vm] {e : ↥H ≃* Multiplicative Vm} {ρ : ↥S →* (Vm ≃ₗ[ZMod p] Vm)}
    (hρ : IsConjModule p H S Vm e ρ) (hUS : U ≤ S)
    (hmin : ∀ K : Subgroup G, K ≤ H → (∀ x ∈ U, ∀ z ∈ K, x * z * x⁻¹ ∈ K) → K = ⊥ ∨ K = H) :
    IsIrreducibleLinear ((U.subgroupOf S).map ρ) := by
  intro W hW
  have hinv : ∀ x ∈ U, ∀ z ∈ CFSG.FeitThompson.Proofs.subgroupOfSubmodule e W,
      x * z * x⁻¹ ∈ CFSG.FeitThompson.Proofs.subgroupOfSubmodule e W := by
    intro x hx z hz
    obtain ⟨hzH, hzW⟩ := CFSG.FeitThompson.Proofs.mem_subgroupOfSubmodule.1 hz
    refine CFSG.FeitThompson.Proofs.mem_subgroupOfSubmodule.2
      ⟨CFSG.FeitThompson.Proofs.conj_mem_of_le_normalizer hHS (hUS hx) hzH, ?_⟩
    rw [← CFSG.FeitThompson.Proofs.toAdd_e_conj hρ hHS ⟨x, hUS hx⟩ ⟨z, hzH⟩]
    exact hW _ (Subgroup.mem_map.2 ⟨⟨x, hUS hx⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩) _ hzW
  rcases hmin _ (CFSG.FeitThompson.Proofs.subgroupOfSubmodule_le e W) hinv with hK | hK
  · exact Or.inl (CFSG.FeitThompson.Proofs.subgroupOfSubmodule_eq_bot_iff.1 hK)
  · exact Or.inr (CFSG.FeitThompson.Proofs.subgroupOfSubmodule_eq_top_iff.1 hK)

theorem forall_conjSubgroup_le_of_forall_conj_mem {U K : Subgroup G}
    (hinv : ∀ x ∈ U, ∀ z ∈ K, x * z * x⁻¹ ∈ K) :
    ∀ u ∈ U, _root_.CFSG.FeitThompson.conjSubgroup K u ≤ K := by
  intro u hu x hx
  have hx' : u * x * u⁻¹ ∈ K := _root_.CFSG.FeitThompson.mem_conjSubgroup'.1 hx
  have h2 := hinv u⁻¹ (U.inv_mem hu) _ hx'
  rwa [show u⁻¹ * (u * x * u⁻¹) * u⁻¹⁻¹ = x by group] at h2

theorem natCard_dvd_natCard_sub_one_of_free [Finite G] {A B : Subgroup G}
    (hnorm : B ≤ normalizer (A : Set G)) (hfree : IsFixedPointFreeOn A B) :
    Nat.card ↥B ∣ Nat.card ↥A - 1 :=
  card_dvd_card_sub_one_of_fixedPointFree (φ := conjOnNormalized A hnorm)
    fun b hb => CFSG.FeitThompson.Proofs.fixedPointFree_conjOnNormalized hnorm hfree b.2
      fun h => hb (Subtype.ext h)

theorem isFixedPointFreeOn_of_centralizer_eq_bot {A B : Subgroup G}
    (h : ∀ b ∈ B, b ≠ 1 → A ⊓ centralizer ({b} : Set G) = ⊥) : IsFixedPointFreeOn A B := by
  intro b hb hb1
  rw [centralizerIn_eq, CFSG.FeitThompson.Proofs.centralizer_zpowers_eq]
  exact h b hb hb1

theorem natCard_mul_relIndex [Finite G] {A B : Subgroup G} (hAB : A ≤ B) :
    Nat.card ↥A * A.relIndex B = Nat.card ↥B := by
  rw [Subgroup.relIndex, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAB).toEquiv]
  exact Subgroup.card_mul_index _

open Finset in
theorem cast_geomSum_mul_sub_one {p q : ℕ} (hp : 1 ≤ p) :
    ((∑ i ∈ range q, p ^ i : ℕ) : ℚ) * ((p : ℚ) - 1) = (p : ℚ) ^ q - 1 := by
  have hcast := congrArg (fun n : ℕ => (n : ℚ)) (sum_range_pow_mul_sub_one (p := p) hp q)
  push_cast [Nat.cast_sub hp] at hcast
  push_cast
  linarith

theorem div_le_sub_one_of_sub_one_le_mul {v k : ℕ} (hk : 0 < k) (h : v - 1 ≤ k * (k - 1)) :
    (v - 1) / k ≤ k - 1 := by
  calc (v - 1) / k ≤ (k * (k - 1)) / k := Nat.div_le_div_right h
    _ = k - 1 := Nat.mul_div_cancel_left _ hk

end PairedSupportingInnerNorm

end

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

public section

open Subgroup CFSG.FeitThompson
open CFSG.FeitThompson.PairedSupportingInnerNorm
open CFSG.FeitThompson.Prep05

universe u

theorem FNI_paired_supporting_inner_full_norm_order
    (h₁ : Statements.FCH_actual_type_I_crossed_control.{u})
    (h₂ : Statements.FCH_type_p_action_kernel_ratio.{u})
    (h₃ : Statements.FNI_paired_supporting_maxima_nonconjugate.{u})
    (h₄ : Statements.FNI_type_p_elementary_core_structure.{u})
    (h₅ : Statements.FTS_type_II_extended_support_ti.{u}) :
    Statements.FNI_paired_supporting_inner_full_norm_order.{u} := by
  intro G _ _ hG S T L U V W₁ W₂ y hsetup hIL heL M hM hIM hHM heM νL φL βL hLdata νM φM βM hMdata
  have hG5 : IsMinimalSimpleOdd G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  set p := Nat.card ↥W₂ with hp
  set q := Nat.card ↥W₁ with hq
  obtain ⟨-, hpp, hqq, hop, hoq, -, -, -, -, hsemiUW, -, hfreeUW, hmod, -⟩ :=
    h₄ G hG5 S U W₁ W₂ hsetup.isCoatom_S hsetup.config_S p q rfl rfl
  have hqp : q < p := hsetup.natCard_lt
  obtain ⟨Vm, _, _, -, ⟨e⟩⟩ := hmod
  have hHS : S ≤ normalizer ((hallCoreOf S : Subgroup G) : Set G) :=
    le_normalizer_map_subtype_hallCore S
  have hρ := isConjModule_conjLinear p hHS e
  have hminK : ∀ K : Subgroup G, K ≤ hallCoreOf S →
      (∀ x ∈ U, ∀ z ∈ K, x * z * x⁻¹ ∈ K) → K = ⊥ ∨ K = hallCoreOf S := fun K hK hinv =>
    FNI_paired_full_support_forces_field_action.{u} h₂ h₄ h₅ G hG S T L U V W₁ W₂ y hsetup
      K hK (forall_conjSubgroup_le_of_forall_conj_mem hinv)
  have hirr := isIrreducibleLinear_map_of_conj_minimal hHS hρ hsetup.config_S.le_M_E hminK
  obtain ⟨-, hqdvd, hqndvd⟩ :=
    FNI_type_p_field_inner_complement_order.{u, u} h₂ h₄ G hG5 S U W₁ W₂ hsetup.isCoatom_S
      hsetup.config_S p q ((p ^ q - 1) / (p - 1)) rfl rfl rfl Vm e _ hρ hirr
  set N : ℕ := ∑ i ∈ Finset.range q, p ^ i with hN
  have hNeq : (p ^ q - 1) / (p - 1) = N := eq_geomSum_of_eq_div hpp rfl
  have horder : Nat.card ↥U = N ∨ (p ≡ 1 [MOD q] ∧ q * Nat.card ↥U = N) := by
    by_cases hd : q ∣ p - 1
    · obtain ⟨hqN, hu⟩ := hqdvd hd
      rw [hNeq] at hqN hu
      exact Or.inr ⟨((Nat.modEq_iff_dvd' hpp.one_le).2 hd).symm,
        by rw [hu, Nat.mul_div_cancel' hqN]⟩
    · exact Or.inl (by rw [← hNeq]; exact hqndvd hd)
  set H : Subgroup G := CFSG.FeitThompson.hallCoreIn L with hHdef
  have hUH : U ≤ H := hsetup.le_hallCoreIn_L
  have hux : Nat.card ↥U * U.relIndex H = Nat.card ↥H := natCard_mul_relIndex hUH
  have hHodd : Odd (Nat.card ↥H) :=
    hG.odd_natCard.of_dvd_nat (Subgroup.card_subgroup_dvd_card H)
  have hxodd : Odd (U.relIndex H) := hHodd.of_dvd_nat ⟨Nat.card ↥U, by rw [← hux]; ring⟩
  have hEnorm : (W₁ ⊔ CFSG.FeitThompson.conjSubgroup W₂ y) ≤ normalizer (H : Set G) :=
    hsetup.isInternalSemidirectProduct.right_le.trans
      hsetup.isInternalSemidirectProduct.le_normalizer
  have hEfree : IsFixedPointFreeOn H (W₁ ⊔ CFSG.FeitThompson.conjSubgroup W₂ y) :=
    isFixedPointFreeOn_of_centralizer_eq_bot hsetup.centralizer_eq_bot
  have hEcard : Nat.card ↥(W₁ ⊔ CFSG.FeitThompson.conjSubgroup W₂ y : Subgroup G) = p * q := by
    rw [← relIndex_eq_natCard_of_isInternalSemidirectProduct
      hsetup.isInternalSemidirectProduct]
    exact heL
  have hpqdvd : p * q ∣ Nat.card ↥H - 1 := by
    rw [← hEcard]; exact natCard_dvd_natCard_sub_one_of_free hEnorm hEfree
  have hHpos : 0 < Nat.card ↥H := Nat.card_pos
  have hhp : Nat.card ↥H ≡ 1 [MOD p] :=
    ((Nat.modEq_iff_dvd' hHpos).2 (dvd_trans (Dvd.intro q rfl) hpqdvd)).symm
  have hhq : Nat.card ↥H ≡ 1 [MOD q] :=
    ((Nat.modEq_iff_dvd' hHpos).2 (dvd_trans (Dvd.intro_left p rfl) hpqdvd)).symm
  have huq : Nat.card ↥U ≡ 1 [MOD q] :=
    ((Nat.modEq_iff_dvd' Nat.card_pos).2 (natCard_dvd_natCard_sub_one_of_free
      (le_sup_right.trans hsemiUW.le_normalizer) hfreeUW)).symm
  have hbound : (Nat.card ↥H - 1) / (p * q) ≤ p * q - 1 ∨ (q = 3 ∧ p = 5) := by
    rcases FNI_paired_supporting_crossed_alternatives.{u} h₁ h₂ h₃ h₄ G hG S T L U V W₁ W₂ y
      hsetup hIL heL M hM hIM hHM heM νL φL βL hLdata νM φM βM hMdata with ⟨-, hb⟩ | ⟨-, h3, h5⟩
    · refine Or.inl (div_le_sub_one_of_sub_one_le_mul (Nat.mul_pos hpp.pos hqq.pos) ?_)
      refine sub_one_le_mul_of_div_le (Nat.mul_pos hpp.pos hqq.pos) Nat.card_pos ?_
      push_cast
      exact hb
    · exact Or.inr ⟨h3, h5⟩
  have hu : Nat.card ↥U = N :=
    eq_geomSum_of_order_alternatives hpp hqq hop hoq hqp hxodd hux.symm hhp hhq huq horder hbound
  have hp1 : (1 : ℚ) < (p : ℚ) := by exact_mod_cast hpp.one_lt
  rw [hu, eq_div_iff (by linarith)]
  exact cast_geomSum_mul_sub_one hpp.one_le

end

end CFSG.FeitThompson.Proofs
