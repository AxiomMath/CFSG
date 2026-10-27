module

public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.PairedFullSupportInnerNotCharacteristic
import CFSG.FeitThompson.Local.TypePFieldInnerComplementOrder
import CFSG.FeitThompson.Local.TypePReducibleInnerActionOrder
import CFSG.FeitThompson.Local.OddFrobeniusComplementPrimeSubgroupsNormal
import CFSG.FeitThompson.OddOrder.LocalTypesConjugationInvariant

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace PairedSupportingMaximaNonconjugate

open Subgroup CFSG.FeitThompson.Prep05

universe u

variable {G : Type u} [Group G]

theorem hallCoreIn_conjSubgroup (M : Subgroup G) (g : G) :
    _root_.CFSG.FeitThompson.hallCoreIn (_root_.CFSG.FeitThompson.conjSubgroup M g)
      = _root_.CFSG.FeitThompson.conjSubgroup (_root_.CFSG.FeitThompson.hallCoreIn M) g := by
  rw [_root_.CFSG.FeitThompson.hallCoreIn_eq, _root_.CFSG.FeitThompson.hallCoreIn_eq,
    _root_.CFSG.FeitThompson.conjSubgroup_eq, _root_.CFSG.FeitThompson.conjSubgroup_eq]
  exact map_subtype_hallCore_of_eq (MulAut.conj g⁻¹) rfl

theorem isCyclic_conjSubgroup {Y : Subgroup G} (hY : IsCyclic ↥Y) (g : G) :
    IsCyclic ↥(_root_.CFSG.FeitThompson.conjSubgroup Y g) := by
  rw [_root_.CFSG.FeitThompson.conjSubgroup_eq]
  exact (isCyclic_map_conj_iff Y g⁻¹).2 hY

theorem isCyclic_reciprocal_complement
    (h₁ : _root_.CFSG.FeitThompson.Statements.FCH_type_p_action_kernel_ratio.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_type_p_elementary_core_structure.{u})
    [Finite G] (hG : IsMinimalSimpleOdd G)
    (T V W₁ W₂ : Subgroup G) (hT : IsCoatom T)
    (hcT : IsWitnessedPConfiguration T V W₂ W₁)
    (hqp : Nat.card ↥W₁ < Nat.card ↥W₂) :
    IsCyclic ↥V := by
  set q := Nat.card ↥W₁ with hq
  set p := Nat.card ↥W₂ with hp
  obtain ⟨-, hqq, -, hoq, -, -, -, -, -, -, -, -, hmod, -⟩ :=
    h₂ G hG T V W₂ W₁ hT hcT q p rfl rfl
  have hq3 : 3 ≤ q := hqq.odd_iff.mp hoq
  obtain ⟨Vt, hVadd, hVmod, -, ⟨e⟩⟩ := hmod
  have hTnorm : T ≤ normalizer ((hallCoreOf T : Subgroup G) : Set G) :=
    le_normalizer_map_subtype_hallCore T
  have hρ := isConjModule_conjLinear q hTnorm e
  have hirr : IsIrreducibleLinear ((V.subgroupOf T).map (conjLinear q hTnorm e)) := by
    by_contra hcon
    rw [IsIrreducibleLinear] at hcon
    push Not at hcon
    obtain ⟨W, hWinv, hWne⟩ := hcon
    obtain ⟨hp3, -⟩ := _root_.CFSG.FeitThompson.Proofs.FNI_type_p_reducible_inner_action_order.{u, u}
      h₁ h₂ G hG T V W₂ W₁ hT hcT q p rfl rfl Vt e (conjLinear q hTnorm e) hρ
      ⟨W, hWne.1, hWne.2, hWinv⟩
    omega
  obtain ⟨hcyc, -⟩ := _root_.CFSG.FeitThompson.Proofs.FNI_type_p_field_inner_complement_order.{u, u}
    h₁ h₂ G hG T V W₂ W₁ hT hcT q p ((q ^ p - 1) / (q - 1)) rfl rfl rfl Vt e
    (conjLinear q hTnorm e) hρ hirr
  exact hcyc

end PairedSupportingMaximaNonconjugate

end

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

public section

open Subgroup CFSG.FeitThompson
open CFSG.FeitThompson.PairedSupportingMaximaNonconjugate
open CFSG.FeitThompson.Prep05

universe u

theorem FNI_paired_supporting_maxima_nonconjugate
    (h₁ : Statements.FCH_type_p_action_kernel_ratio.{u})
    (h₂ : Statements.FNI_type_p_elementary_core_structure.{u})
    (h₃ : Statements.FTS_type_II_extended_support_ti.{u}) :
    Statements.FNI_paired_supporting_maxima_nonconjugate.{u} := by
  intro G _ _ hG S T L U V W₁ W₂ y hsetup M hM hHM g hLM
  have hG5 : IsMinimalSimpleOdd G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hVcyc : IsCyclic ↥V :=
    isCyclic_reciprocal_complement h₁ h₂ hG5 T V W₁ W₂ hsetup.isCoatom_T hsetup.config_T
      hsetup.natCard_lt
  have hHL : _root_.CFSG.FeitThompson.hallCoreIn L = _root_.CFSG.FeitThompson.conjSubgroup V g := by
    rw [hLM, hallCoreIn_conjSubgroup, hHM]
  have hcyc : IsCyclic ↥(_root_.CFSG.FeitThompson.hallCoreIn L) := by
    rw [hHL]; exact isCyclic_conjSubgroup hVcyc g
  have hchar : (U.subgroupOf (_root_.CFSG.FeitThompson.hallCoreIn L)).Characteristic :=
    characteristic_of_isCyclic _
  exact FNI_paired_full_support_inner_not_characteristic h₁ h₂ h₃ G hG S T L U V W₁ W₂ y hsetup
    hchar

end

end CFSG.FeitThompson.Proofs
