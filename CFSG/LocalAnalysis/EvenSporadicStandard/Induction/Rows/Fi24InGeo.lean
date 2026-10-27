module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi24InGeneric
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi24InLocal39
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi24InPinned
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Fi24RowEdge
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Fi24RowUMoves
public import CFSG.Fischer.Uniq.F23Uniq
public import CFSG.Sporadic.Fi24.Generate
public import CFSG.Sporadic.Fi24.Involutions
public import CFSG.Adapters.GeneralizedFitting
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.TBLitPropC
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rows
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi24Common
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Mult
public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.Dichotomy
public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.Input
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.CenterAt
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobBalance
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobFactor
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobSetting
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocGen
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Out1SlimEquiv
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.OuterRowFusion
public import CFSG.LocalAnalysis.OddStandard.SmallF3Interfaces
public import CFSG.LocalAnalysis.SectionRank.KGroupSectionClosure
public import CFSG.Open.MonsterY443Defs
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Co1Base
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyFixedSet
public import CFSG.Sporadic.ThSchreier.AutCore
public import CFSG.Walter.JRFacts
public import Certificates.Certificate3085Base

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Sporadic CFSG.Blueprint.Fischer CFSG.Sporadic.Fi24
open CFSG.Fischer hiding OutTwo
open CFSG.EvenSporadicStandard.Solomon78 CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.Solomon78.Fi24Row (edge_hW LE_trans_W mem_LE_iff)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


noncomputable abbrev fi24inK : Subgroup J := centralizer ({tJ} : Set J) ⊓ M

theorem mem_fi24inK_iff {k : J} :
    k ∈ fi24inK ↔ jR k * (tR * xb) = (tR * xb) * jR k ∧ jR k * tR = tR * jR k := by
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, ← commute_tR_iff]
  refine and_congr ?_ Iff.rfl
  rw [← jR_tJ, ← map_mul, ← map_mul]
  exact ⟨fun h => congrArg jR h, fun h => jR_injective h⟩

local notation "W" => (LocalClass D24 tR ∩ LocalClass D24 xb)

theorem fi24in_conj_mem_W {g : R} (hg : g * (tR * xb) = (tR * xb) * g) {w : R} (hw : w ∈ W) :
    g * w * g⁻¹ ∈ W := by
  obtain ⟨ψ, hψc, -⟩ := edgeLocal_of_localPoints pair_R Fi23.pair_J Fi22.pair_D
    localPoints_D24 (Fi23.localPoints_D23 CFSG.Fischer.polarFacts) ⟨tR, tR_mem_D24⟩
    ⟨xb, xb_mem_D24⟩ tR_ne_xb tR_xb_comm
  exact conj_mem_edge pair_R Fi22.pair_D tR_mem_D24 xb_mem_D24 tR_ne_xb tR_xb_comm ψ hψc
    Fi22.center_eq_bot hg hw

noncomputable def fi24inConj (k : ↥fi24inK) (w : ↥W) : ↥W :=
  ⟨jR (k : J) * (w : R) * (jR (k : J))⁻¹, fi24in_conj_mem_W (mem_fi24inK_iff.1 k.2).1 w.2⟩

theorem fi24inConj_val (k : ↥fi24inK) (w : ↥W) :
    (fi24inConj k w : R) = jR (k : J) * w * (jR (k : J))⁻¹ := by
  simp only [fi24inConj]

@[instance_reducible] noncomputable def fi24inKAction : MulAction ↥fi24inK ↥W where
  smul := fi24inConj
  one_smul w := Subtype.ext (by
    show (fi24inConj 1 w : R) = w
    rw [fi24inConj_val, OneMemClass.coe_one, map_one, one_mul, inv_one, mul_one])
  mul_smul k l w := Subtype.ext (by
    show (fi24inConj (k * l) w : R) = (fi24inConj k (fi24inConj l w) : R)
    rw [fi24inConj_val, fi24inConj_val, fi24inConj_val, Subgroup.coe_mul, map_mul]
    group)

attribute [local instance] fi24inKAction

theorem fi24in_smul_val (k : ↥fi24inK) (w : ↥W) :
    ((k • w : ↥W) : R) = jR (k : J) * w * (jR (k : J))⁻¹ :=
  fi24inConj_val k w

theorem fi24in_commute_smul_iff (k : ↥fi24inK) (p q : ↥W) :
    ((k • p : ↥W) : R) * ((k • q : ↥W) : R) = ((k • q : ↥W) : R) * ((k • p : ↥W) : R) ↔
      (p : R) * q = q * p := by
  rw [fi24in_smul_val, fi24in_smul_val]
  constructor
  · intro h
    have h1 := congrArg (fun x => (jR (k : J))⁻¹ * x * jR (k : J)) h
    simp only [mul_assoc, inv_mul_cancel_left] at h1
    simpa [mul_assoc] using h1
  · intro h
    calc jR (k : J) * (p : R) * (jR (k : J))⁻¹ * (jR (k : J) * (q : R) * (jR (k : J))⁻¹) =
        jR (k : J) * ((p : R) * q) * (jR (k : J))⁻¹ := by group
      _ = jR (k : J) * ((q : R) * p) * (jR (k : J))⁻¹ := by rw [h]
      _ = jR (k : J) * (q : R) * (jR (k : J))⁻¹ * (jR (k : J) * (p : R) * (jR (k : J))⁻¹) := by
        group

theorem fi24in_card_W : Nat.card ↥W = 3510 := by
  obtain ⟨ψ, -, -⟩ := edgeLocal_of_localPoints pair_R Fi23.pair_J Fi22.pair_D
    localPoints_D24 (Fi23.localPoints_D23 CFSG.Fischer.polarFacts) ⟨tR, tR_mem_D24⟩
    ⟨xb, xb_mem_D24⟩ tR_ne_xb tR_xb_comm
  rw [Nat.card_congr ψ, Nat.card_coe_set_eq]
  exact ncard_D

theorem fi24in_card_commuting_W (p : ↥W) :
    Nat.card {q : ↥W // q ≠ p ∧ (p : R) * q = q * p} = 693 := by
  obtain ⟨ψ, hψc, -⟩ := edgeLocal_of_localPoints pair_R Fi23.pair_J Fi22.pair_D
    localPoints_D24 (Fi23.localPoints_D23 CFSG.Fischer.polarFacts) ⟨tR, tR_mem_D24⟩
    ⟨xb, xb_mem_D24⟩ tR_ne_xb tR_xb_comm
  have h1 : Nat.card {q : ↥W // q ≠ p ∧ (p : R) * q = q * p} =
      Nat.card ↥(LocalClass Fi22.D ((ψ p : Fi22.D) : Fi22.J)) := by
    refine Nat.card_congr
      { toFun := fun q => ⟨(ψ q.1 : Fi22.J), (ψ q.1).2,
          fun h => q.2.1 (ψ.injective (Subtype.ext h)), ((hψc q.1 p).1 q.2.2.symm)⟩
        invFun := fun y => ⟨ψ.symm ⟨y.1, y.2.1⟩, fun h => y.2.2.1 (by
            have := congrArg (fun z => ((ψ z : Fi22.D) : Fi22.J)) h
            simpa using this), ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · have h2 := (hψc p (ψ.symm ⟨y.1, y.2.1⟩)).2
      simp only [Equiv.apply_symm_apply] at h2
      exact h2 y.2.2.2.symm
    · intro q
      apply Subtype.ext
      simp
    · intro y
      apply Subtype.ext
      simp
  rw [h1, Nat.card_coe_set_eq]
  exact ncard_localClass_D (ψ p).2

theorem fi24in_tJ_mem_K : tJ ∈ fi24inK := Subgroup.mem_inf.2
  ⟨Subgroup.mem_centralizer_singleton_iff.2 rfl, tJ_mem_M⟩

theorem fi24in_exists_of_mem_LE {ℓ : R} (hℓ : ℓ ∈ Fi24.LE) :
    ∃ k : J, k ∈ fi24inK ∧ jR k = ℓ := by
  obtain ⟨⟨h1, hJ⟩, h2⟩ := mem_LE_iff.1 hℓ
  obtain ⟨k, hk⟩ : ∃ k : J, jR k = ℓ := ⟨⟨(ℓ : GL (Fin 781) (ZMod 3)), (mem_JR_iff ℓ).1 hJ⟩,
    Subtype.ext rfl⟩
  exact ⟨k, mem_fi24inK_iff.2 ⟨by rw [hk]; exact h1, by rw [hk]; exact h2⟩, hk⟩

theorem fi24in_jR_mem_LE {k : J} (hk : k ∈ fi24inK) : jR k ∈ Fi24.LE := by
  obtain ⟨h1, h2⟩ := mem_fi24inK_iff.1 hk
  exact mem_LE_iff.2 ⟨⟨h1, jR_mem_JR k⟩, h2⟩

theorem fi24in_center_K {z : J} (hc : ∀ k ∈ fi24inK, z * k = k * z) : z = 1 ∨ z = tJ := by
  have h := fi24in_cent_LE (jR_mem_JR z) (fun ℓ hℓ => by
    obtain ⟨k, hk, rfl⟩ := fi24in_exists_of_mem_LE hℓ
    rw [← map_mul, ← map_mul, hc k hk])
  rcases h with h | h
  · exact Or.inl (jR_injective (by rw [h, map_one]))
  · exact Or.inr (jR_injective (by rw [h, jR_tJ]))

theorem fi24in_mem_vCandidates_K_iff {v : J} :
    v ∈ vCandidates fi24inK tJ ↔ v ∈ fi24inK ∧ v ≠ 1 ∧ v ≠ tJ ∧ v * v = 1 := by
  rw [fi24in_mem_vCandidates_iff fi24in_tJ_mem_K]
  constructor
  · rintro ⟨hv, hnc, h2⟩
    have hv2 : v * v = 1 := by
      have := pow_orderOf_eq_one v
      rwa [h2, pow_two] at this
    have hv1 : v ≠ 1 := fun h => by
      rw [h, orderOf_one] at h2
      omega
    refine ⟨hv, hv1, fun h => hnc ?_, hv2⟩
    intro k hk
    rw [h]
    exact (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hk).1).symm
  · rintro ⟨hv, hv1, hvt, hv2⟩
    refine ⟨hv, fun h => ?_, orderOf_eq_prime (by rw [pow_two]; exact hv2) hv1⟩
    rcases fi24in_center_K h with h1 | h1
    · exact hv1 h1
    · exact hvt h1

end CFSG.EvenSporadicStandard.Induction
