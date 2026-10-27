module

public import CFSG.GH74.GLS.Stage2.Final.L26.Core
public import CFSG.GH74.Generic.OuterInvolution
public import CFSG.GH74.GLS.Stage2.Local.Bar

public section

namespace CFSG.GH74.GLS.Stage2.Final.L26

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Final.Thm4
  CFSG.ComponentClassification.CatalogueBPrimeJoin
open scoped commutatorElement

section GLevel

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G}

theorem exists_conj_ne_of_ctx (h : Stage2Ctx G z k S) : ∃ t ∈ S, IsConj z t ∧ t ≠ z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := (CFSG.ABGLocalTools.isSylowOf_iff).1 h.sylow_top
  have hidx : ¬ 2 ∣ S.index := by
    have := hS.2.2
    rwa [Subgroup.relIndex_top_right] at this
  let P : Sylow 2 G := hS.2.1.toSylow hidx
  have hP : (P : Subgroup G) = S := IsPGroup.toSylow_coe _ _
  have hzP : z ∈ (P : Subgroup G) := hP ▸ h.z_mem
  obtain ⟨g, hgP, hgz⟩ := CFSG.GH74.Generic.exists_conj_in_sylow_ne h.std.kps.1 h.std.kps.2.1
    h.orderOf_z P hzP (fun t ht => h.S_comm_z (hP ▸ ht))
  refine ⟨g⁻¹ * z * g, hP ▸ hgP, ?_, hgz⟩
  exact isConj_iff.2 ⟨g⁻¹, by simp⟩

omit [Finite G] in
theorem le_O2Of_of_perfect [Finite G] {Λ B : Subgroup G} (hperf : Group.IsPerfect ↥Λ) (hΛB : Λ ≤ B) :
    Λ ≤ O2Of B := by
  have : (oResidual 2 ↥B).Normal := oResidual_normal_aux 2 ↥B
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf' : Group.IsPerfect ↥(Λ.subgroupOf B) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hΛB).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hΛB).symm.surjective
  have hle : Λ.subgroupOf B ≤ oResidual 2 ↥B :=
    perfect_le_of_pmod 2 (oResidual 2 ↥B) hperf' fun x _ => exists_pow_mem_oResidual 2 x
  intro x hx
  exact ⟨⟨x, hΛB hx⟩, hle hx, rfl⟩

theorem S_inf_WC_le_pLayerOf (hctx : Stage2Ctx G z k S)
    (h1 : generalizedFitting (CentralizerBar z) ≤ layer (CentralizerBar z)) :
    S ⊓ WC z ≤ pLayerOf 2 (Cen z) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro s ⟨hsS, hsW⟩
  change s ∈ (O22Res ↥(Cen z)).map (Cen z).subtype at hsW
  obtain ⟨w, hw, hws⟩ := hsW
  have hOn : (O22Res ↥(Cen z)).Normal := O22Res_normal
  have hWn : ((O22Res ↥(Cen z)).map (QuotientGroup.mk' (pPrimeCore 2 ↥(Cen z)))).Normal :=
    Subgroup.Normal.map hOn _ (QuotientGroup.mk'_surjective _)
  have hWp : IsPGroup 2 ↥((O22Res ↥(Cen z)).map (QuotientGroup.mk' (pPrimeCore 2 ↥(Cen z)))) := by
    rintro ⟨_, w', hw', rfl⟩
    obtain ⟨a, ha⟩ := exists_pow_mem_pPrimeCore_of_mem_O22Res hw'
    refine ⟨a, Subtype.ext ?_⟩
    change (QuotientGroup.mk' (pPrimeCore 2 ↥(Cen z)) w') ^ (2 ^ a) = 1
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr ha
  have hle : (O22Res ↥(Cen z)).map (QuotientGroup.mk' (pPrimeCore 2 ↥(Cen z))) ≤
      pCore 2 (CentralizerBar z) := le_sSup ⟨hWn, hWp⟩
  have hF : (QuotientGroup.mk' (pPrimeCore 2 ↥(Cen z)) w) ∈ fittingSubgroup (CentralizerBar z) :=
    pCore_le_fitting (CentralizerBar z) 2 (hle ⟨w, hw, rfl⟩)
  have hπw : (QuotientGroup.mk' (pPrimeCore 2 ↥(Cen z)) w) ∈ layer (CentralizerBar z) :=
    h1 (Subgroup.mem_sup_left hF)
  have hπw' : (QuotientGroup.mk' (pPrimeCore 2 ↥(Cen z)) w) ∈
      (pLayer ↥(Cen z) 2).map (QuotientGroup.mk' (pPrimeCore 2 ↥(Cen z))) := by
    rw [CFSG.ComponentClassification.LBalance.Quot.map_pLayer_eq_layer_quotient (H := ↥(Cen z)) (p := 2)]
    exact hπw
  have hwsup : w ∈ pLayer ↥(Cen z) 2 ⊔ pPrimeCore 2 ↥(Cen z) := by
    have h3 : w ∈ ((pLayer ↥(Cen z) 2).map (QuotientGroup.mk' (pPrimeCore 2 ↥(Cen z)))).comap
        (QuotientGroup.mk' (pPrimeCore 2 ↥(Cen z))) := hπw'
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h3
  obtain ⟨a, ha⟩ := hctx.sylow.isPGroup ⟨s, hsS⟩
  have hw2 : w ^ (2 ^ a) = 1 := by
    refine Subtype.ext ?_
    have h3 : s ^ (2 ^ a) = 1 := by simpa using congrArg Subtype.val ha
    rw [← hws] at h3
    simpa using h3
  have : (pLayer ↥(Cen z) 2).Characteristic := pLayer_characteristic
  have hwL : w ∈ pLayer ↥(Cen z) 2 :=
    mem_of_two_pow_of_mem_sup_odd (fun n hn => coprime_orderOf_of_mem_pPrimeCore hn) hwsup hw2
  rw [pLayerOf_eq_map]
  exact ⟨w, hwL, hws⟩

theorem lemma26_of_layer_data (hctx : Stage2Ctx G z k S)
    (h1 : generalizedFitting (CentralizerBar z) ≤ layer (CentralizerBar z))
    (h2 : ∀ K : Subgroup (CentralizerBar z), K.Normal → K ≤ layer (CentralizerBar z) →
      (¬ ∀ x ∈ K, ∀ e ∈ layer (CentralizerBar z), x * e = e * x) → layer (CentralizerBar z) ≤ K)
    (h4 : Nat.card ↥(center ↥(layer (CentralizerBar z))) ≤ 2) : Lemma26 z S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB1 := S_inf_WC_le_pLayerOf hctx h1
  obtain ⟨t, htS, htc, htz⟩ := exists_conj_ne_of_ctx hctx
  have htC : t ∈ Cen z := hctx.S_le_Cen htS
  have hSp : IsPGroup 2 ↥S := hctx.sylow.isPGroup
  have hker : ∀ (u : G) (huS : u ∈ S), toBar z ⟨u, hctx.S_le_Cen huS⟩ = 1 → u = 1 := by
    intro u huS hu1
    have hmem : (⟨u, hctx.S_le_Cen huS⟩ : ↥(Cen z)) ∈ pPrimeCore 2 ↥(Cen z) :=
      (QuotientGroup.eq_one_iff _).mp hu1
    obtain ⟨a, ha⟩ := hSp ⟨u, huS⟩
    have h3 : (⟨u, hctx.S_le_Cen huS⟩ : ↥(Cen z)) ^ (2 ^ a) = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val ha)
    have h5 := eq_one_of_mem_pPrimeCore_of_two_pow hmem h3
    simpa using congrArg Subtype.val h5
  have hz1 : z ≠ 1 := fun h => by
    have := hctx.orderOf_z
    rw [h, orderOf_one] at this
    omega
  have ht1 : t ≠ 1 := fun h => by
    obtain ⟨c, hc⟩ := isConj_iff.mp htc
    apply hz1
    have : z = c⁻¹ * t * c := by rw [← hc]; group
    rw [this, h]
    group
  have hzS : z ∈ S := hctx.z_mem
  have hy1 : toBar z ⟨t, htC⟩ ≠ 1 := fun h => ht1 (hker t htS h)
  have hyz : toBar z ⟨t, htC⟩ ≠ toBar z ⟨z, mem_Cen_self z⟩ := by
    intro h
    apply htz
    have h5 : toBar z ⟨t⁻¹ * z, hctx.S_le_Cen (S.mul_mem (S.inv_mem htS) hzS)⟩ = 1 := by
      have : (⟨t⁻¹ * z, hctx.S_le_Cen (S.mul_mem (S.inv_mem htS) hzS)⟩ : ↥(Cen z)) =
          (⟨t, htC⟩ : ↥(Cen z))⁻¹ * ⟨z, mem_Cen_self z⟩ := rfl
      rw [this, map_mul, map_inv, h, inv_mul_cancel]
    have h6 := hker _ (S.mul_mem (S.inv_mem htS) hzS) h5
    have h7 : t⁻¹ * z = 1 := h6
    rw [inv_mul_eq_one] at h7
    exact h7
  have hzb1 : toBar z ⟨z, mem_Cen_self z⟩ ≠ 1 := fun h => hz1 (hker z hzS h)
  have hnc := not_centralizes_layer h1 h4 (toBar_z_mem_center z) hzb1 hy1 hyz
  have hE := layer_le_commutator h2 hnc
  have hLz := pLayer_le_commutator_of_bar (⟨t, htC⟩ : ↥(Cen z)) hE
  have hLG : pLayerOf 2 (Cen z) ≤ ⁅Cen z, Subgroup.zpowers t⁆ := by
    rw [pLayerOf_eq_map]
    have hmap : (⁅(⊤ : Subgroup ↥(Cen z)), Subgroup.zpowers (⟨t, htC⟩ : ↥(Cen z))⁆).map (Cen z).subtype =
        ⁅Cen z, Subgroup.zpowers t⁆ := by
      rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype, MonoidHom.map_zpowers]
      rfl
    rw [← hmap]
    exact Subgroup.map_mono hLz
  have hperf : Group.IsPerfect ↥(pLayerOf 2 (Cen z)) := by
    rw [pLayerOf_eq_map]
    have : Group.IsPerfect ↥(pLayer ↥(Cen z) 2) :=
      Subgroup.isPerfect_iff.mpr (CFSG.ComponentClassification.UnbalancedCorr.pLayer_two_isPerfect _)
    exact Group.IsPerfect.map _
  have hOle : pLayerOf 2 (Cen z) ≤ O2Of ⁅Cen z, Subgroup.zpowers t⁆ := le_O2Of_of_perfect hperf hLG
  have hH : O2Of ⁅Cen z, Subgroup.zpowers t⁆ ≤
      ⨆ (t : G) (_ : t ∈ S) (_ : IsConj z t), O2Of ⁅Cen z, Subgroup.zpowers t⁆ :=
    le_iSup_of_le t (le_iSup_of_le htS (le_iSup_of_le htc le_rfl))
  exact sup_le (hOle.trans hH) (hB1.trans (hOle.trans hH))

end GLevel

end CFSG.GH74.GLS.Stage2.Final.L26
