module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1BlockPushUp
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsGroup
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

open scoped Pointwise

namespace CFSG.LocalAnalysis.RankThreeTheoremC.FiveTwentySix

open CFSG.Open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.LocalAnalysis.RankThreeUC.S15 CFSG.QuasithinUnique

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

theorem le_normalizer_iSup {G : Type*} [Group G] {ι : Sort*} {f : ι → Subgroup G}
    {A : Subgroup G} (h : ∀ i, A ≤ Subgroup.normalizer (f i : Set G)) :
    A ≤ Subgroup.normalizer (⨆ i, f i : Subgroup G) :=
  (le_iInf h).trans (Subgroup.iInf_normalizer_le_normalizer_iSup f)

theorem le_normalizer_inf_of_le {G : Type*} [Group G] {A H L : Subgroup G}
    (hH : A ≤ Subgroup.normalizer (H : Set G)) (hL : A ≤ L) :
    A ≤ Subgroup.normalizer (H ⊓ L : Subgroup G) :=
  (le_inf hH (hL.trans Subgroup.le_normalizer)).trans Subgroup.inf_normalizer_le_normalizer_inf

theorem le_normalizer_cgsIn {G : Type*} [Group G] {H S A : Subgroup G}
    (hAH : A ≤ Subgroup.normalizer (H : Set G))
    (hAS : ∀ C : Subgroup G, C ≤ S → C ≠ ⊥ → (C.subgroupOf S).Characteristic →
      A ≤ Subgroup.normalizer (C : Set G)) :
    A ≤ Subgroup.normalizer (CFSG.Quasithin.cgsIn H S : Set G) := by
  unfold CFSG.Quasithin.cgsIn
  refine le_normalizer_iSup fun C => le_normalizer_iSup fun hCS => le_normalizer_iSup fun hC =>
    le_normalizer_iSup fun hchar => ?_
  exact le_normalizer_inf_of_le hAH (hAS C hCS hC hchar)

theorem inf_normalizer_le_cgsIn_of_char {G : Type*} [Group G] {H S C : Subgroup G}
    (hCS : C ≤ S) (hC : C ≠ ⊥) (hchar : (C.subgroupOf S).Characteristic) :
    H ⊓ Subgroup.normalizer (C : Set G) ≤ CFSG.Quasithin.cgsIn H S :=
  le_iSup_of_le C (le_iSup_of_le hCS (le_iSup_of_le hC (le_iSup_of_le hchar le_rfl)))

theorem le_cgsIn_of_normal (hCGT : CFSG.AGLEmbedding.AschbacherLocalCGTBlock)
    (hX : GNSetting X T) {K : Subgroup X} (hK : K.Normal) : K ≤ CFSG.Quasithin.cgsIn K T := by
  classical
  by_cases hT : T = ⊥
  · haveI := hX.subsingleton_of_eq_bot hT
    intro k _
    rw [Subsingleton.elim k 1]
    exact Subgroup.one_mem _
  have hT2 : IsPGroup 2 T := hX.sylow.2.1
  have hTK : T ≤ Subgroup.normalizer (K : Set X) := by
    haveI := hK
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hQD : pCoreOf 2 (⊤ : Subgroup X) ≤ K ⊔ T :=
    (CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf hX.sylow).trans le_sup_right
  have hQcore : pCoreOf 2 (⊤ : Subgroup X) ≤ pCoreOf 2 (K ⊔ T) :=
    CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 _ _ hQD
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hQD).mpr
        (le_top.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2
          (⊤ : Subgroup X))))
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 (⊤ : Subgroup X))
  have hcharD : CharTwo (K ⊔ T) := fun x hx =>
    hQcore (hX.charTwo ⟨Subgroup.mem_top x, Subgroup.centralizer_le hQcore hx.2⟩)
  have hKD : CFSG.Open.IsKGroup ↥(K ⊔ T) :=
    CFSG.KCore.KGroupAllSimple.kGroupNonab (hX.kGroup.subgroup (K ⊔ T))
  have hTD : ¬ 2 ∣ (T.subgroupOf (K ⊔ T)).index := by
    change ¬ 2 ∣ T.relIndex (K ⊔ T)
    intro h2
    have hodd : ¬ 2 ∣ T.relIndex ⊤ := hX.sylow.2.2
    refine hodd ?_
    rw [← Subgroup.relIndex_mul_relIndex T (K ⊔ T) ⊤ le_sup_right le_top]
    exact dvd_mul_of_dvd_left h2 _
  have hcgs : CFSG.Quasithin.cgsIn (K ⊔ T) T = K ⊔ T := by
    by_contra hne
    obtain ⟨Y, hYD, hYsub, hYX, -⟩ :=
      hCGT X (K ⊔ T) T hKD hcharD ⟨le_sup_right, hT2, hTD⟩ hne
    have hYL : Y ≤ K := le_of_le_sup_of_isShort2 hT2 hTK hYD hYX.1.1
    have hYsubK : IsSubnormal Y K := by
      have h := isSubnormal_inf_of_normal hYsub le_sup_left
        (normal_subgroupOf_sup_of_le_normalizer_left hTK)
      rwa [inf_eq_left.mpr hYL] at h
    exact hX.noXBlock Y
      (CFSG.AGLEmbedding.isSubnormal_of_isSubnormal_of_normal hYsubK le_top (hK.subgroupOf ⊤)) hYX
  have hDJ : CFSG.Quasithin.cgsIn (K ⊔ T) T ≤ CFSG.Quasithin.cgsIn K T ⊔ T := by
    unfold CFSG.Quasithin.cgsIn
    refine iSup_le fun C => iSup_le fun hCT => iSup_le fun hC => iSup_le fun hch => ?_
    intro d hd
    obtain ⟨hdD, hdN⟩ := Subgroup.mem_inf.mp hd
    have hdD' : d ∈ ((K : Set X) * (T : Set X)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left K T hTK]
      exact hdD
    obtain ⟨k, hkK, t, htT, hkt⟩ := hdD'
    have htNC : t ∈ Subgroup.normalizer (C : Set X) :=
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hCT).mp (by
        haveI : (C.subgroupOf T).Characteristic := hch
        exact Subgroup.normal_of_characteristic (C.subgroupOf T))) htT
    have hkN : k ∈ Subgroup.normalizer (C : Set X) := by
      let N : Subgroup X := Subgroup.normalizer (C : Set X)
      have htNC' : t ∈ N := htNC
      have hdt : k * t ∈ N := by
        have hkt' : k * t = d := hkt
        rw [hkt']
        exact hdN
      have h := N.mul_mem hdt (N.inv_mem htNC')
      rwa [mul_inv_cancel_right] at h
    have hkJ : k ∈ CFSG.Quasithin.cgsIn K T :=
      inf_normalizer_le_cgsIn_of_char hCT hC hch (Subgroup.mem_inf.mpr ⟨hkK, hkN⟩)
    have hkt' : k * t ∈ CFSG.Quasithin.cgsIn K T ⊔ T :=
      (CFSG.Quasithin.cgsIn K T ⊔ T).mul_mem (Subgroup.mem_sup_left hkJ)
        (Subgroup.mem_sup_right htT)
    rw [← hkt]
    exact hkt'
  have hKJ : K ≤ CFSG.Quasithin.cgsIn K T ⊔ T := by
    have h : K ⊔ T ≤ CFSG.Quasithin.cgsIn K T ⊔ T := by
      rw [← hcgs]
      exact hDJ
    exact le_sup_left.trans h
  have hTJ : T ≤ Subgroup.normalizer (CFSG.Quasithin.cgsIn K T : Set X) :=
    le_normalizer_cgsIn hTK fun C hCT _ hch =>
      (Subgroup.normal_subgroupOf_iff_le_normalizer hCT).mp (by
        haveI : (C.subgroupOf T).Characteristic := hch
        exact Subgroup.normal_of_characteristic (C.subgroupOf T))
  intro k hk
  have hkD : k ∈ CFSG.Quasithin.cgsIn K T ⊔ T := hKJ hk
  have hkD' : k ∈ ((CFSG.Quasithin.cgsIn K T : Set X) * (T : Set X)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left (CFSG.Quasithin.cgsIn K T) T hTJ]
    exact hkD
  obtain ⟨j, hj, t, htT, hjt⟩ := hkD'
  have htK : t ∈ K := by
    have ht : t = j⁻¹ * k := by
      rw [← hjt]
      group
    rw [ht]
    exact K.mul_mem (K.inv_mem ((CFSG.Quasithin.cgsIn_le K T) hj)) hk
  have htJ : t ∈ CFSG.Quasithin.cgsIn K T :=
    CFSG.Quasithin.inf_normalizer_le_cgsIn (H := K) (S := T) hT
      (Subgroup.mem_inf.mpr ⟨htK, Subgroup.le_normalizer htT⟩)
  rw [← hjt]
  exact (CFSG.Quasithin.cgsIn K T).mul_mem hj htJ

end CFSG.LocalAnalysis.RankThreeTheoremC.FiveTwentySix
