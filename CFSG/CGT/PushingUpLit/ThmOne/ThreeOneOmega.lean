module

public import CFSG.CGT.PushingUpLit.ThmOne.ThreeOneOmegaSyl
public import CFSG.CGT.PushingUpLit.ThmOne.ThreeOneOmegaAmb
public import CFSG.CGT.PushingUpLit.ThmOne.ThreeOneOmegaJ

public section

namespace CFSG.CGT.PushingUpLit.ThmOne

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.CGT6
open CFSG.Assembly (KProper InCatalog)

variable {G : Type} [Group G] [Finite G]

theorem not_arrow_of_arrowMaximal {A H : Subgroup G} {D : Subgroup ↥H}
    (hH : IsMaximalTwoLocal H) (hAH : A ≤ H)
    (hmax : ∀ Y : Subgroup G, InOmega Y → Arrow A Y → Y = A)
    (hns : ¬ (A.subgroupOf H).IsSubnormal) (hD : InClassX ↥D) (hDs : D.IsSubnormal) :
    ¬ Arrow (A.subgroupOf H) D := by
  intro harr
  have hDsub : (D.map H.subtype).subgroupOf H = D :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective D
  have hΩ : InOmega (D.map H.subtype) :=
    ⟨InClassX.of_mulEquiv (D.equivMapOfInjective H.subtype H.subtype_injective) hD, H, hH,
      Subgroup.map_subtype_le D, by rw [hDsub]; exact hDs⟩
  have harr' : Arrow A (D.map H.subtype) := by
    have h := arrow_map_subtype harr
    rwa [Subgroup.map_subgroupOf_eq_of_le hAH] at h
  apply hns
  rw [← hmax _ hΩ harr', hDsub]
  exact hDs

theorem ThreeOneOmega.map_le_of_le_normalizer_jIn {M H : Subgroup G} {D : Subgroup ↥H}
    (hM : IsMaximalTwoLocal M) (hQH : oTwoIn M ≤ H)
    (hD : D ≤ Subgroup.normalizer ((jIn ((oTwoIn M).subgroupOf H) : Subgroup ↥H) : Set ↥H)) :
    D.map H.subtype ≤ M := by
  have hQ1 : oTwoIn M ≠ ⊥ := fun h => pCore_ne_bot_of_isPLocal hM.1
    ((Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective).mp h)
  have hN : Subgroup.normalizer ((jIn (oTwoIn M) : Subgroup G) : Set G) = M :=
    normalizer_eq_of_isMaximalTwoLocal_le_normalizer hM (isPGroup_jIn (isPGroup_oTwoIn M))
      (jIn_ne_bot (isPGroup_oTwoIn M) hQ1)
      ((SixThree.le_normalizer_oTwoIn M).trans (normalizer_le_normalizer_jIn _))
  rintro _ ⟨d, hd, rfl⟩
  rw [← hN, ← map_jIn_subgroupOf hQH]
  exact coe_mem_normalizer_map (hD hd)

theorem isSubnormal_of_arrowMaximal_of_oTwoIn_le (hA : AschbacherEmbeddingAmbK')
    {A M H : Subgroup G} (hM : IsMaximalTwoLocal M) (hMc : IsCharacteristicP 2 ↥M)
    (hH : IsMaximalTwoLocal H) (hHc : IsCharacteristicP 2 ↥H) (hKH : CFSG.IsKGroup ↥H)
    (hAcl : InClassX ↥A) (hAM : A ≤ M) (hAsub : (A.subgroupOf M).IsSubnormal) (hAH : A ≤ H)
    (hmax : ∀ Y : Subgroup G, InOmega Y → Arrow A Y → Y = A) (hQH : oTwoIn M ≤ H)
    (hOQ : oTwoIn H ≤ oTwoIn M) : (A.subgroupOf H).IsSubnormal := by
  by_contra hns
  obtain ⟨R, hR, -, hAR, hAsR⟩ :=
    exists_isSylowOf_isSubnormal_normalizer_inf hM hMc hAcl.1 hAM hAsub hQH
  obtain ⟨hCC, hnot, D, hAD, hDs, hCD, hD2, hout⟩ := exists_embedding_of_isSylowOf_inf hA hKH hHc
    hAcl hAH (hOQ.trans (oTwoIn_le_centralizerModCore_of_isSubnormal hAcl.1.residual_eq hAM
      hAsub)) hR hAR hAsR hns
  rcases hout with ⟨hDcl, -, harr⟩ | hΩ
  · exact not_arrow_of_arrowMaximal hH hAH hmax hns hDcl hDs harr.arrow
  have hpQ : pCore 2 ↥H ≤ (oTwoIn M).subgroupOf H := fun x hx =>
    hOQ (by rw [oTwoIn_eq_map]; exact ⟨x, hx, rfl⟩)
  have hVn := SixThree.normal_omegaOneCenterIn (pCore 2 ↥H)
  have hJ := le_normalizer_jIn_of_omegaFourOutcome
    ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 _).mp
      (isElementaryAbelian_omegaOneCenterIn (pCore 2 ↥H)))
    hΩ.toOmegaFourOutcome hAD hDs hCD hD2 hCC ((inClassX_subgroupOf_iff hAH).mpr hAcl) hnot
    ((omegaOneCenterIn_le _).trans hpQ)
    ((ThreeFromEight.oTwoIn_le_pCore_of_isSubnormal hDs).trans hpQ)
  obtain ⟨-, -, -, -, -, -, -, hnsD⟩ := hΩ.toOmegaFourOutcome
  apply hnsD
  have h1 := (CFSG.GroupTheory.isSubnormal_subgroupOf_subgroupOf_iff
    (Subgroup.map_subtype_le D)).mpr (CFSG.GroupTheory.isSubnormal_subgroupOf_of_le
      (ThreeOneOmega.map_le_of_le_normalizer_jIn hM hQH hJ) hAsub)
  have hDsub : (D.map H.subtype).subgroupOf H = D :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective D
  rwa [hDsub] at h1

theorem eq_of_le_sup_inf_centralizer_blockU (hA : AschbacherEmbeddingAmbK')
    (hKH : ∀ H : Subgroup G, IsMaximalTwoLocal H → CFSG.IsKGroup ↥H)
    (hchar : CFSG.Assembly.IsCharTwoType G) {X M H : Subgroup G} (hX : InClassX ↥X)
    (hmax : ∀ Y : Subgroup G, InOmega Y → Arrow X Y → Y = X) (hM : IsMaximalTwoLocal M)
    (hXM : X ≤ M) (hsub : (X.subgroupOf M).IsSubnormal) (hH : IsMaximalTwoLocal H)
    (hXH : X ⊔ (M ⊓ Subgroup.centralizer (blockU X : Set G)) ≤ H) : H = M := by
  by_contra hne
  have hMc := isCharacteristicP_of_isPLocal hchar hM.1
  obtain ⟨m, hm, hAH, hns⟩ := exists_conjugate_le_not_isSubnormal hM hMc hH hX hXM hsub hXH hne
  have hCH : M ⊓ Subgroup.centralizer (blockU X : Set G) ≤ H := le_sup_right.trans hXH
  have hQH : oTwoIn M ≤ H := (le_inf (oTwoIn_le M)
    (le_centralizer_blockU_of_le_centralizerModCore hX.1 (isPGroup_oTwoIn M)
      (oTwoIn_le_centralizerModCore_of_isSubnormal hX.1.residual_eq hXM hsub))).trans hCH
  have hOQ : oTwoIn H ≤ oTwoIn M := oTwoIn_le_of_oTwoIn_inf_eq hM hQH
    (oTwoIn_inf_eq hX hXM hsub (le_sup_left.trans hXH) hCH)
  exact hns (isSubnormal_of_arrowMaximal_of_oTwoIn_le hA hM hMc hH
    (isCharacteristicP_of_isPLocal hchar hH.1) (hKH H hH) (inClassX_conjugate hX m)
    (CFSG.GroupTheory.conjugate_le_of_mem hXM hm) (isSubnormal_conjugate hsub hm) hAH
    (arrowMaximal_conjugate hmax m) hQH hOQ)

theorem threeOne_of_ambK' (hA : AschbacherEmbeddingAmbK')
    (hKH : ∀ H : Subgroup G, IsMaximalTwoLocal H → CFSG.IsKGroup ↥H)
    (hchar : CFSG.Assembly.IsCharTwoType G) {X M : Subgroup G} (hX : InClassX ↥X)
    (hmax : ∀ Y : Subgroup G, InOmega Y → Arrow X Y → Y = X) (hM : IsMaximalTwoLocal M)
    (hXM : X ≤ M) (hsub : (X.subgroupOf M).IsSubnormal) :
    maximalTwoLocalsContaining
      ((X ⊔ (M ⊓ Subgroup.centralizer (blockU X : Set G)) : Subgroup G) : Set G) = {M} := by
  ext H
  constructor
  · rintro ⟨hH, hXH⟩
    exact Set.mem_singleton_iff.mpr (eq_of_le_sup_inf_centralizer_blockU hA hKH hchar hX hmax hM
      hXM hsub hH (SetLike.coe_subset_coe.mp hXH))
  · rintro rfl
    exact ⟨hM, SetLike.coe_subset_coe.mpr (sup_le hXM inf_le_left)⟩

theorem threeOne (hE : AschbacherEmbeddingK) (hK : KProper InCatalog G)
    (hchar : CFSG.Assembly.IsCharTwoType G) (htop : ¬ CFSG.IsPLocal 2 (⊤ : Subgroup G))
    {X M : Subgroup G} (hX : InClassX ↥X)
    (hmax : ∀ Y : Subgroup G, InOmega Y → Arrow X Y → Y = X) (hM : IsMaximalTwoLocal M)
    (hXM : X ≤ M) (hsub : (X.subgroupOf M).IsSubnormal) :
    maximalTwoLocalsContaining
      ((X ⊔ (M ⊓ Subgroup.centralizer (blockU X : Set G)) : Subgroup G) : Set G) = {M} :=
  threeOne_of_ambK' (aschbacherEmbeddingAmbK'_holds hE)
    (fun H hH => CFSG.ComponentClassification.CatalogueKProper.proper_subgroup_isKGroup hK H
      fun h => htop (h ▸ hH.1))
    hchar hX hmax hM hXM hsub

end CFSG.CGT.PushingUpLit.ThmOne
