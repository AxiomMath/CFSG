module

public import CFSG.GroupTheory.SylowIntersectionControl.Isolated
import CFSG.LocalAnalysis.SignalizerFunctor.CoprimeQuotientNormalizers
import CFSG.GroupTheory.SylowIntersectionControl.IsolatedEmbedded
import CFSG.GroupTheory.ComponentCovering
import CFSG.RankThree.PartOne.CTP.StrongPQuotient

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.ABGLocalTools
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

private theorem isPIsolatedOver_quotient_of_centralizer_ccm {L : Type*} [Group L] [Finite L]
    {p : ℕ} [Fact p.Prime] (hL : IsPIsolatedOver p (⊤ : Subgroup L) ⊥)
    {N Y : Subgroup L} [N.Normal] (hN : ¬ p ∣ Nat.card N) (hY : Y.IsSubnormal)
    (hpY : p ∣ Nat.card Y) (hcent : N ≤ Subgroup.centralizer (Y : Set L)) :
    IsPIsolatedOver p (⊤ : Subgroup (L ⧸ N)) ⊥ := by
  obtain ⟨M, hM⟩ := isPIsolatedOver_top_bot_iff.mp hL
  obtain ⟨P, hP', hPM⟩ := hM.exists_isSylowOf_le
  have hP : IsSylowOf p P ⊤ := isSylowOf_iff.mpr hP'
  have hYopen : CFSG.Open.IsSubnormal Y ⊤ := CFSG.Open.IsSubnormal.top_iff.mpr hY
  have hPY : IsSylowOf p (P ⊓ Y : Subgroup L) Y :=
    CFSG.ABGLocalTools.IsSylowOf.inf_of_isSubnormal hP hYopen
  have hpPY : p ∣ Nat.card (P ⊓ Y : Subgroup L) := by
    rw [CFSG.ABGLocalTools.IsSylowOf.card_eq hPY]
    exact dvd_pow_self p ((Fact.out : p.Prime).factorization_pos_of_dvd Nat.card_pos.ne' hpY).ne'
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpPY
  have hx1 : (x : L) ≠ 1 := by
    intro h1
    have hxeq : x = 1 := Subtype.ext h1
    rw [hxeq, orderOf_one] at hx
    exact absurd hx.symm (Fact.out : p.Prime).one_lt.ne'
  have hxp : (x : L) ^ p = 1 := by
    have h := pow_orderOf_eq_one x
    rw [hx] at h
    simpa using congrArg Subtype.val h
  have hxY : (x : L) ∈ Y := x.2.2
  have hNM : N ≤ M := hcent.trans <|
    (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hxY)).trans <|
      hM.centralizer_le hx1 hxp (hPM x.2.1)
  exact isPIsolatedOver_top_bot_iff.mpr ⟨_, hM.map_quotient hNM hN⟩

omit [Finite G] in
private theorem normal_map_sup_inf_ker_ccm {G' : Type*} [Group G'] {φ : G →* G'}
    {H K : Subgroup G} (hHK : H ≤ K) [(H.subgroupOf K).Normal] :
    (((H ⊔ (K ⊓ φ.ker)).subgroupOf K).map (QuotientGroup.mk' (H.subgroupOf K))).Normal := by
  have hCsub : (K ⊓ φ.ker).subgroupOf K = φ.ker.subgroupOf K := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
  have hCnormal : ((K ⊓ φ.ker).subgroupOf K).Normal := by rw [hCsub]; infer_instance
  have hMnormal : ((H ⊔ (K ⊓ φ.ker)).subgroupOf K).Normal := by
    rw [Subgroup.subgroupOf_sup hHK inf_le_left]
    have : (H.subgroupOf K).Normal := inferInstance
    have : ((K ⊓ φ.ker).subgroupOf K).Normal := hCnormal
    infer_instance
  exact hMnormal.map _ (QuotientGroup.mk'_surjective _)

private noncomputable def toImage_ccm {G' : Type*} [Group G'] {φ : G →* G'} (K : Subgroup G) :
    K →* K.map φ :=
  (φ.comp K.subtype).codRestrict (K.map φ) (fun k => Subgroup.mem_map_of_mem φ k.2)

private noncomputable def mapToQuotient_ccm {G' : Type*} [Group G'] {φ : G →* G'}
    {H K : Subgroup G} [((H.map φ).subgroupOf (K.map φ)).Normal] :
    K →* (K.map φ) ⧸ (H.map φ).subgroupOf (K.map φ) :=
  (QuotientGroup.mk' ((H.map φ).subgroupOf (K.map φ))).comp (toImage_ccm (φ := φ) K)

omit [Finite G] in
private theorem surjective_mapToQuotient_ccm {G' : Type*} [Group G'] {φ : G →* G'}
    {H K : Subgroup G} [((H.map φ).subgroupOf (K.map φ)).Normal] :
    Function.Surjective (mapToQuotient_ccm (φ := φ) (H := H) (K := K)) := by
  intro y
  obtain ⟨y', hy'⟩ := QuotientGroup.mk'_surjective _ y
  obtain ⟨k, hkK, hk⟩ := y'.2
  refine ⟨⟨k, hkK⟩, ?_⟩
  rw [← hy']
  exact congrArg (QuotientGroup.mk' _) (Subtype.ext hk)

omit [Finite G] in
private theorem ker_mapToQuotient_ccm {G' : Type*} [Group G'] {φ : G →* G'}
    {H K : Subgroup G} (hHK : H ≤ K) [(H.subgroupOf K).Normal]
    [((H.map φ).subgroupOf (K.map φ)).Normal] :
    (mapToQuotient_ccm (φ := φ) (H := H) (K := K)).ker = (H ⊔ (K ⊓ φ.ker)).subgroupOf K := by
  have hCsub : (K ⊓ φ.ker).subgroupOf K = φ.ker.subgroupOf K := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
  have hCnormal : ((K ⊓ φ.ker).subgroupOf K).Normal := by rw [hCsub]; infer_instance
  ext k
  rw [MonoidHom.mem_ker]
  constructor
  · intro hk
    have hk' : toImage_ccm (φ := φ) K k ∈ (H.map φ).subgroupOf (K.map φ) :=
      (QuotientGroup.eq_one_iff _).mp hk
    rw [Subgroup.mem_subgroupOf] at hk'
    obtain ⟨h, hh, hhk⟩ := hk'
    have hc : h⁻¹ * (k : G) ∈ K ⊓ φ.ker := by
      refine ⟨K.mul_mem (K.inv_mem (hHK hh)) k.2, ?_⟩
      show φ (h⁻¹ * (k : G)) = 1
      rw [map_mul, map_inv, hhk]
      change (φ (k : G))⁻¹ * φ (k : G) = 1
      rw [inv_mul_cancel]
    have h1 : h * (h⁻¹ * (k : G)) ∈ H ⊔ (K ⊓ φ.ker) :=
      Subgroup.mul_mem_sup (S := H) (T := K ⊓ φ.ker) hh hc
    rwa [mul_inv_cancel_left] at h1
  · intro hk
    have hsub : k ∈ (H ⊔ (K ⊓ φ.ker)).subgroupOf K := hk
    rw [Subgroup.subgroupOf_sup hHK inf_le_left] at hsub
    have : ((K ⊓ φ.ker).subgroupOf K).Normal := hCnormal
    obtain ⟨h, hh, c, hc, hck⟩ := Subgroup.mem_sup_of_normal_right.mp hsub
    have hcφ : φ (c : G) = 1 := hc.2
    have hmem : toImage_ccm (φ := φ) K k ∈ (H.map φ).subgroupOf (K.map φ) := by
      rw [Subgroup.mem_subgroupOf]
      have hval : (toImage_ccm (φ := φ) K k).val = (toImage_ccm (φ := φ) K h).val := by
        change φ (k : G) = φ (h : G)
        rw [← hck]
        change φ ((h : G) * (c : G)) = φ (h : G)
        rw [map_mul, hcφ, mul_one]
      rw [hval]
      exact Subgroup.mem_map_of_mem φ hh
    exact (QuotientGroup.eq_one_iff _).mpr hmem

private noncomputable def quotientEquivCoprimeKer_ccm {G' : Type*} [Group G'] [Finite G']
    {φ : G →* G'} {H K : Subgroup G} (hHK : H ≤ K)
    [hHn : (H.subgroupOf K).Normal] [hNn : ((H.map φ).subgroupOf (K.map φ)).Normal]
    [_hMn : (((H ⊔ (K ⊓ φ.ker)).subgroupOf K).map
        (QuotientGroup.mk' (H.subgroupOf K))).Normal] :
    ((K ⧸ H.subgroupOf K) ⧸ (((H ⊔ (K ⊓ φ.ker)).subgroupOf K).map
        (QuotientGroup.mk' (H.subgroupOf K)))) ≃*
      ((K.map φ) ⧸ (H.map φ).subgroupOf (K.map φ)) := by
  have hCsub : (K ⊓ φ.ker).subgroupOf K = φ.ker.subgroupOf K := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
  have hCnormal : ((K ⊓ φ.ker).subgroupOf K).Normal := by rw [hCsub]; infer_instance
  have hMnormal : ((H ⊔ (K ⊓ φ.ker)).subgroupOf K).Normal := by
    rw [Subgroup.subgroupOf_sup hHK inf_le_left]
    have : (H.subgroupOf K).Normal := hHn
    have : ((K ⊓ φ.ker).subgroupOf K).Normal := hCnormal
    infer_instance
  have hHMsub : H.subgroupOf K ≤ (H ⊔ (K ⊓ φ.ker)).subgroupOf K :=
    Subgroup.subgroupOf_mono K le_sup_left
  have : ((H ⊔ (K ⊓ φ.ker)).subgroupOf K).Normal := hMnormal
  exact (QuotientGroup.quotientQuotientEquivQuotient (H.subgroupOf K)
      ((H ⊔ (K ⊓ φ.ker)).subgroupOf K) hHMsub).trans
    ((QuotientGroup.quotientMulEquivOfEq
        (ker_mapToQuotient_ccm (φ := φ) hHK).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _
        (surjective_mapToQuotient_ccm (φ := φ) (H := H) (K := K))))

private theorem map_of_coprime_ker_quotient_ccm {G' : Type*} [Group G'] [Finite G'] {φ : G →* G'}
    (hker : Nat.Coprime (Nat.card φ.ker) p) {H K Y : Subgroup G}
    [(H.subgroupOf K).Normal]
    [hMn : (((H ⊔ (K ⊓ φ.ker)).subgroupOf K).map
        (QuotientGroup.mk' (H.subgroupOf K))).Normal]
    (h : IsPIsolatedOver p K H) (hH : IsPGroup p H)
    (hHY : H ≤ Y) (hYK : Y ≤ K) (hY : (Y.subgroupOf K).IsSubnormal) (hp : p ∣ H.relIndex Y)
    (hcent : K ⊓ φ.ker ≤ centralizer (Y : Set G)) :
    IsPIsolatedOver p (⊤ : Subgroup ((K ⧸ H.subgroupOf K) ⧸
      (((H ⊔ (K ⊓ φ.ker)).subgroupOf K).map (QuotientGroup.mk' (H.subgroupOf K))))) ⊥ := by
  have hHK : H ≤ K := hHY.trans hYK
  have hker' : ¬ p ∣ Nat.card φ.ker := (Fact.out : p.Prime).coprime_iff_not_dvd.mp hker.symm
  have hL : IsPIsolatedOver p (⊤ : Subgroup (K ⧸ H.subgroupOf K)) ⊥ :=
    (isPIsolatedOver_iff_quotient hHK hH).mp h
  let C : Subgroup G := K ⊓ φ.ker
  let f : K →* K ⧸ H.subgroupOf K := QuotientGroup.mk' (H.subgroupOf K)
  let N : Subgroup (K ⧸ H.subgroupOf K) := ((H ⊔ C).subgroupOf K).map f
  let Ybar : Subgroup (K ⧸ H.subgroupOf K) := (Y.subgroupOf K).map f
  have : N.Normal := hMn
  have hNC : N = (C.subgroupOf K).map f := by
    change ((H ⊔ C).subgroupOf K).map f = (C.subgroupOf K).map f
    rw [Subgroup.subgroupOf_sup hHK inf_le_left, Subgroup.map_sup]
    have hHmap : (H.subgroupOf K).map f = ⊥ :=
      (Subgroup.map_eq_bot_iff (H.subgroupOf K)).mpr
        (le_of_eq (QuotientGroup.ker_mk' (H.subgroupOf K)).symm)
    rw [hHmap, bot_sup_eq]
  have hN : ¬ p ∣ Nat.card N := by
    have hcardN : Nat.card N ∣ Nat.card (C.subgroupOf K) := by
      rw [hNC]; exact Subgroup.card_map_dvd (C.subgroupOf K) f
    have hcardC : Nat.card (C.subgroupOf K) = Nat.card C :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    intro hpN
    exact hker' ((hcardC ▸ hpN.trans hcardN).trans (Subgroup.card_dvd_of_le inf_le_right))
  have hYbar : Ybar.IsSubnormal := hY.map (QuotientGroup.mk'_surjective (H.subgroupOf K))
  have hcardY : Nat.card Ybar = H.relIndex Y := by
    rw [← Subgroup.relIndex_ker, QuotientGroup.ker_mk', Subgroup.relIndex_subgroupOf hYK]
  have hpYbar : p ∣ Nat.card Ybar := hcardY ▸ hp
  have hcent' : N ≤ Subgroup.centralizer (Ybar : Set (K ⧸ H.subgroupOf K)) := by
    rw [hNC]
    rintro n ⟨c, hc, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro y ⟨y', hy', rfl⟩
    have hcomm : y' * c = c * y' :=
      Subtype.ext (Subgroup.mem_centralizer_iff.mp (hcent hc) y'.val hy')
    rw [← map_mul, ← map_mul, hcomm]
  exact isPIsolatedOver_quotient_of_centralizer_ccm hL hN hYbar hpYbar hcent'

theorem IsPIsolatedOver.map_of_coprime_ker {G' : Type*} [Group G'] [Finite G'] {φ : G →* G'}
    (hker : Nat.Coprime (Nat.card φ.ker) p) {H K Y : Subgroup G}
    (h : IsPIsolatedOver p K H) (hH : IsPGroup p H) (hKN : K ≤ normalizer (H : Set G))
    (hHY : H ≤ Y) (hYK : Y ≤ K) (hY : (Y.subgroupOf K).IsSubnormal) (hp : p ∣ H.relIndex Y)
    (hcent : K ⊓ φ.ker ≤ centralizer (Y : Set G)) :
    IsPIsolatedOver p (K.map φ) (H.map φ) := by
  have hHK : H ≤ K := hHY.trans hYK
  have hHn : (H.subgroupOf K).Normal := (normal_subgroupOf_iff_le_normalizer hHK).mpr hKN
  have hNn : ((H.map φ).subgroupOf (K.map φ)).Normal :=
    (normal_subgroupOf_iff_le_normalizer (Subgroup.map_mono hHK)).mpr
      ((Subgroup.map_mono hKN).trans (Subgroup.le_normalizer_map φ))
  have hMn := normal_map_sup_inf_ker_ccm (φ := φ) hHK
  have hq := map_of_coprime_ker_quotient_ccm hker h hH hHY hYK hY hp hcent
  have e := quotientEquivCoprimeKer_ccm (φ := φ) hHK
  have hker_bot : e.toMonoidHom.ker = ⊥ :=
    (MonoidHom.ker_eq_bot_iff e.toMonoidHom).mpr e.injective
  have key := (isPIsolatedOver_map_iff (p := p) (f := e.toMonoidHom) e.surjective
    (by rw [hker_bot]; exact IsPGroup.of_bot) (by rw [hker_bot])
    (by rw [hker_bot]; exact bot_le)).mpr hq
  rw [Subgroup.map_top_of_surjective _ e.surjective, Subgroup.map_bot] at key
  exact (isPIsolatedOver_iff_quotient (G := G') (Subgroup.map_mono hHK) (hH.map φ)).mpr key

theorem IsPIsolatedOver.normalizer_map_mk' (O : Subgroup G) [O.Normal]
    (hO : Nat.Coprime (Nat.card O) p) {H Y : Subgroup G}
    (h : IsPIsolatedOver p (normalizer (H : Set G)) H) (hH : IsPGroup p H) (hHY : H ≤ Y)
    (hYN : Y ≤ normalizer (H : Set G)) (hY : (Y.subgroupOf (normalizer (H : Set G))).IsSubnormal)
    (hp : p ∣ H.relIndex Y) (hcent : normalizer (H : Set G) ⊓ O ≤ centralizer (Y : Set G)) :
    IsPIsolatedOver p
      (normalizer ((H.map (QuotientGroup.mk' O) : Subgroup (G ⧸ O)) : Set (G ⧸ O)))
      (H.map (QuotientGroup.mk' O)) := by
  have hmap :=
    CFSG.SignalizerFunctor.Helpers.coprime_quotient_normalizer_image p Fact.out O H hO.symm hH
  have hcent' : normalizer (H : Set G) ⊓ (QuotientGroup.mk' O).ker ≤
      centralizer (Y : Set G) := by
    rwa [QuotientGroup.ker_mk']
  have key := IsPIsolatedOver.map_of_coprime_ker (φ := QuotientGroup.mk' O)
    (by rw [QuotientGroup.ker_mk']; exact hO) h hH le_rfl hHY hYN hY hp hcent'
  rwa [hmap] at key

end CFSG.GroupTheory
