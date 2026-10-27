module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafAlt
public import CFSG.LocalAnalysis.ComponentClassification.TBLitTools
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.ComponentClassification.CatLeaf

open CFSG Subgroup CFSG.ComponentClassification.UnbalancingLocal
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem nonempty_fusionZStar_equiv_center (K : Type*) [Group K] :
    Nonempty (K ⧸ Open.fusionZStar K ≃* (K ⧸ pPrimeCore 2 K) ⧸ center (K ⧸ pPrimeCore 2 K)) := by
  have hmapZ : (centralPreimage (pPrimeCore 2 K)).map (QuotientGroup.mk' (pPrimeCore 2 K)) =
      center (K ⧸ pPrimeCore 2 K) :=
    map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  exact ⟨(QuotientGroup.quotientMulEquivOfEq (TBLit.fusionZStar_eq_centralPreimage K)).trans
    ((QuotientGroup.quotientQuotientEquivQuotient (pPrimeCore 2 K)
      (centralPreimage (pPrimeCore 2 K)) (le_centralPreimage _)).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hmapZ))⟩

theorem exists_involution_of_isL34Type {J : Subgroup G}
    (hJ : GrSLit.IsL34Type (J ⧸ Open.fusionZStar J)) : ∃ s ∈ J, orderOf s = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card J := by
    have h1 := Subgroup.card_quotient_dvd_card (Open.fusionZStar J)
    rw [card_of_isL34Type hJ] at h1
    exact (show 2 ∣ 20160 by norm_num).trans h1
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := J) 2 h2
  exact ⟨s, s.2, by rw [Subgroup.orderOf_coe, hs]⟩

theorem eq_of_isPComponent_of_involution {K K' J : Subgroup G} (hK : IsPComponent 2 K)
    (hK' : IsPComponent 2 K') (hJK : J ≤ K) (hJK' : J ≤ K') (hJ : ⁅J, J⁆ = J) {s : G}
    (hs : s ∈ J) (hs2 : orderOf s = 2) : K = K' := by
  by_contra hne
  obtain ⟨-, -, hcomm, -⟩ := (CatalogueBPrimeJoin.distinct_p_components_core_commutation 2
    Nat.prime_two _ _ hK hK').2 hne
  have hsKK : s ∈ ⁅K, K'⁆ := commutator_mono hJK hJK' (by rw [hJ]; exact hs)
  exact TBLit.not_mem_oddCoreIn_of_orderOf_two K hs2 (mem_inf.mp (hcomm hsKK)).1

theorem mem_normalizer_of_le_pComponent {K J : Subgroup G} (hK : IsPComponent 2 K)
    (hJK : J ≤ K) (hJ : ⁅J, J⁆ = J) {s : G} (hs : s ∈ J) (hs2 : orderOf s = 2) {g : G}
    (hg : g ∈ normalizer (J : Set G)) : g ∈ normalizer (K : Set G) := by
  have hJg : J ≤ conjugate K g := by
    intro y hy
    rw [UnbalancedLayer.mem_conjugate_iff]
    exact hJK ((mem_normalizer_iff.mp hg y).mp hy)
  have heq := eq_of_isPComponent_of_involution hK (UnbalancedLayer.isPComponent_conjugate hK g)
    hJK hJg hJ hs hs2
  rw [mem_normalizer_iff]
  intro y
  rw [← UnbalancedLayer.mem_conjugate_iff, ← heq]

theorem commutator_eq_of_involution_mem {K X : Subgroup G} (hK : IsPComponent 2 K)
    (hXK : X ≤ normalizer (K : Set G)) {s : G} (hs : s ∈ ⁅K, X⁆) (hs2 : orderOf s = 2) :
    ⁅K, X⁆ = K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine TBLit.commutator_eq_self_of_exists
    (CatalogueBPrimeJoin.primeResidual_eq_top_of_pComponent 2 K hK)
    (CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple 2 K hK) hXK ?_
  by_contra hall
  push Not at hall
  have hle : ⁅K, X⁆ ≤ TBLit.oddCoreIn K := by
    rw [commutator_le]
    intro k hk h hh
    exact hall h hh k hk
  exact TBLit.not_mem_oddCoreIn_of_orderOf_two K hs2 (hle hs)

theorem exists_unbalanced_almostSimple_of_hull_pointed {K D : Subgroup G} {x : G}
    (hK : IsPComponent 2 K) (hx : orderOf x = 2) (hxK : x ∈ normalizer (K : Set G))
    (hDK : D ≤ normalizer (K : Set G)) (hDx : D ≤ centralizer ({x} : Set G))
    (hDodd : Nat.Coprime 2 (Nat.card D))
    (hDn : ∀ c ∈ centralizer ({x} : Set G) ⊓ normalizer (K : Set G), ∀ d ∈ D, c * d * c⁻¹ ∈ D)
    (hKx : ⁅K, zpowers x⁆ = K) (hKD : ⁅K, D⁆ = K) :
    ∃ (B : Type) (_ : Group B) (_ : Finite B), IsSimpleGroup (GeneralizedFitting.subgroup B) ∧
      (∃ a b : GeneralizedFitting.subgroup B, a * b ≠ b * a) ∧
      Nonempty (GeneralizedFitting.subgroup B ≃* K ⧸ Open.fusionZStar K) ∧
      ∃ z : B, orderOf z = 2 ∧ CFSG.oddCore (centralizer ({z} : Set B)) ≠ ⊥ ∧
        ((∃ k ∈ K, ∀ l ∈ K,
          (x * l * x⁻¹) * (k * l * k⁻¹)⁻¹ ∈ (Open.fusionZStar K).map K.subtype) →
          z ∈ GeneralizedFitting.subgroup B) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := hull K x D with hHdef
  have hKH : K ≤ H := le_hull_left K x D
  have hDH : D ≤ H := le_hull_right K x D
  have hLn : (K.subgroupOf H).Normal := hull_normal hKx.le hKD.le
  have hHN : H ≤ normalizer (K : Set G) :=
    sup_le (sup_le le_normalizer (zpowers_le.mpr hxK)) hDK
  have hQ : IsQuasisimple (K.subgroupOf H ⧸ pPrimeCore 2 (K.subgroupOf H)) :=
    CatalogueBPrimeJoin.quasisimple_primeCore_quotient_of_equiv 2 (subgroupOfEquivOfLe hKH).symm
      (CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple 2 K hK)
  obtain ⟨hS, -, -, -, -, hαK, -, -, hF, ⟨hFe⟩, hy1, hD1⟩ :=
    normal_quasisimple_section_automorphism_image (K.subgroupOf H) (pPrimeCore 2 (K.subgroupOf H))
      hQ
  set α := conjQuotAction (K.subgroupOf H) (centralPreimage (pPrimeCore 2 (K.subgroupOf H)))
    with hαdef
  set yH : H := ⟨x, mem_hull_elem K x D⟩ with hyHdef
  have hyH : orderOf yH = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hx
  have hDy : D.subgroupOf H ≤ centralizer {yH} := by
    intro d hd
    refine mem_centralizer_singleton.mpr (Subtype.ext ?_)
    exact mem_centralizer_singleton.mp (hDx (mem_subgroupOf.mp hd))
  have hDn' : ((D.subgroupOf H).subgroupOf (centralizer {yH})).Normal := by
    rw [normal_subgroupOf_iff hDy]
    intro d c hd hc
    rw [mem_subgroupOf] at hd ⊢
    have hcx : (c : G) ∈ centralizer ({x} : Set G) :=
      mem_centralizer_singleton.mpr (congrArg Subtype.val (mem_centralizer_singleton.mp hc))
    exact hDn c ⟨hcx, hHN c.2⟩ d hd
  have hDodd' : Nat.Coprime 2 (Nat.card (D.subgroupOf H)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hDH).toEquiv]
    exact hDodd
  have hcore := odd_two_quotient_core (LH := K.subgroupOf H) (DH := D.subgroupOf H) (hLn := hLn)
    hQ hyH hDy hDn' hDodd' (hull_sup_eq_top K D x) (hull_commutator_elem hKx)
    (hull_commutator_right hKD)
  have hαDcore := map_rangeRestrict_le_of_ker_eq 2 (pPrimeCore 2 H) (pCore 2 (H ⧸ pPrimeCore 2 H))
    α hcore.1 (D.subgroupOf H) yH hcore.2
  have hαD : (D.subgroupOf H).map α.rangeRestrict ≠ ⊥ := by
    rw [ne_eq, map_rangeRestrict_eq_bot_iff]
    exact hD1 (D.subgroupOf H) (hull_commutator_right hKD)
  have hαy1 : α yH ≠ 1 := hy1 yH (hull_commutator_elem hKx)
  have hy2 : yH ^ 2 = 1 := by
    rw [← hyH]
    exact pow_orderOf_eq_one yH
  have hαy : orderOf (α yH) = 2 := orderOf_eq_prime (by rw [← map_pow, hy2, map_one]) hαy1
  have hbridge : CFSG.generalizedFitting α.range = GeneralizedFitting.subgroup α.range :=
    CFSG.generalizedFitting_eq_componentClassification α.range
  let eF : GeneralizedFitting.subgroup α.range ≃* hullSection K H :=
    (MulEquiv.subgroupCongr (hbridge.symm.trans hF)).trans hFe
  have hfit : (∃ k ∈ K, ∀ l ∈ K,
      (x * l * x⁻¹) * (k * l * k⁻¹)⁻¹ ∈ (Open.fusionZStar K).map K.subtype) →
      α.rangeRestrict yH ∈ GeneralizedFitting.subgroup α.range := by
    rintro ⟨k, hkK, hk⟩
    have hkH : k ∈ H := hKH hkK
    let kH : H := ⟨k, hkH⟩
    have hkLH : kH ∈ K.subgroupOf H := hkK
    let eLH : K.subgroupOf H ≃* K := Subgroup.subgroupOfEquivOfLe hKH
    have hZmap : (centralPreimage (pPrimeCore 2 (K.subgroupOf H))).map eLH.toMonoidHom =
        centralPreimage (pPrimeCore 2 K) :=
      TBLit.map_centralPreimage_mulEquiv eLH _ _ (pPrimeCore_map_iso 2 _)
    have hαeq : α yH = α kH := by
      refine MulEquiv.ext fun q => ?_
      induction q using QuotientGroup.induction_on with
      | H l =>
        have hyconj : yH * l * yH⁻¹ ∈ K.subgroupOf H := hLn.conj_mem l l.2 yH
        have hkconj : kH * l * kH⁻¹ ∈ K.subgroupOf H := hLn.conj_mem l l.2 kH
        rw [conjQuotAction_mk' yH l hyconj, conjQuotAction_mk' kH l hkconj]
        rw [QuotientGroup.eq_iff_div_mem]
        apply (Subgroup.mem_map_iff_mem (f := eLH.toMonoidHom) eLH.injective).mp
        rw [hZmap]
        obtain ⟨n, hn, hne⟩ := hk ((l : H) : G) l.2
        rw [TBLit.fusionZStar_eq_centralPreimage] at hn
        have heq : eLH (⟨yH * l * yH⁻¹, hyconj⟩ / ⟨kH * l * kH⁻¹, hkconj⟩) = n := by
          apply Subtype.ext
          dsimp only [eLH]
          rw [Subgroup.subgroupOfEquivOfLe_apply_coe]
          simp only [Subgroup.coe_div, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk,
            yH, kH, div_eq_mul_inv]
          rw [← hne]
          rfl
        change eLH (⟨yH * l * yH⁻¹, hyconj⟩ / ⟨kH * l * kH⁻¹, hkconj⟩) ∈
          centralPreimage (pPrimeCore 2 K)
        rw [heq]
        exact hn
    have hαkInn : α yH ∈ (MulAut.conj :
        (K.subgroupOf H) ⧸ centralPreimage (pPrimeCore 2 (K.subgroupOf H)) →*
        MulAut ((K.subgroupOf H) ⧸ centralPreimage (pPrimeCore 2 (K.subgroupOf H)))).range := by
      rw [hαeq, ← hαK]
      exact Subgroup.mem_map_of_mem α hkLH
    rw [← hbridge, hF, Subgroup.mem_subgroupOf]
    exact hαkInn
  have := hS.1
  have hnonab : ∃ a b : GeneralizedFitting.subgroup α.range, a * b ≠ b * a := by
    obtain ⟨s, t, hst⟩ := hS.2
    exact ⟨eF.symm s, eF.symm t, fun h => hst (by simpa using congrArg eF h)⟩
  have hz2 : orderOf (α.rangeRestrict yH) = 2 := by
    rw [← orderOf_injective _ α.range.subtype_injective]
    exact hαy
  have hzodd : CFSG.oddCore (centralizer ({α.rangeRestrict yH} : Set α.range)) ≠ ⊥ := by
    rw [TBLit.oddCore_eq_pPrimeCore_two]
    exact ne_bot_of_le_map_subtype hαD hαDcore
  exact ⟨α.range, inferInstance, inferInstance, eF.isSimpleGroup, hnonab,
    ⟨eF.trans (TBLit.hullSectionEquiv hKH)⟩, α.rangeRestrict yH, hz2, hzodd,
    fun hw => hfit hw⟩

theorem exists_unbalanced_almostSimple_of_hull {K D : Subgroup G} {x : G}
    (hK : IsPComponent 2 K) (hx : orderOf x = 2) (hxK : x ∈ normalizer (K : Set G))
    (hDK : D ≤ normalizer (K : Set G)) (hDx : D ≤ centralizer ({x} : Set G))
    (hDodd : Nat.Coprime 2 (Nat.card D))
    (hDn : ∀ c ∈ centralizer ({x} : Set G) ⊓ normalizer (K : Set G), ∀ d ∈ D, c * d * c⁻¹ ∈ D)
    (hKx : ⁅K, zpowers x⁆ = K) (hKD : ⁅K, D⁆ = K) :
    ∃ (B : Type) (_ : Group B) (_ : Finite B), IsSimpleGroup (GeneralizedFitting.subgroup B) ∧
      (∃ a b : GeneralizedFitting.subgroup B, a * b ≠ b * a) ∧
      Nonempty (GeneralizedFitting.subgroup B ≃* K ⧸ Open.fusionZStar K) ∧
      ∃ z : B, orderOf z = 2 ∧ CFSG.oddCore (centralizer ({z} : Set B)) ≠ ⊥ := by
  obtain ⟨B, hB, hBfin, hFs, hFna, he, z, hz2, hzodd, -⟩ :=
    exists_unbalanced_almostSimple_of_hull_pointed hK hx hxK hDK hDx hDodd hDn hKx hKD
  exact ⟨B, hB, hBfin, hFs, hFna, he, z, hz2, hzodd⟩

end CFSG.ComponentClassification.CatLeaf
