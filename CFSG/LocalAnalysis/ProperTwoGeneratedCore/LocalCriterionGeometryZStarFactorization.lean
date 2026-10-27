module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeometryZStar
public import CFSG.Adapters.Involutions
public import CFSG.LocalAnalysis.ComponentClassification.OddCore

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

open CFSG.Open CFSG.BenderSuzuki CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open scoped Pointwise

universe u

variable {G : Type u} [Group G]

@[expose] def pairOddCore (H : Subgroup G) (beta : rightCosetSpace H) : Subgroup G :=
  (oddCore (pairPointStabilizer H beta)).map (pairPointStabilizer H beta).subtype

@[expose] def pairInvertedSet (H : Subgroup G) (beta : rightCosetSpace H) (t : G) : Set G :=
  {x | x ∈ pairOddCore H beta ∧ rightConjugateElem x t = x⁻¹}

theorem native_zStar_of_isolated_involution [Finite G] {t : G} (ht : orderOf t = 2)
    (hisolated : ∀ g : G, Commute (g⁻¹ * t * g) t → g⁻¹ * t * g = t) :
    (QuotientGroup.mk t : G ⧸ oddCore G) ∈ Subgroup.center (G ⧸ oddCore G) ∧
      ∀ g : G, ∃ c ∈ Subgroup.centralizer ({t} : Set G),
        ∃ x ∈ oddCore G, g = c * x := by
  let e : G ≃* Shrink.{0} G := (Shrink.mulEquiv.{0, u} (α := G)).symm
  let : Fintype (Shrink.{0} G) := Fintype.ofFinite _
  have het : orderOf (e t) = 2 := e.orderOf_eq t |>.trans ht
  have hett : e t * e t = 1 := by
    simpa only [pow_two] using (orderOf_eq_prime_iff.mp het).1
  have heisolated : ∀ g : Shrink.{0} G,
      (g * e t * g⁻¹) * e t = e t * (g * e t * g⁻¹) → g * e t * g⁻¹ = e t := by
    intro g hcomm
    let a := e.symm g⁻¹
    have hcommG : Commute (a⁻¹ * t * a) t := by
      apply e.injective
      simpa only [map_mul, map_inv, a, map_inv, e.apply_symm_apply, inv_inv] using hcomm
    have heq := congrArg e (hisolated a hcommG)
    simpa only [map_mul, map_inv, a, e.apply_symm_apply, inv_inv] using heq
  obtain ⟨N, hNnormal, hNodd, hNcomm⟩ := CFSG.ZStar.glauberman_zStar
    (Shrink.{0} G) (e t) ((orderOf_eq_prime_iff.mp het).2) hett heisolated
  let M : Subgroup G := N.comap e.toMonoidHom
  have hMnormal : M.Normal := hNnormal.comap e.toMonoidHom
  have hModd : Odd (Nat.card M) := by
    have eM : M ≃* N :=
      { toFun := fun a => ⟨e a, a.property⟩
        invFun := fun a => ⟨e.symm a, by
          change e (e.symm a.val) ∈ N
          simpa only [e.apply_symm_apply] using a.property⟩
        left_inv := fun a => Subtype.ext (e.symm_apply_apply a.val)
        right_inv := fun a => Subtype.ext (e.apply_symm_apply a.val)
        map_mul' := fun a b => Subtype.ext (e.map_mul a b) }
    rw [Nat.card_congr eM.toEquiv]
    exact hNodd
  have hMcore : M ≤ oddCore G := le_sSup ⟨hMnormal, hModd⟩
  have hcenter : (QuotientGroup.mk t : G ⧸ oddCore G) ∈
      Subgroup.center (G ⧸ oddCore G) := by
    apply Subgroup.mem_center_iff.mpr
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    have hcommM : g * t * g⁻¹ * t⁻¹ ∈ M := by
      change e (g * t * g⁻¹ * t⁻¹) ∈ N
      simpa only [map_mul, map_inv] using hNcomm (e g)
    have hquot : (QuotientGroup.mk (g * t * g⁻¹ * t⁻¹) : G ⧸ oddCore G) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (hMcore hcommM)
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at hquot
    have hconj := mul_eq_one_iff_eq_inv.mp hquot
    rw [inv_inv] at hconj
    have hh := congrArg (fun x : G ⧸ oddCore G =>
      x * (QuotientGroup.mk g : G ⧸ oddCore G)) hconj
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh
  refine ⟨hcenter, ?_⟩
  apply CFSG.Adapters.eq_centralizer_mul_oddCore
  · simpa only [pow_two] using (orderOf_eq_prime_iff.mp ht).1
  · exact hcenter

theorem odd_subgroup_eq_bot_of_card_two [Finite G]
    (hcard : Nat.card G = 2) (N : Subgroup G) (hodd : Odd (Nat.card N)) : N = ⊥ := by
  have hdiv := N.card_subgroup_dvd_card
  rw [hcard] at hdiv
  have hcardN : Nat.card N = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with h | h
    · exact h
    · rw [h] at hodd
      norm_num at hodd
  exact Subgroup.card_eq_one.mp hcardN

theorem oddCore_le_index_two [Finite G] (B : Subgroup G) [B.Normal]
    (hindex : B.index = 2) : oddCore G ≤ B := by
  let q := QuotientGroup.mk' B
  have hodd : Odd (Nat.card ((oddCore G).map q)) := by
    exact (CFSG.ComponentClassification.OddCore.odd_card G).of_dvd_nat
      ((oddCore G).card_map_dvd q)
  have himage : (oddCore G).map q = ⊥ :=
    odd_subgroup_eq_bot_of_card_two hindex ((oddCore G).map q) hodd
  intro x hx
  have him := Subgroup.mem_map_of_mem q hx
  rw [himage] at him
  exact (QuotientGroup.eq_one_iff x).mp (Subgroup.mem_bot.mp him)

theorem pair_group_oddCore_eq [Finite G] {H : Subgroup G} {z t : G}
    (hz : orderOf z = 2) {beta : rightCosetSpace H}
    (hbeta : beta ≠ rightCosetMk H 1) (ht : t ∈ rightPairFlipFiber H z beta) :
    (oddCore (pairFlipGroup H beta t)).map (pairFlipGroup H beta t).subtype =
      pairOddCore H beta := by
  let B := pairPointStabilizer H beta
  let K := pairFlipGroup H beta t
  let BK := B.subgroupOf K
  let : BK.Normal := pair_stabilizer_normal hz hbeta ht
  have hcoreB : oddCore K ≤ BK := oddCore_le_index_two BK (pair_group_index_two hz hbeta ht)
  have hintersection : (oddCore BK).map BK.subtype = BK ⊓ oddCore K :=
    CFSG.ComponentClassification.OddCore.normal_intersection K BK
  rw [inf_eq_right.mpr hcoreB] at hintersection
  let e : BK ≃* B := Subgroup.subgroupOfEquivOfLe
    (pairPointStabilizer_le_pairFlipGroup H beta t)
  have hmap : (oddCore BK).map e.toMonoidHom = oddCore B :=
    CFSG.ComponentClassification.OddCore.equiv_invariant e
  have hhom : K.subtype.comp BK.subtype = B.subtype.comp e.toMonoidHom := by
    ext x
    simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply, MulEquiv.coe_toMonoidHom, e] using
      (Subgroup.subgroupOfEquivOfLe_apply_coe
      (pairPointStabilizer_le_pairFlipGroup H beta t) x).symm
  change (oddCore K).map K.subtype = (oddCore B).map B.subtype
  rw [← hintersection, Subgroup.map_map, hhom, ← Subgroup.map_map, hmap]

theorem pairOddCore_le [Finite G] (H : Subgroup G) (beta : rightCosetSpace H) (t : G) :
    pairOddCore H beta ≤ pairPointStabilizer H beta ∧
      pairOddCore H beta ≤ pairFlipGroup H beta t ∧ pairOddCore H beta ≤ H := by
  have hJB : pairOddCore H beta ≤ pairPointStabilizer H beta := Subgroup.map_subtype_le _
  exact ⟨hJB, hJB.trans (pairPointStabilizer_le_pairFlipGroup H beta t),
    hJB.trans (pairPointStabilizer_le_point H beta)⟩

theorem pairOddCore_odd [Finite G] (H : Subgroup G) (beta : rightCosetSpace H) :
    Odd (Nat.card (pairOddCore H beta)) := by
  rw [pairOddCore, Subgroup.card_subtype]
  exact CFSG.ComponentClassification.OddCore.odd_card _

theorem pair_group_oddCore_subgroupOf_eq [Finite G] {H : Subgroup G} {z t : G}
    (hz : orderOf z = 2) {beta : rightCosetSpace H}
    (hbeta : beta ≠ rightCosetMk H 1) (ht : t ∈ rightPairFlipFiber H z beta) :
    oddCore (pairFlipGroup H beta t) =
      (pairOddCore H beta).subgroupOf (pairFlipGroup H beta t) := by
  rw [← pair_group_oddCore_eq hz hbeta ht]
  exact (Subgroup.comap_map_eq_self_of_injective
    (pairFlipGroup H beta t).subtype_injective _).symm

theorem pairOddCore_normal_in_pair_group [Finite G] {H : Subgroup G} {z t : G}
    (hz : orderOf z = 2) {beta : rightCosetSpace H}
    (hbeta : beta ≠ rightCosetMk H 1) (ht : t ∈ rightPairFlipFiber H z beta) :
    ((pairOddCore H beta).subgroupOf (pairFlipGroup H beta t)).Normal := by
  rw [← pair_group_oddCore_subgroupOf_eq hz hbeta ht]
  infer_instance

theorem pair_flip_zStar_factorization [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta) :
    let K := pairFlipGroup H beta t
    let J := (pairOddCore H beta).subgroupOf K
    letI : J.Normal := pairOddCore_normal_in_pair_group h.distinguished_order hbeta ht
    (QuotientGroup.mk (⟨t, flip_mem_pairFlipGroup H beta t⟩ : K) : K ⧸ J) ∈
      Subgroup.center (K ⧸ J) ∧
    ∀ g ∈ K, ∃ c ∈ K ⊓ Subgroup.centralizer ({t} : Set G),
      ∃ x ∈ pairOddCore H beta, g = c * x := by
  let K := pairFlipGroup H beta t
  let J := (pairOddCore H beta).subgroupOf K
  let : J.Normal := pairOddCore_normal_in_pair_group h.distinguished_order hbeta ht
  let tK : K := ⟨t, flip_mem_pairFlipGroup H beta t⟩
  have htK : orderOf tK = 2 :=
    (Subgroup.orderOf_coe tK).symm.trans (order_two_of_mem_pointClass h.distinguished_order ht.1)
  have hisolated : ∀ g : K, Commute (g⁻¹ * tK * g) tK → g⁻¹ * tK * g = tK := by
    intro g hcomm
    have hcommG : Commute (rightConjugateElem t (g : G)) t :=
      congrArg Subtype.val hcomm.eq
    apply Subtype.ext
    exact (pair_flips_commute_iff_eq h S hzS hzcenter hbeta
      (pair_group_conjugate_flip_mem h.distinguished_order hbeta ht ht g.property) ht).mp hcommG
  obtain ⟨hcenter, hfactor⟩ := native_zStar_of_isolated_involution htK hisolated
  have hcore := pair_group_oddCore_subgroupOf_eq h.distinguished_order hbeta ht
  refine ⟨?_, ?_⟩
  · apply Subgroup.mem_center_iff.mpr
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    have hc := Subgroup.mem_center_iff.mp hcenter
      (QuotientGroup.mk g : K ⧸ oddCore K)
    have hmem : (g * tK)⁻¹ * (tK * g) ∈ oddCore K := by
      apply QuotientGroup.eq.mp
      simpa only [QuotientGroup.mk_mul] using hc
    have hmemJ : (g * tK)⁻¹ * (tK * g) ∈ J :=
      by
        change (g * tK)⁻¹ * (tK * g) ∈
          (pairOddCore H beta).subgroupOf (pairFlipGroup H beta t)
        exact hcore ▸ hmem
    have hcommJ : (QuotientGroup.mk (g * tK) : K ⧸ J) = QuotientGroup.mk (tK * g) :=
      QuotientGroup.eq.mpr hmemJ
    simpa only [QuotientGroup.mk_mul] using hcommJ
  · intro g hg
    obtain ⟨c, hc, x, hx, hcx⟩ := hfactor (⟨g, hg⟩ : K)
    refine ⟨c, ⟨c.property, ?_⟩, x, ?_, congrArg Subtype.val hcx⟩
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hc))
    · exact (pair_group_oddCore_eq h.distinguished_order hbeta ht) ▸
        Subgroup.mem_map_of_mem K.subtype hx

theorem pair_flip_fiber_eq_pair_class [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta) :
    rightPairFlipFiber H z beta = conjugacyWithin (pairFlipGroup H beta t) t := by
  let K := pairFlipGroup H beta t
  let tK : K := ⟨t, flip_mem_pairFlipGroup H beta t⟩
  have htK : orderOf tK = 2 :=
    (Subgroup.orderOf_coe tK).symm.trans (order_two_of_mem_pointClass h.distinguished_order ht.1)
  have hcyclic : IsPGroup 2 (Subgroup.zpowers tK) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, htK]; norm_num)
  obtain ⟨P, hP⟩ := hcyclic.exists_le_sylow
  have htP : tK ∈ (P : Subgroup K) := hP (Subgroup.mem_zpowers tK)
  have hcenter := (pair_flip_central_and_weakly_closed h S hzS hzcenter hbeta ht P htP).1
  ext s
  constructor
  · intro hs
    let sK : K := ⟨s, pair_flip_mem_group h.distinguished_order ht hs⟩
    have hsK : orderOf sK = 2 :=
      (Subgroup.orderOf_coe sK).symm.trans (order_two_of_mem_pointClass h.distinguished_order hs.1)
    obtain ⟨a, ha⟩ := involution_conjugate_into_sylow P hsK
    have hsa : rightConjugateElem s (a : G) ∈ rightPairFlipFiber H z beta :=
      pair_group_conjugate_flip_mem h.distinguished_order hbeta ht hs a.property
    have hcomm : Commute (rightConjugateElem s (a : G)) t := by
      exact congrArg (fun x : (P : Subgroup K) => ((x : K) : G))
        ((Subgroup.mem_center_iff.mp hcenter) (⟨a⁻¹ * sK * a, ha⟩ : (P : Subgroup K)))
    have heq := (pair_flips_commute_iff_eq h S hzS hzcenter hbeta hsa ht).mp hcomm
    refine ⟨a⁻¹, ?_⟩
    change (a : G)⁻¹⁻¹ * t * (a : G)⁻¹ = s
    rw [← heq]
    unfold rightConjugateElem
    group
  · rintro ⟨a, rfl⟩
    exact pair_group_conjugate_flip_mem h.distinguished_order hbeta ht ht a.property

theorem pair_flip_fiber_eq_odd_class [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta) :
    rightPairFlipFiber H z beta = conjugacyWithin (pairOddCore H beta) t := by
  have hfactor := (pair_flip_zStar_factorization h S hzS hzcenter hbeta ht).2
  have hclass := pair_flip_fiber_eq_pair_class h S hzS hzcenter hbeta ht
  ext s
  constructor
  · intro hs
    obtain ⟨a, ha⟩ := hclass ▸ hs
    obtain ⟨c, hc, x, hx, hcx⟩ := hfactor a a.property
    refine ⟨⟨x, hx⟩, ?_⟩
    have hct : c⁻¹ * t * c = t := by
      have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hc.2
      rw [mul_assoc, ← hcomm, inv_mul_cancel_left]
    calc
      x⁻¹ * t * x = (c * x)⁻¹ * t * (c * x) := by
        calc
          x⁻¹ * t * x = x⁻¹ * (c⁻¹ * t * c) * x := by rw [hct]
          _ = (c * x)⁻¹ * t * (c * x) := by group
      _ = (a : G)⁻¹ * t * a := by rw [← hcx]
      _ = s := ha
  · rintro ⟨a, rfl⟩
    exact pair_group_conjugate_flip_mem h.distinguished_order hbeta ht ht
      ((pairOddCore_le H beta t).2.1 a.property)

theorem inverted_odd_element_mul_involution_conjugate [Finite G]
    (J : Subgroup G) (hJodd : Odd (Nat.card J)) {t x : G}
    (ht : t * t = 1) (hx : x ∈ J)
    (hinverted : t⁻¹ * x * t = x⁻¹) :
    x * t ∈ conjugacyWithin J t := by
  have hodd : Odd (orderOf x) := by
    apply hJodd.of_dvd_nat
    simpa only [Subgroup.orderOf_mk] using (orderOf_dvd_natCard (⟨x, hx⟩ : J))
  obtain ⟨k, hk⟩ := hodd
  let n := x ^ (k + 1)
  have hnJ : n ∈ J := J.pow_mem hx _
  have hnn : n * n = x := by
    change x ^ (k + 1) * x ^ (k + 1) = x
    rw [← pow_add, show k + 1 + (k + 1) = orderOf x + 1 by omega,
      pow_succ, pow_orderOf_eq_one, one_mul]
  have htinverse : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have htnt : t⁻¹ * n * t = n⁻¹ := by
    change t⁻¹ * x ^ (k + 1) * t = (x ^ (k + 1))⁻¹
    calc
      t⁻¹ * x ^ (k + 1) * t = (t⁻¹ * x * t) ^ (k + 1) := by
        simpa only [inv_inv] using (conj_pow (a := t⁻¹) (b := x) (i := k + 1)).symm
      _ = (x⁻¹) ^ (k + 1) := by rw [hinverted]
      _ = (x ^ (k + 1))⁻¹ := inv_pow _ _
  have htn : t * n = n⁻¹ * t := by
    have hh := congrArg (fun a : G => a * t) htnt
    simpa only [htinverse, mul_assoc, ht, mul_one] using hh
  refine ⟨⟨n⁻¹, J.inv_mem hnJ⟩, ?_⟩
  change n⁻¹⁻¹ * t * n⁻¹ = x * t
  rw [inv_inv, ← hnn]
  calc
    n * t * n⁻¹ = n * n * (t * n) * n⁻¹ := by rw [htn]; group
    _ = n * n * t := by group

theorem pair_inverted_set_eq_products [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta) :
    pairInvertedSet H beta t = rightPairFlipProducts H z beta t := by
  let K := pairFlipGroup H beta t
  let tK : K := ⟨t, flip_mem_pairFlipGroup H beta t⟩
  have htt : t * t = 1 := by
    simpa only [pow_two] using (orderOf_eq_prime_iff.mp
      (order_two_of_mem_pointClass h.distinguished_order ht.1)).1
  have htinverse : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hcenter := (pair_flip_zStar_factorization h S hzS hzcenter hbeta ht).1
  have hclass := pair_flip_fiber_eq_odd_class h S hzS hzcenter hbeta ht
  let J := (pairOddCore H beta).subgroupOf K
  let : J.Normal := pairOddCore_normal_in_pair_group h.distinguished_order hbeta ht
  ext x
  constructor
  · rintro ⟨hxJ, hxinverted⟩
    have hxtclass : x * t ∈ conjugacyWithin (pairOddCore H beta) t :=
      inverted_odd_element_mul_involution_conjugate _ (pairOddCore_odd H beta)
        htt hxJ hxinverted
    have hxtF : x * t ∈ rightPairFlipFiber H z beta := hclass.symm ▸ hxtclass
    refine ⟨x * t, hxtF, ?_⟩
    change x * t * t = x
    rw [mul_assoc, htt, mul_one]
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨a, ha⟩ := hclass ▸ hs
    let aK : K := ⟨a, (pairOddCore_le H beta t).2.1 a.property⟩
    have heq : (QuotientGroup.mk (aK⁻¹ * tK * aK) : K ⧸ J) = QuotientGroup.mk tK := by
      have hc := Subgroup.mem_center_iff.mp hcenter (QuotientGroup.mk aK : K ⧸ J)
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        mul_assoc, ← hc, inv_mul_cancel_left]
    have hstJ : aK⁻¹ * tK * aK * tK ∈ J := by
      apply (QuotientGroup.eq_one_iff _).mp
      rw [QuotientGroup.mk_mul, heq, ← QuotientGroup.mk_mul]
      have htKtwo : tK * tK = 1 := Subtype.ext htt
      rw [htKtwo, QuotientGroup.mk_one]
    have hsorder := order_two_of_mem_pointClass h.distinguished_order hs.1
    refine ⟨?_, ?_⟩
    · change s * t ∈ pairOddCore H beta
      have hmem : (a : G)⁻¹ * t * a * t ∈ pairOddCore H beta := hstJ
      rwa [ha] at hmem
    · change t⁻¹ * (s * t) * t = (s * t)⁻¹
      rw [mul_inv_rev, htinverse, inv_eq_self_of_orderOf_eq_two hsorder]
      simp only [mul_assoc, htt, mul_one]

theorem pair_inverted_set_card [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta) :
    Nat.card (pairInvertedSet H beta t) = Nat.card (conjugacyWithin H z) := by
  rw [pair_inverted_set_eq_products h S hzS hzcenter hbeta ht,
    rightPairFlipProducts, Nat.card_image_of_injective (fun _ _ hh => mul_right_cancel hh)]
  exact (involution_point_uniform_pair_flips h beta hbeta).1

theorem point_subgroup_eq_centralizer_mul_inverted_set [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta) :
    (H : Set G) = (Subgroup.centralizer ({z} : Set G) : Set G) *
      pairInvertedSet H beta t := by
  have hI := pair_inverted_set_eq_products h S hzS hzcenter hbeta ht
  have htransversal := ((involution_point_uniform_pair_flips h beta hbeta).2.2 t ht).2
  ext g
  constructor
  · intro hg
    obtain ⟨x, hxcoset, _⟩ := htransversal (⟨g, hg⟩ : H)
    have hxg : (x : G) * g⁻¹ ∈ Subgroup.centralizer ({z} : Set G) :=
      (mem_rightCoset_iff
        (s := (Subgroup.centralizer ({z} : Set G) : Set G)) g).mp hxcoset
    have hginverse : g * (x : G)⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := by
      simpa only [mul_inv_rev, inv_inv] using
        (Subgroup.centralizer ({z} : Set G)).inv_mem hxg
    exact Set.mem_mul.mpr ⟨g * (x : G)⁻¹, hginverse, x, hI.symm ▸ x.property,
      by group⟩
  · intro hg
    obtain ⟨c, hc, x, hx, rfl⟩ := Set.mem_mul.mp hg
    exact H.mul_mem (point_centralizer_le h hc)
      ((pairOddCore_le H beta t).2.2 hx.1)

theorem pair_group_eq_centralizer_mul_odd_core [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta) :
    (pairFlipGroup H beta t : Set G) =
      (pairFlipGroup H beta t ⊓ Subgroup.centralizer ({t} : Set G) : Set G) *
        (pairOddCore H beta : Set G) := by
  ext g
  constructor
  · intro hg
    obtain ⟨c, hc, x, hx, hcx⟩ :=
      (pair_flip_zStar_factorization h S hzS hzcenter hbeta ht).2 g hg
    exact Set.mem_mul.mpr ⟨c, hc, x, hx, hcx.symm⟩
  · intro hg
    obtain ⟨c, hc, x, hx, rfl⟩ := Set.mem_mul.mp hg
    exact (pairFlipGroup H beta t).mul_mem hc.1 ((pairOddCore_le H beta t).2.1 hx)

theorem involution_point_pair_flip_zStar_factorization [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (t : G) (ht : t ∈ rightPairFlipFiber H z beta) :
    let B := pairPointStabilizer H beta
    let K := pairFlipGroup H beta t
    let J := pairOddCore H beta
    let JK := J.subgroupOf K
    letI : JK.Normal := pairOddCore_normal_in_pair_group h.distinguished_order hbeta ht
    (B.subgroupOf K).Normal ∧ B.relIndex K = 2 ∧
      (oddCore K).map K.subtype = J ∧
      (QuotientGroup.mk (⟨t, flip_mem_pairFlipGroup H beta t⟩ : K) : K ⧸ JK) ∈
        Subgroup.center (K ⧸ JK) ∧
      (K : Set G) = (K ⊓ Subgroup.centralizer ({t} : Set G) : Set G) * (J : Set G) ∧
      rightPairFlipFiber H z beta = conjugacyWithin K t ∧
      rightPairFlipFiber H z beta = conjugacyWithin J t ∧
      pairInvertedSet H beta t = rightPairFlipProducts H z beta t ∧
      Nat.card (pairInvertedSet H beta t) = Nat.card (conjugacyWithin H z) ∧
      (H : Set G) = (Subgroup.centralizer ({z} : Set G) : Set G) *
        pairInvertedSet H beta t := by
  exact ⟨pair_stabilizer_normal h.distinguished_order hbeta ht,
    pair_group_index_two h.distinguished_order hbeta ht,
    pair_group_oddCore_eq h.distinguished_order hbeta ht,
    (pair_flip_zStar_factorization h S hzS hzcenter hbeta ht).1,
    pair_group_eq_centralizer_mul_odd_core h S hzS hzcenter hbeta ht,
    pair_flip_fiber_eq_pair_class h S hzS hzcenter hbeta ht,
    pair_flip_fiber_eq_odd_class h S hzS hzcenter hbeta ht,
    pair_inverted_set_eq_products h S hzS hzcenter hbeta ht,
    pair_inverted_set_card h S hzS hzcenter hbeta ht,
    point_subgroup_eq_centralizer_mul_inverted_set h S hzS hzcenter hbeta ht⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
