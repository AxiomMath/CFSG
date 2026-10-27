module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Std

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem isPComponent_of_pumpUp_eq (hS : SchreierFor Blueprint.Catalog)
    (hK : Assembly.KProper Blueprint.Catalog G) {J : Subgroup G} {b t : G} (hb : orderOf b = 2)
    (ht : orderOf t = 2) (hbt : b * t = t * b) (htZ : t ∉ center G)
    (hJb : J ≤ centralizer ({b} : Set G))
    (hJp : IsPComponent 2 (J.subgroupOf (centralizer ({b} : Set G))))
    (hJt : J ≤ centralizer ({t} : Set G)) (hP : pumpUp J t = J) :
    IsPComponent 2 (J.subgroupOf (centralizer ({t} : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({t} : Set G) with hC
  have hgs := gsFixedLayer_eq_of_le hJb hJp hJt
  have hJbb : conjugate J b = J := UnbalancedCorr.conjugate_eq_self_of_le_centralizer hJb
  have hKe : ∀ k ∈ J ⊔ conjugate J b, k⁻¹ * t⁻¹ * k * t ∈
      (pPrimeCore 2 (centralizer ({b} : Set G))).map (centralizer ({b} : Set G)).subtype := by
    rw [hJbb, sup_idem]
    intro k hk
    have hkt : k * t = t * k := mem_centralizer_singleton_iff.mp (hJt hk)
    rw [show k⁻¹ * t⁻¹ * k * t = k⁻¹ * t⁻¹ * (k * t) by group, hkt,
      show k⁻¹ * t⁻¹ * (t * k) = 1 by group]
    exact one_mem _
  obtain ⟨-, -, -, -, -, -, hTV, hVE, -, -, -, -⟩ :=
    UGSChain.kProper_core_trivial_orbit_fixed_layer_containment_of_schreier hS hK (a := b)
      (b := b) (e := t) hb ht rfl hbt htZ hJb hJp hKe
  have hJL : J ≤ layerIn C := by
    rw [← hgs]
    exact hTV.trans hVE
  have hPN : layerIn C ≤ normalizer (J : Set G) := by
    intro g hg
    apply mem_normalizer_of_conjugate_eq
    have h1 : conjugate J g ≤ J := by
      have h2 : conjugate (gsFixedLayer J t) g ≤ pumpUp J t := le_iSup₂_of_le g hg le_rfl
      rwa [hgs, hP] at h2
    refine eq_of_le_of_card_ge h1 ?_
    rw [conjugate, card_map_of_injective (MulAut.conj g⁻¹).injective]
  have hLs : ((layerIn C).subgroupOf C).IsSubnormal := by
    have : (pLayer ↥C 2).Characteristic := CatalogueBPrimeJoin.pLayer_characteristic
    have hP' : (layerIn C).subgroupOf C = pLayer ↥C 2 :=
      comap_map_eq_self_of_injective C.subtype_injective _
    rw [hP']
    exact Subgroup.Normal.isSubnormal inferInstance
  have hJn : ((J.subgroupOf C).subgroupOf ((layerIn C).subgroupOf C)).Normal := by
    constructor
    intro x hx g
    rw [mem_subgroupOf, mem_subgroupOf] at hx ⊢
    have hgP : ((g : C) : G) ∈ layerIn C := mem_subgroupOf.mp g.2
    have := (mem_normalizer_iff.mp (hPN hgP) _).mp hx
    simpa using this
  have hsub : (J.subgroupOf C).IsSubnormal :=
    Subgroup.IsSubnormal.trans (fun x hx => hJL hx) hJn.isSubnormal hLs
  obtain ⟨-, hres, hq⟩ := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 J _ hJb).mp hJp
  exact (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 J C hJt).mpr ⟨hsub, hres, hq⟩

omit [Finite G] in
theorem conj_pow_eq_inv_of_involutions {a t : G} (ha : a * a = 1) (ht : t * t = 1) (k : ℕ) :
    a * (a * t) ^ k * a⁻¹ = ((a * t) ^ k)⁻¹ ∧ t * (a * t) ^ k * t⁻¹ = ((a * t) ^ k)⁻¹ := by
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have h1 : a * (a * t) * a⁻¹ = (a * t)⁻¹ := by
    rw [hainv, mul_inv_rev, hainv, htinv, ← mul_assoc, ha, one_mul]
  have h2 : t * (a * t) * t⁻¹ = (a * t)⁻¹ := by
    rw [htinv, mul_inv_rev, hainv, htinv]
    calc t * (a * t) * t = t * a * (t * t) := by group
      _ = t * a := by rw [ht, mul_one]
  refine ⟨?_, ?_⟩
  · rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply, h1, inv_pow]
  · rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply, h2, inv_pow]

theorem dihedral_cases {a t : G} (ha : a * a = 1) (ht : t * t = 1) :
    (∃ k : ℕ, t = ((a * t) ^ k)⁻¹ * a * (a * t) ^ k) ∨
      ∃ z ∈ zpowers (a * t), z * z = 1 ∧ z ≠ 1 ∧ z * a = a * z ∧ z * t = t * z := by
  set r := a * t with hr
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hn := orderOf_pos r
  rcases Nat.even_or_odd (orderOf r) with ⟨m, hm⟩ | ⟨m, hm⟩
  ·
    right
    have hm0 : 0 < m := by omega
    have hz2 : r ^ m * r ^ m = 1 := by rw [← pow_add, ← hm, pow_orderOf_eq_one]
    have hzinv : (r ^ m)⁻¹ = r ^ m := inv_eq_of_mul_eq_one_right hz2
    obtain ⟨h1, h2⟩ := conj_pow_eq_inv_of_involutions ha ht m
    rw [hzinv] at h1 h2
    refine ⟨r ^ m, pow_mem (mem_zpowers r) m, hz2, fun h => ?_, ?_, ?_⟩
    · have := orderOf_le_of_pow_eq_one hm0 h
      omega
    · calc r ^ m * a = a * (r ^ m) * a⁻¹ * a := by rw [h1]
        _ = a * r ^ m := by group
    · calc r ^ m * t = t * (r ^ m) * t⁻¹ * t := by rw [h2]
        _ = t * r ^ m := by group
  ·
    left
    refine ⟨m + 1, ?_⟩
    obtain ⟨h1, -⟩ := conj_pow_eq_inv_of_involutions ha ht (m + 1)
    rw [← h1, hainv]
    have e : a * r ^ (m + 1) * a * a * r ^ (m + 1) = a * r ^ (2 * m + 1) * r := by
      rw [mul_assoc (a * r ^ (m + 1)) a a, ha, mul_one, mul_assoc, ← pow_add,
        show m + 1 + (m + 1) = 2 * m + 1 + 1 by ring, pow_succ, mul_assoc]
    rw [e, ← hm, pow_orderOf_eq_one, mul_one, hr, ← mul_assoc, ha, one_mul]

theorem centralizer_le_normalizer_of_cor211 (hS : SchreierFor Blueprint.Catalog)
    (hK : Assembly.KProper Blueprint.Catalog G) (hZ : ∀ g : G, g ≠ 1 → g ∉ center G)
    {J : Subgroup G} {a : G} (ha : orderOf a = 2) (hJa : J ≤ centralizer ({a} : Set G))
    (hJp : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G))))
    (hT91 : ∀ t : G, orderOf t = 2 → J ≤ centralizer ({t} : Set G) →
      (⨆ (g : G) (_ : conjugate J g ≤ centralizer ({t} : Set G)), conjugate J g) ≤
        oddIn (centralizer ({t} : Set G)) ⊔ J)
    (hT92 : ∀ g : G, ¬ ⁅J, conjugate J g⁆ ≤ oddIn J ⊓ oddIn (conjugate J g))
    (hbad : ∀ b t : G, orderOf b = 2 → J ≤ centralizer ({b} : Set G) →
      IsPComponent 2 (J.subgroupOf (centralizer ({b} : Set G))) → orderOf t = 2 →
      b * t = t * b → J ≤ centralizer ({t} : Set G) →
      oddIn (pumpUp J t) ≤ (center ↥J).map J.subtype) :
    ∀ t : G, orderOf t = 2 → J ≤ centralizer ({t} : Set G) →
      centralizer ({t} : Set G) ≤ normalizer (J : Set G) := by
  have hstep : ∀ b t : G, orderOf b = 2 → J ≤ centralizer ({b} : Set G) →
      IsPComponent 2 (J.subgroupOf (centralizer ({b} : Set G))) → orderOf t = 2 →
      b * t = t * b → J ≤ centralizer ({t} : Set G) →
      IsPComponent 2 (J.subgroupOf (centralizer ({t} : Set G))) ∧
        centralizer ({t} : Set G) ≤ normalizer (J : Set G) := by
    intro b t hb hJb hJbp ht hbt hJt
    have hgs := gsFixedLayer_eq_of_le hJb hJbp hJt
    have hP := pumpUp_eq_of_oddIn_le_center hJt hgs (hT91 t ht hJt)
      (hbad b t hb hJb hJbp ht hbt hJt)
    have ht1 : t ≠ 1 := by rintro rfl; simp at ht
    have hJtp := isPComponent_of_pumpUp_eq hS hK hb ht hbt (hZ t ht1) hJb hJbp hJt hP
    exact ⟨hJtp, centralizer_le_normalizer_of_isPComponent hT92 hJt hJtp⟩
  intro t ht hJt
  have ha2 : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have hJC : ∀ x ∈ zpowers (a * t), J ≤ centralizer ({x} : Set G) := by
    intro x hx l hl
    have hla : l ∈ centralizer ({a} : Set G) := hJa hl
    have hlt : l ∈ centralizer ({t} : Set G) := hJt hl
    have hlat : l ∈ centralizer ({a * t} : Set G) := by
      rw [mem_centralizer_singleton_iff] at hla hlt ⊢
      calc l * (a * t) = (l * a) * t := by group
        _ = a * l * t := by rw [hla]
        _ = a * (l * t) := by group
        _ = a * (t * l) := by rw [hlt]
        _ = a * t * l := by group
    have hx' := zpowers_le.mpr (show a * t ∈ centralizer ({l} : Set G) from
      mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hlat).symm) hx
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hx').symm
  rcases dihedral_cases ha2 ht2 with ⟨k, hk⟩ | ⟨z, hzr, hz2, hz1, hza, hzt⟩
  ·
    set d := (a * t) ^ k with hd
    have hdJ : J ≤ centralizer ({d} : Set G) := hJC d (pow_mem (mem_zpowers _) k)
    have hdN : d ∈ normalizer (J : Set G) := mem_normalizer_of_commute fun l hl =>
      (mem_centralizer_singleton_iff.mp (hdJ hl)).symm
    have haN := (hstep a a ha hJa hJp ha rfl hJa).2
    intro c hc
    have hc' : d * c * d⁻¹ ∈ centralizer ({a} : Set G) := by
      rw [mem_centralizer_singleton_iff] at hc ⊢
      rw [hk] at hc
      calc d * c * d⁻¹ * a = d * (c * (d⁻¹ * a * d)) * d⁻¹ := by group
        _ = d * ((d⁻¹ * a * d) * c) * d⁻¹ := by rw [hc]
        _ = a * (d * c * d⁻¹) := by group
    have h1 := haN hc'
    have : c = d⁻¹ * (d * c * d⁻¹) * d := by group
    rw [this]
    exact mul_mem (mul_mem (inv_mem hdN) h1) hdN
  ·
    have hzo : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two, hz2]) hz1
    have hJz := hJC z hzr
    obtain ⟨hJzp, -⟩ := hstep a z ha hJa hJp hzo hza.symm hJz
    exact (hstep z t hzo hJz hJzp ht hzt hJt).2

theorem isStandardSubgroup_of_cor211 (hS : SchreierFor Blueprint.Catalog)
    (hK : Assembly.KProper Blueprint.Catalog G) (hZ : ∀ g : G, g ≠ 1 → g ∉ center G)
    {J : Subgroup G} {a : G} (ha : orderOf a = 2) (hJa : J ≤ centralizer ({a} : Set G))
    (hJp : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G))))
    (hT91 : ∀ t : G, orderOf t = 2 → J ≤ centralizer ({t} : Set G) →
      (⨆ (g : G) (_ : conjugate J g ≤ centralizer ({t} : Set G)), conjugate J g) ≤
        oddIn (centralizer ({t} : Set G)) ⊔ J)
    (hT92 : ∀ g : G, ¬ ⁅J, conjugate J g⁆ ≤ oddIn J ⊓ oddIn (conjugate J g))
    (hbad : ∀ b t : G, orderOf b = 2 → J ≤ centralizer ({b} : Set G) →
      IsPComponent 2 (J.subgroupOf (centralizer ({b} : Set G))) → orderOf t = 2 →
      b * t = t * b → J ≤ centralizer ({t} : Set G) →
      oddIn (pumpUp J t) ≤ (center ↥J).map J.subtype) :
    IsStandardSubgroup J ∧ oddIn J ≤ (center ↥J).map J.subtype := by
  have hgs := gsFixedLayer_eq_of_le hJa hJp hJa
  have hPa := pumpUp_eq_of_oddIn_le_center hJa hgs (hT91 a ha hJa)
    (hbad a a ha hJa hJp ha rfl hJa)
  have hO : oddIn J ≤ (center ↥J).map J.subtype := by
    have h := hbad a a ha hJa hJp ha rfl hJa
    rwa [hPa] at h
  refine ⟨isStandardSubgroup_of_normal (isQuasisimple_of_oddIn_le_center hJa hJp hO) ha hJa
    (centralizer_le_normalizer_of_cor211 hS hK hZ ha hJa hJp hT91 hT92 hbad) fun g hg => ?_, hO⟩
  apply hT92 g
  rw [hg]
  exact bot_le

end CFSG.ComponentClassification.GrSLit.GrS5
