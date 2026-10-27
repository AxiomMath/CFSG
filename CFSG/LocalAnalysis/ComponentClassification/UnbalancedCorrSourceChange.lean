module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrNestedNormalClosure
public import CFSG.Open.FusionDefs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAOrbitFixedComponent

public section

namespace CFSG.ComponentClassification.UnbalancedCorr

open CFSG CFSG.LocalCores Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement Pointwise

variable {G : Type*} [Group G]

theorem exists_centerQuotient_congr {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    ∃ f : X ⧸ center X ≃* Y ⧸ center Y, ∀ x : X, f x = ((e x : Y) : Y ⧸ center Y) :=
  ⟨QuotientGroup.congr (center X) (center Y) e (Subgroup.map_center_eq e),
    fun x => QuotientGroup.congr_mk _ _ _ _ x⟩

theorem exists_centerQuotient_equiv_of_surjective {A D : Type*} [Group A] [Group D]
    (hA : Group.IsPerfect A) (δ : A →* D) (hδ : Function.Surjective δ)
    (hker : δ.ker ≤ center A) :
    ∃ f : A ⧸ center A ≃* D ⧸ center D, ∀ u : A, f u = ((δ u : D) : D ⧸ center D) := by
  have hcomap := comap_center_eq_of_perfect hA δ hδ hker
  let ψ : A →* D ⧸ center D := (QuotientGroup.mk' (center D)).comp δ
  have hψ : Function.Surjective ψ := (QuotientGroup.mk'_surjective _).comp hδ
  have hkerψ : ψ.ker = center A := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', hcomap]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hkerψ.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψ), fun u => rfl⟩

theorem exists_zstar_equiv (X : Type*) [Group X] :
    ∃ f : X ⧸ Open.fusionZStar X ≃* (X ⧸ pPrimeCore 2 X) ⧸ center (X ⧸ pPrimeCore 2 X),
      ∀ x : X, f (x : X ⧸ Open.fusionZStar X) =
        (((x : X ⧸ pPrimeCore 2 X)) : (X ⧸ pPrimeCore 2 X) ⧸ center (X ⧸ pPrimeCore 2 X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : CFSG.oddCore X ≤ Open.fusionZStar X := by
    intro x hx
    change (QuotientGroup.mk' (CFSG.oddCore X) x : X ⧸ CFSG.oddCore X) ∈
      center (X ⧸ CFSG.oddCore X)
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact one_mem _
  have hmap : (Open.fusionZStar X).map (QuotientGroup.mk' (CFSG.oddCore X)) =
      center (X ⧸ CFSG.oddCore X) :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  let e₁ : (X ⧸ CFSG.oddCore X) ⧸ center (X ⧸ CFSG.oddCore X) ≃* X ⧸ Open.fusionZStar X :=
    (QuotientGroup.quotientMulEquivOfEq hmap.symm).trans
      (QuotientGroup.quotientQuotientEquivQuotient _ _ hle)
  have he₁ : ∀ x : X, e₁ ((x : X ⧸ CFSG.oddCore X) : (X ⧸ CFSG.oddCore X) ⧸ center _) =
      (x : X ⧸ Open.fusionZStar X) := fun x => rfl
  have hO : CFSG.oddCore X = pPrimeCore 2 X :=
    (CFSG.oddCore_eq_piCore (G := X)).trans (CFSG.pPrimeCore_eq_piCore (G := X) 2).symm
  let e₂ : X ⧸ CFSG.oddCore X ≃* X ⧸ pPrimeCore 2 X := QuotientGroup.quotientMulEquivOfEq hO
  obtain ⟨e₃, he₃⟩ := exists_centerQuotient_congr e₂
  refine ⟨e₁.symm.trans e₃, fun x => ?_⟩
  rw [MulEquiv.trans_apply, ← he₁, MulEquiv.symm_apply_apply, he₃]
  rfl

theorem commutatorElement_mul_mul_of_commute {Q : Type*} [Group Q] {x y d e : Q}
    (hdy : d * y = y * d) (hex : e * x = x * e) (hde : d * e = e * d) :
    ⁅x * d, y * e⁆ = ⁅x, y⁆ := by
  have hdye : d * (y * e) = (y * e) * d := by
    rw [← mul_assoc, hdy, mul_assoc, hde, ← mul_assoc]
  have hexi : e * x⁻¹ = x⁻¹ * e := by
    rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, ← hex, mul_assoc, mul_inv_cancel, mul_one]
  rw [commutatorElement_def, commutatorElement_def]
  calc x * d * (y * e) * (x * d)⁻¹ * (y * e)⁻¹
      = x * (d * (y * e)) * d⁻¹ * x⁻¹ * e⁻¹ * y⁻¹ := by group
    _ = x * ((y * e) * d) * d⁻¹ * x⁻¹ * e⁻¹ * y⁻¹ := by rw [hdye]
    _ = x * y * (e * x⁻¹) * e⁻¹ * y⁻¹ := by group
    _ = x * y * (x⁻¹ * e) * e⁻¹ * y⁻¹ := by rw [hexi]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem exists_diagonal_hom {Q : Type*} [Group Q] {A B Δ : Subgroup Q} {γ : Q}
    (hAB : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) (hγ : ∀ u ∈ A, γ * u * γ⁻¹ ∈ B)
    (hΔ : ∀ x, x ∈ Δ ↔ ∃ u ∈ A, x = u * (γ * u * γ⁻¹)) :
    ∃ δ : A →* Δ, Function.Surjective δ ∧ (∀ u : A, (δ u : Q) = u * (γ * u * γ⁻¹)) ∧
      (∀ u : A, δ u = 1 ↔ (u : Q) ∈ B ∧ γ * u * γ⁻¹ = (u : Q)⁻¹) ∧ δ.ker ≤ center A := by
  let δ₀ : A →* Q :=
    { toFun := fun u => u * (γ * u * γ⁻¹)
      map_one' := by simp
      map_mul' := by
        intro u v
        have hc := hAB v v.2 _ (hγ u u.2)
        simp only [coe_mul]
        calc (u : Q) * v * (γ * (u * v) * γ⁻¹) = u * (v * (γ * u * γ⁻¹)) * (γ * v * γ⁻¹) := by
              group
          _ = u * ((γ * u * γ⁻¹) * v) * (γ * v * γ⁻¹) := by rw [hc]
          _ = u * (γ * u * γ⁻¹) * (v * (γ * v * γ⁻¹)) := by group }
  have hrange : ∀ u : A, δ₀ u ∈ Δ := fun u => (hΔ _).mpr ⟨u, u.2, rfl⟩
  refine ⟨δ₀.codRestrict Δ hrange, ?_, fun u => rfl, ?_, ?_⟩
  · intro x
    obtain ⟨u, hu, hx⟩ := (hΔ x).mp x.2
    exact ⟨⟨u, hu⟩, Subtype.ext hx.symm⟩
  · intro u
    constructor
    · intro h1
      have h2 : (u : Q) * (γ * u * γ⁻¹) = 1 := congrArg Subtype.val h1
      have h3 : γ * u * γ⁻¹ = (u : Q)⁻¹ := eq_inv_of_mul_eq_one_right h2
      refine ⟨?_, h3⟩
      have h4 := hγ u u.2
      rw [h3] at h4
      simpa using inv_mem h4
    · rintro ⟨-, h3⟩
      apply Subtype.ext
      show (u : Q) * (γ * u * γ⁻¹) = 1
      rw [h3, mul_inv_cancel]
  · intro u hu
    have h2 : (u : Q) * (γ * u * γ⁻¹) = 1 := congrArg Subtype.val hu
    have h3 : γ * u * γ⁻¹ = (u : Q)⁻¹ := eq_inv_of_mul_eq_one_right h2
    rw [mem_center_iff]
    intro v
    apply Subtype.ext
    have h4 := hAB v v.2 _ (hγ u u.2)
    rw [h3] at h4
    show (v : Q) * u = u * v
    set x : Q := (u : Q)
    set y : Q := (v : Q)
    calc y * x = x * (x⁻¹ * y) * x := by group
      _ = x * (y * x⁻¹) * x := by rw [h4]
      _ = x * y := by group

theorem exists_centerQuotient_chain {X₁ X₂ X₃ X₄ X₅ : Type*} [Group X₁] [Group X₂] [Group X₃]
    [Group X₄] [Group X₅] (e₁ : X₂ ≃* X₁) (e₂ : X₂ ≃* X₃) (δ : X₄ →* X₃)
    (hδ : Function.Surjective δ) (hker : δ.ker ≤ center X₄) (hX₄ : Group.IsPerfect X₄)
    (e₃ : X₅ ≃* X₄) :
    ∃ f : X₁ ⧸ center X₁ ≃* X₅ ⧸ center X₅, ∀ (x₂ : X₂) (x₅ : X₅), e₂ x₂ = δ (e₃ x₅) →
      f ((e₁ x₂ : X₁) : X₁ ⧸ center X₁) = (x₅ : X₅ ⧸ center X₅) := by
  obtain ⟨c₁, hc₁⟩ := exists_centerQuotient_congr e₁
  obtain ⟨c₂, hc₂⟩ := exists_centerQuotient_congr e₂
  obtain ⟨d, hd⟩ := exists_centerQuotient_equiv_of_surjective hX₄ δ hδ hker
  obtain ⟨c₃, hc₃⟩ := exists_centerQuotient_congr e₃
  refine ⟨c₁.symm.trans (c₂.trans (d.symm.trans c₃.symm)), fun x₂ x₅ hx => ?_⟩
  rw [MulEquiv.trans_apply, ← hc₁, MulEquiv.symm_apply_apply, MulEquiv.trans_apply, hc₂, hx,
    MulEquiv.trans_apply, ← hd, MulEquiv.symm_apply_apply, ← hc₃, MulEquiv.symm_apply_apply]

variable [Finite G]

theorem map_pPrimeCore_eq_inf_of_isSubnormal {X : Type*} [Group X] [Finite X] {N : Subgroup X}
    (hN : N.IsSubnormal) : (pPrimeCore 2 N).map N.subtype = N ⊓ pPrimeCore 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [pPrimeCore_eq_piCore (G := N) 2, pPrimeCore_eq_piCore (G := X) 2]
  exact prime_set_core_subnormal_intersection _ hN

theorem exists_restriction_quotient_equiv_of_subnormal {X H : Subgroup G} (hXH : X ≤ H)
    (hX : (X.subgroupOf H).IsSubnormal) :
    ∃ e : X ⧸ pPrimeCore 2 X ≃* ↥((X.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 H))),
      ∀ (x : X) (hx : (x : G) ∈ H),
        ((e x : ↥((X.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 H)))) :
          H ⧸ pPrimeCore 2 H) = ((⟨x, hx⟩ : H) : H ⧸ pPrimeCore 2 H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 H) with hπ
  let φ : X →* H ⧸ pPrimeCore 2 H := π.comp (inclusion hXH)
  have hrange : φ.range = (X.subgroupOf H).map π := by
    rw [MonoidHom.range_comp]
    congr 1
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact x.2
    · intro hy
      exact ⟨⟨y, hy⟩, rfl⟩
  have hker : pPrimeCore 2 X = φ.ker := by
    apply le_antisymm
    ·
      intro x hx
      rw [MonoidHom.mem_ker]
      show π (inclusion hXH x) = 1
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      have h1 := map_pPrimeCore_eq_inf_of_isSubnormal hX
      have h4 : (x : G) ∈
          ((pPrimeCore 2 (X.subgroupOf H)).map (X.subgroupOf H).subtype).map H.subtype := by
        rw [pPrimeCore_map_subgroupOf 2 X H hXH]
        exact ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hyx⟩ := mem_map.mp h4
      rw [h1] at hy
      have hyeq : y = inclusion hXH x := Subtype.ext hyx
      rw [← hyeq]
      exact (mem_inf.mp hy).2
    · refine le_sSup ⟨φ.normal_ker, ?_⟩
      have hk : φ.ker = (pPrimeCore 2 H).comap (inclusion hXH) := by
        ext x
        rw [MonoidHom.mem_ker, mem_comap]
        show π (inclusion hXH x) = 1 ↔ _
        rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      rw [hk]
      exact Nat.Coprime.coprime_dvd_right
        (card_comap_dvd_of_injective _ _ (inclusion_injective hXH))
        (pPrimeCore_coprime_card (p := 2) (G := H))
  refine ⟨((QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivRange φ)).trans (MulEquiv.subgroupCongr hrange),
    fun x hx => rfl⟩

theorem isPComponent_subgroupOf_subgroupOf_iff' {X Y L : Subgroup G} (hYX : Y ≤ X) (p : ℕ)
    (hp : p.Prime) :
    IsPComponent p ((L.subgroupOf X).subgroupOf (Y.subgroupOf X)) ↔
      IsPComponent p (L.subgroupOf Y) := by
  rw [(LocalAnalysis.ComponentInitial.p_component_isomorphism_transport p hp
    (Subgroup.subgroupOfEquivOfLe hYX)).1]
  congr! 1
  ext ⟨x, hx⟩
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : ((y : X) : G) = x := congrArg Subtype.val hyx
    rw [← this]
    exact hy
  · intro h
    exact ⟨⟨⟨x, hYX hx⟩, Subgroup.mem_subgroupOf.2 hx⟩, h, rfl⟩

theorem gsFixedLayer_isPComponent {X J : Subgroup G} {t : G} (hJX : J ≤ X)
    (hJsub : (J.subgroupOf X).IsSubnormal) (htX : t ∈ X) (ht : orderOf t = 2)
    (htJ : t ∈ normalizer (J : Set G)) (hJq : IsQuasisimple (J ⧸ pPrimeCore 2 J))
    (hcomm : ∀ j ∈ J, j⁻¹ * t⁻¹ * j * t ∈ (pPrimeCore 2 J).map J.subtype) :
    IsPComponent 2
      ((UnbalancedGS.gsFixedLayer J t).subgroupOf (X ⊓ centralizer ({t} : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htt : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  set t' : X := ⟨t, htX⟩ with ht'
  set J' := J.subgroupOf X with hJ'
  have hcore : ∀ x : X, x ∈ (pPrimeCore 2 J').map J'.subtype ↔
      (x : G) ∈ (pPrimeCore 2 J).map J.subtype := by
    intro x
    have h3 := pPrimeCore_map_subgroupOf 2 J X hJX
    constructor
    · intro hx
      rw [← h3]
      exact mem_map_of_mem X.subtype hx
    · intro hx
      rw [← h3] at hx
      obtain ⟨y, hy, hyx⟩ := mem_map.mp hx
      have hyeq : y = x := Subtype.ext hyx
      rwa [← hyeq]
  have hBN : zpowers t' ≤ normalizer (J' : Set X) :=
    zpowers_le.mpr (mem_normalizer_subgroupOf_of_mem htJ)
  have hB : IsPGroup 2 (zpowers t') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, ht, pow_one])
  have hQ : IsQuasisimple (J' ⧸ pPrimeCore 2 J') :=
    isQuasisimple_of_mulEquiv
      (UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 (subgroupOfEquivOfLe hJX)).symm
      hJq
  have hzp : ∀ g ∈ zpowers t', g = 1 ∨ g = t' := by
    intro g hg
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
    have htt' : t' * t' = 1 := Subtype.ext htt
    rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
    · left
      rw [zpow_mul, zpow_two, htt', one_zpow]
    · right
      rw [zpow_add, zpow_mul, zpow_two, htt', one_zpow, one_mul, zpow_one]
  have hcomm' : ⁅J', zpowers t'⁆ ≤ (pPrimeCore 2 J').map J'.subtype := by
    rw [commutator_le]
    intro j hj g hg
    rcases hzp g hg with rfl | rfl
    · rw [commutatorElement_one_right]
      exact one_mem _
    · rw [hcore]
      have h1 := hcomm _ (inv_mem (show ((j : X) : G) ∈ J from hj))
      rw [inv_inv, htinv] at h1
      show (j : G) * t * (j : G)⁻¹ * t⁻¹ ∈ _
      rwa [htinv]
  have hcen : centralizer ((zpowers t' : Subgroup X) : Set X) =
      (X ⊓ centralizer ({t} : Set G)).subgroupOf X := by
    rw [centralizer_zpowers_eq]
    ext x
    rw [mem_centralizer_singleton_iff, mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff]
    constructor
    · intro h1
      exact ⟨x.2, congrArg Subtype.val h1⟩
    · intro h1
      exact Subtype.ext h1.2
  have hC : J' ⊓ centralizer ((zpowers t' : Subgroup X) : Set X) =
      (J ⊓ centralizer ({t} : Set G)).subgroupOf X := by
    rw [hcen]
    ext x
    simp only [mem_inf, mem_subgroupOf, hJ']
    tauto
  obtain ⟨-, -, -, -, hpc, -⟩ := UnbalancedGS.trivial_quotient_action_fixed_layer_is_p_component 2
    J' hJsub (zpowers t') hBN hB hQ hcomm' _ rfl _ rfl
  have hTX : (pLayer ↥(J' ⊓ centralizer ((zpowers t' : Subgroup X) : Set X)) 2).map
      (J' ⊓ centralizer ((zpowers t' : Subgroup X) : Set X)).subtype =
      (UnbalancedGS.gsFixedLayer J t).subgroupOf X := by
    apply map_injective X.subtype_injective
    rw [map_subgroupOf_eq_of_le ((UnbalancedGS.gsFixedLayer_le_inf J t).trans
      (inf_le_left.trans hJX)), hC, map_pLayer_subgroupOf_eq X _,
      inf_of_le_right (inf_le_left.trans hJX)]
    rfl
  rw [hTX, hcen] at hpc
  exact (isPComponent_subgroupOf_subgroupOf_iff' inf_le_left 2 Nat.prime_two).mp hpc


omit [Finite G] in
theorem corrImage_conj_mem {c b : G} {J L : Subgroup G} (h : UnbalancedGS.GSCorr c J b L)
    (hcH : c ∈ centralizer ({b} : Set G)) :
    ∀ u ∈ UnbalancingLocal.corrImage b L,
      ((⟨c, hcH⟩ : centralizer ({b} : Set G)) : UnbalancingLocal.CorrQuotient b) * u *
        ((⟨c, hcH⟩ : centralizer ({b} : Set G)) : UnbalancingLocal.CorrQuotient b)⁻¹ ∈
        UnbalancingLocal.corrImage b (conjugate L c) := by
  obtain ⟨hco, -⟩ := h
  have hcc : c * c = 1 := by rw [← pow_two, ← hco, pow_orderOf_eq_one]
  intro u hu
  obtain ⟨l, hl, rfl⟩ := mem_map.mp hu
  refine ⟨⟨c, hcH⟩ * l * ⟨c, hcH⟩⁻¹, ?_, by rw [map_mul, map_mul, map_inv]; rfl⟩
  show ((⟨c, hcH⟩ * l * ⟨c, hcH⟩⁻¹ : centralizer ({b} : Set G)) : G) ∈ conjugate L c
  rw [mem_conjugate_iff]
  have hl' : (l : G) ∈ L := hl
  rwa [show c * ((⟨c, hcH⟩ * l * ⟨c, hcH⟩⁻¹ : centralizer ({b} : Set G)) : G) * c⁻¹ =
      (l : G) by
    simp only [coe_mul, coe_inv]
    rw [show c * (c * (l : G) * c⁻¹) * c⁻¹ = (c * c) * l * (c * c)⁻¹ by group, hcc]
    group]

theorem corrImage_gsFixedLayer_eq {c b : G} {J L : Subgroup G} (h : UnbalancedGS.GSCorr c J b L)
    (hne : conjugate L c ≠ L) (hcH : c ∈ centralizer ({b} : Set G)) :
    ∀ x, x ∈ UnbalancingLocal.corrImage b (UnbalancedGS.gsFixedLayer J b) ↔
      ∃ u ∈ UnbalancingLocal.corrImage b L,
        x = u * (((⟨c, hcH⟩ : centralizer ({b} : Set G)) : UnbalancingLocal.CorrQuotient b) * u *
          ((⟨c, hcH⟩ : centralizer ({b} : Set G)) : UnbalancingLocal.CorrQuotient b)⁻¹) := by
  obtain ⟨α, hαk, -, -, -, -, -, -, hmemT, -⟩ :=
    (UnbalancingLocal.correspondence_quotient_order_comparison h).2.2.1 hne hcH
  intro x
  rw [hmemT x]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, by rw [coe_mul, hαk u]⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨⟨u, le_sup_left (a := UnbalancingLocal.corrImage b L) hu⟩, hu, by rw [coe_mul, hαk]⟩

theorem source_change_moved {a c b : G} {J L : Subgroup G} (ha : orderOf a = 2)
    (hac : a * c = c * a) (hab : a * b = b * a) (hJa : J ≤ centralizer ({a} : Set G))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G))))
    (h : UnbalancedGS.GSCorr c J b L) (hne : conjugate L c ≠ L) : conjugate L a ≠ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hLa
  have hcmp := UnbalancingLocal.correspondence_quotient_order_comparison h
  have hγ := corrImage_conj_mem h
  have hΔ := corrImage_gsFixedLayer_eq h hne
  have hcorr := h
  obtain ⟨-, hbo, hcb, -, -, hLb, hL, hbN, hcomm, -⟩ := hcorr
  set H := centralizer ({b} : Set G) with hHdef
  have haa : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have haH : a ∈ H := mem_centralizer_singleton_iff.mpr hab
  have hcH : c ∈ H := mem_centralizer_singleton_iff.mpr hcb
  obtain ⟨α, -, -, hABc, hAq, -, hDcent, -, -, -⟩ := hcmp.2.2.1 hne hcH
  have hγ' := hγ hcH
  have hΔ' := hΔ hcH
  set T := UnbalancedGS.gsFixedLayer J b with hTdef
  have hTJ : T ≤ J := (UnbalancedGS.gsFixedLayer_le_inf J b).trans inf_le_left
  have hTH : T ≤ H := (UnbalancedGS.gsFixedLayer_le_inf J b).trans inf_le_right
  set π := QuotientGroup.mk' (pPrimeCore 2 H) with hπ
  set A := UnbalancingLocal.corrImage b L with hAdef
  set B := UnbalancingLocal.corrImage b (conjugate L c) with hBdef
  set abar : UnbalancingLocal.CorrQuotient b := ((⟨a, haH⟩ : H) : UnbalancingLocal.CorrQuotient b)
    with habardef
  set cbar : UnbalancingLocal.CorrQuotient b := ((⟨c, hcH⟩ : H) : UnbalancingLocal.CorrQuotient b)
    with hcbardef
  set β : MulAut (UnbalancingLocal.CorrQuotient b) := MulAut.conj abar with hβdef
  have hβ : ∀ x, β x = abar * x * abar⁻¹ := fun x => MulAut.conj_apply abar x
  have hβc : β cbar = cbar := by
    rw [hβ, mul_inv_eq_iff_eq_mul, habardef, hcbardef, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext hac
  have hβA : ∀ u ∈ A, β u ∈ A := by
    intro u hu
    obtain ⟨l, hl, rfl⟩ := mem_map.mp hu
    refine ⟨⟨a, haH⟩ * l * ⟨a, haH⟩⁻¹, ?_, ?_⟩
    · show ((⟨a, haH⟩ * l * ⟨a, haH⟩⁻¹ : H) : G) ∈ L
      have hl' : (l : G) ∈ conjugate L a := by
        rw [hLa]
        exact hl
      rw [mem_conjugate_iff] at hl'
      simpa using hl'
    · rw [hβ, map_mul, map_mul, map_inv]
      rfl
  have hβT : ∀ x ∈ UnbalancingLocal.corrImage b T, β x = x := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := mem_map.mp hx
    have hta : (t : G) * a = a * t := mem_centralizer_singleton_iff.mp (hJa (hTJ ht))
    have h1 : (⟨a, haH⟩ : H) * t * (⟨a, haH⟩ : H)⁻¹ = t := by
      apply Subtype.ext
      simp only [coe_mul, coe_inv]
      rw [← hta, mul_inv_cancel_right]
    rw [hβ]
    calc abar * π t * abar⁻¹ = π ((⟨a, haH⟩ : H) * t * (⟨a, haH⟩ : H)⁻¹) := by
          rw [map_mul, map_mul, map_inv]
          rfl
      _ = π t := by rw [h1]
  have hβD : ∀ u ∈ A, u⁻¹ * β u ∈ A ⊓ B := by
    intro u hu
    have hw := hβA u hu
    have h1 := hβT _ ((hΔ' _).mpr ⟨u, hu, rfl⟩)
    rw [map_mul, map_mul, map_mul, map_inv, hβc] at h1
    have h2 : u⁻¹ * β u = cbar * (u * (β u)⁻¹) * cbar⁻¹ := by
      calc u⁻¹ * β u = u⁻¹ * (β u * (cbar * β u * cbar⁻¹)) * (cbar * β u * cbar⁻¹)⁻¹ := by group
        _ = u⁻¹ * (u * (cbar * u * cbar⁻¹)) * (cbar * β u * cbar⁻¹)⁻¹ := by rw [h1]
        _ = cbar * (u * (β u)⁻¹) * cbar⁻¹ := by group
    refine mem_inf.mpr ⟨mul_mem (inv_mem hu) hw, ?_⟩
    rw [h2]
    exact hγ' _ (mul_mem hu (inv_mem hw))
  have hAperf : ⁅A, A⁆ = A := Subgroup.isPerfect_iff.mp hAq.1
  have hβfix : ∀ u ∈ A, β u = u := by
    have hle : A ≤ MonoidHom.eqLocus β.toMonoidHom (MonoidHom.id _) := by
      rw [← hAperf, commutator_le]
      intro x hx y hy
      show β ⁅x, y⁆ = ⁅x, y⁆
      rw [map_commutatorElement]
      have hdx := hβD x hx
      have hdy := hβD y hy
      have h1 := commutatorElement_mul_mul_of_commute (x := x) (y := y) (d := x⁻¹ * β x)
        (e := y⁻¹ * β y) (hDcent _ hdx _ (mem_sup_left hy)) (hDcent _ hdy _ (mem_sup_left hx))
        (hDcent _ hdx _ (mem_sup_left (mem_inf.mp hdy).1))
      rwa [show x * (x⁻¹ * β x) = β x by group, show y * (y⁻¹ * β y) = β y by group] at h1
    intro u hu
    exact hle hu
  have hLsub : (L.subgroupOf H).IsSubnormal := by
    obtain ⟨-, -, hs, -, -⟩ := id hL
    exact hs
  have hOL := map_pPrimeCore_eq_inf_of_isSubnormal hLsub
  have hOLN : ∀ y ∈ (pPrimeCore 2 L).map L.subtype, ∀ hy : y ∈ H,
      (⟨y, hy⟩ : H) ∈ pPrimeCore 2 H := by
    intro y hy hyH
    rw [← pPrimeCore_map_subgroupOf 2 L H hLb] at hy
    obtain ⟨z, hz, hzy⟩ := mem_map.mp hy
    rw [hOL] at hz
    have hzeq : z = ⟨y, hyH⟩ := Subtype.ext hzy
    rw [← hzeq]
    exact (mem_inf.mp hz).2
  have hLa' : ∀ l ∈ L, l⁻¹ * a⁻¹ * l * a ∈ (pPrimeCore 2 L).map L.subtype := by
    intro l hl
    rw [hainv]
    have hlH : l ∈ H := hLb hl
    have hal : a * l * a ∈ L := by
      have hl' : l ∈ conjugate L a := by
        rw [hLa]
        exact hl
      rw [mem_conjugate_iff, hainv] at hl'
      exact hl'
    have hyL : l⁻¹ * a * l * a ∈ L := by
      rw [show l⁻¹ * a * l * a = l⁻¹ * (a * l * a) by group]
      exact mul_mem (inv_mem hl) hal
    have hyH : l⁻¹ * a * l * a ∈ H := mul_mem (mul_mem (mul_mem (inv_mem hlH) haH) hlH) haH
    rw [← pPrimeCore_map_subgroupOf 2 L H hLb]
    refine ⟨⟨l⁻¹ * a * l * a, hyH⟩, ?_, rfl⟩
    rw [hOL]
    refine mem_inf.mpr ⟨hyL, ?_⟩
    have hfix := hβfix (π ⟨l, hlH⟩) ⟨⟨l, hlH⟩, hl, rfl⟩
    rw [hβ] at hfix
    have hgoal : (⟨l⁻¹ * a * l * a, hyH⟩ : H) =
        (⟨l, hlH⟩ : H)⁻¹ * ((⟨a, haH⟩ : H) * ⟨l, hlH⟩ * (⟨a, haH⟩ : H)⁻¹) := by
      apply Subtype.ext
      simp only [coe_mul, coe_inv]
      rw [hainv]
      group
    rw [← QuotientGroup.eq_one_iff, hgoal, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have h1 : (((⟨a, haH⟩ : H) * ⟨l, hlH⟩ * (⟨a, haH⟩ : H)⁻¹ : H) :
        UnbalancingLocal.CorrQuotient b) = π ⟨l, hlH⟩ := by
      rw [← hfix]
      rfl
    rw [h1]
    exact inv_mul_cancel _
  have haN : a ∈ normalizer (L : Set G) := mem_normalizer_of_conjugate_eq hLa
  have hLq : IsQuasisimple (L ⧸ pPrimeCore 2 L) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 L _ hLb).mp hL).2.2
  set W := UnbalancedGS.gsFixedLayer L a with hWdef
  have hWpc : IsPComponent 2 (W.subgroupOf (H ⊓ centralizer ({a} : Set G))) :=
    gsFixedLayer_isPComponent hLb hLsub haH ha haN hLq hLa'
  have hWsup : W ⊔ (pPrimeCore 2 L).map L.subtype = L :=
    gsFixedLayer_sup_map_pPrimeCore ha hLq haN hLa'
  have hWL : W ≤ L := le_sup_left.trans hWsup.le
  have hOW : (pPrimeCore 2 W).map W.subtype ≤ (pPrimeCore 2 L).map L.subtype := by
    rw [(restriction_quotient_mulEquiv hWL hWsup).1]
    exact inf_le_right
  have hWA : ∀ v ∈ A, ∃ w ∈ W, ∃ hw : w ∈ H, π ⟨w, hw⟩ = v := by
    intro v hv
    obtain ⟨l, hl, rfl⟩ := mem_map.mp hv
    have hl' : (l : G) ∈ (W : Set G) * ((pPrimeCore 2 L).map L.subtype : Set G) := by
      rw [← UnbalancedGS.coe_sup_primeCore_eq_mul hWL, hWsup]
      exact hl
    obtain ⟨w, hw, n, hn, hwn⟩ := Set.mem_mul.mp hl'
    have hwH : w ∈ H := hLb (hWL hw)
    have hnH : n ∈ H := hLb ((map_subtype_le _) hn)
    refine ⟨w, hw, hwH, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have hwl : (⟨w, hwH⟩ : H)⁻¹ * l = ⟨n, hnH⟩ := by
      apply Subtype.ext
      simp only [coe_mul, coe_inv]
      rw [← hwn]
      group
    rw [hwl]
    exact hOLN n hn hnH
  have hJsub : (J.subgroupOf (centralizer ({a} : Set G))).IsSubnormal := by
    obtain ⟨-, -, hs, -, -⟩ := id hJ
    exact hs
  have hJq : IsQuasisimple (J ⧸ pPrimeCore 2 J) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 J _ hJa).mp hJ).2.2
  have hbCa : b ∈ centralizer ({a} : Set G) := mem_centralizer_singleton_iff.mpr hab.symm
  have hTpc : IsPComponent 2 (T.subgroupOf (centralizer ({a} : Set G) ⊓ H)) :=
    gsFixedLayer_isPComponent hJa hJsub hbCa hbo hbN hJq hcomm
  rw [inf_comm] at hTpc
  have hcommA : ∀ v ∈ A, ∀ u ∈ A, ⁅v, u⁆ = 1 := by
    by_cases hTW : T = W
    · have hΔA : ∀ x ∈ UnbalancingLocal.corrImage b T, x ∈ A := by
        intro x hx
        rw [hTW] at hx
        have hWL' : W.subgroupOf H ≤ L.subgroupOf H := fun y hy => hWL hy
        exact map_mono hWL' hx
      have hcen : ∀ u ∈ A, cbar * u * cbar⁻¹ ∈ A ⊓ B := by
        intro u hu
        have h1 := hΔA _ ((hΔ' _).mpr ⟨u, hu, rfl⟩)
        have h2 : cbar * u * cbar⁻¹ = u⁻¹ * (u * (cbar * u * cbar⁻¹)) := by group
        refine mem_inf.mpr ⟨?_, hγ' u hu⟩
        rw [h2]
        exact mul_mem (inv_mem hu) h1
      intro v hv u hu
      have h1 := hDcent _ (hcen v hv) _ (mem_sup_left (mem_inf.mp (hcen u hu)).1)
      have h2 : cbar * ⁅v, u⁆ * cbar⁻¹ = 1 := by
        rw [show cbar * ⁅v, u⁆ * cbar⁻¹ = ⁅cbar * v * cbar⁻¹, cbar * u * cbar⁻¹⁆ by
          simp only [commutatorElement_def]
          group, commutatorElement_eq_one_iff_mul_comm.mpr h1]
      calc ⁅v, u⁆ = cbar⁻¹ * (cbar * ⁅v, u⁆ * cbar⁻¹) * cbar := by group
        _ = 1 := by rw [h2]; group
    · set Y := H ⊓ centralizer ({a} : Set G) with hYdef
      have hTY : T ≤ Y := le_inf hTH (hTJ.trans hJa)
      have hWY : W ≤ Y :=
        (UnbalancedGS.gsFixedLayer_le_inf L a).trans (inf_le_inf_right _ hLb)
      have hne₁ : T.subgroupOf Y ≠ W.subgroupOf Y := by
        intro heq
        apply hTW
        rw [subgroupOf_inj, inf_of_le_left hTY, inf_of_le_left hWY] at heq
        exact heq
      obtain ⟨-, -, hcore, -⟩ := (CatalogueBPrimeJoin.distinct_p_components_core_commutation 2
        Nat.prime_two _ _ hTpc hWpc).2 hne₁
      have hTW' : ∀ t ∈ T, ∀ w ∈ W, ⁅t, w⁆ ∈ (pPrimeCore 2 L).map L.subtype := by
        intro t ht w hw
        have h1 : ⁅(⟨t, hTY ht⟩ : Y), ⟨w, hWY hw⟩⁆ ∈ ⁅T.subgroupOf Y, W.subgroupOf Y⁆ :=
          commutator_mem_commutator (show (⟨t, hTY ht⟩ : Y) ∈ T.subgroupOf Y from ht)
            (show (⟨w, hWY hw⟩ : Y) ∈ W.subgroupOf Y from hw)
        have h2 := mem_map_of_mem Y.subtype (mem_inf.mp (hcore h1)).2
        rw [pPrimeCore_map_subgroupOf 2 W Y hWY] at h2
        apply hOW
        have h3 : Y.subtype ⁅(⟨t, hTY ht⟩ : Y), ⟨w, hWY hw⟩⁆ = ⁅t, w⁆ := by
          simp [commutatorElement_def]
        rwa [h3] at h2
      intro v hv u hu
      obtain ⟨w, hw, hwH, rfl⟩ := hWA v hv
      obtain ⟨t, ht, htu⟩ := mem_map.mp ((hΔ' _).mpr ⟨u, hu, rfl⟩)
      have hvw : π ⟨w, hwH⟩ * (cbar * u * cbar⁻¹) = (cbar * u * cbar⁻¹) * π ⟨w, hwH⟩ :=
        hABc _ hv _ (hγ' u hu)
      have hwv : (cbar * u * cbar⁻¹) * (π ⟨w, hwH⟩)⁻¹ = (π ⟨w, hwH⟩)⁻¹ * (cbar * u * cbar⁻¹) :=
        (Commute.inv_right (show Commute (cbar * u * cbar⁻¹) (π ⟨w, hwH⟩) from hvw.symm)).eq
      have hid : ⁅π ⟨w, hwH⟩, u⁆ = ⁅π ⟨w, hwH⟩, u * (cbar * u * cbar⁻¹)⁆ := by
        rw [commutatorElement_def, commutatorElement_def]
        calc π ⟨w, hwH⟩ * u * (π ⟨w, hwH⟩)⁻¹ * u⁻¹ =
            π ⟨w, hwH⟩ * u * ((π ⟨w, hwH⟩)⁻¹ * (cbar * u * cbar⁻¹)) * (cbar * u * cbar⁻¹)⁻¹ *
              u⁻¹ := by
              group
          _ = π ⟨w, hwH⟩ * u * ((cbar * u * cbar⁻¹) * (π ⟨w, hwH⟩)⁻¹) *
              (cbar * u * cbar⁻¹)⁻¹ * u⁻¹ := by rw [hwv]
          _ = π ⟨w, hwH⟩ * (u * (cbar * u * cbar⁻¹)) * (π ⟨w, hwH⟩)⁻¹ *
              (u * (cbar * u * cbar⁻¹))⁻¹ := by group
      rw [hid, ← htu, ← map_commutatorElement, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      have htT : (t : G) ∈ T := ht
      have h2 : ⁅w, (t : G)⁆ ∈ (pPrimeCore 2 L).map L.subtype := by
        rw [← commutatorElement_inv]
        exact inv_mem (hTW' _ htT w hw)
      have hcH' : ⁅w, (t : G)⁆ ∈ H := by
        rw [commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem hwH t.2) (inv_mem hwH)) (inv_mem t.2)
      have heq : ⁅(⟨w, hwH⟩ : H), t⁆ = ⟨⁅w, (t : G)⁆, hcH'⟩ := by
        apply Subtype.ext
        simp [commutatorElement_def]
      rw [heq]
      exact hOLN _ h2 hcH'
  have hAnt : Nontrivial A := by
    have : IsSimpleGroup (A ⧸ center A) := hAq.2.1
    exact (QuotientGroup.mk'_surjective (center A)).nontrivial
  have hbot : A = ⊥ := eq_bot_of_perfect_of_comm hAperf fun x hx y hy =>
    commutatorElement_eq_one_iff_mul_comm.mp (hcommA x hx y hy)
  exact (Subgroup.nontrivial_iff_ne_bot _).mp hAnt hbot

theorem commuting_source_change_and_quotient_control {a c b : G} {J L : Subgroup G}
    (ha : orderOf a = 2) (hac : a * c = c * a) (hab : a * b = b * a)
    (hJa : J ≤ centralizer ({a} : Set G))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G))))
    (h : UnbalancedGS.GSCorr c J b L) {T K : Subgroup G}
    (hT : T = UnbalancedGS.gsFixedLayer J b) (hK : K = L ⊔ conjugate L c) :
    a ∈ normalizer (K : Set G) ∧
    (fun U => conjugate U a) '' {L, conjugate L c} = {L, conjugate L c} ∧
    (conjugate L c = L → conjugate L a = L) ∧
    (conjugate L c ≠ L → conjugate L a = conjugate L c) ∧
    K = L ⊔ conjugate L a ∧ T ≤ K ⊓ centralizer ({a} : Set G) ∧
    IsPComponent 2 (T.subgroupOf (K ⊓ centralizer ({a} : Set G))) ∧
    T ⊔ (pPrimeCore 2 J).map J.subtype = J ∧
    (pPrimeCore 2 T).map T.subtype = T ⊓ (pPrimeCore 2 J).map J.subtype ∧
    (∃ e : T ⧸ pPrimeCore 2 T ≃* J ⧸ pPrimeCore 2 J,
      ∀ (t : T) (ht : (t : G) ∈ J), e t = ((⟨t, ht⟩ : J) : J ⧸ pPrimeCore 2 J)) ∧
    (pPrimeCore 2 J).index ≤ (pPrimeCore 2 L).index ∧
    ((conjugate L c ≠ L ∨ (pPrimeCore 2 J).index = (pPrimeCore 2 L).index) →
      UnbalancedGS.GSCorr a J b L ∧
        Nonempty (J ⧸ Open.fusionZStar J ≃* L ⧸ Open.fusionZStar L)) ∧
    ((pPrimeCore 2 J).index = (pPrimeCore 2 L).index → conjugate L c = L →
      UnbalancedGS.GSIsoCorr a J b L) ∧
    (conjugate L c ≠ L → ∀ hc : c ∈ centralizer ({b} : Set G),
      (∃ δ : ↥(UnbalancingLocal.corrImage b L) →* ↥(UnbalancingLocal.corrImage b T),
        Function.Surjective δ ∧
        (∀ u, (δ u : UnbalancingLocal.CorrQuotient b) =
          u * (((⟨c, hc⟩ : centralizer ({b} : Set G)) : UnbalancingLocal.CorrQuotient b) * u *
            ((⟨c, hc⟩ : centralizer ({b} : Set G)) : UnbalancingLocal.CorrQuotient b)⁻¹)) ∧
        (∀ u, δ u = 1 ↔ (u : UnbalancingLocal.CorrQuotient b) ∈
            UnbalancingLocal.corrImage b (conjugate L c) ∧
          ((⟨c, hc⟩ : centralizer ({b} : Set G)) : UnbalancingLocal.CorrQuotient b) * u *
            ((⟨c, hc⟩ : centralizer ({b} : Set G)) : UnbalancingLocal.CorrQuotient b)⁻¹ =
            (u : UnbalancingLocal.CorrQuotient b)⁻¹) ∧
        δ.ker ≤ center ↥(UnbalancingLocal.corrImage b L)) ∧
      (∃ eL : L ⧸ pPrimeCore 2 L ≃* ↥(UnbalancingLocal.corrImage b L),
        ∀ (l : L) (hl : (l : G) ∈ centralizer ({b} : Set G)),
          (eL l : UnbalancingLocal.CorrQuotient b) =
            ((⟨l, hl⟩ : centralizer ({b} : Set G)) : UnbalancingLocal.CorrQuotient b)) ∧
      (∃ eT : T ⧸ pPrimeCore 2 T ≃* ↥(UnbalancingLocal.corrImage b T),
        ∀ (t : T) (ht : (t : G) ∈ centralizer ({b} : Set G)),
          (eT t : UnbalancingLocal.CorrQuotient b) =
            ((⟨t, ht⟩ : centralizer ({b} : Set G)) : UnbalancingLocal.CorrQuotient b)) ∧
      ∃ φ : J ⧸ Open.fusionZStar J ≃* L ⧸ Open.fusionZStar L,
        ∀ (t : J) (l : L) (_htT : (t : G) ∈ T) (ht : (t : G) ∈ centralizer ({b} : Set G))
          (hl : (l : G) ∈ centralizer ({b} : Set G))
          (hlc : c * l * c⁻¹ ∈ centralizer ({b} : Set G)),
          ((⟨t, ht⟩ : centralizer ({b} : Set G)) : UnbalancingLocal.CorrQuotient b) =
            ((⟨l, hl⟩ : centralizer ({b} : Set G)) : UnbalancingLocal.CorrQuotient b) *
              ((⟨c * l * c⁻¹, hlc⟩ : centralizer ({b} : Set G)) :
                UnbalancingLocal.CorrQuotient b) →
          φ (t : J ⧸ Open.fusionZStar J) = (l : L ⧸ Open.fusionZStar L)) ∧
    ((pPrimeCore 2 J).index = (pPrimeCore 2 L).index → conjugate L c = L →
      (∃ e : T ⧸ pPrimeCore 2 T ≃* L ⧸ pPrimeCore 2 L,
        ∀ (t : T) (ht : (t : G) ∈ L), e t = ((⟨t, ht⟩ : L) : L ⧸ pPrimeCore 2 L)) ∧
      ∃ φ : J ⧸ Open.fusionZStar J ≃* L ⧸ Open.fusionZStar L,
        ∀ (t : T) (htJ : (t : G) ∈ J) (htL : (t : G) ∈ L),
          φ ((⟨t, htJ⟩ : J) : J ⧸ Open.fusionZStar J) =
            ((⟨t, htL⟩ : L) : L ⧸ Open.fusionZStar L)) ∧
    ((¬ UnbalancedGS.GSCorr a J b L ∨
        IsEmpty (J ⧸ Open.fusionZStar J ≃* L ⧸ Open.fusionZStar L)) →
      conjugate L a = L ∧ conjugate L c = L ∧ (pPrimeCore 2 J).index < (pPrimeCore 2 L).index) ∧
    (¬ UnbalancedGS.GSCorr a J b L → T < UnbalancedGS.gsFixedLayer L a ∧
      IsPComponent 2 (T.subgroupOf (L ⊓ centralizer ({a} : Set G)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  subst hT hK
  have hcard := UnbalancingLocal.Correspondence.card_gsFixedLayer_quotient h
  have hcmp := UnbalancingLocal.correspondence_quotient_order_comparison h
  have hnc := (correspondence_normal_closure h rfl rfl rfl).2.2.2
  have hcorr := h
  obtain ⟨hco, hbo, hcb, -, -, hLb, hL, hbN, hcomm, hfix⟩ := hcorr
  set H := centralizer ({b} : Set G) with hHdef
  set T := UnbalancedGS.gsFixedLayer J b with hTdef
  have haa : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  have hcc : c * c = 1 := by rw [← pow_two, ← hco, pow_orderOf_eq_one]
  have haH : a ∈ H := mem_centralizer_singleton_iff.mpr hab
  have hcH : c ∈ H := mem_centralizer_singleton_iff.mpr hcb
  have hbCa : b ∈ centralizer ({a} : Set G) := mem_centralizer_singleton_iff.mpr hab.symm
  have haJ : a ∈ normalizer (J : Set G) :=
    mem_normalizer_of_conjugate_eq (conjugate_eq_self_of_le_centralizer hJa)
  obtain ⟨haK, hperm⟩ := hnc a (mem_inf.mpr ⟨haH, haJ⟩)
  have hmemL : conjugate L a ∈ ({L, conjugate L c} : Set (Subgroup G)) := by
    rw [← hperm]
    exact ⟨L, Or.inl rfl, rfl⟩
  have horbit₁ : conjugate L c = L → conjugate L a = L := by
    intro hLc
    rcases hmemL with h1 | h1
    · exact h1
    · rw [h1, hLc]
  have horbit₂ : conjugate L c ≠ L → conjugate L a = conjugate L c := by
    intro hne
    rcases hmemL with h1 | h1
    · exact absurd h1 (source_change_moved ha hac hab hJa hJ h hne)
    · exact h1
  have hKeq : L ⊔ conjugate L c = L ⊔ conjugate L a := by
    by_cases hLc : conjugate L c = L
    · rw [hLc, horbit₁ hLc]
    · rw [horbit₂ hLc]
  have hTJ : T ≤ J := (UnbalancedGS.gsFixedLayer_le_inf J b).trans inf_le_left
  have hTH : T ≤ H := (UnbalancedGS.gsFixedLayer_le_inf J b).trans inf_le_right
  have hTK : T ≤ L ⊔ conjugate L c := by
    rw [hfix]
    exact (UnbalancedGS.gsFixedLayer_le_inf _ c).trans inf_le_left
  have hTKa : T ≤ (L ⊔ conjugate L c) ⊓ centralizer ({a} : Set G) := le_inf hTK (hTJ.trans hJa)
  have hJsub : (J.subgroupOf (centralizer ({a} : Set G))).IsSubnormal := by
    obtain ⟨-, -, hs, -, -⟩ := id hJ
    exact hs
  have hJq : IsQuasisimple (J ⧸ pPrimeCore 2 J) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 J _ hJa).mp hJ).2.2
  have hLaH : conjugate L a ≤ H := fun y hy => by
    rw [mem_conjugate_iff] at hy
    have h1 := mul_mem (mul_mem (inv_mem haH) (hLb hy)) haH
    rwa [show a⁻¹ * (a * y * a⁻¹) * a = y by group] at h1
  have hLcH : conjugate L c ≤ H := fun y hy => by
    rw [mem_conjugate_iff] at hy
    have h1 := mul_mem (mul_mem (inv_mem hcH) (hLb hy)) hcH
    rwa [show c⁻¹ * (c * y * c⁻¹) * c = y by group] at h1
  have hKH : L ⊔ conjugate L c ≤ H := sup_le hLb hLcH
  have hTpc0 : IsPComponent 2 (T.subgroupOf (centralizer ({a} : Set G) ⊓ H)) :=
    gsFixedLayer_isPComponent hJa hJsub hbCa hbo hbN hJq hcomm
  have hTpc : IsPComponent 2 (T.subgroupOf ((L ⊔ conjugate L c) ⊓ centralizer ({a} : Set G))) :=
    CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hTKa
      (le_inf inf_le_right (inf_le_left.trans hKH)) hTpc0
  have hTsupJ : T ⊔ (pPrimeCore 2 J).map J.subtype = J :=
    gsFixedLayer_sup_map_pPrimeCore hbo hJq hbN hcomm
  obtain ⟨hcoreJ, eJ, heJ⟩ := restriction_quotient_mulEquiv hTJ hTsupJ
  have hindexle : (pPrimeCore 2 J).index ≤ (pPrimeCore 2 L).index := by
    rw [index_eq_card, index_eq_card]
    exact hcmp.1
  set a' : H := ⟨a, haH⟩ with ha'def
  have ha' : orderOf a' = 2 := by rw [Subgroup.orderOf_mk, ha]
  have hMa : conjugate (L.subgroupOf H) a' = (conjugate L a).subgroupOf H :=
    conjugate_subgroupOf_eq L H a'
  have hKH' : (L ⊔ conjugate L a).subgroupOf H =
      L.subgroupOf H ⊔ conjugate (L.subgroupOf H) a' := by
    rw [hMa]
    apply map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le (sup_le hLb hLaH), Subgroup.map_sup,
      map_subgroupOf_eq_of_le hLb, map_subgroupOf_eq_of_le hLaH]
  have hCH : (L ⊔ conjugate L a).subgroupOf H ⊓ centralizer ({a'} : Set H) =
      ((L ⊔ conjugate L a) ⊓ centralizer ({a} : Set G)).subgroupOf H := by
    ext x
    rw [mem_inf, mem_subgroupOf, mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff,
      mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, congrArg Subtype.val h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, Subtype.ext h2⟩
  have hKaH : (L ⊔ conjugate L a) ⊓ centralizer ({a} : Set G) ≤ H :=
    inf_le_left.trans (sup_le hLb hLaH)
  have hTCH : T.subgroupOf H ≤ (L ⊔ conjugate L a).subgroupOf H ⊓ centralizer ({a'} : Set H) := by
    rw [hCH]
    intro y hy
    have := hTKa hy
    rwa [hKeq] at this
  have hTpcH : IsPComponent 2 ((T.subgroupOf H).subgroupOf
      ((L ⊔ conjugate L a).subgroupOf H ⊓ centralizer ({a'} : Set H))) := by
    rw [hCH, isPComponent_subgroupOf_subgroupOf_iff' hKaH 2 Nat.prime_two]
    rw [← hKeq]
    exact hTpc
  obtain ⟨-, hcmpH₂, hcmpH₃⟩ := UnbalancedGS.involution_orbit_fixed_component_quotient_comparison
    ha' (L.subgroupOf H) hL _ hKH' _ rfl (T.subgroupOf H) hTCH hTpcH
  have hlayer : (pLayer ↥((L ⊔ conjugate L a).subgroupOf H ⊓ centralizer ({a'} : Set H)) 2).map
      ((L ⊔ conjugate L a).subgroupOf H ⊓ centralizer ({a'} : Set H)).subtype = T.subgroupOf H →
      T = UnbalancedGS.gsFixedLayer (L ⊔ conjugate L a) a := by
    intro h1
    have h2 := UnbalancingLocal.Correspondence.gsFixedLayer_subgroupOf (sup_le hLb hLaH) haH
    have h3 : (UnbalancedGS.gsFixedLayer (L ⊔ conjugate L a) a).subgroupOf H = T.subgroupOf H :=
      h2.trans h1
    have hFH : UnbalancedGS.gsFixedLayer (L ⊔ conjugate L a) a ≤ H :=
      (UnbalancedGS.gsFixedLayer_le_inf _ a).trans hKaH
    rw [subgroupOf_inj, inf_of_le_left hFH, inf_of_le_left hTH] at h3
    exact h3.symm
  have hTindex : (pPrimeCore 2 (T.subgroupOf H)).index = (pPrimeCore 2 J).index := by
    rw [index_eq_card, index_eq_card, ← hcard,
      UnbalancingLocal.Correspondence.card_quotient_pPrimeCore_congr (subgroupOfEquivOfLe hTH)]
  have hLindex : (pPrimeCore 2 (L.subgroupOf H)).index = (pPrimeCore 2 L).index := by
    rw [index_eq_card, index_eq_card,
      UnbalancingLocal.Correspondence.card_quotient_pPrimeCore_congr (subgroupOfEquivOfLe hLb)]
  have hcorrA : (conjugate L c ≠ L ∨ (pPrimeCore 2 J).index = (pPrimeCore 2 L).index) →
      UnbalancedGS.GSCorr a J b L := by
    intro hcase
    have hfix' : T = UnbalancedGS.gsFixedLayer (L ⊔ conjugate L a) a := by
      rcases hcase with hne | heq
      · apply hlayer
        apply hcmpH₂
        intro hMM
        apply hne
        rw [← horbit₂ hne]
        have h1 := congrArg (Subgroup.map H.subtype) hMM
        rw [hMa, map_subgroupOf_eq_of_le hLb, map_subgroupOf_eq_of_le hLaH] at h1
        exact h1.symm
      · exact hlayer (hcmpH₃ (by rw [hTindex, hLindex, heq])).1
    exact ⟨ha, hbo, hab, hJa, hJ, hLb, hL, hbN, hcomm, hfix'⟩
  have hiso : (pPrimeCore 2 J).index = (pPrimeCore 2 L).index → conjugate L c = L →
      UnbalancedGS.GSIsoCorr a J b L := by
    intro heq hLc
    have hLa := horbit₁ hLc
    have hcorr' := hcorrA (Or.inr heq)
    have h1 := (hcmpH₃ (by rw [hTindex, hLindex, heq])).2 (by rw [hMa, hLa])
    have h2 := congrArg (Subgroup.map H.subtype) h1
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hTH, pPrimeCore_map_subgroupOf 2 L H hLb,
      map_subgroupOf_eq_of_le hLb] at h2
    exact UnbalancedGS.gsIsoCorr_iff_sup.mpr ⟨hcorr', by rw [hLa, sup_idem], h2⟩
  obtain ⟨zJ, hzJ⟩ := exists_zstar_equiv J
  obtain ⟨zL, hzL⟩ := exists_zstar_equiv L
  have hAq : ∀ hne : conjugate L c ≠ L,
      IsQuasisimple ↥(UnbalancingLocal.corrImage b L) := fun hne => by
    obtain ⟨α, -, -, -, hAq, -⟩ := hcmp.2.2.1 hne hcH
    exact hAq
  have hmoved : conjugate L c ≠ L → ∀ hc : c ∈ centralizer ({b} : Set G),
      (∃ δ : ↥(UnbalancingLocal.corrImage b L) →* ↥(UnbalancingLocal.corrImage b T),
        Function.Surjective δ ∧
        (∀ u, (δ u : UnbalancingLocal.CorrQuotient b) =
          u * (((⟨c, hc⟩ : centralizer ({b} : Set G)) : UnbalancingLocal.CorrQuotient b) * u *
            ((⟨c, hc⟩ : centralizer ({b} : Set G)) : UnbalancingLocal.CorrQuotient b)⁻¹)) ∧
        (∀ u, δ u = 1 ↔ (u : UnbalancingLocal.CorrQuotient b) ∈
            UnbalancingLocal.corrImage b (conjugate L c) ∧
          ((⟨c, hc⟩ : centralizer ({b} : Set G)) : UnbalancingLocal.CorrQuotient b) * u *
            ((⟨c, hc⟩ : centralizer ({b} : Set G)) : UnbalancingLocal.CorrQuotient b)⁻¹ =
            (u : UnbalancingLocal.CorrQuotient b)⁻¹) ∧
        δ.ker ≤ center ↥(UnbalancingLocal.corrImage b L)) ∧
      (∃ eL : L ⧸ pPrimeCore 2 L ≃* ↥(UnbalancingLocal.corrImage b L),
        ∀ (l : L) (hl : (l : G) ∈ centralizer ({b} : Set G)),
          (eL l : UnbalancingLocal.CorrQuotient b) =
            ((⟨l, hl⟩ : centralizer ({b} : Set G)) : UnbalancingLocal.CorrQuotient b)) ∧
      (∃ eT : T ⧸ pPrimeCore 2 T ≃* ↥(UnbalancingLocal.corrImage b T),
        ∀ (t : T) (ht : (t : G) ∈ centralizer ({b} : Set G)),
          (eT t : UnbalancingLocal.CorrQuotient b) =
            ((⟨t, ht⟩ : centralizer ({b} : Set G)) : UnbalancingLocal.CorrQuotient b)) ∧
      ∃ φ : J ⧸ Open.fusionZStar J ≃* L ⧸ Open.fusionZStar L,
        ∀ (t : J) (l : L) (_htT : (t : G) ∈ T) (ht : (t : G) ∈ centralizer ({b} : Set G))
          (hl : (l : G) ∈ centralizer ({b} : Set G))
          (hlc : c * l * c⁻¹ ∈ centralizer ({b} : Set G)),
          ((⟨t, ht⟩ : centralizer ({b} : Set G)) : UnbalancingLocal.CorrQuotient b) =
            ((⟨l, hl⟩ : centralizer ({b} : Set G)) : UnbalancingLocal.CorrQuotient b) *
              ((⟨c * l * c⁻¹, hlc⟩ : centralizer ({b} : Set G)) :
                UnbalancingLocal.CorrQuotient b) →
          φ (t : J ⧸ Open.fusionZStar J) = (l : L ⧸ Open.fusionZStar L) := by
    intro hne hc
    obtain ⟨α, -, -, hABc, hAq', -, -, -, -, ⟨eT, heT⟩, -⟩ := hcmp.2.2.1 hne hc
    obtain ⟨δ, hδs, hδf, hδk, hδc⟩ := exists_diagonal_hom hABc (corrImage_conj_mem h hc)
      (corrImage_gsFixedLayer_eq h hne hc)
    have hLsub : (L.subgroupOf H).IsSubnormal := by
      obtain ⟨-, -, hs, -, -⟩ := id hL
      exact hs
    obtain ⟨eL, heL⟩ := exists_restriction_quotient_equiv_of_subnormal hLb hLsub
    obtain ⟨f, hf⟩ := exists_centerQuotient_chain eJ eT δ hδs hδc hAq'.1 eL
    refine ⟨⟨δ, hδs, hδf, hδk, hδc⟩, ⟨eL, heL⟩, ⟨eT, heT⟩, zJ.trans (f.trans zL.symm), ?_⟩
    intro t l htT ht hl hlc htl
    have h1 : ((t : J) : J ⧸ pPrimeCore 2 J) = eJ ((⟨t, htT⟩ : T) : T ⧸ pPrimeCore 2 T) := by
      rw [heJ ⟨t, htT⟩ t.2]
    have h2 : eT ((⟨t, htT⟩ : T) : T ⧸ pPrimeCore 2 T) = δ (eL (l : L ⧸ pPrimeCore 2 L)) := by
      apply Subtype.ext
      refine (heT ⟨t, htT⟩ ht).trans (Eq.trans ?_ (hδf (eL (l : L ⧸ pPrimeCore 2 L))).symm)
      rw [heL l hl, htl, show (⟨c * l * c⁻¹, hlc⟩ : centralizer ({b} : Set G)) =
        ⟨c, hc⟩ * ⟨l, hl⟩ * (⟨c, hc⟩ : centralizer ({b} : Set G))⁻¹ from Subtype.ext rfl,
        QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [MulEquiv.trans_apply, hzJ, h1, MulEquiv.trans_apply, hf _ _ h2,
      MulEquiv.symm_apply_eq, hzL]
  have hstable : (pPrimeCore 2 J).index = (pPrimeCore 2 L).index → conjugate L c = L →
      (∃ e : T ⧸ pPrimeCore 2 T ≃* L ⧸ pPrimeCore 2 L,
        ∀ (t : T) (ht : (t : G) ∈ L), e t = ((⟨t, ht⟩ : L) : L ⧸ pPrimeCore 2 L)) ∧
      ∃ φ : J ⧸ Open.fusionZStar J ≃* L ⧸ Open.fusionZStar L,
        ∀ (t : T) (htJ : (t : G) ∈ J) (htL : (t : G) ∈ L),
          φ ((⟨t, htJ⟩ : J) : J ⧸ Open.fusionZStar J) =
            ((⟨t, htL⟩ : L) : L ⧸ Open.fusionZStar L) := by
    intro heq hLc
    have hisoc := hiso heq hLc
    obtain ⟨-, hLL, hsupL⟩ := UnbalancedGS.gsIsoCorr_iff_sup.mp hisoc
    have hTL : T ≤ L := le_sup_left.trans hsupL.le
    obtain ⟨-, eL, heL⟩ := restriction_quotient_mulEquiv hTL hsupL
    obtain ⟨g, hg⟩ := exists_centerQuotient_congr (eJ.symm.trans eL)
    refine ⟨⟨eL, heL⟩, zJ.trans (g.trans zL.symm), fun t htJ htL => ?_⟩
    rw [MulEquiv.trans_apply, hzJ, MulEquiv.trans_apply, ← heJ t htJ, hg,
      MulEquiv.trans_apply, MulEquiv.symm_apply_apply, heL t htL, MulEquiv.symm_apply_eq, hzL]
  have hZiso : (conjugate L c ≠ L ∨ (pPrimeCore 2 J).index = (pPrimeCore 2 L).index) →
      Nonempty (J ⧸ Open.fusionZStar J ≃* L ⧸ Open.fusionZStar L) := by
    intro hcase
    by_cases hLc : conjugate L c = L
    · rcases hcase with hne | heq
      · exact absurd hLc hne
      · obtain ⟨-, φ, -⟩ := hstable heq hLc
        exact ⟨φ⟩
    · obtain ⟨-, -, -, φ, -⟩ := hmoved hLc hcH
      exact ⟨φ⟩
  have hfail : (¬ UnbalancedGS.GSCorr a J b L ∨
      IsEmpty (J ⧸ Open.fusionZStar J ≃* L ⧸ Open.fusionZStar L)) →
      conjugate L a = L ∧ conjugate L c = L ∧
        (pPrimeCore 2 J).index < (pPrimeCore 2 L).index := by
    intro hf
    have hgood : ¬ (conjugate L c ≠ L ∨ (pPrimeCore 2 J).index = (pPrimeCore 2 L).index) := by
      intro hcase
      rcases hf with hf | hf
      · exact hf (hcorrA hcase)
      · obtain ⟨φ⟩ := hZiso hcase
        exact hf.false φ
    push Not at hgood
    exact ⟨horbit₁ hgood.1, hgood.1, lt_of_le_of_ne hindexle hgood.2⟩
  refine ⟨haK, hperm, horbit₁, horbit₂, hKeq, hTKa, hTpc, hTsupJ, hcoreJ, ⟨eJ, heJ⟩, hindexle,
    fun hcase => ⟨hcorrA hcase, hZiso hcase⟩, hiso, hmoved, hstable, hfail, fun hnot => ?_⟩
  obtain ⟨hLa, hLc, -⟩ := hfail (Or.inl hnot)
  have hKL : L ⊔ conjugate L c = L := by rw [hLc, sup_idem]
  have hTpcL : IsPComponent 2 (T.subgroupOf (L ⊓ centralizer ({a} : Set G))) := by
    have h1 := hTpc
    rwa [hKL] at h1
  have hTle : T ≤ UnbalancedGS.gsFixedLayer L a := by
    have h1 : T.subgroupOf (L ⊓ centralizer ({a} : Set G)) ≤
        pLayer ↥(L ⊓ centralizer ({a} : Set G)) 2 := le_sSup hTpcL
    have hTLa : T ≤ L ⊓ centralizer ({a} : Set G) := by
      have h2 := hTKa
      rwa [hKL] at h2
    have h3 := map_mono (f := (L ⊓ centralizer ({a} : Set G)).subtype) h1
    rwa [map_subgroupOf_eq_of_le hTLa] at h3
  refine ⟨lt_of_le_of_ne hTle fun heq => hnot ?_, hTpcL⟩
  have hfix' : T = UnbalancedGS.gsFixedLayer (L ⊔ conjugate L a) a := by
    rw [hLa, sup_idem]
    exact heq
  exact ⟨ha, hbo, hab, hJa, hJ, hLb, hL, hbN, hcomm, hfix'⟩

end CFSG.ComponentClassification.UnbalancedCorr
