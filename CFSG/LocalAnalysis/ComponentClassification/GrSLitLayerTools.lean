module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitGW35
public import CFSG.LieType.AlgebraicGroups.RationalCentralizerCocycleComponents
public import CFSG.ClassicalInvolution.LBalance.Main
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAFixedLayerPComponent

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem isPComponent_subgroupOf_of_isSubnormal {K N H : Subgroup G} (hKN : K ≤ N) (hNH : N ≤ H)
    (hN : (N.subgroupOf H).IsSubnormal) (hK : IsPComponent 2 (K.subgroupOf N)) :
    IsPComponent 2 (K.subgroupOf H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := (LieType.AlgebraicGroups.isPComponent_subgroupOf_subgroupOf_iff (L := K) hNH 2
    Nat.prime_two).mpr hK
  exact (CatalogueBPrimeJoin.pComponent_subnormal_overgroup_iff 2 (K.subgroupOf H)
    (N.subgroupOf H) (fun x hx => hKN hx) hN).mp h1

omit [Finite G] in
theorem isPComponent_map_subgroupOf {N : Subgroup G} {K : Subgroup N} (hK : IsPComponent 2 K) :
    IsPComponent 2 ((K.map N.subtype).subgroupOf N) := by
  have h : (K.map N.subtype).subgroupOf N = K :=
    comap_map_eq_self_of_injective N.subtype_injective K
  rwa [h]

theorem pLayer_map_le_of_isSubnormal {N H : Subgroup G} (hNH : N ≤ H)
    (hN : (N.subgroupOf H).IsSubnormal) :
    (pLayer ↥N 2).map N.subtype ≤ (pLayer ↥H 2).map H.subtype := by
  rw [map_le_iff_le_comap]
  refine sSup_le fun K hK => ?_
  have hK' := isPComponent_subgroupOf_of_isSubnormal (map_subtype_le K) hNH hN
    (isPComponent_map_subgroupOf hK)
  have hle : (K.map N.subtype).subgroupOf H ≤ pLayer ↥H 2 := le_sSup hK'
  intro x hx
  refine ⟨⟨x, hNH x.2⟩, hle ?_, rfl⟩
  rw [mem_subgroupOf]
  exact ⟨x, hx, rfl⟩

theorem pLayer_map_le_of_le_sup {Q A Y : Subgroup G} (hQY : Q ≤ Y) (hYQA : Y ≤ Q ⊔ A)
    (hA : IsPGroup 2 A) (hAQ : A ≤ normalizer (Q : Set G)) :
    (pLayer ↥Y 2).map Y.subtype ≤ (pLayer ↥Q 2).map Q.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup Y := Q.subgroupOf Y with hNdef
  have hN : N.Normal := by
    rw [normal_subgroupOf_iff hQY]
    intro q y hq hy
    have hy' : y ∈ normalizer (Q : Set G) := sup_le le_normalizer hAQ (hYQA hy)
    exact (mem_normalizer_iff.mp hy' q).mp hq
  have hq : IsPGroup 2 (Y ⧸ N) := by
    intro z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N z
    obtain ⟨q, hq, a, ha, hqa⟩ := exists_mul_of_mem_sup_of_le_normalizer hAQ (hYQA y.2)
    obtain ⟨n, hn⟩ := hA ⟨a, ha⟩
    refine ⟨n, ?_⟩
    have ha' : a ∈ Y := by
      have : a = q⁻¹ * y := by rw [← hqa]; group
      rw [this]
      exact mul_mem (inv_mem (hQY hq)) y.2
    have h1 : QuotientGroup.mk' N y = QuotientGroup.mk' N ⟨a, ha'⟩ := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      change ((y : G)⁻¹ * a) ∈ Q
      have : (y : G)⁻¹ * a = a⁻¹ * q⁻¹ * a⁻¹⁻¹ := by rw [← hqa]; group
      rw [this]
      exact (mem_normalizer_iff.mp (inv_mem (hAQ ha)) q⁻¹).mp (inv_mem hq)
    rw [h1, ← map_pow]
    have h2 : (⟨a, ha'⟩ : Y) ^ 2 ^ n = 1 := by
      apply Subtype.ext
      have := congrArg Subtype.val hn
      simpa using this
    rw [h2, map_one]
  have : Group.IsSolvable (Y ⧸ N) := by
    have : Group.IsNilpotent (Y ⧸ N) := hq.isNilpotent
    infer_instance
  rw [map_le_iff_le_comap]
  refine sSup_le fun K hK => ?_
  obtain ⟨hKN, hK'⟩ :=
    (CatalogueBFixedCentralQuotient.p_components_solvable_quotient_invariance 2 Nat.prime_two N
      K).mp hK
  set K₀ : Subgroup G := K.map Y.subtype with hK₀
  have hK₀Q : K₀ ≤ Q := by
    rintro _ ⟨k, hk, rfl⟩
    exact hKN hk
  have hK₀eq : K₀.subgroupOf Y = K := comap_map_eq_self_of_injective Y.subtype_injective K
  have h1 : IsPComponent 2 ((K₀.subgroupOf Y).subgroupOf (Q.subgroupOf Y)) := by
    rw [hK₀eq]
    exact hK'
  have h2 := (LieType.AlgebraicGroups.isPComponent_subgroupOf_subgroupOf_iff (L := K₀) hQY 2
    Nat.prime_two).mp h1
  have hle : K₀.subgroupOf Q ≤ pLayer ↥Q 2 := le_sSup h2
  intro y hy
  refine ⟨⟨y, hKN hy⟩, hle ?_, rfl⟩
  rw [mem_subgroupOf]
  exact ⟨y, hy, rfl⟩

theorem pLayer_inf_centralizer_le {Y A : Subgroup G} (hAY : A ≤ Y) (hA : IsPGroup 2 A) :
    (pLayer ↥(Y ⊓ centralizer (A : Set G)) 2).map (Y ⊓ centralizer (A : Set G)).subtype ≤
      (pLayer ↥Y 2).map Y.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A' : Subgroup Y := A.subgroupOf Y with hA'
  have hA'2 : IsPGroup 2 A' := hA.comap_of_injective Y.subtype Y.subtype_injective
  have hbal := ClassicalInvolution.l2PrimeBalance ↥Y A' hA'2
  set Z : Subgroup Y := centralizer (A' : Set Y) with hZ
  have hZmap : Z.map Y.subtype = Y ⊓ centralizer (A : Set G) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine mem_inf.mpr ⟨z.2, mem_centralizer_iff.mpr fun a ha => ?_⟩
      exact congrArg Subtype.val (mem_centralizer_iff.mp hz ⟨a, hAY ha⟩ ha)
    · intro hx
      obtain ⟨hxY, hxC⟩ := mem_inf.mp hx
      refine ⟨⟨x, hxY⟩, mem_centralizer_iff.mpr fun a ha => ?_, rfl⟩
      exact Subtype.ext (mem_centralizer_iff.mp hxC (a : G) ha)
  let e : ↥Z ≃* ↥(Y ⊓ centralizer (A : Set G)) :=
    (Z.equivMapOfInjective Y.subtype Y.subtype_injective).trans (MulEquiv.subgroupCongr hZmap)
  have hlayer := UnbalancedGS.FixedLayerPComponent.map_pLayer_mulEquiv 2 e
  have key : (pLayer ↥(Y ⊓ centralizer (A : Set G)) 2).map
      (Y ⊓ centralizer (A : Set G)).subtype = ((pLayer ↥Z 2).map Z.subtype).map Y.subtype := by
    rw [← hlayer, map_map, map_map]
    congr 1
  rw [key]
  exact map_mono hbal

theorem pLayer_inf_centralizer_le_of_normalizes {Q A : Subgroup G} (hA : IsPGroup 2 A)
    (hAQ : A ≤ normalizer (Q : Set G)) :
    (pLayer ↥(Q ⊓ centralizer (A : Set G)) 2).map (Q ⊓ centralizer (A : Set G)).subtype ≤
      (pLayer ↥Q 2).map Q.subtype := by
  set Y : Subgroup G := Q ⊔ A with hY
  have hQY : Q ≤ Y := le_sup_left
  have hAY : A ≤ Y := le_sup_right
  have hsub : ((Q ⊓ centralizer (A : Set G)).subgroupOf (Y ⊓ centralizer (A : Set G))).IsSubnormal
      := by
    apply Subgroup.Normal.isSubnormal
    rw [normal_subgroupOf_iff (inf_le_inf_right _ hQY)]
    intro q y hq hy
    obtain ⟨hqQ, hqC⟩ := mem_inf.mp hq
    obtain ⟨hyY, hyC⟩ := mem_inf.mp hy
    have hyN : y ∈ normalizer (Q : Set G) := sup_le le_normalizer hAQ hyY
    exact mem_inf.mpr ⟨(mem_normalizer_iff.mp hyN q).mp hqQ,
      mul_mem (mul_mem hyC hqC) (inv_mem hyC)⟩
  have h1 := pLayer_map_le_of_isSubnormal (inf_le_inf_right _ hQY) hsub
  have h2 := pLayer_inf_centralizer_le hAY hA
  have h3 := pLayer_map_le_of_le_sup hQY le_rfl hA hAQ
  exact h1.trans (h2.trans h3)

theorem exists_twoComponent_centralizer_of_isPGroup {H : Type} [Group H] [Finite H]
    (K : Subgroup H) (hK : IsPComponent 2 K) (R : Subgroup H) (hR : IsPGroup 2 R)
    (hKR : ⁅K, R⁆ ≤ pPrimeCore 2 H) :
    ∃ K1 : Subgroup (centralizer (R : Set H)), IsPComponent 2 K1 ∧
      K ≤ K1.map (centralizer (R : Set H)).subtype ⊔ pPrimeCore 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Kt, hKt, -, hmap, -⟩ := hK
  set N := pPrimeCore 2 H with hN
  have hNn : N.Normal := pPrimeCore_normal
  have hNodd : Odd (Nat.card N) := by
    have := ComponentClassification.OddCore.odd_card H
    rwa [← CatalogueBAlternating.primeCore_two_eq_oddCore] at this
  have hcop : Nat.Coprime 2 (Nat.card N) := (Nat.coprime_two_left).2 hNodd
  let q := QuotientGroup.mk' N
  let C : Subgroup H := centralizer (R : Set H)
  let Ĉ : Subgroup (H ⧸ N) := centralizer ((R.map q : Subgroup (H ⧸ N)) : Set (H ⧸ N))
  have hKtC : Kt ≤ Ĉ := by
    rw [← hmap]
    rintro _ ⟨k, hk, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨r, hr, rfl⟩
    change q r * q k = q k * q r
    rw [← map_mul, ← map_mul]
    apply (QuotientGroup.eq (s := N)).2
    have h1 : ⁅k⁻¹, r⁻¹⁆ ∈ ⁅K, R⁆ := commutator_mem_commutator (K.inv_mem hk) (R.inv_mem hr)
    have h2 := hKR h1
    have h4 : (r * k)⁻¹ * (k * r) = ⁅k⁻¹, r⁻¹⁆ := by
      rw [commutatorElement_def]
      group
    rw [h4]
    exact h2
  have hcomp : IsComponent (Kt.subgroupOf Ĉ) :=
    LocalAnalysis.ComponentInitial.component_overgroup hKt hKtC
  have hOddĈ : Odd (Nat.card (pPrimeCore 2 Ĉ)) := by
    have := ComponentClassification.OddCore.odd_card Ĉ
    rwa [← CatalogueBAlternating.primeCore_two_eq_oddCore] at this
  have hsolv : Group.IsSolvable (pPrimeCore 2 Ĉ) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hOddĈ
  have hKtP : IsPComponent 2 (Kt.subgroupOf Ĉ) :=
    LocalAnalysis.ComponentInitial.isPComponent_of_isComponent_of_not_le 2 hcomp
      (LocalAnalysis.ComponentInitial.not_le_of_isComponent_of_isSolvable hcomp hsolv)
  have : Fact (IsPGroup 2 R) := ⟨hR⟩
  have hcent : Ĉ = C.map q := centralizer_map_quotient_eq_map_centralizer 2 R N hNn hcop
  let f : C →* Ĉ := (q.comp C.subtype).codRestrict Ĉ
    (fun c => by rw [hcent]; exact ⟨c, c.2, rfl⟩)
  have hf_surj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    rw [hcent] at hy
    obtain ⟨c, hc, rfl⟩ := hy
    exact ⟨⟨c, hc⟩, Subtype.ext rfl⟩
  have hf_ker : Odd (Nat.card f.ker) := by
    have hinj : Function.Injective
        ((((C.subtype.comp f.ker.subtype).codRestrict N
          (fun c => by
            have h1 : f (c : C) = 1 := c.2
            have h2 := congrArg Subtype.val h1
            change q (c : C) = 1 at h2
            exact (QuotientGroup.eq_one_iff _).1 h2)) : f.ker →* N)) := by
      intro a b hab
      have h1 := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h1)
    exact Odd.of_dvd_nat hNodd (Subgroup.card_dvd_of_injective _ hinj)
  have hKtT : TwoComponents.IsTwoComponent (Kt.subgroupOf Ĉ) :=
    (CatalogueBAlternating.pComponent_two_iff _).1 hKtP
  obtain ⟨K1, hK1, hK1map⟩ :=
    OddKernelTwoComponents.exists_lift f hf_surj hf_ker (Kt.subgroupOf Ĉ) hKtT
  refine ⟨K1, (CatalogueBAlternating.pComponent_two_iff K1).2 hK1, ?_⟩
  have himg : (K1.map C.subtype).map q = Kt := by
    have h0 : (K1.map C.subtype).map q = (K1.map f).map Ĉ.subtype := by
      rw [Subgroup.map_map, Subgroup.map_map]
      rfl
    rw [h0, hK1map, Subgroup.map_subgroupOf_eq_of_le hKtC]
  have hle : K.map q ≤ (K1.map C.subtype).map q := by rw [himg, hmap]
  have h := Subgroup.map_le_iff_le_comap.1 hle
  rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h

theorem le_pLayer_sup_of_cover {H : Type} [Group H] [Finite H] {L R : Subgroup H}
    (hL : IsPComponent 2 L) (hRL : R ≤ L)
    (hcov : ∀ l ∈ L, ∃ r ∈ R, ∃ x ∈ (pPrimeCore 2 L).map L.subtype, l = r * x) :
    L ≤ (pLayer ↥R 2).map R.subtype ⊔ (pPrimeCore 2 L).map L.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := pPrimeCore 2 ↥L with hN
  let f : ↥R →* ↥L ⧸ N := (QuotientGroup.mk' N).comp (Subgroup.inclusion hRL)
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective N q
    obtain ⟨r, hr, x, hx, hlrx⟩ := hcov l l.2
    obtain ⟨x', hx', hxx⟩ := hx
    refine ⟨⟨r, hr⟩, ?_⟩
    change QuotientGroup.mk' N (Subgroup.inclusion hRL ⟨r, hr⟩) = QuotientGroup.mk' N l
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have h1 : (Subgroup.inclusion hRL ⟨r, hr⟩)⁻¹ * l = x' := by
      apply Subtype.ext
      simp only [coe_mul, coe_inv, coe_inclusion]
      rw [hlrx, ← hxx]
      simp
    rw [h1]
    exact hx'
  have hker : Odd (Nat.card f.ker) := by
    let g : f.ker →* N := ((Subgroup.inclusion hRL).comp f.ker.subtype).codRestrict N
      (fun c => by
        have h1 : f (c : R) = 1 := c.2
        exact (QuotientGroup.eq_one_iff _).1 h1)
    have hginj : Function.Injective g := by
      intro a b hab
      have h1 := congrArg (fun x : N => ((x : L) : H)) hab
      exact Subtype.ext (Subtype.ext h1)
    exact (Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := L))).of_dvd_nat
      (Subgroup.card_dvd_of_injective _ hginj)
  have hQ : CFSG.IsQuasisimple (↥L ⧸ N) :=
    CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple 2 L hL
  have hQO : pPrimeCore 2 (↥L ⧸ N) = ⊥ := pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have hcomp : IsComponent (⊤ : Subgroup (↥L ⧸ N)) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hQ,
      Subgroup.IsSubnormal.top⟩
  have hsolv : Group.IsSolvable (pPrimeCore 2 (↥L ⧸ N)) := by
    rw [hQO]
    infer_instance
  have htop : TwoComponents.IsTwoComponent (⊤ : Subgroup (↥L ⧸ N)) :=
    (CatalogueBAlternating.pComponent_two_iff _).1
      (LocalAnalysis.ComponentInitial.isPComponent_of_isComponent_of_not_le 2 hcomp
        (LocalAnalysis.ComponentInitial.not_le_of_isComponent_of_isSolvable hcomp hsolv))
  obtain ⟨K1, hK1, hK1map⟩ := OddKernelTwoComponents.exists_lift f hsurj hker ⊤ htop
  have hK1P : IsPComponent 2 K1 := (CatalogueBAlternating.pComponent_two_iff K1).2 hK1
  intro l hl
  have hmem : QuotientGroup.mk' N (⟨l, hl⟩ : L) ∈ K1.map f := hK1map ▸ mem_top _
  obtain ⟨k, hk, hkl⟩ := hmem
  have hx : (Subgroup.inclusion hRL k)⁻¹ * ⟨l, hl⟩ ∈ N := by
    have := hkl
    change QuotientGroup.mk' N (Subgroup.inclusion hRL k) = QuotientGroup.mk' N ⟨l, hl⟩ at this
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at this
    exact this
  have hK1le : K1 ≤ pLayer ↥R 2 := le_sSup hK1P
  have hkmem : (k : H) ∈ (pLayer ↥R 2).map R.subtype := ⟨k, hK1le hk, rfl⟩
  have hxmem : (k : H)⁻¹ * l ∈ (pPrimeCore 2 L).map L.subtype := ⟨_, hx, by simp⟩
  have : l = (k : H) * ((k : H)⁻¹ * l) := by group
  rw [this]
  exact mul_mem (mem_sup_left hkmem) (mem_sup_right hxmem)

end CFSG.ComponentClassification.GrSLit
