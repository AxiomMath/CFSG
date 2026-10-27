module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrTwoLocalQuotient
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrTwoLocalTools

public section

namespace CFSG.ComponentClassification.UnbalancedCorr

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem centralizer_inf_normal (A B : Subgroup G) :
    ((centralizer (A : Set G) ⊓ centralizer (B : Set G)).subgroupOf
      (centralizer (A : Set G) ⊓ normalizer (B : Set G))).Normal := by
  refine ⟨fun y hy z => ?_⟩
  rw [mem_subgroupOf] at hy ⊢
  obtain ⟨hyA, hyB⟩ := mem_inf.mp hy
  have hzA : (z : G) ∈ centralizer (A : Set G) := (mem_inf.mp z.2).1
  have hzB : (z : G) ∈ normalizer (B : Set G) := (mem_inf.mp z.2).2
  refine mem_inf.mpr ⟨?_, ?_⟩
  · simp only [coe_mul, coe_inv]
    exact mul_mem (mul_mem hzA hyA) (inv_mem hzA)
  rw [mem_centralizer_iff] at hyB ⊢
  intro b hb
  have hn : (z : G)⁻¹ * b * z ∈ B := by
    have := (mem_normalizer_iff.mp (inv_mem hzB) b).mp hb
    rwa [inv_inv] at this
  have h1 := hyB _ hn
  simp only [coe_mul, coe_inv]
  calc b * ((z : G) * y * (z : G)⁻¹)
      = (z : G) * ((z : G)⁻¹ * b * z * y) * (z : G)⁻¹ := by group
    _ = (z : G) * (y * ((z : G)⁻¹ * b * z)) * (z : G)⁻¹ := by rw [h1]
    _ = (z : G) * y * (z : G)⁻¹ * b := by group

theorem two_local_layer_facts (hS : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    [IsSimpleGroup G] (hnonab : ∃ x y : G, x * y ≠ y * x)
    (hK : Assembly.KProper Blueprint.Catalog G) {a : G} (ha : orderOf a = 2) {J : Subgroup G}
    (hJa : J ≤ centralizer ({a} : Set G))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G))))
    {S B T : Subgroup G} (hSX : S ≤ centralizer ({a} : Set G) ⊓ normalizer (J : Set G))
    (hS2 : IsPGroup 2 S) (hB1 : B ≠ ⊥) (hBP : B ≤ S ⊓ UnbalancedLayer.coreActionKernel J)
    (hT : T = (pLayer ↥(J ⊓ centralizer (B : Set G)) 2).map
      (J ⊓ centralizer (B : Set G)).subtype) :
    IsPGroup 2 B ∧ a ∈ normalizer (B : Set G) ∧
      normalizer (B : Set G) ≠ ⊤ ∧ SectionRank.IsKGroupCat ↥(normalizer (B : Set G)) ∧
      (pPrimeCore 2 ↥(normalizer (B : Set G))).map (normalizer (B : Set G)).subtype =
        (pPrimeCore 2 ↥(centralizer (B : Set G))).map (centralizer (B : Set G)).subtype ∧
      T ⊔ (pPrimeCore 2 J).map J.subtype = J ∧
      (pPrimeCore 2 T).map T.subtype = T ⊓ (pPrimeCore 2 J).map J.subtype ∧
      T ≤ centralizer ({a} : Set G) ⊓ centralizer (B : Set G) ∧
      IsPComponent 2 (T.subgroupOf (centralizer ({a} : Set G) ⊓ centralizer (B : Set G))) ∧
      T ≤ centralizer ({a} : Set G) ⊓ normalizer (B : Set G) ∧
      IsPComponent 2 (T.subgroupOf (centralizer ({a} : Set G) ⊓ normalizer (B : Set G))) ∧
      T ≤ (pLayer ↥(normalizer (B : Set G)) 2).map (normalizer (B : Set G)).subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBS : B ≤ S := hBP.trans inf_le_left
  have hB2 : IsPGroup 2 B := hS2.to_le hBS
  have hBa : B ≤ centralizer ({a} : Set G) := hBS.trans (hSX.trans inf_le_left)
  have hBJ : B ≤ normalizer (J : Set G) := hBS.trans (hSX.trans inf_le_right)
  have haC : a ∈ centralizer (B : Set G) := by
    rw [mem_centralizer_iff]
    intro b hb
    exact mem_centralizer_singleton_iff.mp (hBa hb)
  have haN : a ∈ normalizer (B : Set G) := centralizer_le_normalizer' B haC
  have hH : normalizer (B : Set G) ≠ ⊤ := normalizer_ne_top_of_isSimpleGroup hnonab hB1 hB2
  have hKH := isKGroupCat_of_ne_top hK hH
  have hJsub : (J.subgroupOf (centralizer ({a} : Set G))).IsSubnormal := by
    obtain ⟨-, -, hs, -, -⟩ := id hJ
    exact hs
  have hJq : IsQuasisimple (J ⧸ pPrimeCore 2 J) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 J _ hJa).mp hJ).2.2
  have hcomm : ∀ b ∈ B, ∀ j ∈ J, j⁻¹ * b⁻¹ * j * b ∈ (pPrimeCore 2 J).map J.subtype :=
    fun b hb j hj => ((hBP hb).2).2 j hj
  obtain ⟨hsup, hcore, hpc⟩ := fixedLayer_facts hJa hJsub hBa hBJ hB2 hJq hcomm hT
  have hTJC : T ≤ J ⊓ centralizer (B : Set G) := hT ▸ map_subtype_le _
  have hTaB : T ≤ centralizer ({a} : Set G) ⊓ centralizer (B : Set G) := fun t ht =>
    ⟨hJa (hTJC ht).1, (hTJC ht).2⟩
  have hYZ : centralizer ({a} : Set G) ⊓ centralizer (B : Set G) ≤
      centralizer ({a} : Set G) ⊓ normalizer (B : Set G) :=
    inf_le_inf_left _ (centralizer_le_normalizer' B)
  have hTaN : T ≤ centralizer ({a} : Set G) ⊓ normalizer (B : Set G) := hTaB.trans hYZ
  have hnorm : ((centralizer ({a} : Set G) ⊓ centralizer (B : Set G)).subgroupOf
      (centralizer ({a} : Set G) ⊓ normalizer (B : Set G))).Normal := by
    have h := centralizer_inf_normal (zpowers a) B
    rwa [UnbalancedLayer.centralizer_zpowers_eq] at h
  have hpcN : IsPComponent 2 (T.subgroupOf (centralizer ({a} : Set G) ⊓ normalizer (B : Set G))) :=
    isPComponent_subgroupOf_of_isSubnormal hTaB hYZ hnorm.isSubnormal hpc
  have hTN : T ≤ centralizer ({a} : Set G) ⊓ normalizer (B : Set G) := hTaN
  exact ⟨hB2, haN, hH, hKH, pPrimeCore_normalizer_eq_centralizer hB2, hsup, hcore, hTaB, hpc,
    hTaN, hpcN, le_pLayer_of_isPComponent_centralizer hS hKH haN ha hTN hpcN⟩

theorem map_pPrimeCore_eq_inf_of_subgroupOf {X H : Subgroup G} (hXH : X ≤ H)
    (hX : (X.subgroupOf H).IsSubnormal) :
    (pPrimeCore 2 ↥X).map X.subtype = X ⊓ (pPrimeCore 2 ↥H).map H.subtype := by
  have h := congrArg (map H.subtype) (map_pPrimeCore_eq_inf_of_isSubnormal hX)
  rwa [pPrimeCore_map_subgroupOf 2 X H hXH, map_inf_eq _ _ _ H.subtype_injective,
    map_subgroupOf_eq_of_le hXH] at h

omit [Finite G] in
theorem normalizer_subgroupOf_eq {A H : Subgroup G} (hAH : A ≤ H) :
    normalizer ((A.subgroupOf H : Subgroup H) : Set H) = (normalizer (A : Set G)).subgroupOf H := by
  ext x
  rw [mem_normalizer_iff, mem_subgroupOf, mem_normalizer_iff]
  constructor
  · intro h y
    by_cases hy : y ∈ H
    · exact h ⟨y, hy⟩
    · have h1 : y ∉ A := fun h' => hy (hAH h')
      have h2 : (x : G) * y * (x : G)⁻¹ ∉ A := fun h' => by
        apply hy
        have := mul_mem (mul_mem (inv_mem x.2) (hAH h')) x.2
        rwa [show (x : G)⁻¹ * ((x : G) * y * (x : G)⁻¹) * x = y by group] at this
      exact ⟨fun h' => absurd h' h1, fun h' => absurd h' h2⟩
  · intro h y
    exact h y

omit [Finite G] in
theorem centralizer_sup_zpowers (B : Subgroup G) (a : G) :
    centralizer ((B ⊔ zpowers a : Subgroup G) : Set G) =
      centralizer (B : Set G) ⊓ centralizer ({a} : Set G) := by
  apply le_antisymm
  · exact le_inf (centralizer_le (fun x hx => mem_sup_left hx))
      (centralizer_le (Set.singleton_subset_iff.mpr (mem_sup_right (mem_zpowers a))))
  · intro g hg
    obtain ⟨hgB, hga⟩ := mem_inf.mp hg
    have hle : B ⊔ zpowers a ≤ centralizer ({g} : Set G) := by
      refine sup_le (fun b hb => ?_) (zpowers_le.mpr ?_)
      · rw [mem_centralizer_singleton_iff]
        exact mem_centralizer_iff.mp hgB b hb
      · rw [mem_centralizer_singleton_iff]
        exact (mem_centralizer_singleton_iff.mp hga).symm
    rw [mem_centralizer_iff]
    intro h hh
    exact mem_centralizer_singleton_iff.mp (hle hh)

omit [Finite G] in
theorem mem_normalizer_orbit {M : Subgroup G} {t : G} (ht : t * t = 1) :
    t ∈ normalizer ((M ⊔ conjugate M t : Subgroup G) : Set G) := by
  apply UnbalancedLayer.mem_normalizer_of_conjugate_eq
  have h : conjugate (M ⊔ conjugate M t) t = conjugate M t ⊔ conjugate (conjugate M t) t := by
    unfold conjugate
    rw [Subgroup.map_sup]
  rw [h, UnbalancedLayer.conjugate_conjugate_self_of_mul_self ht, sup_comm]


omit [Finite G] in
theorem coe_mul_pPrimeCore_eq {T M : Subgroup G} (hTM : T ≤ M)
    (hsup : T ⊔ (pPrimeCore 2 ↥M).map M.subtype = M) :
    (T : Set G) * ((pPrimeCore 2 ↥M).map M.subtype : Set G) = M := by
  ext x
  constructor
  · rintro ⟨t, ht, o, ho, rfl⟩
    exact mul_mem (hTM ht) (map_subtype_le _ ho)
  · intro hx
    have hsup' : T.subgroupOf M ⊔ pPrimeCore 2 ↥M = ⊤ := by
      apply map_injective M.subtype_injective
      rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hTM, ← MonoidHom.range_eq_map, range_subtype,
        hsup]
    have hx' : (⟨x, hx⟩ : M) ∈ ((T.subgroupOf M ⊔ pPrimeCore 2 ↥M : Subgroup M) : Set M) := by
      rw [hsup']
      exact mem_top _
    rw [mul_normal] at hx'
    obtain ⟨t, ht, o, ho, hto⟩ := Set.mem_mul.mp hx'
    refine ⟨t, ht, o, mem_map_of_mem M.subtype ho, ?_⟩
    have := congrArg Subtype.val hto
    exact this

theorem two_local_orbit_facts
    (hS : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    [IsSimpleGroup G] (hnonab : ∃ x y : G, x * y ≠ y * x)
    (hK : Assembly.KProper Blueprint.Catalog G) {a : G} (ha : orderOf a = 2) {J : Subgroup G}
    (hJa : J ≤ centralizer ({a} : Set G))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G))))
    {S B T V : Subgroup G} (hSX : S ≤ centralizer ({a} : Set G) ⊓ normalizer (J : Set G))
    (hS2 : IsPGroup 2 S) (hB1 : B ≠ ⊥) (hBP : B ≤ S ⊓ UnbalancedLayer.coreActionKernel J)
    (hT : T = (pLayer ↥(J ⊓ centralizer (B : Set G)) 2).map
      (J ⊓ centralizer (B : Set G)).subtype)
    (hV : V = ⨆ e ∈ (pLayer ↥(normalizer (B : Set G)) 2).map (normalizer (B : Set G)).subtype,
      conjugate T e) :
    ∃ M : Subgroup G, M ≤ normalizer (B : Set G) ∧
      IsPComponent 2 (M.subgroupOf (normalizer (B : Set G))) ∧
      IsPComponent 2 ((conjugate M a).subgroupOf (normalizer (B : Set G))) ∧
      V = M ⊔ conjugate M a ∧
      V ≤ (pLayer ↥(normalizer (B : Set G)) 2).map (normalizer (B : Set G)).subtype ∧
      (pLayer ↥(normalizer (B : Set G)) 2).map (normalizer (B : Set G)).subtype ≤
        normalizer (V : Set G) ∧
      Nat.card ((↥J ⧸ pPrimeCore 2 ↥J) ⧸ center (↥J ⧸ pPrimeCore 2 ↥J)) ≤
        Nat.card ((↥V ⧸ pPrimeCore 2 ↥V) ⧸ center (↥V ⧸ pPrimeCore 2 ↥V)) ∧
      (Nat.card ((↥V ⧸ pPrimeCore 2 ↥V) ⧸ center (↥V ⧸ pPrimeCore 2 ↥V)) =
          Nat.card ((↥J ⧸ pPrimeCore 2 ↥J) ⧸ center (↥J ⧸ pPrimeCore 2 ↥J)) ↔
        M = conjugate M a ∧ ⁅V, zpowers a⁆ ≤ (pPrimeCore 2 ↥V).map V.subtype) ∧
      (Nat.card ((↥V ⧸ pPrimeCore 2 ↥V) ⧸ center (↥V ⧸ pPrimeCore 2 ↥V)) =
          Nat.card ((↥J ⧸ pPrimeCore 2 ↥J) ⧸ center (↥J ⧸ pPrimeCore 2 ↥J)) →
        IsPComponent 2 (V.subgroupOf (normalizer (B : Set G))) ∧
          (T : Set G) * ((pPrimeCore 2 ↥V).map V.subtype : Set G) = V ∧
          T = UnbalancedGS.gsFixedLayer V a) ∧
      (Nat.card ((↥J ⧸ pPrimeCore 2 ↥J) ⧸ center (↥J ⧸ pPrimeCore 2 ↥J)) <
          Nat.card ((↥V ⧸ pPrimeCore 2 ↥V) ⧸ center (↥V ⧸ pPrimeCore 2 ↥V)) ↔
        ⁅V, zpowers a⁆ = V) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hB2, haN, -, hKH, -, hsupT, hcoreT, hTaB, hpcB, hTaN, hpcN, hTE⟩ :=
    two_local_layer_facts hS hnonab hK ha hJa hJ hSX hS2 hB1 hBP hT
  set H := normalizer (B : Set G) with hHdef
  set R := (pPrimeCore 2 ↥H).map H.subtype with hRdef
  have haa : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  obtain ⟨M, hMH, hM, hTK, hpcK⟩ := exists_orbit_component ha haN hTaN hpcN hTE
  have hTKa : T ≤ (M ⊔ conjugate M a) ⊓ centralizer ({a} : Set G) := fun t ht =>
    ⟨hTK ht, (hTaN ht).1⟩
  obtain ⟨hKE, hEK, hSeq⟩ := iSup_conjugate_eq_orbit haN hMH hM hTKa hpcK
  rw [← hV] at hSeq
  subst hSeq
  set K := M ⊔ conjugate M a with hKdef
  have hMaH : conjugate M a ≤ H := conjugate_le_of_mem hMH haN
  have hMa : IsPComponent 2 ((conjugate M a).subgroupOf H) :=
    isPComponent_conjugate_subgroupOf haN hM
  have hKH' : K ≤ H := sup_le hMH hMaH
  have hTH : T ≤ H := hTKa.trans (inf_le_left.trans hKH')
  have haK : a ∈ normalizer (K : Set G) := mem_normalizer_orbit haa
  refine ⟨M, hMH, hM, hMa, rfl, hKE, hEK, ?_⟩
  have hMsub : (M.subgroupOf H).IsSubnormal := by
    obtain ⟨-, -, hs, -, -⟩ := id hM
    exact hs
  have hEn : (pLayer ↥H 2).Normal := by
    have : (pLayer ↥H 2).Characteristic := CatalogueBPrimeJoin.pLayer_characteristic
    infer_instance
  have hK'E : K.subgroupOf H ≤ pLayer ↥H 2 := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := mem_map.mp (hKE (mem_subgroupOf.mp hx))
    rwa [← Subtype.ext hyx]
  have hKsub : (K.subgroupOf H).IsSubnormal := by
    refine IsSubnormal.step _ _ hK'E hEn.isSubnormal ?_
    rw [normal_subgroupOf_iff_le_normalizer hK'E]
    intro e he
    exact UnbalancedLayer.mem_normalizer_subgroupOf_of_mem
      (hEK (mem_map_of_mem H.subtype he))
  have hOK := map_pPrimeCore_eq_inf_of_subgroupOf hKH' hKsub
  have hOM := map_pPrimeCore_eq_inf_of_subgroupOf hMH hMsub
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥H) with hπdef
  set a' : H := ⟨a, haN⟩ with ha'def
  set Ab := (M.subgroupOf H).map π with hAbdef
  set Ub := (K.subgroupOf H).map π with hUbdef
  set Tb := (T.subgroupOf H).map π with hTbdef
  obtain ⟨Kc, hKc, -, hmapM, -⟩ := id hM
  have hAq : IsQuasisimple ↥Ab := by rw [hAbdef, hmapM]; exact hKc.1
  have hconjAb : ((conjugate M a).subgroupOf H).map π = conjugate Ab (π a') := by
    rw [← UnbalancedLayer.conjugate_subgroupOf_eq M H a', map_conjugate]
  have hUbsup : Ub = Ab ⊔ conjugate Ab (π a') := by
    rw [hUbdef, hKdef, subgroupOf_sup hMH hMaH, Subgroup.map_sup, hconjAb]
  have hMperf : ⁅M, M⁆ = M := by
    have h1 : Group.IsPerfect ↥(M.subgroupOf H) := CatalogueBAlternating.pComponent_perfect hM
    have h2 : Group.IsPerfect ↥M :=
      Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hMH).toMonoidHom)
        (subgroupOfEquivOfLe hMH).surjective
    exact Subgroup.isPerfect_iff.mp h2
  have hMaperf : ⁅conjugate M a, conjugate M a⁆ = conjugate M a := by
    unfold conjugate
    rw [← map_commutator, hMperf]
  have hKperf : ⁅K, K⁆ = K := by
    apply le_antisymm (commutator_le_self K)
    refine sup_le ?_ ?_
    · calc M = ⁅M, M⁆ := hMperf.symm
        _ ≤ ⁅K, K⁆ := commutator_mono le_sup_left le_sup_left
    · calc conjugate M a = ⁅conjugate M a, conjugate M a⁆ := hMaperf.symm
        _ ≤ ⁅K, K⁆ := commutator_mono le_sup_right le_sup_right
  have hK'perf : ⁅K.subgroupOf H, K.subgroupOf H⁆ = K.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hKH', hKperf]
  have hUbperf : ⁅Ub, Ub⁆ = Ub := by rw [hUbdef, ← map_commutator, hK'perf]
  have hUbperf' : Group.IsPerfect ↥Ub := Subgroup.isPerfect_iff.mpr hUbperf
  have hTbUb : Tb ≤ Ub := map_mono (fun x hx => hTKa hx |>.1)
  obtain ⟨hcle, hceq⟩ := card_center_quotient_le hTbUb hUbperf'
  have hdJ : Nat.card ((↥J ⧸ pPrimeCore 2 ↥J) ⧸ center (↥J ⧸ pPrimeCore 2 ↥J)) =
      Nat.card (↥Tb ⧸ center ↥Tb) := by
    have hTJ : T ≤ J := hT ▸ (map_subtype_le _).trans inf_le_left
    obtain ⟨eTJ, -⟩ := exists_quotient_equiv_of_sup hTJ hsupT hcoreT
    obtain ⟨fTJ, -⟩ := exists_centerQuotient_congr eTJ
    rw [← Nat.card_congr fTJ.toEquiv]
    rw [card_centerQuotient_pPrimeCore_congr (subgroupOfEquivOfLe hTH).symm]
    obtain ⟨fz, -⟩ := exists_zstar_equiv ↥(T.subgroupOf H)
    rw [← Nat.card_congr fz.toEquiv]
    set A := (B ⊔ zpowers a).subgroupOf H with hAdef
    have hza2 : IsPGroup 2 (zpowers a) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])
    have hzaB : zpowers a ≤ normalizer (B : Set G) := zpowers_le.mpr haN
    have hBa2 : IsPGroup 2 (B ⊔ zpowers a : Subgroup G) :=
      IsPGroup.to_sup_of_normal_left' hB2 hza2 hzaB
    have hBaH : B ⊔ zpowers a ≤ H := sup_le le_normalizer hzaB
    have hA2 : IsPGroup 2 A := hBa2.comap_of_injective H.subtype H.subtype_injective
    have hA1 : A ≠ ⊥ := by
      obtain ⟨b, hb⟩ := ne_bot_iff_exists_ne_one.mp hB1
      refine ne_bot_iff_exists_ne_one.mpr ⟨⟨⟨b, le_normalizer b.2⟩, mem_sup_left b.2⟩, ?_⟩
      intro h
      apply hb
      exact Subtype.ext (congrArg (fun z : A => ((z : H) : G)) h)
    have hCA : centralizer ((B ⊔ zpowers a : Subgroup G) : Set G) =
        centralizer ({a} : Set G) ⊓ centralizer (B : Set G) := by
      rw [centralizer_sup_zpowers, inf_comm]
    have hTCA : T ≤ centralizer ((B ⊔ zpowers a : Subgroup G) : Set G) := hCA ▸ hTaB
    have hNA : normalizer ((A : Subgroup H) : Set H) =
        (normalizer ((B ⊔ zpowers a : Subgroup G) : Set G) ⊓ H).subgroupOf H := by
      rw [hAdef, normalizer_subgroupOf_eq hBaH, inf_subgroupOf_right]
    have hTA : T.subgroupOf H ≤ normalizer ((A : Subgroup H) : Set H) := by
      rw [hNA]
      intro t ht
      exact ⟨centralizer_le_normalizer' _ (hTCA ht), t.2⟩
    have hYZ : centralizer ((B ⊔ zpowers a : Subgroup G) : Set G) ≤
        normalizer ((B ⊔ zpowers a : Subgroup G) : Set G) ⊓ H :=
      le_inf (centralizer_le_normalizer' _) (hCA.le.trans (inf_le_right.trans
        (centralizer_le_normalizer' B)))
    have hYZn : ((centralizer ((B ⊔ zpowers a : Subgroup G) : Set G)).subgroupOf
        (normalizer ((B ⊔ zpowers a : Subgroup G) : Set G) ⊓ H)).Normal := by
      refine ⟨fun y hy z => ?_⟩
      have h1 := (centralizer_normal_normalizer (B ⊔ zpowers a)).conj_mem
        ⟨y, (mem_inf.mp y.2).1⟩ hy ⟨z, (mem_inf.mp z.2).1⟩
      exact h1
    have hpcA : IsPComponent 2 (T.subgroupOf
        (normalizer ((B ⊔ zpowers a : Subgroup G) : Set G) ⊓ H)) := by
      have h1 : IsPComponent 2 (T.subgroupOf
          (centralizer ((B ⊔ zpowers a : Subgroup G) : Set G))) := by
        rw [hCA]; exact hpcB
      exact isPComponent_subgroupOf_of_isSubnormal hTCA hYZ hYZn.isSubnormal h1
    have hTApc : IsPComponent 2 ((T.subgroupOf H).subgroupOf
        (normalizer ((A : Subgroup H) : Set H))) := by
      rw [hNA, isPComponent_subgroupOf_subgroupOf_iff' inf_le_right 2 Nat.prime_two]
      exact hpcA
    obtain ⟨-, -, -, -, -, -, -, -, -, -, ⟨e, -⟩, -⟩ :=
      kGroup_odd_times_two_normalizer_component_transport_of_inputs hS hU hheld hKH ⊥
        IsPGroup.of_bot π (QuotientGroup.mk'_surjective _)
        (by rw [QuotientGroup.ker_mk', sup_bot_eq]) A hA2 hA1 bot_le (T.subgroupOf H) hTA hTApc
    exact Nat.card_congr e.toEquiv
  have hdV : Nat.card ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K)) =
      Nat.card (↥Ub ⧸ center ↥Ub) := card_centerQuotient_eq_of_subnormal hKH' hKsub
  rw [hdJ, hdV]
  have hE1 : Tb = Ub → ∀ u ∈ Ub, u * π a' = π a' * u := by
    intro h u hu
    rw [← h] at hu
    obtain ⟨t, ht, rfl⟩ := hu
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hTaN ht).1)
  have hzmap : (zpowers a').map H.subtype = zpowers a := by
    rw [MonoidHom.map_zpowers]
    rfl
  have hLmap : (⁅K.subgroupOf H, zpowers a'⁆).map H.subtype = ⁅K, zpowers a⁆ := by
    rw [map_commutator, map_subgroupOf_eq_of_le hKH', hzmap]
  have hLπ : (⁅K.subgroupOf H, zpowers a'⁆).map π = ⁅Ub, zpowers (π a')⁆ := by
    rw [map_commutator, MonoidHom.map_zpowers]
  have hLK : ⁅K, zpowers a⁆ ≤ K :=
    UnbalancedLayer.commutator_le_left_of_le_normalizer (zpowers_le.mpr haK)
  have hcent_iff : (∀ u ∈ Ub, u * π a' = π a' * u) ↔ ⁅Ub, zpowers (π a')⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer, UnbalancedLayer.centralizer_zpowers_eq]
    constructor
    · intro h u hu
      exact mem_centralizer_singleton_iff.mpr (h u hu)
    · intro h u hu
      exact mem_centralizer_singleton_iff.mp (h hu)
  have hE3 : (∀ u ∈ Ub, u * π a' = π a' * u) ↔
      ⁅K, zpowers a⁆ ≤ (pPrimeCore 2 ↥K).map K.subtype := by
    rw [hcent_iff, hOK, ← hLπ, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    constructor
    · intro h
      refine le_inf hLK ?_
      rw [← hLmap]
      exact map_mono h
    · intro h
      rw [← map_le_map_iff_of_injective H.subtype_injective, hLmap]
      exact h.trans inf_le_right
  have hE2 : (∀ u ∈ Ub, u * π a' = π a' * u) →
      M = conjugate M a ∧ T ⊔ (pPrimeCore 2 ↥M).map M.subtype = M ∧
        T = UnbalancedGS.gsFixedLayer M a ∧ Tb = Ub := by
    intro hcent
    have hAbc : Ab ≤ centralizer ({π a'} : Set (↥H ⧸ pPrimeCore 2 ↥H)) := fun u hu =>
      mem_centralizer_singleton_iff.mpr (hcent u (by rw [hUbsup]; exact mem_sup_left hu))
    have hAbconj : conjugate Ab (π a') = Ab := conjugate_eq_self_of_le_centralizer hAbc
    have hMaM₁ : (conjugate M a).subgroupOf H = M.subgroupOf H := by
      have hbij := (CatalogueBPrimeJoin.canonical_prime_component_lift (X := ↥H) 2).2
      exact hbij.injOn hMa hM (by rw [hconjAb, hAbconj])
    have hMaM : conjugate M a = M := UGSChain.eq_of_subgroupOf_eq hMaH hMH hMaM₁
    have hKM : K = M := by rw [hKdef, hMaM, sup_idem]
    have haM : a ∈ normalizer (M : Set G) := UnbalancedLayer.mem_normalizer_of_conjugate_eq hMaM
    have hcommM : ∀ b ∈ zpowers a, ∀ m ∈ M,
        m⁻¹ * b⁻¹ * m * b ∈ (pPrimeCore 2 ↥M).map M.subtype := by
      intro b hb m hm
      rcases UnbalancedGS.OrbitFixedComponent.eq_one_or_eq_of_mem_zpowers haa hb with hb1 | hba
      · rw [hb1, inv_one, mul_one, mul_one, inv_mul_cancel]
        exact one_mem _
      · rw [hba, hOM]
        refine mem_inf.mpr ⟨?_, ?_⟩
        · have h1 : a⁻¹ * m * a ∈ M := by
            have := (mem_normalizer_iff.mp (inv_mem haM) m).mp hm
            rwa [inv_inv] at this
          rw [show m⁻¹ * a⁻¹ * m * a = m⁻¹ * (a⁻¹ * m * a) by group]
          exact mul_mem (inv_mem hm) h1
        · set m' : H := ⟨m, hMH hm⟩
          have hπm : π m' ∈ Ub :=
            mem_map_of_mem π (show m' ∈ K.subgroupOf H from mem_sup_left hm)
          have hc := hcent _ hπm
          have h2 : π (m'⁻¹ * a'⁻¹ * m' * a') = 1 := by
            rw [map_mul, map_mul, map_mul, map_inv, map_inv]
            calc (π m')⁻¹ * (π a')⁻¹ * π m' * π a' = (π m')⁻¹ * (π a')⁻¹ * (π m' * π a') := by
                  group
              _ = (π m')⁻¹ * (π a')⁻¹ * (π a' * π m') := by rw [hc]
              _ = 1 := by group
          have h3 : m'⁻¹ * a'⁻¹ * m' * a' ∈ pPrimeCore 2 ↥H := (QuotientGroup.eq_one_iff _).mp h2
          exact ⟨_, h3, rfl⟩
    have hMq : IsQuasisimple (↥M ⧸ pPrimeCore 2 ↥M) :=
      ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 M H hMH).mp hM).2.2
    have hza2 : IsPGroup 2 (zpowers a) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])
    obtain ⟨hsupF, -, hpcF⟩ := fixedLayer_facts hMH hMsub (zpowers_le.mpr haN)
      (zpowers_le.mpr haM) hza2 hMq hcommM rfl
    rw [UnbalancedLayer.centralizer_zpowers_eq a] at hsupF hpcF
    change UnbalancedGS.gsFixedLayer M a ⊔ (pPrimeCore 2 ↥M).map M.subtype = M at hsupF
    change IsPComponent 2 ((UnbalancedGS.gsFixedLayer M a).subgroupOf
      (H ⊓ centralizer ({a} : Set G))) at hpcF
    have hTCMa : T ≤ M ⊓ centralizer ({a} : Set G) := by
      intro t ht
      have h1 := hTKa ht
      rw [hKM] at h1
      exact h1
    have hpcK' : IsPComponent 2 (T.subgroupOf (M ⊓ centralizer ({a} : Set G))) := by
      have h1 := hpcK
      rw [hKM] at h1
      exact h1
    have hTF₁ : T.subgroupOf (M ⊓ centralizer ({a} : Set G)) ≤
        pLayer ↥(M ⊓ centralizer ({a} : Set G)) 2 := le_sSup hpcK'
    have hTF : T ≤ UnbalancedGS.gsFixedLayer M a := fun t ht =>
      ⟨⟨t, hTCMa ht⟩, hTF₁ (show (⟨t, hTCMa ht⟩ : ↥(M ⊓ centralizer ({a} : Set G))) ∈
        T.subgroupOf (M ⊓ centralizer ({a} : Set G)) from ht), rfl⟩
    have hFle : UnbalancedGS.gsFixedLayer M a ≤ M ⊓ centralizer ({a} : Set G) :=
      UnbalancedGS.gsFixedLayer_le_inf M a
    have hpcF' : IsPComponent 2 ((UnbalancedGS.gsFixedLayer M a).subgroupOf
        (M ⊓ centralizer ({a} : Set G))) :=
      isPComponent_subgroupOf_of_le hFle (inf_le_inf_right _ hMH) hpcF
    have hTFeq : T = UnbalancedGS.gsFixedLayer M a := by
      have h1 := CatalogueBPrimeJoin.eq_of_le 2 _ _ hpcK' hpcF' (fun x hx => hTF hx)
      exact UGSChain.eq_of_subgroupOf_eq hTCMa hFle h1
    have hsupTM : T ⊔ (pPrimeCore 2 ↥M).map M.subtype = M := by rw [hTFeq]; exact hsupF
    have hOMR : (pPrimeCore 2 ↥M).map M.subtype ≤ R := hOM ▸ inf_le_right
    have hOMH : (pPrimeCore 2 ↥M).map M.subtype ≤ H := hOMR.trans (map_subtype_le _)
    have hOMbot : (((pPrimeCore 2 ↥M).map M.subtype).subgroupOf H).map π = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
      intro x hx
      obtain ⟨y, hy, hyx⟩ := mem_map.mp (hOMR (mem_subgroupOf.mp hx))
      rwa [← Subtype.ext hyx]
    have hTbUbeq : Tb = Ub := by
      rw [hUbdef, hKM, ← hsupTM, subgroupOf_sup hTH hOMH, Subgroup.map_sup, hOMbot,
        sup_bot_eq]
    exact ⟨hMaM.symm, hsupTM, hTFeq, hTbUbeq⟩
  have hE4 : ¬ (∀ u ∈ Ub, u * π a' = π a' * u) → ⁅K, zpowers a⁆ = K := by
    intro hnc
    have hEM : (pLayer ↥H 2).map H.subtype ≤ normalizer (M : Set G) :=
      UGSChain.map_pLayer_le_normalizer hMH hM
    have hK₁M : K.subgroupOf H ≤ normalizer (M.subgroupOf H : Set H) := fun k hk =>
      UnbalancedLayer.mem_normalizer_subgroupOf_of_mem (hEM (hKE hk))
    have hAbn : Ub ≤ normalizer (Ab : Set (↥H ⧸ pPrimeCore 2 ↥H)) :=
      (map_mono hK₁M).trans (le_normalizer_map π)
    have hta : π a' ∈ normalizer (Ub : Set (↥H ⧸ pPrimeCore 2 ↥H)) :=
      le_normalizer_map π (mem_map_of_mem π
        (UnbalancedLayer.mem_normalizer_subgroupOf_of_mem haK))
    rw [hUbsup] at hAbn hta hUbperf hnc
    have hW := commutator_zpowers_eq_of_not_centralizes hAq hAbn hta hUbperf hnc
    rw [← hUbsup] at hW
    have hLπK : (⁅K.subgroupOf H, zpowers a'⁆).map π = (K.subgroupOf H).map π := by
      rw [hLπ, hW]
    set L := ⁅K, zpowers a⁆ with hLdef
    have hKL : K ≤ normalizer (L : Set G) := normalizer_commutator_ge_left K (zpowers a)
    set N := L.subgroupOf K with hNdef
    have hNn : N.Normal := (normal_subgroupOf_iff_le_normalizer hLK).mpr hKL
    have hRodd : Nat.Coprime 2 (Nat.card R) := by
      rw [hRdef, card_map_of_injective H.subtype_injective]
      exact pPrimeCore_coprime_card
    let f : ↥(R.subgroupOf K) →* ↥K ⧸ N := (QuotientGroup.mk' N).comp (R.subgroupOf K).subtype
    have hf : Function.Surjective f := by
      intro q
      obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective _ q
      set k' : H := ⟨k, hKH' k.2⟩
      have hk' : π k' ∈ (⁅K.subgroupOf H, zpowers a'⁆).map π := by
        rw [hLπK]
        exact mem_map_of_mem π (show k' ∈ K.subgroupOf H from k.2)
      obtain ⟨l', hl', hlk⟩ := mem_map.mp hk'
      have hlL : (l' : G) ∈ L := by
        rw [← hLmap]
        exact mem_map_of_mem H.subtype hl'
      have hr : l'⁻¹ * k' ∈ pPrimeCore 2 ↥H := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
        change (π l')⁻¹ * π k' = 1
        rw [hlk, inv_mul_cancel]
      have hrR : (l' : G)⁻¹ * k ∈ R := ⟨_, hr, rfl⟩
      have hrK : (l' : G)⁻¹ * k ∈ K := mul_mem (inv_mem (hLK hlL)) k.2
      refine ⟨⟨⟨(l' : G)⁻¹ * k, hrK⟩, hrR⟩, ?_⟩
      show (QuotientGroup.mk' N) ⟨(l' : G)⁻¹ * k, hrK⟩ = (QuotientGroup.mk' N) k
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      show ((⟨(l' : G)⁻¹ * k, hrK⟩ : K)⁻¹ * k : K) ∈ N
      rw [mem_subgroupOf]
      have h1 : ((((⟨(l' : G)⁻¹ * k, hrK⟩ : K)⁻¹ * k : K)) : G) = (k : G)⁻¹ * l' * k := by
        simp only [coe_mul, coe_inv]
        group
      rw [h1]
      have h2 := (mem_normalizer_iff.mp (hKL (inv_mem k.2)) l').mp hlL
      rwa [inv_inv] at h2
    have hidx : Nat.Coprime 2 N.index := by
      rw [index_eq_card]
      have h1 : Nat.card (↥K ⧸ N) ∣ Nat.card ↥(R.subgroupOf K) := card_dvd_of_surjective f hf
      have h2 : Nat.card ↥(R.subgroupOf K) ∣ Nat.card R := by
        let g : ↥(R.subgroupOf K) →* ↥R :=
          { toFun := fun x => ⟨((x : K) : G), x.2⟩
            map_one' := rfl
            map_mul' := fun _ _ => rfl }
        refine card_dvd_of_injective g fun x y h => ?_
        have h' := congrArg Subtype.val h
        exact Subtype.ext (Subtype.ext h')
      exact Nat.Coprime.coprime_dvd_right (h1.trans h2) hRodd
    have hres := CatalogueBPrimeJoin.primeResidual_le_normal_of_coprime_index 2 N hidx
    have hMres : M.subgroupOf K ≤ CatalogueBPrimeJoin.primeResidual 2 ↥K := by
      have h1 := ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 M H hMH).mp hM).2.1
      have h2 := CatalogueBPrimeJoin.primeResidual_map_le 2 (inclusion (le_sup_left : M ≤ K))
      rw [h1, ← MonoidHom.range_eq_map, inclusion_range] at h2
      exact h2
    have hMares : (conjugate M a).subgroupOf K ≤ CatalogueBPrimeJoin.primeResidual 2 ↥K := by
      have h1 := ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 _ H hMaH).mp hMa).2.1
      have h2 := CatalogueBPrimeJoin.primeResidual_map_le 2
        (inclusion (le_sup_right : conjugate M a ≤ K))
      rw [h1, ← MonoidHom.range_eq_map, inclusion_range] at h2
      exact h2
    have hKsup : (⊤ : Subgroup ↥K) = M.subgroupOf K ⊔ (conjugate M a).subgroupOf K := by
      rw [← subgroupOf_sup le_sup_left le_sup_right]
      exact (subgroupOf_self K).symm
    have htopK : (⊤ : Subgroup K) ≤ N := by
      rw [hKsup]
      exact (sup_le hMres hMares).trans hres
    refine le_antisymm hLK fun k hk => ?_
    have h1 := htopK (mem_top (⟨k, hk⟩ : K))
    exact h1
  have hOKR : (pPrimeCore 2 ↥K).map K.subtype ≤ R := hOK ▸ inf_le_right
  refine ⟨hcle, ⟨fun h => ?_, fun h => ?_⟩, fun h => ?_, ⟨fun h => ?_, fun h => ?_⟩⟩
  · have hcent := hE1 (hceq h.symm)
    exact ⟨(hE2 hcent).1, hE3.mp hcent⟩
  · obtain ⟨-, hLO⟩ := h
    rw [(hE2 (hE3.mpr hLO)).2.2.2]
  · have hcent := hE1 (hceq h.symm)
    obtain ⟨hMaM, hsupM, hTF, -⟩ := hE2 hcent
    have hKM : K = M := by rw [hKdef, ← hMaM, sup_idem]
    rw [hKM]
    refine ⟨hM, ?_, hTF⟩
    exact coe_mul_pPrimeCore_eq (le_sup_left.trans hsupM.le) hsupM
  · apply hE4
    intro hcent
    rw [(hE2 hcent).2.2.2] at h
    exact lt_irrefl _ h
  · refine lt_of_le_of_ne hcle fun heq => ?_
    have hLO := hE3.mp (hE1 (hceq heq))
    rw [h] at hLO
    have hKR : K ≤ R := hLO.trans hOKR
    have hAbbot : Ab = ⊥ := by
      rw [hAbdef, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
      intro x hx
      obtain ⟨y, hy, hyx⟩ := mem_map.mp (hKR (le_sup_left (a := M) (mem_subgroupOf.mp hx)))
      rwa [← Subtype.ext hyx]
    have hnt := LocalCores.isQuasisimple_nontrivial hAq
    rw [hAbbot] at hnt
    exact (Subgroup.nontrivial_iff_ne_bot ⊥).mp hnt rfl

theorem two_local_core_facts (hS : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    [IsSimpleGroup G] (hnonab : ∃ x y : G, x * y ≠ y * x)
    (hK : Assembly.KProper Blueprint.Catalog G) {a : G} (ha : orderOf a = 2) {J : Subgroup G}
    (hJa : J ≤ centralizer ({a} : Set G))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G))))
    {S B T X : Subgroup G} (hSX : S ≤ centralizer ({a} : Set G) ⊓ normalizer (J : Set G))
    (hS2 : IsPGroup 2 S) (hB1 : B ≠ ⊥) (hBP : B ≤ S ⊓ UnbalancedLayer.coreActionKernel J)
    (hT : T = (pLayer ↥(J ⊓ centralizer (B : Set G)) 2).map
      (J ⊓ centralizer (B : Set G)).subtype)
    (hX : X = T ⊔ (pPrimeCore 2 ↥(normalizer (B : Set G))).map (normalizer (B : Set G)).subtype) :
    (pPrimeCore 2 ↥X).map X.subtype =
        (pPrimeCore 2 ↥(normalizer (B : Set G))).map (normalizer (B : Set G)).subtype ⊔
          (pPrimeCore 2 ↥T).map T.subtype ∧
      (∃ e : ↥X ⧸ pPrimeCore 2 ↥X ≃* ↥J ⧸ pPrimeCore 2 ↥J,
        (∀ (x : X) (j : J), (x : G) ∈ T → (x : G) = j → e x = j) ∧
        ∀ q ∈ S ⊓ normalizer (B : Set G), ∀ (x : X) (j : J) (hx : q * x * q⁻¹ ∈ X)
          (hj : q * j * q⁻¹ ∈ J), e x = j → e (⟨q * x * q⁻¹, hx⟩ : X) = (⟨q * j * q⁻¹, hj⟩ : J)) ∧
      ∀ q ∈ S ⊓ normalizer (B : Set G), q ∈ normalizer (X : Set G) ∧
        q ∈ normalizer (J : Set G) ∧
        ((∀ x ∈ X, x⁻¹ * q⁻¹ * x * q ∈ (pPrimeCore 2 ↥X).map X.subtype) ↔
          q ∈ (S ⊓ UnbalancedLayer.coreActionKernel J) ⊓ normalizer (B : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hB2, haN, -, hKH, -, hsupT, hcoreT, hTaB, hpcB, hTaN, hpcN, hTE⟩ :=
    two_local_layer_facts hS hnonab hK ha hJa hJ hSX hS2 hB1 hBP hT
  set H := normalizer (B : Set G) with hHdef
  set R := (pPrimeCore 2 ↥H).map H.subtype with hRdef
  set O := (pPrimeCore 2 ↥J).map J.subtype with hOdef
  set OT := (pPrimeCore 2 ↥T).map T.subtype with hOTdef
  set OX := (pPrimeCore 2 ↥X).map X.subtype with hOXdef
  have hTJ : T ≤ J := hT ▸ (map_subtype_le _).trans inf_le_left
  have hTH : T ≤ H := hTaN.trans inf_le_right
  have hRH : R ≤ H := map_subtype_le _
  have hHR : H ≤ normalizer (R : Set G) := fun h hh =>
    UnbalancedGS.normalizer_le_normalizer_map_of_characteristic H (pPrimeCore 2 ↥H)
      (le_normalizer hh)
  have hXset : (X : Set G) = (T : Set G) * (R : Set G) := by
    rw [hX]
    exact coe_mul_of_left_le_normalizer_right T R (hTH.trans hHR)
  have hXH : X ≤ H := hX ▸ sup_le hTH hRH
  have hTX : T ≤ X := hX ▸ le_sup_left
  have hRX : R ≤ X := hX ▸ le_sup_right
  have hRodd : Nat.Coprime 2 (Nat.card R) := by
    rw [hRdef, card_map_of_injective H.subtype_injective]
    exact pPrimeCore_coprime_card
  have hROX : R ≤ OX := by
    have hle : R.subgroupOf X ≤ pPrimeCore 2 ↥X := by
      refine le_sSup ⟨⟨fun r hr x => ?_⟩, ?_⟩
      · rw [mem_subgroupOf] at hr ⊢
        exact (mem_normalizer_iff.mp (hHR (hXH x.2)) _).mp hr
      · rwa [Nat.card_congr (subgroupOfEquivOfLe hRX).toEquiv]
    intro r hr
    exact ⟨⟨r, hRX hr⟩, hle (show (⟨r, hRX hr⟩ : X) ∈ R.subgroupOf X from hr), rfl⟩
  let f : ↥T →* ↥X ⧸ pPrimeCore 2 ↥X := (QuotientGroup.mk' _).comp (inclusion hTX)
  have hfker : ∀ t : T, t ∈ f.ker ↔ (t : G) ∈ OX := by
    intro t
    rw [MonoidHom.mem_ker]
    show (QuotientGroup.mk' (pPrimeCore 2 ↥X)) (inclusion hTX t) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · exact fun h => ⟨_, h, rfl⟩
    · rintro ⟨y, hy, hyt⟩
      rwa [show inclusion hTX t = y from Subtype.ext hyt.symm]
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ q
    have hx : (x : G) ∈ (T : Set G) * (R : Set G) := hXset ▸ x.2
    obtain ⟨t, ht, r, hr, htr⟩ := Set.mem_mul.mp hx
    refine ⟨⟨t, ht⟩, ?_⟩
    show (QuotientGroup.mk' _) (inclusion hTX ⟨t, ht⟩) = (QuotientGroup.mk' _) x
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    obtain ⟨y, hy, hyr⟩ := hROX hr
    have hyr' : (y : G) = r := hyr
    have hxy : (inclusion hTX ⟨t, ht⟩)⁻¹ * x = y := by
      apply Subtype.ext
      rw [hyr']
      simp only [coe_mul, coe_inv, coe_inclusion]
      rw [← htr]
      group
    rw [hxy]
    exact hy
  have hTOX : ∀ t : T, (t : G) ∈ OX → t ∈ pPrimeCore 2 ↥T := by
    intro t ht
    have hle : f.ker ≤ pPrimeCore 2 ↥T := by
      refine le_sSup ⟨f.normal_ker, ?_⟩
      have h1 : Nat.card f.ker ∣ Nat.card OX := by
        let g : f.ker →* OX :=
          { toFun := fun x => ⟨((x : T) : G), (hfker x).mp x.2⟩
            map_one' := rfl
            map_mul' := fun _ _ => rfl }
        refine card_dvd_of_injective g fun x y h => ?_
        have h' := congrArg Subtype.val h
        exact Subtype.ext (Subtype.ext h')
      have h2 : Nat.Coprime 2 (Nat.card OX) := by
        rw [hOXdef, card_map_of_injective X.subtype_injective]
        exact pPrimeCore_coprime_card
      exact Nat.Coprime.coprime_dvd_right h1 h2
    exact hle ((hfker t).mpr ht)
  have hOTker : pPrimeCore 2 ↥T ≤ f.ker := by
    have hn : ((pPrimeCore 2 ↥T).map f).Normal := Subgroup.Normal.map inferInstance f hf
    have hodd : Nat.Coprime 2 (Nat.card ((pPrimeCore 2 ↥T).map f)) :=
      Nat.Coprime.coprime_dvd_right (card_map_dvd _ _) pPrimeCore_coprime_card
    have hle : (pPrimeCore 2 ↥T).map f ≤ pPrimeCore 2 (↥X ⧸ pPrimeCore 2 ↥X) :=
      le_sSup ⟨hn, hodd⟩
    rw [pPrimeCore_quotient_pPrimeCore_eq_bot 2, le_bot_iff, Subgroup.map_eq_bot_iff] at hle
    exact hle
  have hker : pPrimeCore 2 ↥T = f.ker := by
    apply le_antisymm hOTker
    intro t ht
    exact hTOX t ((hfker t).mp ht)
  have hOTOX : OT ≤ OX := by
    rintro _ ⟨t, ht, rfl⟩
    exact (hfker t).mp (hOTker ht)
  have hOXeq : OX = R ⊔ OT := by
    apply le_antisymm
    · intro y hy
      have hyX : y ∈ X := map_subtype_le _ hy
      have hy' : y ∈ (T : Set G) * (R : Set G) := hXset ▸ hyX
      obtain ⟨t, ht, r, hr, rfl⟩ := Set.mem_mul.mp hy'
      have htO : t ∈ OX := by
        have := mul_mem hy (inv_mem (hROX hr))
        rwa [mul_inv_cancel_right] at this
      have htOT : t ∈ OT := ⟨⟨t, ht⟩, hTOX ⟨t, ht⟩ htO, rfl⟩
      exact mul_mem (mem_sup_right htOT) (mem_sup_left hr)
    · exact sup_le hROX hOTOX
  obtain ⟨eTJ, heTJ⟩ := exists_quotient_equiv_of_sup hTJ hsupT hcoreT
  let eTX : ↥T ⧸ pPrimeCore 2 ↥T ≃* ↥X ⧸ pPrimeCore 2 ↥X :=
    (QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have heTX : ∀ t : T, eTX t = f t := fun t => rfl
  set e := eTX.symm.trans eTJ with hedef
  have he : ∀ (x : X) (j : J), (x : G) ∈ T → (x : G) = j → e x = j := by
    intro x j hxT hxj
    have h1 : (x : ↥X ⧸ pPrimeCore 2 ↥X) = eTX ((⟨x, hxT⟩ : T) : ↥T ⧸ pPrimeCore 2 ↥T) := rfl
    rw [hedef, MulEquiv.trans_apply, h1, MulEquiv.symm_apply_apply]
    exact heTJ ⟨x, hxT⟩ j hxj
  have hQ : ∀ q ∈ S ⊓ normalizer (B : Set G), q ∈ normalizer (J : Set G) ∧ q ∈ H ∧
      q ∈ normalizer (T : Set G) ∧ q ∈ normalizer (R : Set G) ∧ q ∈ normalizer (X : Set G) ∧
      q ∈ normalizer (O : Set G) ∧ q ∈ normalizer (OX : Set G) := by
    intro q hq
    have hqJ : q ∈ normalizer (J : Set G) := (hSX (mem_inf.mp hq).1).2
    have hqH : q ∈ H := (mem_inf.mp hq).2
    have hqCB : q ∈ normalizer (centralizer (B : Set G) : Set G) := by
      rw [mem_normalizer_iff]
      intro y
      rw [mem_centralizer_iff, mem_centralizer_iff]
      constructor
      · intro h b hb
        have hb' : q⁻¹ * b * q ∈ B := by
          have := (mem_normalizer_iff.mp (inv_mem hqH) b).mp hb
          rwa [inv_inv] at this
        have := h _ hb'
        calc b * (q * y * q⁻¹) = q * ((q⁻¹ * b * q) * y) * q⁻¹ := by group
          _ = q * (y * (q⁻¹ * b * q)) * q⁻¹ := by rw [this]
          _ = (q * y * q⁻¹) * b := by group
      · intro h b hb
        have hb' : q * b * q⁻¹ ∈ B := (mem_normalizer_iff.mp hqH b).mp hb
        have := h _ hb'
        calc b * y = q⁻¹ * ((q * b * q⁻¹) * (q * y * q⁻¹)) * q := by group
          _ = q⁻¹ * ((q * y * q⁻¹) * (q * b * q⁻¹)) * q := by rw [this]
          _ = y * b := by group
    have hqC : q ∈ normalizer ((J ⊓ centralizer (B : Set G) : Subgroup G) : Set G) :=
      UnbalancedLayer.normalizer_inf_mem hqJ hqCB
    have hqT : q ∈ normalizer (T : Set G) := by
      rw [hT]
      have : (pLayer ↥(J ⊓ centralizer (B : Set G)) 2).Characteristic :=
        CatalogueBPrimeJoin.pLayer_characteristic
      exact UnbalancedGS.normalizer_le_normalizer_map_of_characteristic _ _ hqC
    have hqR : q ∈ normalizer (R : Set G) := hHR hqH
    have hqX : q ∈ normalizer (X : Set G) := by rw [hX]; exact mem_normalizer_sup hqT hqR
    have hqO : q ∈ normalizer (O : Set G) :=
      UnbalancedGS.normalizer_le_normalizer_map_of_characteristic J (pPrimeCore 2 ↥J) hqJ
    have hqOX : q ∈ normalizer (OX : Set G) :=
      UnbalancedGS.normalizer_le_normalizer_map_of_characteristic X (pPrimeCore 2 ↥X) hqX
    exact ⟨hqJ, hqH, hqT, hqR, hqX, hqO, hqOX⟩
  have hOTO : OT ≤ O := by
    intro y hy
    have h1 : y ∈ T ⊓ O := by rw [← hcoreT]; exact hy
    exact h1.2
  refine ⟨hOXeq, ⟨e, he, ?_⟩, fun q hq => ?_⟩
  ·
    intro q hq x j hx hj hxj
    obtain ⟨-, -, hqT, hqR, -, hqO, -⟩ := hQ q hq
    have hx' : (x : G) ∈ (T : Set G) * (R : Set G) := hXset ▸ x.2
    obtain ⟨t, ht, r, hr, htr⟩ := Set.mem_mul.mp hx'
    have hrOX : (⟨r, hRX hr⟩ : X) ∈ pPrimeCore 2 ↥X := by
      obtain ⟨y, hy, hyr⟩ := hROX hr
      rwa [show (⟨r, hRX hr⟩ : X) = y from Subtype.ext hyr.symm]
    have hex : e x = e ((⟨t, hTX ht⟩ : X) : ↥X ⧸ pPrimeCore 2 ↥X) := by
      have h1 : x = ⟨t, hTX ht⟩ * ⟨r, hRX hr⟩ := Subtype.ext htr.symm
      rw [h1, QuotientGroup.mk_mul, map_mul, (QuotientGroup.eq_one_iff _).mpr hrOX, map_one,
        mul_one]
    have het : e ((⟨t, hTX ht⟩ : X) : ↥X ⧸ pPrimeCore 2 ↥X) = (⟨t, hTJ ht⟩ : J) :=
      he ⟨t, hTX ht⟩ ⟨t, hTJ ht⟩ ht rfl
    have hjt : (⟨t, hTJ ht⟩ : J)⁻¹ * j ∈ pPrimeCore 2 ↥J := by
      rw [← QuotientGroup.eq]
      rw [← het, ← hex]
      exact hxj
    have hqt : q * t * q⁻¹ ∈ T := (mem_normalizer_iff.mp hqT t).mp ht
    have hqr : q * r * q⁻¹ ∈ R := (mem_normalizer_iff.mp hqR r).mp hr
    have hqrOX : (⟨q * r * q⁻¹, hRX hqr⟩ : X) ∈ pPrimeCore 2 ↥X := by
      obtain ⟨y, hy, hyr⟩ := hROX hqr
      rwa [show (⟨q * r * q⁻¹, hRX hqr⟩ : X) = y from Subtype.ext hyr.symm]
    have hcx : (⟨q * x * q⁻¹, hx⟩ : X) = ⟨q * t * q⁻¹, hTX hqt⟩ * ⟨q * r * q⁻¹, hRX hqr⟩ := by
      apply Subtype.ext
      simp only [coe_mul]
      rw [← htr]
      group
    rw [hcx, QuotientGroup.mk_mul, map_mul, (QuotientGroup.eq_one_iff _).mpr hqrOX, map_one,
      mul_one, he ⟨q * t * q⁻¹, hTX hqt⟩ ⟨q * t * q⁻¹, hTJ hqt⟩ hqt rfl, QuotientGroup.eq]
    obtain ⟨o, ho, hoe⟩ : (((⟨t, hTJ ht⟩ : J)⁻¹ * j : J) : G) ∈ O := ⟨_, hjt, rfl⟩
    have hqo := (mem_normalizer_iff.mp hqO _).mp (show ((((⟨t, hTJ ht⟩ : J)⁻¹ * j : J) : G)) ∈ O
      from ⟨o, ho, hoe⟩)
    obtain ⟨o', ho', ho'e⟩ := hqo
    have ho'e' : (o' : G) = q * ((((⟨t, hTJ ht⟩ : J)⁻¹ * j : J)) : G) * q⁻¹ := ho'e
    have hfin : (⟨q * t * q⁻¹, hTJ hqt⟩ : J)⁻¹ * ⟨q * j * q⁻¹, hj⟩ = o' := by
      apply Subtype.ext
      rw [ho'e']
      simp only [coe_mul, coe_inv]
      group
    rw [hfin]
    exact ho'
  · obtain ⟨hqJ, hqH, hqT, hqR, hqX, hqO, hqOX⟩ := hQ q hq
    refine ⟨hqX, hqJ, ⟨fun h => ?_, fun h => ?_⟩⟩
    ·
      refine mem_inf.mpr ⟨mem_inf.mpr ⟨(mem_inf.mp hq).1, hqJ, fun j hj => ?_⟩, (mem_inf.mp hq).2⟩
      have hj' : j ∈ ((T ⊔ O : Subgroup G) : Set G) := by rw [hsupT]; exact hj
      rw [coe_mul_of_left_le_normalizer_right T O (hTJ.trans (fun y hy =>
        UnbalancedGS.normalizer_le_normalizer_map_of_characteristic J (pPrimeCore 2 ↥J)
          (le_normalizer hy)))] at hj'
      obtain ⟨t, ht, o, ho, rfl⟩ := Set.mem_mul.mp hj'
      have hqt : t⁻¹ * q⁻¹ * t * q ∈ T := by
        have h1 : q⁻¹ * t * q ∈ T := by
          have := (mem_normalizer_iff.mp (inv_mem hqT) t).mp ht
          rwa [inv_inv] at this
        rw [show t⁻¹ * q⁻¹ * t * q = t⁻¹ * (q⁻¹ * t * q) by group]
        exact mul_mem (inv_mem ht) h1
      have hqtOX : t⁻¹ * q⁻¹ * t * q ∈ OX := h t (hTX ht)
      have hqtO : t⁻¹ * q⁻¹ * t * q ∈ O :=
        hOTO ⟨⟨_, hqt⟩, hTOX ⟨_, hqt⟩ hqtOX, rfl⟩
      have hqo : q⁻¹ * o * q ∈ O := by
        have := (mem_normalizer_iff.mp (inv_mem hqO) o).mp ho
        rwa [inv_inv] at this
      rw [show (t * o)⁻¹ * q⁻¹ * (t * o) * q = o⁻¹ * (t⁻¹ * q⁻¹ * t * q) * (q⁻¹ * o * q) by group]
      exact mul_mem (mul_mem (inv_mem ho) hqtO) hqo
    ·
      have hqP := ((mem_inf.mp (mem_inf.mp h).1).2).2
      intro x hx
      have hx' : x ∈ (T : Set G) * (R : Set G) := hXset ▸ hx
      obtain ⟨t, ht, r, hr, rfl⟩ := Set.mem_mul.mp hx'
      have hqt : t⁻¹ * q⁻¹ * t * q ∈ T := by
        have h1 : q⁻¹ * t * q ∈ T := by
          have := (mem_normalizer_iff.mp (inv_mem hqT) t).mp ht
          rwa [inv_inv] at this
        rw [show t⁻¹ * q⁻¹ * t * q = t⁻¹ * (q⁻¹ * t * q) by group]
        exact mul_mem (inv_mem ht) h1
      have hqtO : t⁻¹ * q⁻¹ * t * q ∈ O := hqP t (hTJ ht)
      have hqtOT : t⁻¹ * q⁻¹ * t * q ∈ OT := by
        rw [hcoreT]
        exact ⟨hqt, hqtO⟩
      have hqr : q⁻¹ * r * q ∈ R := by
        have := (mem_normalizer_iff.mp (inv_mem hqR) r).mp hr
        rwa [inv_inv] at this
      rw [show (t * r)⁻¹ * q⁻¹ * (t * r) * q = r⁻¹ * (t⁻¹ * q⁻¹ * t * q) * (q⁻¹ * r * q) by group]
      exact mul_mem (mul_mem (hROX (inv_mem hr)) (hOTOX hqtOT)) (hROX hqr)

omit [Finite G] in
theorem normalizer_zpowers_eq_centralizer {b : G} (hb : orderOf b = 2) :
    normalizer ((zpowers b : Subgroup G) : Set G) = centralizer ({b} : Set G) := by
  have hbb : b * b = 1 := by rw [← pow_two, ← hb, pow_orderOf_eq_one]
  apply le_antisymm
  · intro g hg
    rw [mem_centralizer_singleton_iff]
    have h1 : g * b * g⁻¹ ∈ zpowers b := (mem_normalizer_iff.mp hg b).mp (mem_zpowers b)
    rcases UnbalancedGS.OrbitFixedComponent.eq_one_or_eq_of_mem_zpowers hbb h1 with h | h
    · exfalso
      have hb1 : b = 1 := by
        have h2 : g⁻¹ * (g * b * g⁻¹) * g = g⁻¹ * 1 * g := by rw [h]
        simpa [mul_assoc] using h2
      rw [hb1, orderOf_one] at hb
      exact absurd hb (by norm_num)
    · calc g * b = (g * b * g⁻¹) * g := by group
        _ = b * g := by rw [h]
  · intro g hg
    rw [← UnbalancedLayer.centralizer_zpowers_eq] at hg
    exact centralizer_le_normalizer' (zpowers b) hg

theorem pPrimeCore_le_normalizer_of_isPComponent {H M : Subgroup G} (hMH : M ≤ H)
    (hM : IsPComponent 2 (M.subgroupOf H)) :
    (pPrimeCore 2 ↥H).map H.subtype ≤ normalizer (M : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro _ ⟨r, hr, rfl⟩
  have hc : IsPComponent 2 (conjugate (M.subgroupOf H) r) :=
    UnbalancedLayer.isPComponent_conjugate hM r
  have hr1 : (QuotientGroup.mk' (pPrimeCore 2 ↥H)) r = 1 := (QuotientGroup.eq_one_iff r).mpr hr
  have himg : (conjugate (M.subgroupOf H) r).map (QuotientGroup.mk' (pPrimeCore 2 ↥H)) =
      (M.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 ↥H)) := by
    rw [map_conjugate, hr1, UnbalancedLayer.conjugate_one]
  have hbij := (CatalogueBPrimeJoin.canonical_prime_component_lift (X := ↥H) 2).2
  have heq := hbij.injOn hc hM himg
  exact UnbalancedLayer.mem_normalizer_of_subgroupOf hMH
    (UnbalancedLayer.mem_normalizer_of_conjugate_eq heq)

theorem le_of_primeResidual_eq_top {Y V R : Subgroup G} (hYW : Y ≤ V ⊔ R)
    (hY : CatalogueBPrimeJoin.primeResidual 2 ↥Y = ⊤) (hRV : R ≤ normalizer (V : Set G))
    (hR : Nat.Coprime 2 (Nat.card R)) : Y ≤ V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := V ⊔ R with hWdef
  have hWV : W ≤ normalizer (V : Set G) := sup_le le_normalizer hRV
  set N := V.subgroupOf W with hNdef
  have hNn : N.Normal := (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hWV
  have hWset : (W : Set G) = (V : Set G) * (R : Set G) :=
    coe_mul_of_right_le_normalizer_left V R hRV
  let f : ↥(R.subgroupOf W) →* ↥W ⧸ N := (QuotientGroup.mk' N).comp (R.subgroupOf W).subtype
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective _ q
    have hw : (w : G) ∈ (V : Set G) * (R : Set G) := hWset ▸ w.2
    obtain ⟨v, hv, r, hr, hvr⟩ := Set.mem_mul.mp hw
    refine ⟨⟨⟨r, mem_sup_right hr⟩, hr⟩, ?_⟩
    show (QuotientGroup.mk' N) ⟨r, mem_sup_right hr⟩ = (QuotientGroup.mk' N) w
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    show (((⟨r, mem_sup_right hr⟩ : W)⁻¹ * w : W) : G) ∈ V
    have h1 : (((⟨r, mem_sup_right hr⟩ : W)⁻¹ * w : W) : G) = r⁻¹ * v * r := by
      simp only [coe_mul, coe_inv]
      rw [← hvr]
      group
    rw [h1]
    have h2 := (mem_normalizer_iff.mp (hRV (inv_mem hr)) v).mp hv
    rwa [inv_inv] at h2
  have hidx : Nat.Coprime 2 N.index := by
    rw [index_eq_card]
    have h1 : Nat.card (↥W ⧸ N) ∣ Nat.card ↥(R.subgroupOf W) := card_dvd_of_surjective f hf
    have h2 : Nat.card ↥(R.subgroupOf W) = Nat.card R :=
      Nat.card_congr (subgroupOfEquivOfLe le_sup_right).toEquiv
    rw [h2] at h1
    exact Nat.Coprime.coprime_dvd_right h1 hR
  have hres := CatalogueBPrimeJoin.primeResidual_le_normal_of_coprime_index 2 N hidx
  have hYres : Y.subgroupOf W ≤ CatalogueBPrimeJoin.primeResidual 2 ↥W := by
    have h2 := CatalogueBPrimeJoin.primeResidual_map_le 2 (inclusion hYW)
    rw [hY, ← MonoidHom.range_eq_map, inclusion_range] at h2
    exact h2
  intro y hy
  exact hres (hYres (show (⟨y, hYW hy⟩ : W) ∈ Y.subgroupOf W from hy))

theorem map_pLayer_subgroup (φ : G ≃* G) (H : Subgroup G) :
    ((pLayer ↥H 2).map H.subtype).map φ.toMonoidHom =
      (pLayer ↥(H.map φ.toMonoidHom) 2).map (H.map φ.toMonoidHom).subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e : H ≃* H.map φ.toMonoidHom := H.equivMapOfInjective φ.toMonoidHom φ.injective
  have hcomm : φ.toMonoidHom.comp H.subtype = (H.map φ.toMonoidHom).subtype.comp e.toMonoidHom := by
    ext j
    rfl
  rw [map_map, hcomm, ← map_map, UnbalancedGS.FixedLayerPComponent.map_pLayer_mulEquiv 2 e]

theorem conjugate_orbit_le {g : G} {T X E V T' R' X' E' V' : Subgroup G}
    (hE : conjugate E g = E') (hX : conjugate X g = X') (hX' : X' = T' ⊔ R')
    (hV : V = ⨆ e ∈ E, conjugate T e) (hTX : T ≤ X)
    (hTres : CatalogueBPrimeJoin.primeResidual 2 ↥T = ⊤) (hT'V' : T' ≤ V')
    (hR'V' : R' ≤ normalizer (V' : Set G)) (hR' : Nat.Coprime 2 (Nat.card R'))
    (hE'V' : E' ≤ normalizer (V' : Set G)) : conjugate V g ≤ V' := by
  have hTg : conjugate T g ≤ V' := by
    refine le_of_primeResidual_eq_top (R := R') ?_ ?_ hR'V' hR'
    · calc conjugate T g ≤ conjugate X g := map_mono hTX
        _ = T' ⊔ R' := hX.trans hX'
        _ ≤ V' ⊔ R' := sup_le_sup_right hT'V' _
    · exact CatalogueBPrimeJoin.primeResidual_eq_top_of_equiv 2
        (T.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective) hTres
  rw [hV]
  show (⨆ e ∈ E, conjugate T e).map (MulAut.conj g⁻¹).toMonoidHom ≤ V'
  rw [map_le_iff_le_comap]
  refine iSup₂_le fun e he => ?_
  rw [← map_le_iff_le_comap]
  show conjugate (conjugate T e) g ≤ V'
  have he' : g⁻¹ * e * g ∈ E' := by
    rw [← hE, UnbalancedLayer.mem_conjugate_iff]
    rwa [show g * (g⁻¹ * e * g) * g⁻¹ = e by group]
  have h1 : conjugate (conjugate T e) g = conjugate (conjugate T g) (g⁻¹ * e * g) := by
    rw [UnbalancedLayer.conjugate_conjugate, UnbalancedLayer.conjugate_conjugate,
      show g * (g⁻¹ * e * g) = e * g by group]
  rw [h1, ← UnbalancedLayer.conjugate_eq_of_mem_normalizer (hE'V' he')]
  exact map_mono hTg

theorem two_local_conj_facts
    (hS : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    [IsSimpleGroup G] (hnonab : ∃ x y : G, x * y ≠ y * x)
    (hK : Assembly.KProper Blueprint.Catalog G) {a : G} (ha : orderOf a = 2) {J : Subgroup G}
    (hJa : J ≤ centralizer ({a} : Set G))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G))))
    {S B T R X E V : Subgroup G} (hSX : S ≤ centralizer ({a} : Set G) ⊓ normalizer (J : Set G))
    (hS2 : IsPGroup 2 S) (hB1 : B ≠ ⊥) (hBP : B ≤ S ⊓ UnbalancedLayer.coreActionKernel J)
    (hT : T = (pLayer ↥(J ⊓ centralizer (B : Set G)) 2).map
      (J ⊓ centralizer (B : Set G)).subtype)
    (hR : R = (pPrimeCore 2 ↥(normalizer (B : Set G))).map (normalizer (B : Set G)).subtype)
    (hX : X = T ⊔ R)
    (hE : E = (pLayer ↥(normalizer (B : Set G)) 2).map (normalizer (B : Set G)).subtype)
    (hV : V = ⨆ e ∈ E, conjugate T e) :
    T ≤ X ∧ CatalogueBPrimeJoin.primeResidual 2 ↥T = ⊤ ∧ T ≤ V ∧
      R ≤ normalizer (V : Set G) ∧ Nat.Coprime 2 (Nat.card R) ∧ E ≤ normalizer (V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, haN, -, -, -, -, -, -, -, hTaN, hpcN, -⟩ :=
    two_local_layer_facts hS hnonab hK ha hJa hJ hSX hS2 hB1 hBP hT
  obtain ⟨M, hMH, hM, hMa, hVK, -, hEV, -⟩ :=
    two_local_orbit_facts hS hU hheld hnonab hK ha hJa hJ hSX hS2 hB1 hBP hT (hV.trans (by rw [hE]))
  have hMaH : conjugate M a ≤ normalizer (B : Set G) := conjugate_le_of_mem hMH haN
  refine ⟨hX ▸ le_sup_left, ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 T _ hTaN).mp
    hpcN).2.1, ?_, ?_, ?_, hE ▸ hEV⟩
  · rw [hV]
    have h1 : conjugate T 1 ≤ ⨆ e ∈ E, conjugate T e :=
      le_iSup₂_of_le (1 : G) (one_mem E) le_rfl
    rwa [UnbalancedLayer.conjugate_one] at h1
  · rw [hR, hVK]
    intro r hr
    exact mem_normalizer_sup (pPrimeCore_le_normalizer_of_isPComponent hMH hM hr)
      (pPrimeCore_le_normalizer_of_isPComponent hMaH hMa hr)
  · rw [hR, card_map_of_injective (Subgroup.subtype_injective _)]
    exact pPrimeCore_coprime_card

theorem two_local_fixed_layer_facts
    (hS : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    [IsSimpleGroup G] (hnonab : ∃ x y : G, x * y ≠ y * x)
    (hK : Assembly.KProper Blueprint.Catalog G) {a : G} (ha : orderOf a = 2) {J : Subgroup G}
    (hJa : J ≤ centralizer ({a} : Set G))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G))))
    {S B H T R X E V : Subgroup G} (hSX : S ≤ centralizer ({a} : Set G) ⊓ normalizer (J : Set G))
    (hS2 : IsPGroup 2 S) (hB1 : B ≠ ⊥) (hBP : B ≤ S ⊓ UnbalancedLayer.coreActionKernel J)
    (hH : H = normalizer (B : Set G))
    (hT : T = (pLayer ↥(J ⊓ centralizer (B : Set G)) 2).map
      (J ⊓ centralizer (B : Set G)).subtype)
    (hR : R = (pPrimeCore 2 ↥H).map H.subtype) (hX : X = T ⊔ R)
    (hE : E = (pLayer ↥H 2).map H.subtype) (hV : V = ⨆ e ∈ E, conjugate T e)
    (d : Subgroup G → ℕ)
    (hd : ∀ W : Subgroup G,
      d W = Nat.card ((↥W ⧸ pPrimeCore 2 ↥W) ⧸ center (↥W ⧸ pPrimeCore 2 ↥W))) :
    (H ≠ ⊤ ∧ SectionRank.IsKGroupCat ↥H) ∧
      R = (pPrimeCore 2 ↥(centralizer (B : Set G))).map (centralizer (B : Set G)).subtype ∧
      T ⊔ (pPrimeCore 2 ↥J).map J.subtype = J ∧
      (∃ e : ↥T ⧸ pPrimeCore 2 ↥T ≃* ↥J ⧸ pPrimeCore 2 ↥J,
        ∀ (t : T) (j : J), (t : G) = j → e t = j) ∧
      T ≤ H ⊓ centralizer ({a} : Set G) ∧
      IsPComponent 2 (T.subgroupOf (H ⊓ centralizer ({a} : Set G))) ∧ T ≤ E ∧
      (∃ M : Subgroup G, M ≤ H ∧ IsPComponent 2 (M.subgroupOf H) ∧
        IsPComponent 2 ((conjugate M a).subgroupOf H) ∧ V = M ⊔ conjugate M a ∧
        V ≤ E ∧ (V.subgroupOf E).Normal ∧ d J ≤ d V ∧
        (d V = d J ↔ M = conjugate M a ∧ ⁅V, zpowers a⁆ ≤ (pPrimeCore 2 ↥V).map V.subtype) ∧
        (d V = d J → IsPComponent 2 (V.subgroupOf H) ∧
          (T : Set G) * ((pPrimeCore 2 ↥V).map V.subtype : Set G) = V ∧
          T = UnbalancedGS.gsFixedLayer V a) ∧
        (d J < d V ↔ ⁅V, zpowers a⁆ = V) ∧
        ∀ b : G, B = zpowers b → orderOf b = 2 → d V = d J → UnbalancedGS.GSIsoCorr a J b V) ∧
      (pPrimeCore 2 ↥X).map X.subtype = R ⊔ (pPrimeCore 2 ↥T).map T.subtype ∧
      (∃ e : ↥X ⧸ pPrimeCore 2 ↥X ≃* ↥J ⧸ pPrimeCore 2 ↥J,
        (∀ (x : X) (j : J), (x : G) ∈ T → (x : G) = j → e x = j) ∧
        ∀ q ∈ S ⊓ normalizer (B : Set G), ∀ (x : X) (j : J) (hx : q * x * q⁻¹ ∈ X)
          (hj : q * j * q⁻¹ ∈ J), e x = j → e (⟨q * x * q⁻¹, hx⟩ : X) = (⟨q * j * q⁻¹, hj⟩ : J)) ∧
      (∀ q ∈ S ⊓ normalizer (B : Set G), q ∈ normalizer (X : Set G) ∧
        q ∈ normalizer (J : Set G) ∧
        ((∀ x ∈ X, x⁻¹ * q⁻¹ * x * q ∈ (pPrimeCore 2 ↥X).map X.subtype) ↔
          q ∈ (S ⊓ UnbalancedLayer.coreActionKernel J) ⊓ normalizer (B : Set G))) ∧
      ∀ g ∈ H ⊓ normalizer (X : Set G), g ∈ normalizer (V : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  subst hH
  simp only [hd]
  obtain ⟨hB2, haN, hHtop, hKH, hRC, hsupT, hcoreT, hTaB, hpcB, hTaN, hpcN, hTE⟩ :=
    two_local_layer_facts hS hnonab hK ha hJa hJ hSX hS2 hB1 hBP hT
  obtain ⟨M, hMH, hM, hMa, hVK, hVE, hEV, hdle, hdeq, hdeqc, hdlt⟩ :=
    two_local_orbit_facts hS hU hheld hnonab hK ha hJa hJ hSX hS2 hB1 hBP hT (hV.trans (by rw [hE]))
  obtain ⟨hOX, ⟨eX, heX, heXq⟩, hQ⟩ :=
    two_local_core_facts hS hnonab hK ha hJa hJ hSX hS2 hB1 hBP hT (hX.trans (by rw [hR]))
  obtain ⟨hTX, hTres, hTV, hRV, hRodd, hEV'⟩ :=
    two_local_conj_facts hS hU hheld hnonab hK ha hJa hJ hSX hS2 hB1 hBP hT (hR.trans rfl) hX
      (hE.trans rfl) hV
  have hTJ : T ≤ J := hT ▸ (map_subtype_le _).trans inf_le_left
  refine ⟨⟨hHtop, hKH⟩, hR.trans hRC, hsupT, exists_quotient_equiv_of_sup hTJ hsupT hcoreT,
    fun t ht => ⟨(hTaN ht).2, (hTaN ht).1⟩, by rw [inf_comm]; exact hpcN, hE ▸ hTE,
    ⟨M, hMH, hM, hMa, hVK, hE ▸ hVE,
      (normal_subgroupOf_iff_le_normalizer (hE ▸ hVE)).mpr (hE ▸ hEV), hdle, hdeq, hdeqc, hdlt,
      ?_⟩, hR ▸ hOX, ⟨eX, heX, heXq⟩, hQ, ?_⟩
  ·
    intro b hBb hb2 hdeqJ
    obtain ⟨hpcV, hmulV, hTV'⟩ := hdeqc hdeqJ
    obtain ⟨hMaM, -⟩ := hdeq.mp hdeqJ
    have hNb : normalizer (B : Set G) = centralizer ({b} : Set G) := by
      rw [hBb]
      exact normalizer_zpowers_eq_centralizer hb2
    have hbB : b ∈ B := hBb ▸ mem_zpowers b
    have hbS : b ∈ S := (hBP hbB).1
    have hab : a * b = b * a := (mem_centralizer_singleton_iff.mp (hSX hbS).1).symm
    have hCB : centralizer (B : Set G) = centralizer ({b} : Set G) := by
      rw [hBb, UnbalancedLayer.centralizer_zpowers_eq]
    have hVM : V = M := by rw [hVK, ← hMaM, sup_idem]
    have hVV : V ⊔ conjugate V a = V := by rw [hVM, ← hMaM, sup_idem]
    have hTfix : UnbalancedGS.gsFixedLayer J b = T := by
      rw [hT]
      show (pLayer ↥(J ⊓ centralizer ({b} : Set G)) 2).map (J ⊓ centralizer ({b} : Set G)).subtype =
        (pLayer ↥(J ⊓ centralizer (B : Set G)) 2).map (J ⊓ centralizer (B : Set G)).subtype
      rw [hCB]
    have hVb : V ≤ centralizer ({b} : Set G) := by
      rw [← hNb]
      exact hVE.trans (map_subtype_le _)
    refine ⟨⟨ha, hb2, hab, hJa, hJ, hVb, ?_, (hSX hbS).2, ((hBP hbB).2).2, ?_⟩, hVV, ?_⟩
    · rw [← hNb]
      exact hpcV
    · rw [hVV, hTfix]
      exact hTV'
    · rw [hTfix]
      exact hmulV
  ·
    intro g hg
    obtain ⟨hgH, hgX⟩ := mem_inf.mp hg
    have hcharE : ∀ g' ∈ normalizer (B : Set G), g' ∈ normalizer (E : Set G) := by
      intro g' hg'
      rw [hE]
      have : (pLayer ↥(normalizer (B : Set G)) 2).Characteristic :=
        CatalogueBPrimeJoin.pLayer_characteristic
      exact UnbalancedGS.normalizer_le_normalizer_map_of_characteristic _ _ (le_normalizer hg')
    have key : ∀ g' : G, g' ∈ normalizer (B : Set G) → g' ∈ normalizer (X : Set G) →
        conjugate V g' ≤ V := fun g' hgB hgX' =>
      conjugate_orbit_le (UnbalancedLayer.conjugate_eq_of_mem_normalizer (hcharE g' hgB))
        (UnbalancedLayer.conjugate_eq_of_mem_normalizer hgX') hX hV hTX hTres hTV hRV hRodd hEV'
    have h1 := key g hgH hgX
    have h2 := key g⁻¹ (inv_mem hgH) (inv_mem hgX)
    apply UnbalancedLayer.mem_normalizer_of_conjugate_eq
    apply le_antisymm h1
    calc V = conjugate (conjugate V g⁻¹) g := by
          rw [UnbalancedLayer.conjugate_conjugate, inv_mul_cancel, UnbalancedLayer.conjugate_one]
      _ ≤ conjugate V g := map_mono h2

theorem actual_two_local_fixed_layer_orbits_of_inputs
    (hS : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    [IsSimpleGroup G] (hnonab : ∃ x y : G, x * y ≠ y * x)
    (hK : Assembly.KProper Blueprint.Catalog G) {a : G} (ha : orderOf a = 2) {J : Subgroup G}
    (hJa : J ≤ centralizer ({a} : Set G))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G))))
    {S P : Subgroup G} (hSX : S ≤ centralizer ({a} : Set G) ⊓ normalizer (J : Set G))
    (hSsyl : ∃ P₀ : Sylow 2 ↥(centralizer ({a} : Set G) ⊓ normalizer (J : Set G)),
      (P₀ : Subgroup _) = S.subgroupOf (centralizer ({a} : Set G) ⊓ normalizer (J : Set G)))
    (hP : P = S ⊓ UnbalancedLayer.coreActionKernel J)
    (H R T X E V : Subgroup G → Subgroup G) (hH : ∀ B, H B = normalizer (B : Set G))
    (hR : ∀ B, R B = (pPrimeCore 2 ↥(H B)).map (H B).subtype)
    (hT : ∀ B, T B = (pLayer ↥(J ⊓ centralizer (B : Set G)) 2).map
      (J ⊓ centralizer (B : Set G)).subtype)
    (hX : ∀ B, X B = T B ⊔ R B) (hE : ∀ B, E B = (pLayer ↥(H B) 2).map (H B).subtype)
    (hV : ∀ B, V B = ⨆ e ∈ E B, conjugate (T B) e) (d : Subgroup G → ℕ)
    (hd : ∀ W : Subgroup G,
      d W = Nat.card ((↥W ⧸ pPrimeCore 2 ↥W) ⧸ center (↥W ⧸ pPrimeCore 2 ↥W))) :
    (∀ B : Subgroup G, B ≠ ⊥ → B ≤ P →
      (H B ≠ ⊤ ∧ SectionRank.IsKGroupCat ↥(H B)) ∧
      R B = (pPrimeCore 2 ↥(centralizer (B : Set G))).map (centralizer (B : Set G)).subtype ∧
      T B ⊔ (pPrimeCore 2 ↥J).map J.subtype = J ∧
      (∃ e : ↥(T B) ⧸ pPrimeCore 2 ↥(T B) ≃* ↥J ⧸ pPrimeCore 2 ↥J,
        ∀ (t : T B) (j : J), (t : G) = j → e t = j) ∧
      T B ≤ H B ⊓ centralizer ({a} : Set G) ∧
      IsPComponent 2 ((T B).subgroupOf (H B ⊓ centralizer ({a} : Set G))) ∧ T B ≤ E B ∧
      (∃ M : Subgroup G, M ≤ H B ∧ IsPComponent 2 (M.subgroupOf (H B)) ∧
        IsPComponent 2 ((conjugate M a).subgroupOf (H B)) ∧ V B = M ⊔ conjugate M a ∧
        V B ≤ E B ∧ ((V B).subgroupOf (E B)).Normal ∧ d J ≤ d (V B) ∧
        (d (V B) = d J ↔
          M = conjugate M a ∧ ⁅V B, zpowers a⁆ ≤ (pPrimeCore 2 ↥(V B)).map (V B).subtype) ∧
        (d (V B) = d J → IsPComponent 2 ((V B).subgroupOf (H B)) ∧
          (T B : Set G) * ((pPrimeCore 2 ↥(V B)).map (V B).subtype : Set G) = V B ∧
          T B = UnbalancedGS.gsFixedLayer (V B) a) ∧
        (d J < d (V B) ↔ ⁅V B, zpowers a⁆ = V B) ∧
        ∀ b : G, B = zpowers b → orderOf b = 2 → d (V B) = d J →
          UnbalancedGS.GSIsoCorr a J b (V B)) ∧
      (pPrimeCore 2 ↥(X B)).map (X B).subtype = R B ⊔ (pPrimeCore 2 ↥(T B)).map (T B).subtype ∧
      (∃ e : ↥(X B) ⧸ pPrimeCore 2 ↥(X B) ≃* ↥J ⧸ pPrimeCore 2 ↥J,
        (∀ (x : X B) (j : J), (x : G) ∈ T B → (x : G) = j → e x = j) ∧
        ∀ q ∈ S ⊓ normalizer (B : Set G), ∀ (x : X B) (j : J) (hx : q * x * q⁻¹ ∈ X B)
          (hj : q * j * q⁻¹ ∈ J),
          e x = j → e (⟨q * x * q⁻¹, hx⟩ : X B) = (⟨q * j * q⁻¹, hj⟩ : J)) ∧
      (∀ q ∈ S ⊓ normalizer (B : Set G), q ∈ normalizer (X B : Set G) ∧
        q ∈ normalizer (J : Set G) ∧
        ((∀ x ∈ X B, x⁻¹ * q⁻¹ * x * q ∈ (pPrimeCore 2 ↥(X B)).map (X B).subtype) ↔
          q ∈ P ⊓ normalizer (B : Set G))) ∧
      ∀ g ∈ H B ⊓ normalizer (X B : Set G), g ∈ normalizer (V B : Set G)) ∧
    ∀ (B B' : Subgroup G) (g : G), B ≠ ⊥ → B ≤ P → conjugate B g = B' → B' ≤ P →
      conjugate (X B) g = X B' → conjugate (V B) g = V B' ∧ d (V B) = d (V B') := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 S := by
    obtain ⟨P₀, hP₀⟩ := hSsyl
    have h1 : IsPGroup 2 (S.subgroupOf (centralizer ({a} : Set G) ⊓ normalizer (J : Set G))) :=
      hP₀ ▸ P₀.isPGroup'
    exact h1.of_equiv (subgroupOfEquivOfLe hSX)
  subst hP
  refine ⟨fun B hB1 hBP => two_local_fixed_layer_facts hS hU hheld hnonab hK ha hJa hJ hSX hS2 hB1
    hBP (hH B) (hT B) (hR B) (hX B) (hE B) (hV B) d hd, ?_⟩
  intro B B' g hB1 hBP hBB' hB'P hXX'
  have hB'1 : B' ≠ ⊥ := by
    rw [← hBB']
    intro h
    apply hB1
    have h1 : B.map (MulAut.conj g⁻¹).toMonoidHom = ⊥ := h
    rwa [map_eq_bot_iff_of_injective _ (MulAut.conj g⁻¹).injective] at h1
  have hRf : ∀ C, R C = (pPrimeCore 2 ↥(normalizer (C : Set G))).map
      (normalizer (C : Set G)).subtype := fun C => by rw [hR, hH]
  have hEf : ∀ C, E C = (pLayer ↥(normalizer (C : Set G)) 2).map
      (normalizer (C : Set G)).subtype := fun C => by rw [hE, hH]
  obtain ⟨hTX, hTres, hTV, hRV, hRodd, hEV⟩ :=
    two_local_conj_facts hS hU hheld hnonab hK ha hJa hJ hSX hS2 hB1 hBP (hT B) (hRf B) (hX B)
      (hEf B) (hV B)
  obtain ⟨hTX', hTres', hTV', hRV', hRodd', hEV'⟩ :=
    two_local_conj_facts hS hU hheld hnonab hK ha hJa hJ hSX hS2 hB'1 hB'P (hT B') (hRf B')
      (hX B') (hEf B') (hV B')
  have hNN' : (normalizer (B : Set G)).map (MulAut.conj g⁻¹).toMonoidHom =
      normalizer (B' : Set G) := by
    rw [map_equiv_normalizer_eq, ← hBB']
    rfl
  have hEE' : conjugate (E B) g = E B' := by
    rw [hEf, hEf]
    show ((pLayer ↥(normalizer (B : Set G)) 2).map (normalizer (B : Set G)).subtype).map
      (MulAut.conj g⁻¹).toMonoidHom = _
    rw [map_pLayer_subgroup, hNN']
  have hEE : conjugate (E B') g⁻¹ = E B := by
    rw [← hEE', UnbalancedLayer.conjugate_conjugate, mul_inv_cancel, UnbalancedLayer.conjugate_one]
  have hXX : conjugate (X B') g⁻¹ = X B := by
    rw [← hXX', UnbalancedLayer.conjugate_conjugate, mul_inv_cancel, UnbalancedLayer.conjugate_one]
  have h1 := conjugate_orbit_le hEE' hXX' (hX B') (hV B) hTX hTres hTV' hRV' hRodd' hEV'
  have h2 := conjugate_orbit_le hEE hXX (hX B) (hV B') hTX' hTres' hTV hRV hRodd hEV
  have heq : conjugate (V B) g = V B' := by
    apply le_antisymm h1
    calc V B' = conjugate (conjugate (V B') g⁻¹) g := by
          rw [UnbalancedLayer.conjugate_conjugate, inv_mul_cancel, UnbalancedLayer.conjugate_one]
      _ ≤ conjugate (V B) g := map_mono h2
  refine ⟨heq, ?_⟩
  rw [← heq, hd, hd]
  exact card_centerQuotient_pPrimeCore_congr
    ((V B).equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective)

end CFSG.ComponentClassification.UnbalancedCorr
