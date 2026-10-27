module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldG2P3
public import CFSG.Quasithin.EmptyFaithfulMultiple.G2TwoUnitary
public import CFSG.Quasithin.H13.GoldschmidtC137SQRkU33

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

theorem centralizer_eq_bot_of_index_two {J : Type*} [Group J] [Finite J] (T : Subgroup J)
    [T.Normal] (hT : T.index = 2) (hZT : Subgroup.center T = ⊥)
    (hZJ : Subgroup.center J = ⊥) : Subgroup.centralizer (T : Set J) = ⊥ := by
  classical
  set Z := Subgroup.centralizer (T : Set J) with hZdef
  have hZT' : ∀ z ∈ Z, z ∈ T → z = 1 := by
    intro z hz hzT
    have hc : (⟨z, hzT⟩ : T) ∈ Subgroup.center T := by
      rw [Subgroup.mem_center_iff]
      intro t
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.1 hz) t t.2)
    rw [hZT, Subgroup.mem_bot] at hc
    exact congrArg Subtype.val hc
  let π : Z →* J ⧸ T := (QuotientGroup.mk' T).comp Z.subtype
  have hπ : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro z hz
    rw [MonoidHom.mem_ker] at hz
    have hzT : (z : J) ∈ T := (QuotientGroup.eq_one_iff (z : J)).1 hz
    exact (Subgroup.mem_bot).2 (Subtype.ext (hZT' z z.2 hzT))
  have hZ2 : Nat.card Z ≤ 2 := by
    have h1 := Nat.card_le_card_of_injective π hπ
    rwa [← Subgroup.index, hT] at h1
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  by_contra hz1
  have hcen : z ∈ Subgroup.center J := by
    rw [Subgroup.mem_center_iff]
    intro a
    have hmem : a * z * a⁻¹ ∈ Z := (Subgroup.normal_centralizer (H := T)).conj_mem z hz a
    by_contra hne
    have hne' : a * z * a⁻¹ ≠ z := fun h => hne (by
      calc a * z = a * z * a⁻¹ * a := by group
        _ = z * a := by rw [h])
    have hne1 : a * z * a⁻¹ ≠ 1 := fun h => hz1 (by
      calc z = a⁻¹ * (a * z * a⁻¹) * a := by group
        _ = 1 := by rw [h]; group)
    have h3 : 3 ≤ Nat.card Z := by
      have : Fintype Z := Fintype.ofFinite Z
      rw [Nat.card_eq_fintype_card]
      let s : Finset Z := {1, ⟨z, hz⟩, ⟨a * z * a⁻¹, hmem⟩}
      have hs : s.card = 3 := by
        rw [Finset.card_eq_three]
        refine ⟨1, ⟨z, hz⟩, ⟨a * z * a⁻¹, hmem⟩, ?_, ?_, ?_, rfl⟩
        · exact fun h => hz1 (congrArg Subtype.val h).symm
        · exact fun h => hne1 (congrArg Subtype.val h).symm
        · exact fun h => hne' (congrArg Subtype.val h).symm
      rw [← hs]
      exact Finset.card_le_univ s
    omega
  rw [hZJ, Subgroup.mem_bot] at hcen
  exact hz1 hcen

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.LieType.SeitzGeneration CFSG.LieType.Chevalley
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.TauCetiBridge CFSG.RankThree.Chevalley
  CFSG.RankThree.Chevalley.SteinbergBT

theorem commutator_self_le_and_normalized {C : Type*} [Group C] (J : Subgroup C) :
    ⁅J, J⁆ ≤ J ∧ ∀ f ∈ J, ∀ t ∈ ⁅J, J⁆, f * t * f⁻¹ ∈ ⁅J, J⁆ := by
  refine ⟨?_, fun f hf t ht => ?_⟩
  · rw [← Subgroup.map_subtype_commutator J]
    exact Subgroup.map_subtype_le _
  · rw [← Subgroup.map_subtype_commutator J] at ht ⊢
    obtain ⟨t', ht', rfl⟩ := ht
    exact ⟨⟨f, hf⟩ * t' * ⟨f, hf⟩⁻¹,
      (inferInstance : (commutator J).Normal).conj_mem _ ht' _, rfl⟩

theorem fixes_of_fixes_derived {C : Type*} [Group C] [Finite C] (J : Subgroup C)
    (hidx : (⁅J, J⁆.subgroupOf J).index = 2) (hZT : Subgroup.center ↥⁅J, J⁆ = ⊥)
    (hZJ : Subgroup.center J = ⊥) (g : MulAut C) (hgJ : ∀ j ∈ J, g j ∈ J)
    (hgT : ∀ t ∈ ⁅J, J⁆, g t = t) : ∀ j ∈ J, g j = j := by
  classical
  obtain ⟨hTJ, hTn⟩ := commutator_self_le_and_normalized J
  have hnorm : (⁅J, J⁆.subgroupOf J).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hTn g.1 g.2 n.1 hn
  have hZT' : Subgroup.center (⁅J, J⁆.subgroupOf J) = ⊥ := by
    have e := Subgroup.subgroupOfEquivOfLe hTJ
    have h1 := Subgroup.map_center_eq e
    rw [hZT] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ (f := e.toMonoidHom) e.injective).1 h1
  have hcen := centralizer_eq_bot_of_index_two (⁅J, J⁆.subgroupOf J) hidx hZT' hZJ
  intro j hj
  have hgj := hgJ j hj
  have hc : (⟨j⁻¹ * g j, J.mul_mem (J.inv_mem hj) hgj⟩ : J) ∈
      Subgroup.centralizer ((⁅J, J⁆.subgroupOf J : Subgroup J) : Set J) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at ht
    apply Subtype.ext
    change (t : C) * (j⁻¹ * g j) = j⁻¹ * g j * t
    have h1 := hgT _ (hTn j hj _ ht)
    rw [map_mul, map_mul, map_inv, hgT _ ht] at h1
    calc (t : C) * (j⁻¹ * g j) = j⁻¹ * (j * t * j⁻¹) * g j := by group
      _ = j⁻¹ * (g j * t * (g j)⁻¹) * g j := by rw [h1]
      _ = j⁻¹ * g j * t := by group
  rw [hcen, Subgroup.mem_bot] at hc
  have h2 : j⁻¹ * g j = 1 := congrArg Subtype.val hc
  calc g j = j * (j⁻¹ * g j) := by group
    _ = j := by rw [h2, mul_one]

theorem simple_card_commutator_adjointG2_two (k : Type) [Field k]
    [Finite k] (hk : Nat.card k = 2) :
    IsSimpleGroup ↥⁅adjointGroup Tag.G2 k, adjointGroup Tag.G2 k⁆ ∧
      Nat.card ↥⁅adjointGroup Tag.G2 k, adjointGroup Tag.G2 k⁆ = 6048 :=
  CFSG.Quasithin.H13.U3.GC137.SQ.simple_card_of_lieModel_psu_three_three
    (CFSG.Quasithin.EmptyFaithfulMultiple.g2TwoDerivedUnitaryTransport_holds k hk)

section G2Eight


theorem derived_range_adjointG2_two {C : Type*} [Group C] (k : Type) [Field k] [Finite k]
    (hk : Nat.card k = 2) (φ : adjointGroup Tag.G2 k →* C) (hφ : Function.Injective φ) :
    CFSG.IsQuasisimple ↥⁅φ.range, φ.range⁆ ∧ Nat.card ↥⁅φ.range, φ.range⁆ = 6048 ∧
      Subgroup.center ↥⁅φ.range, φ.range⁆ = ⊥ ∧ Nat.card φ.range = 12096 ∧
      Subgroup.center φ.range = ⊥ := by
  classical
  have : Finite (ModGL Tag.G2 k) := finite_modGL
  have hT : ⁅φ.range, φ.range⁆ = (commutator (adjointGroup Tag.G2 k)).map φ := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map]
  let eT : ↥⁅φ.range, φ.range⁆ ≃* ↥⁅adjointGroup Tag.G2 k, adjointGroup Tag.G2 k⁆ :=
    ((MulEquiv.subgroupCongr hT).trans
      ((commutator (adjointGroup Tag.G2 k)).equivMapOfInjective φ hφ).symm).trans
      (((commutator (adjointGroup Tag.G2 k)).equivMapOfInjective
        (adjointGroup Tag.G2 k).subtype Subtype.val_injective).trans
        (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator _)))
  obtain ⟨hsimple, hcard⟩ := simple_card_commutator_adjointG2_two k hk
  have hTcard : Nat.card ↥⁅φ.range, φ.range⁆ = 6048 := by rw [Nat.card_congr eT.toEquiv, hcard]
  have hZ0 : Subgroup.center ↥⁅adjointGroup Tag.G2 k, adjointGroup Tag.G2 k⁆ = ⊥ :=
    CFSG.Quasithin.H13.U3.GC137.SQ.center_eq_bot_of_simple (by rw [hcard]; norm_num)
  have hZT : Subgroup.center ↥⁅φ.range, φ.range⁆ = ⊥ := by
    have h1 := Subgroup.map_center_eq eT
    rw [hZ0] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ (f := eT.toMonoidHom) eT.injective).1 h1
  have hnc : ¬ ∀ a b : ↥⁅φ.range, φ.range⁆, a * b = b * a := by
    intro hab
    have htop : Subgroup.center ↥⁅φ.range, φ.range⁆ = ⊤ := by
      rw [eq_top_iff]
      intro a _
      exact Subgroup.mem_center_iff.2 fun b => hab b a
    rw [hZT] at htop
    have h1 : Nat.card ↥⁅φ.range, φ.range⁆ = 1 := by
      rw [← Subgroup.card_top (G := ↥⁅φ.range, φ.range⁆), ← htop, Subgroup.card_bot]
    omega
  have : IsSimpleGroup ↥⁅φ.range, φ.range⁆ := eT.isSimpleGroup
  refine ⟨isQuasisimple_of_simple_nonabelian hnc, hTcard, hZT, ?_, ?_⟩
  · rw [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv,
      CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hk]
    norm_num [ordG2]
  · have h0 : Subgroup.center (adjointGroup Tag.G2 k) = ⊥ := center_adjointGroup_eq_bot
    have h1 := Subgroup.map_center_eq (MonoidHom.ofInjective hφ)
    rw [h0, Subgroup.map_bot] at h1
    exact h1.symm

theorem fieldCoreAt_entrywise_G2_eight {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ 3)
    {σ : K ≃+* K} (hσp : orderOf σ = 3) : FieldCoreAt 3 (entrywiseAdjointAut Tag.G2 σ) := by
  classical
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  obtain ⟨-, hk, hJC, hfixeq, -, -, -, -, -, -, hcent, -, -⟩ :=
    even_G2_canonical_field_centralizer_all_orders (by norm_num : 2 ≤ 3) hK σ
  rw [hσp] at hk
  have hk2 : Nat.card (fixSubfield σ) = 2 := hk.trans (by norm_num)
  have : Finite (fixSubfield σ) := Subtype.finite
  have hmemφ : ∀ a : adjointGroup Tag.G2 (fixSubfield σ),
      baseChangeGL (fixSubfield σ).subtype (a : ModGL Tag.G2 (fixSubfield σ)) ∈
        adjointGroup Tag.G2 K := fun a => hJC ⟨a, a.2, rfl⟩
  obtain ⟨φ, hφdef⟩ : ∃ φ : adjointGroup Tag.G2 (fixSubfield σ) →* adjointGroup Tag.G2 K,
      ∀ a, (φ a : ModGL Tag.G2 K) =
        baseChangeGL (fixSubfield σ).subtype (a : ModGL Tag.G2 (fixSubfield σ)) :=
    ⟨((baseChangeGL (fixSubfield σ).subtype).comp
      (adjointGroup Tag.G2 (fixSubfield σ)).subtype).codRestrict _ hmemφ, fun _ => rfl⟩
  have hφ : Function.Injective φ := fun a b h =>
    Subtype.ext (baseChangeGL_injective _ (by rw [← hφdef, ← hφdef, h]))
  have hJfix : ∀ g : adjointGroup Tag.G2 K, g ∈ φ.range ↔ entrywiseAdjointAut Tag.G2 σ g = g := by
    intro g
    have h1 : g ∈ φ.range ↔ (g : ModGL Tag.G2 K) ∈ fixedFieldImage Tag.G2 σ := by
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨a, a.2, (hφdef a).symm⟩
      · rintro ⟨a, ha, hga⟩
        exact ⟨⟨a, ha⟩, Subtype.ext ((hφdef _).trans hga)⟩
    rw [h1, ← hfixeq]
    constructor
    · rintro ⟨g', hg', hgg'⟩
      have : g' = g := Subtype.ext hgg'
      subst this
      exact hg'
    · intro h
      exact ⟨g, h, rfl⟩
  obtain ⟨hq, hTcard, hZT, hJcard, hZJ⟩ := derived_range_adjointG2_two (fixSubfield σ) hk2 φ hφ
  obtain ⟨hTJ, hTn⟩ := commutator_self_le_and_normalized φ.range
  have hidx : (⁅φ.range, φ.range⁆.subgroupOf φ.range).index = 2 := by
    have h := (⁅φ.range, φ.range⁆.subgroupOf φ.range).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTJ).toEquiv, hTcard, hJcard] at h
    omega
  refine ⟨⁅φ.range, φ.range⁆, fun t ht => (hJfix t).1 (hTJ ht),
    fun f hf t ht => hTn f ((hJfix f).2 hf) t ht, hq, ?_, ?_⟩
  · rw [hTcard, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    norm_num
  · intro g hgp hgδ hgT
    have hgJ : ∀ j ∈ φ.range, g j ∈ φ.range := by
      intro j hj
      rw [hJfix]
      have h1 := congrArg (fun β : MulAut (adjointGroup Tag.G2 K) => β j) hgδ
      simp only [MulAut.mul_apply] at h1
      rw [← h1, (hJfix j).1 hj]
    have hfixJ := fixes_of_fixes_derived φ.range hidx hZT hZJ g hgJ hgT
    have hJ₀ : φ.range = (fixedFieldImage Tag.G2 σ).subgroupOf (adjointGroup Tag.G2 K) := by
      ext j
      rw [Subgroup.mem_subgroupOf]
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨a, a.2, (hφdef a).symm⟩
      · rintro ⟨a, ha, hga⟩
        exact ⟨⟨a, ha⟩, Subtype.ext ((hφdef _).trans hga)⟩
    have hg1 : g ∈ Subgroup.centralizer {entrywiseAdjointAut Tag.G2 σ} ⊓
        Subgroup.centralizer ((((fixedFieldImage Tag.G2 σ).subgroupOf
          (adjointGroup Tag.G2 K)).map MulAut.conj : Subgroup (MulAut (adjointGroup Tag.G2 K))) :
            Set (MulAut (adjointGroup Tag.G2 K))) := by
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 hgδ, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨j, hj, rfl⟩
      rw [← hJ₀] at hj
      have h1 := mul_conj_mul_inv g j
      rw [hfixJ j hj] at h1
      change MulAut.conj j * g = g * MulAut.conj j
      calc MulAut.conj j * g = (g * MulAut.conj j * g⁻¹) * g := by rw [h1]
        _ = g * MulAut.conj j := by group
    rw [hcent] at hg1
    have hδp : orderOf (entrywiseAdjointAut Tag.G2 σ) = 3 :=
      (orderOf_entrywiseAdjointAut (by decide : 0 < Tag.G2.rank) σ).trans hσp
    have hdvd : orderOf g ∣ 3 := hδp ▸ orderOf_dvd_of_mem_zpowers hg1
    exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hgp.symm hdvd)

theorem g2EightFieldCore : G2EightFieldCore := by
  intro K _ hK x hxp hxo
  classical
  have hK8 : Nat.card K = 2 ^ 3 := hK.trans (by norm_num)
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have hNF := conj_normalForm_of_pointwise
    (CFSG.ComponentClassification.UnbalancedCatalog.even_G2_exact_automorphism_normal_form
      (by norm_num : 2 ≤ 3) K hK8).1
  obtain ⟨⟨y, σ⟩, hyσ, -⟩ := hNF x
  have hαp : orderOf (⟨x, Subgroup.mem_top x⟩ :
      (⊤ : Subgroup (MulAut (adjointGroup Tag.G2 K)))) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact hxp
  obtain ⟨hσp, -, ⟨h, hh⟩, -⟩ := even_G2_noninner_prime_local_core_trivial
    (by norm_num : 2 ≤ 3) hK8 Nat.prime_three ⊤ le_top ⟨x, Subgroup.mem_top x⟩ hxo hαp y σ hyσ
  exact fieldCoreAt_of_conj (fieldCoreAt_entrywise_G2_eight hK8 hσp) (MulAut.conj h) hh

end G2Eight

section Family


theorem crossCharFamAt_G2_open :
    CrossCharFamAt .G2 fun idx p => ¬ regimeG2Vac idx p ∧ ¬ regimeG2Field idx p :=
  crossCharFamAt_G2_open_of_fieldCore g2EightFieldCore

end Family

end CFSG.HardMathSupport.Timmesfeld.CrossChar
