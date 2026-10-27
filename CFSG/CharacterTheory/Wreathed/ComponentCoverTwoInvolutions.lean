module

public import CFSG.CharacterTheory.Wreathed.ComponentCoverFactorizations

public section

open scoped Classical Pointwise

namespace CFSG.Wreathed.ComponentCoverFactorizations

variable {G : Type} [Group G]

theorem layer_map_mulEquiv {A B : Type*} [Group A] [Group B] (f : A ≃* B) :
    (CFSG.layer A).map f.toMonoidHom = CFSG.layer B := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    apply sSup_le
    intro K hK
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup (CFSG.LocalCores.isComponent_map_mulEquiv f hK)
  · apply sSup_le
    intro L hL
    have hL' : CFSG.IsComponent (L.map f.symm.toMonoidHom) :=
      CFSG.LocalCores.isComponent_map_mulEquiv f.symm hL
    have hle : L.map f.symm.toMonoidHom ≤ CFSG.layer A := le_sSup hL'
    have := Subgroup.map_mono (f := f.toMonoidHom) hle
    rwa [Subgroup.map_map, show f.toMonoidHom.comp f.symm.toMonoidHom = MonoidHom.id B from by
      ext; simp, Subgroup.map_id] at this

@[expose] def ComponentCovered (a : G) (K : Subgroup G) : Prop :=
  CFSG.layer (Subgroup.centralizer ({a} : Set G) ⧸
      CFSG.oddCore (Subgroup.centralizer ({a} : Set G))) ≤
    (K.subgroupOf (Subgroup.centralizer ({a} : Set G))).map
      (QuotientGroup.mk' (CFSG.oddCore (Subgroup.centralizer ({a} : Set G))))

theorem centralizer_map_conj (g a : G) :
    (Subgroup.centralizer ({a} : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ({g * a * g⁻¹} : Set G) := by
  ext b
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · rintro ⟨c, hc, rfl⟩
    calc g * c * g⁻¹ * (g * a * g⁻¹) = g * (c * a) * g⁻¹ := by group
      _ = g * (a * c) * g⁻¹ := by rw [hc]
      _ = g * a * g⁻¹ * (g * c * g⁻¹) := by group
  · intro hb
    refine ⟨g⁻¹ * b * g, ?_, by group⟩
    calc g⁻¹ * b * g * a = g⁻¹ * (b * (g * a * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * a * g⁻¹) * b) * g := by rw [hb]
      _ = a * (g⁻¹ * b * g) := by group

theorem ComponentCovered.conj {a : G} {K : Subgroup G} (h : ComponentCovered a K) (g : G) :
    ComponentCovered (g * a * g⁻¹) (K.map (MulAut.conj g).toMonoidHom) := by
  let C := Subgroup.centralizer ({a} : Set G)
  let C' := Subgroup.centralizer ({g * a * g⁻¹} : Set G)
  let ψ : C ≃* C' := (C.equivMapOfInjective (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr (centralizer_map_conj g a))
  have hcore : (CFSG.oddCore C).map ψ.toMonoidHom = CFSG.oddCore C' :=
    CFSG.ComponentClassification.OddCore.equiv_invariant ψ
  let Ψ : C ⧸ CFSG.oddCore C ≃* C' ⧸ CFSG.oddCore C' :=
    QuotientGroup.congr (CFSG.oddCore C) (CFSG.oddCore C') ψ hcore
  have hΨ : ∀ c : C, Ψ (QuotientGroup.mk' (CFSG.oddCore C) c) =
      QuotientGroup.mk' (CFSG.oddCore C') (ψ c) := fun c => QuotientGroup.congr_mk' _ _ _ _ c
  have hsub : (K.subgroupOf C).map ψ.toMonoidHom =
      (K.map (MulAut.conj g).toMonoidHom).subgroupOf C' := by
    ext c
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b, hb, rfl⟩
    · rintro ⟨k, hk, hkc⟩
      refine ⟨ψ.symm c, ?_, ψ.apply_symm_apply c⟩
      have hval : ((ψ.symm c : C) : G) = k := by
        apply (MulAut.conj g).injective
        have := congrArg Subtype.val (ψ.apply_symm_apply c)
        rw [← hkc] at this
        exact this
      rw [hval]
      exact hk
  unfold ComponentCovered
  change CFSG.layer (C' ⧸ CFSG.oddCore C') ≤
    ((K.map (MulAut.conj g).toMonoidHom).subgroupOf C').map (QuotientGroup.mk' (CFSG.oddCore C'))
  rw [← layer_map_mulEquiv Ψ, ← hsub, Subgroup.map_map]
  have hcomm : (QuotientGroup.mk' (CFSG.oddCore C')).comp ψ.toMonoidHom =
      Ψ.toMonoidHom.comp (QuotientGroup.mk' (CFSG.oddCore C)) := by
    ext c
    exact (hΨ c).symm
  rw [hcomm, ← Subgroup.map_map]
  exact Subgroup.map_mono h

@[expose] def CentralModOddCore (K : Subgroup G) (u : G) : Prop :=
  ∀ k ∈ K, u * k * u⁻¹ * k⁻¹ ∈ (CFSG.oddCore K).map K.subtype

theorem centralModOddCore_of_mem_center {K : Subgroup G} {u : G} (hu : u ∈ K)
    (h : QuotientGroup.mk' (CFSG.oddCore K) ⟨u, hu⟩ ∈ Subgroup.center (K ⧸ CFSG.oddCore K)) :
    CentralModOddCore K u := by
  intro k hk
  have hc := Subgroup.mem_center_iff.mp h (QuotientGroup.mk' (CFSG.oddCore K) ⟨k, hk⟩)
  refine ⟨⟨u, hu⟩ * ⟨k, hk⟩ * (⟨u, hu⟩ : K)⁻¹ * (⟨k, hk⟩ : K)⁻¹, ?_, rfl⟩
  apply (QuotientGroup.eq_one_iff (N := CFSG.oddCore K) _).mp
  change QuotientGroup.mk' (CFSG.oddCore K) (⟨u, hu⟩ * ⟨k, hk⟩ * (⟨u, hu⟩ : K)⁻¹ *
    (⟨k, hk⟩ : K)⁻¹) = 1
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hc]
  group

theorem CentralModOddCore.conj {K : Subgroup G} {u : G} (h : CentralModOddCore K u) (g : G) :
    CentralModOddCore (K.map (MulAut.conj g).toMonoidHom) (g * u * g⁻¹) := by
  intro k' hk'
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hk'
  obtain ⟨c, hcO, hcval⟩ := h k hk
  let E := K.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  have hcore : (CFSG.oddCore K).map E.toMonoidHom =
      CFSG.oddCore (K.map (MulAut.conj g).toMonoidHom) :=
    CFSG.ComponentClassification.OddCore.equiv_invariant E
  refine ⟨E c, hcore ▸ Subgroup.mem_map_of_mem _ hcO, ?_⟩
  change g * (c : G) * g⁻¹ = _
  simp only [Subgroup.subtype_apply] at hcval
  rw [hcval]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

theorem eq_of_orderOf_eq_two_of_isCyclic {A : Type*} [Group A] [Finite A] [IsCyclic A]
    {u v : A} (hu : orderOf u = 2) (hv : orderOf v = 2) : u = v := by
  classical
  let _ := Fintype.ofFinite A
  have hd : 2 ∣ Fintype.card A := by
    rw [← hu, ← Nat.card_eq_fintype_card]; exact orderOf_dvd_natCard u
  have hcard := IsCyclic.card_orderOf_eq_totient hd
  rw [Nat.totient_two] at hcard
  have hmu : u ∈ Finset.univ.filter (fun a : A => orderOf a = 2) := by simp [hu]
  have hmv : v ∈ Finset.univ.filter (fun a : A => orderOf a = 2) := by simp [hv]
  exact Finset.card_le_one.mp hcard.le u hmu v hmv

theorem map_conj_eq_self_of_mem {K : Subgroup G} {k : G} (hk : k ∈ K) :
    K.map (MulAut.conj k).toMonoidHom = K := by
  ext b
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact K.mul_mem (K.mul_mem hk ha) (K.inv_mem hk)
  · intro hb
    exact ⟨k⁻¹ * b * k, K.mul_mem (K.mul_mem (K.inv_mem hk) hb) hk, by group⟩

theorem CentralModOddCore.conj_mem {K : Subgroup G} {u : G} (h : CentralModOddCore K u)
    {k : G} (hk : k ∈ K) : CentralModOddCore K (k * u * k⁻¹) := by
  have := h.conj k
  rwa [map_conj_eq_self_of_mem hk] at this

theorem isPGroup_two_sup_zpowers {A : Type*} [Group A] {a b : A} (ha : orderOf a = 2)
    (hb : orderOf b = 2) (hab : a * b = b * a) :
    IsPGroup 2 (Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup A) := by
  have hpa : IsPGroup 2 (Subgroup.zpowers a) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, ha, pow_one])
  have hpb : IsPGroup 2 (Subgroup.zpowers b) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hb, pow_one])
  refine IsPGroup.to_sup_of_normal_right' hpa hpb ?_
  rw [Subgroup.zpowers_le]
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · intro hc
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    have : a * b ^ j * a⁻¹ = b ^ j := by
      rw [(Commute.zpow_right hab j).eq, mul_inv_cancel_right]
    rw [this]
    exact Subgroup.zpow_mem_zpowers b j
  · intro hc
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hc
    have : c = a⁻¹ * b ^ j * a := by rw [hj]; group
    rw [this]
    have hc' : a⁻¹ * b ^ j * a = b ^ j := by
      rw [mul_assoc, ← (Commute.zpow_right hab j).eq, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [hc']
    exact Subgroup.zpow_mem_zpowers b j

section Main

variable [Finite G] [IsSimpleGroup G]

open CFSG.Assembly.LowTwoRank FullSylowCoveringObstruction SmallerRecognitionOriginalField
  OriginalCoveringLocalFamily

theorem oddCore_eq_bot_of_two_commuting_covers
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hlocal : StatedClassicalModel (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (hrec : SmallerWreathedRecognition G)
    (y : G) (hy : orderOf y = 2) (hyx : y ≠ wreathModelHom S e (Original.x (2 ^ n)))
    (hcomm : y * wreathModelHom S e (Original.x (2 ^ n)) =
      wreathModelHom S e (Original.x (2 ^ n)) * y)
    (K : Subgroup G) (hproper : K < ⊤)
    (hxK : wreathModelHom S e (Original.x (2 ^ n)) ∈ K) (hyK : y ∈ K)
    (hcover : ComponentCovered (wreathModelHom S e (Original.x (2 ^ n))) K)
    (hcovery : ComponentCovered y K) : CFSG.oddCore K = ⊥ := by
  set x := wreathModelHom S e (Original.x (2 ^ n)) with hxdef
  have hx2 : orderOf x = 2 := CFSG.Wreathed.CompatibleFamilies.orderOf_x S e hn
  by_contra hO
  have hfacx :=
    smaller_recognition_factors_every_involution_containing_component_covering_subgroup hnonab n
      hn S e hfour p f hp hpodd hf hq hlocal hrec K hproper hxK hcover hO
  have hxc : CentralModOddCore K x := centralModOddCore_of_mem_center hxK hfacx.2.1
  obtain ⟨g, hg⟩ := isConj_iff.mp
    ((CFSG.Wreathed.simple_wreathed_one_involution_class_and_local_S3 hnonab n hn S e).2.2.1
      x y hx2 hy)
  have hgx : g⁻¹ * y * g⁻¹⁻¹ = x := by rw [← hg]; group
  set K' := K.map (MulAut.conj g⁻¹).toMonoidHom with hK'def
  have hcov' : ComponentCovered x K' := hgx ▸ hcovery.conj g⁻¹
  have hxK' : x ∈ K' := ⟨y, hyK, by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; exact hgx⟩
  have hK' : K' < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => ?_
    apply (lt_top_iff_ne_top.mp hproper)
    have := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) htop
    rw [hK'def, Subgroup.map_map, Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective]
      at this
    rw [← this]
    convert (Subgroup.map_id K).symm
    ext b
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulAut.conj_apply, inv_inv, MonoidHom.id_apply]
    group
  have hO' : CFSG.oddCore K' ≠ ⊥ := by
    intro h
    apply hO
    let E := K.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective
    have hcore : (CFSG.oddCore K).map E.toMonoidHom = CFSG.oddCore K' :=
      CFSG.ComponentClassification.OddCore.equiv_invariant E
    rw [h, Subgroup.map_eq_bot_iff_of_injective _ E.injective] at hcore
    exact hcore
  have hfac' :=
    smaller_recognition_factors_every_involution_containing_component_covering_subgroup hnonab n
      hn S e hfour p f hp hpodd hf hq hlocal hrec K' hK' hxK' hcov' hO'
  have hxc' : CentralModOddCore K' x := centralModOddCore_of_mem_center hxK' hfac'.2.1
  have hyc : CentralModOddCore K y := by
    have h1 := hxc'.conj g
    have hKK : K'.map (MulAut.conj g).toMonoidHom = K := by
      rw [hK'def, Subgroup.map_map]
      convert Subgroup.map_id K
      ext b
      simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
        MulAut.conj_apply, inv_inv, MonoidHom.id_apply]
      group
    rw [hKK, hg] at h1
    exact h1
  let Q : Sylow 2 (originalComponentPreimage n S e K) := Classical.choice inferInstance
  obtain ⟨P, hxP, g₀, hPS, -, -, -, hinj, hY, -, -⟩ :=
    original_component_covering_quaternion_sylow_position hnonab n hn S e hfour K hxK hcover Q
  set i := positionedSylowEmbedding S e K P g₀ hPS with hidef
  have hstr := CFSG.Wreathed.wreath_center_involution_and_quaternion_coordinates n hn
  have hnab : ∃ u v : i.range, u * v ≠ v * u := by
    obtain ⟨u, v, huv⟩ := CFSG.Wreathed.originalY_is_nonabelian n hn
    exact ⟨⟨u, hY u.2⟩, ⟨v, hY v.2⟩, fun h => huv (Subtype.ext (by
      simpa using congrArg Subtype.val h))⟩
  have hcent := (hstr.nonabelian_centralizers i.range hnab).1
  let xK : K := ⟨x, hxK⟩
  let yK : K := ⟨y, hyK⟩
  have hxK2 : orderOf xK = 2 := by rw [← Subgroup.orderOf_coe]; exact hx2
  have hyK2 : orderOf yK = 2 := by rw [← Subgroup.orderOf_coe]; exact hy
  have hcommK : xK * yK = yK * xK := Subtype.ext hcomm.symm
  obtain ⟨P', hTP'⟩ := (isPGroup_two_sup_zpowers hxK2 hyK2 hcommK).exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K P' P
  have hconjP : ∀ a : K, a ∈ (P' : Subgroup K) → k * a * k⁻¹ ∈ (P : Subgroup K) := by
    intro a ha
    rw [← hk, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul a (MulAut.conj k) (P' : Subgroup K) ha
  have hxP' : k * xK * k⁻¹ ∈ (P : Subgroup K) :=
    hconjP xK (hTP' (Subgroup.mem_sup_left (Subgroup.mem_zpowers xK)))
  have hyP' : k * yK * k⁻¹ ∈ (P : Subgroup K) :=
    hconjP yK (hTP' (Subgroup.mem_sup_right (Subgroup.mem_zpowers yK)))
  have hdisj : (P : Subgroup K) ⊓ CFSG.oddCore K = ⊥ := by
    apply disjoint_iff.mp
    apply Subgroup.disjoint_of_coprime_natCard
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp P.isPGroup'
    rw [hm]
    exact Nat.Coprime.pow_left m
      (Nat.coprime_two_left.mpr (CFSG.ComponentClassification.OddCore.odd_card K))
  have hcentP : ∀ a : K, CentralModOddCore K (a : G) → a ∈ (P : Subgroup K) →
      ∀ w : K, w ∈ (P : Subgroup K) → a * w = w * a := by
    intro a hca haP w hwP
    obtain ⟨c, hcO, hcval⟩ := hca (w : G) w.property
    have hceq : c = a * w * a⁻¹ * w⁻¹ := Subtype.ext (by simpa using hcval)
    have hcP : c ∈ (P : Subgroup K) := by
      rw [hceq]
      exact (P : Subgroup K).mul_mem ((P : Subgroup K).mul_mem ((P : Subgroup K).mul_mem haP hwP)
        ((P : Subgroup K).inv_mem haP)) ((P : Subgroup K).inv_mem hwP)
    have hc1 : c = 1 := by
      have hmem : c ∈ (P : Subgroup K) ⊓ CFSG.oddCore K := ⟨hcP, hcO⟩
      rw [hdisj] at hmem
      exact hmem
    have h1 : a * w * a⁻¹ * w⁻¹ = 1 := hceq ▸ hc1
    calc a * w = a * w * a⁻¹ * w⁻¹ * (w * a) := by group
      _ = w * a := by rw [h1, one_mul]
  have hxc₁ : CentralModOddCore K ((k : G) * x * (k : G)⁻¹) := hxc.conj_mem k.property
  have hyc₁ : CentralModOddCore K ((k : G) * y * (k : G)⁻¹) := hyc.conj_mem k.property
  let pu : P := ⟨k * xK * k⁻¹, hxP'⟩
  let pv : P := ⟨k * yK * k⁻¹, hyP'⟩
  have himage : ∀ pw : P, CentralModOddCore K (((pw : K) : G)) →
      i pw ∈ Original.Z (2 ^ n) := by
    intro pw hpw
    rw [← hcent]
    rw [Subgroup.mem_centralizer_iff]
    rintro h ⟨a, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcentP (pw : K) hpw pw.property (a : K) a.property).symm
  have hu := himage pu (by simpa [pu, xK] using hxc₁)
  have hv := himage pv (by simpa [pv, yK] using hyc₁)
  have hconjord : ∀ a : K, orderOf (k * a * k⁻¹) = orderOf a := fun a =>
    orderOf_injective (MulAut.conj k).toMonoidHom (MulAut.conj k).injective a
  have hpu2 : orderOf (⟨i pu, hu⟩ : Original.Z (2 ^ n)) = 2 := by
    rw [Subgroup.orderOf_mk, orderOf_injective i hinj pu, ← Subgroup.orderOf_coe pu]
    change orderOf (k * xK * k⁻¹) = 2
    rw [hconjord, hxK2]
  have hpv2 : orderOf (⟨i pv, hv⟩ : Original.Z (2 ^ n)) = 2 := by
    rw [Subgroup.orderOf_mk, orderOf_injective i hinj pv, ← Subgroup.orderOf_coe pv]
    change orderOf (k * yK * k⁻¹) = 2
    rw [hconjord, hyK2]
  have hZcyc : IsCyclic (Original.Z (2 ^ n)) := by
    unfold Original.Z
    infer_instance
  have heq := eq_of_orderOf_eq_two_of_isCyclic hpu2 hpv2
  have hpuv : pu = pv := hinj (congrArg Subtype.val heq)
  have hxy : xK = yK := by
    have h1 : (k * xK * k⁻¹ : K) = k * yK * k⁻¹ := congrArg Subtype.val hpuv
    simpa using h1
  exact hyx (congrArg Subtype.val hxy).symm

theorem two_commuting_involution_component_covers_force_trivial_proper_subgroup_odd_core
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hlocal : StatedClassicalModel (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (hrec : SmallerWreathedRecognition G)
    (y : G) (hy : orderOf y = 2) (hyx : y ≠ wreathModelHom S e (Original.x (2 ^ n)))
    (hcomm : y * wreathModelHom S e (Original.x (2 ^ n)) =
      wreathModelHom S e (Original.x (2 ^ n)) * y)
    (K : Subgroup G) (hproper : K < ⊤)
    (hxK : wreathModelHom S e (Original.x (2 ^ n)) ∈ K) (hyK : y ∈ K)
    (hcover : CFSG.layer (centralizerOddCoreQuotient n S e) ≤
      ComponentCoveringLocal.originalImage n S e K)
    (hcovery : ComponentCovered y K) :
    CFSG.oddCore K = ⊥ ∧
      ∀ W : Subgroup G, W ≤ K → (W.subgroupOf K).Normal → Odd (Nat.card W) → W = ⊥ := by
  have hcore := oddCore_eq_bot_of_two_commuting_covers hnonab n hn S e hfour p f hp hpodd hf hq
    hlocal hrec y hy hyx hcomm K hproper hxK hyK hcover hcovery
  refine ⟨hcore, fun W hWK hWn hWodd => ?_⟩
  have hle : W.subgroupOf K ≤ CFSG.oddCore K := by
    apply le_sSup
    refine ⟨hWn, ?_⟩
    rw [CFSG.natCard_subgroupOf_eq _ _ hWK]
    exact hWodd
  rw [hcore, le_bot_iff] at hle
  rw [eq_bot_iff]
  intro w hw
  have hwK : (⟨w, hWK hw⟩ : K) ∈ W.subgroupOf K := hw
  rw [hle, Subgroup.mem_bot] at hwK
  exact (Subgroup.mem_bot).mpr (congrArg Subtype.val hwK)

end Main

end CFSG.Wreathed.ComponentCoverFactorizations
