module

public import CFSG.ClassicalInvolution.Asc77.AscSteps182

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic
open scoped commutatorElement

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

omit [Fact p.Prime] in
theorem subgroupOf_map_subtype' {Y : Subgroup G} (L' : Subgroup Y) :
    (L'.map Y.subtype).subgroupOf Y = L' :=
  Subgroup.comap_map_eq_self_of_injective Y.subtype_injective L'

omit [Fact p.Prime] in
theorem inf_subgroupOf_eq (K J Y : Subgroup G) :
    K.subgroupOf Y ⊓ J.subgroupOf Y = (K ⊓ J).subgroupOf Y := by
  ext x
  simp [Subgroup.mem_subgroupOf]

theorem mem_restrictFamily_iff {Y : Subgroup G} {L' : Subgroup Y} :
    L' ∈ restrictFamily Ω Y ↔ L'.map Y.subtype ∈ Ω := by
  constructor
  · rintro ⟨L, hL, hLY, rfl⟩
    rwa [Subgroup.map_subgroupOf_eq_of_le hLY]
  · intro h
    exact ⟨L'.map Y.subtype, h, Subgroup.map_subtype_le L', (subgroupOf_map_subtype' L').symm⟩

theorem subgroupOf_mem_restrictFamily {Y K : Subgroup G} (hK : K ∈ Ω) (hKY : K ≤ Y) :
    K.subgroupOf Y ∈ restrictFamily Ω Y :=
  ⟨K, hK, hKY, rfl⟩

omit [Fact p.Prime] in
theorem isUniqueInvolution_subgroupOf {Y K : Subgroup G} {z : G} (h : IsUniqueInvolution K z)
    (hKY : K ≤ Y) : IsUniqueInvolution (K.subgroupOf Y) (⟨z, hKY h.mem⟩ : Y) where
  mem := Subgroup.mem_subgroupOf.mpr h.mem
  ne_one := fun h1 => h.ne_one (congrArg Subtype.val h1)
  sq := Subtype.ext h.sq
  unique := by
    intro y hy hy2
    rcases h.unique (y : G) (Subgroup.mem_subgroupOf.mp hy) (congrArg Subtype.val hy2) with h1 | h1
    · exact Or.inl (Subtype.ext h1)
    · exact Or.inr (Subtype.ext h1)

omit [Fact p.Prime] in
theorem isUniqueInvolution_of_subgroupOf {Y K : Subgroup G} {z : Y}
    (h : IsUniqueInvolution (K.subgroupOf Y) z) (hKY : K ≤ Y) : IsUniqueInvolution K (z : G) where
  mem := Subgroup.mem_subgroupOf.mp h.mem
  ne_one := fun h1 => h.ne_one (Subtype.ext h1)
  sq := congrArg Subtype.val h.sq
  unique := by
    intro y hy hy2
    rcases h.unique ⟨y, hKY hy⟩ (Subgroup.mem_subgroupOf.mpr hy) (Subtype.ext hy2) with h1 | h1
    · exact Or.inl (congrArg Subtype.val h1)
    · exact Or.inr (congrArg Subtype.val h1)

omit [Fact p.Prime] in
theorem isPGroup_zpowers_coe_iff [Finite G] {Y : Subgroup G} {v : Y} :
    IsPGroup 2 (Subgroup.zpowers (v : G)) ↔ IsPGroup 2 (Subgroup.zpowers v) := by
  have h : orderOf (v : G) = orderOf v := Subgroup.orderOf_coe v
  constructor
  · intro hv
    obtain ⟨n, hn⟩ := hv.exists_card_eq
    rw [Nat.card_zpowers, h] at hn
    exact IsPGroup.of_card (n := n) (by rw [Nat.card_zpowers, hn])
  · intro hv
    obtain ⟨n, hn⟩ := hv.exists_card_eq
    rw [Nat.card_zpowers] at hn
    exact IsPGroup.of_card (n := n) (by rw [Nat.card_zpowers, h, hn])

theorem mem_normalizer_subgroupOf_iff {Y K : Subgroup G} (hKY : K ≤ Y) {y : Y} :
    (y : G) ∈ Subgroup.normalizer (K : Set G) ↔
      y ∈ Subgroup.normalizer ((K.subgroupOf Y : Subgroup Y) : Set Y) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h x
    simpa [Subgroup.mem_subgroupOf] using h (x : G)
  · intro h x
    constructor
    · intro hx
      have := (h ⟨x, hKY hx⟩).mp (Subgroup.mem_subgroupOf.mpr hx)
      simpa [Subgroup.mem_subgroupOf] using this
    · intro hx
      have hxY : x ∈ Y := by
        have h1 : (y : G)⁻¹ * ((y : G) * x * (y : G)⁻¹) * (y : G) ∈ Y :=
          Y.mul_mem (Y.mul_mem (Y.inv_mem y.2) (hKY hx)) y.2
        simpa [mul_assoc] using h1
      have := (h ⟨x, hxY⟩).mpr (by simpa [Subgroup.mem_subgroupOf] using hx)
      simpa [Subgroup.mem_subgroupOf] using this

omit [Fact p.Prime] in
theorem isSylow2In_map_subtype_iff {Y : Subgroup G} {T' J' : Subgroup Y} :
    IsSylow2In (T'.map Y.subtype) (J'.map Y.subtype) ↔ IsSylow2In T' J' := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨(Subgroup.map_le_map_iff_of_injective Y.subtype_injective).mp h1, ?_, ?_⟩
    · have := h2.comap_of_injective Y.subtype Y.subtype_injective
      rwa [Subgroup.comap_map_eq_self_of_injective Y.subtype_injective] at this
    · intro V' hV'J hV'2 hle
      have h4 : V'.map Y.subtype = T'.map Y.subtype :=
        h3 _ (Subgroup.map_mono hV'J) (hV'2.map _) (Subgroup.map_mono hle)
      exact Subgroup.map_injective Y.subtype_injective h4
  · rintro ⟨h1, h2, h3⟩
    refine ⟨Subgroup.map_mono h1, h2.map _, ?_⟩
    intro V hVJ hV2 hle
    have hVY : V ≤ Y := hVJ.trans (Subgroup.map_subtype_le J')
    set V' : Subgroup Y := V.subgroupOf Y with hV'
    have hVV' : V'.map Y.subtype = V := Subgroup.map_subgroupOf_eq_of_le hVY
    have h4 : V' ≤ J' := by
      rw [← Subgroup.map_le_map_iff_of_injective Y.subtype_injective, hVV']
      exact hVJ
    have h5 : IsPGroup 2 V' := hV2.comap_subtype
    have h6 : T' ≤ V' := by
      rw [← Subgroup.map_le_map_iff_of_injective Y.subtype_injective, hVV']
      exact hle
    have h7 := h3 V' h4 h5 h6
    rw [← hVV', h7]

theorem IsSylow2In.subgroupOf {Y T J : Subgroup G} (h : IsSylow2In T J) (hJY : J ≤ Y) :
    IsSylow2In (T.subgroupOf Y) (J.subgroupOf Y) := by
  rw [← isSylow2In_map_subtype_iff, Subgroup.map_subgroupOf_eq_of_le (h.1.trans hJY),
    Subgroup.map_subgroupOf_eq_of_le hJY]
  exact h

theorem mem_RSet_restrict {Y J T : Subgroup G} (hJ : J ∈ Ω) (hJY : J ≤ Y) (h : IsSylow2In T J) :
    T.subgroupOf Y ∈ RSet (restrictFamily Ω Y) :=
  mem_RSet_of_isSylow2In (subgroupOf_mem_restrictFamily hJ hJY) (h.subgroupOf hJY)

theorem exists_isSylow2In_of_mem_RSet_restrict {Y : Subgroup G} {T' : Subgroup Y}
    (hT : T' ∈ RSet (restrictFamily Ω Y)) :
    ∃ J ∈ Ω, J ≤ Y ∧ IsSylow2In (T'.map Y.subtype) J := by
  obtain ⟨J', hJ', hT'J'⟩ := exists_isSylow2In_of_mem_RSet hT
  exact ⟨J'.map Y.subtype, mem_restrictFamily_iff.mp hJ', Subgroup.map_subtype_le J',
    isSylow2In_map_subtype_iff.mpr hT'J'⟩

theorem map_mem_RSet_restrict {Y : Subgroup G} {T' : Subgroup Y}
    (hT : T' ∈ RSet (restrictFamily Ω Y)) : T'.map Y.subtype ∈ RSet Ω := by
  obtain ⟨J, hJ, -, hTJ⟩ := exists_isSylow2In_of_mem_RSet_restrict hT
  exact mem_RSet_of_isSylow2In hJ hTJ

theorem map_mem_USet_restrict {Y : Subgroup G} {U' : Subgroup Y}
    (hU : U' ∈ USet (restrictFamily Ω Y)) : U'.map Y.subtype ∈ USet Ω := by
  obtain ⟨T', hT', hUT, hcyc, hidx⟩ := hU
  refine ⟨T'.map Y.subtype, map_mem_RSet_restrict hT', Subgroup.map_mono hUT, ?_, ?_⟩
  · exact (MulEquiv.isCyclic (Subgroup.equivMapOfInjective U' Y.subtype Y.subtype_injective)).mp
      hcyc
  · rw [Subgroup.relIndex_map_map_of_injective _ _ Y.subtype_injective]
    exact hidx

theorem HypOmegaMod.restrict [Finite G] (hΩ : HypOmegaMod p f Ω) (Y : Subgroup G) :
    HypOmegaMod p f (restrictFamily Ω Y) where
  conjInvariant := by
    rintro n _ ⟨L, hL, hLY, rfl⟩
    refine ⟨conjSub (n : G) L, hΩ.conjInvariant _ L hL, ?_, conjSub_subgroupOf Y n L⟩
    have := conjSub_mono (n := (n : G)) hLY
    rwa [conjSub_eq_self_of_mem n.2] at this
  classical := by
    rintro _ ⟨L, hL, hLY, rfl⟩
    obtain ⟨z, hz⟩ := hΩ.classical L hL
    exact ⟨_, hz.subgroupOf p f hLY⟩
  omega4 := by
    rintro _ ⟨K, hK, hKY, rfl⟩ _ ⟨J, hJ, hJY, rfl⟩ hne
    have hKJ : K ≠ J := fun h => hne (by rw [h])
    obtain ⟨h1, h2⟩ := hΩ.omega4 K hK J hJ hKJ
    have hcard : Nat.card ↥(K.subgroupOf Y ⊓ J.subgroupOf Y) = Nat.card ↥(K ⊓ J) := by
      rw [inf_subgroupOf_eq]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hKY)).toEquiv
    rw [hcard]
    refine ⟨h1, fun h => ?_⟩
    have hle := h2 h
    rw [oddCoreOf_subgroupOf hKY, oddCoreOf_subgroupOf hJY]
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    have hab : (⁅(a : G), (b : G)⁆) ∈ ⁅K, J⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp ha)
        (Subgroup.mem_subgroupOf.mp hb)
    exact ⟨Subgroup.mem_subgroupOf.mpr (hle hab).1, Subgroup.mem_subgroupOf.mpr (hle hab).2⟩
  omega5 := by
    rintro _ ⟨K, hK, hKY, rfl⟩ _ ⟨J, hJ, hJY, rfl⟩ hne z' hz' v hv hnc hv2 hvz
    have hKJ : K ≠ J := fun h => hne (by rw [h])
    have hzK : IsUniqueInvolution K (z' : G) := isUniqueInvolution_of_subgroupOf hz' hKY
    have hvJ : (v : G) ∈ J := Subgroup.mem_subgroupOf.mp hv
    have hnc' : ¬ ∀ w ∈ J, (v : G) * w = w * (v : G) := by
      intro h
      apply hnc
      rintro ⟨w, hw⟩ hw'
      exact Subtype.ext (h w (Subgroup.mem_subgroupOf.mp hw'))
    have hv2' : IsPGroup 2 (Subgroup.zpowers (v : G)) := isPGroup_zpowers_coe_iff.mpr hv2
    have hn := hΩ.omega5 K hK J hJ hKJ (z' : G) hzK (v : G) hvJ hnc' hv2' (congrArg Subtype.val hvz)
    exact (mem_normalizer_subgroupOf_iff hKY).mp hn

omit [Fact p.Prime] in
theorem subgroupOf_ne_of_ne {Y K J : Subgroup G} (hKY : K ≤ Y) (hJY : J ≤ Y) (h : J ≠ K) :
    J.subgroupOf Y ≠ K.subgroupOf Y := by
  intro h'
  apply h
  have := Subgroup.subgroupOf_inj.mp h'
  rwa [inf_eq_left.mpr hJY, inf_eq_left.mpr hKY] at this

theorem omegaStarNbr_of_restrict {Y K J : Subgroup G} (hKY : K ≤ Y) (hJY : J ≤ Y)
    (h : J.subgroupOf Y ∈ omegaStarNbr (restrictFamily Ω Y) (K.subgroupOf Y)) :
    J ∈ omegaStarNbr Ω K := by
  obtain ⟨hJ', hne, U', hU', hU'J, hU'N⟩ := h
  have hJ : J ∈ Ω := by
    have := mem_restrictFamily_iff.mp hJ'
    rwa [Subgroup.map_subgroupOf_eq_of_le hJY] at this
  refine ⟨hJ, fun h => hne (by rw [h]), U'.map Y.subtype, map_mem_USet_restrict hU', ?_, ?_⟩
  · calc U'.map Y.subtype ≤ (J.subgroupOf Y).map Y.subtype := Subgroup.map_mono hU'J
      _ = J := Subgroup.map_subgroupOf_eq_of_le hJY
  · rintro _ ⟨u, hu, rfl⟩
    exact (mem_normalizer_subgroupOf_iff hKY).mpr (hU'N hu)

theorem omegaNbr_of_restrict {Y K J : Subgroup G} (hKY : K ≤ Y) (hJY : J ≤ Y)
    (h : J.subgroupOf Y ∈ omegaNbr (restrictFamily Ω Y) (K.subgroupOf Y)) :
    J ∈ omegaNbr Ω K := by
  obtain ⟨hJ', hne, T', hT', hT'J, hT'N⟩ := h
  have hJ : J ∈ Ω := by
    have := mem_restrictFamily_iff.mp hJ'
    rwa [Subgroup.map_subgroupOf_eq_of_le hJY] at this
  refine ⟨hJ, fun h => hne (by rw [h]), T'.map Y.subtype, map_mem_RSet_restrict hT', ?_, ?_⟩
  · calc T'.map Y.subtype ≤ (J.subgroupOf Y).map Y.subtype := Subgroup.map_mono hT'J
      _ = J := Subgroup.map_subgroupOf_eq_of_le hJY
  · rintro _ ⟨u, hu, rfl⟩
    exact (mem_normalizer_subgroupOf_iff hKY).mpr (hT'N hu)

theorem E187C.omegaNbr_subgroupOf_of [Finite G]
    (hsyl : ∀ {J T : Subgroup G}, J ∈ Ω → T ∈ RSet Ω → T ≤ J → IsSylow2In T J)
    {Y K J : Subgroup G}
    (hKY : K ≤ Y) (hJY : J ≤ Y) (hJ : J ∈ Ω) (h : J ∈ omegaNbr Ω K) :
    J.subgroupOf Y ∈ omegaNbr (restrictFamily Ω Y) (K.subgroupOf Y) := by
  obtain ⟨-, hne, T, hT, hTJ, hTN⟩ := h
  have hTsyl : IsSylow2In T J := hsyl hJ hT hTJ
  refine ⟨subgroupOf_mem_restrictFamily hJ hJY, subgroupOf_ne_of_ne hKY hJY hne, T.subgroupOf Y,
    mem_RSet_restrict hJ hJY hTsyl, Subgroup.subgroupOf_mono Y hTJ, fun x hx => ?_⟩
  exact (mem_normalizer_subgroupOf_iff hKY).mp (hTN (Subgroup.mem_subgroupOf.mp hx))

theorem omegaNbr_subgroupOf [Finite G] (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) {Y K J : Subgroup G}
    (hKY : K ≤ Y) (hJY : J ≤ Y) (hJ : J ∈ Ω) (h : J ∈ omegaNbr Ω K) :
    J.subgroupOf Y ∈ omegaNbr (restrictFamily Ω Y) (K.subgroupOf Y) :=
  E187C.omegaNbr_subgroupOf_of (fun hJ hT hTJ => hΩ.isSylow2In_of_mem_RSet_of_le hp hJ hT hTJ) hKY
    hJY hJ h

theorem twinSet_subgroupOf {Y K J : Subgroup G} (hKY : K ≤ Y) (hJY : J ≤ Y)
    (h : J ∈ twinSet Ω K) : J.subgroupOf Y ∈ twinSet (restrictFamily Ω Y) (K.subgroupOf Y) := by
  obtain ⟨hJ, z, hzK, hzJ⟩ := h
  exact ⟨subgroupOf_mem_restrictFamily hJ hJY, ⟨z, hKY hzK.mem⟩,
    isUniqueInvolution_subgroupOf hzK hKY, isUniqueInvolution_subgroupOf hzJ hJY⟩

omit [Fact p.Prime] in
theorem map_closure_pair_subtype {Y : Subgroup G} (a b : Y) :
    (Subgroup.closure ({a, b} : Set Y)).map Y.subtype =
      Subgroup.closure ({(a : G), (b : G)} : Set G) := by
  rw [MonoidHom.map_closure, Set.image_pair]
  rfl

theorem E187C.AEmpty.restrict_of [Finite G]
    (hsyl : ∀ {J T : Subgroup G}, J ∈ Ω → T ∈ RSet Ω → T ≤ J → IsSylow2In T J)
    {Y K : Subgroup G}
    (hKY : K ≤ Y) (hA : AEmpty Ω K) : AEmpty (restrictFamily Ω Y) (K.subgroupOf Y) := by
  intro J' hJ'star hJ'nbr zK' zJ' hzK' hzJ'
  set J : Subgroup G := J'.map Y.subtype with hJdef
  have hJ'eq : J.subgroupOf Y = J' := subgroupOf_map_subtype' J'
  have hJY : J ≤ Y := Subgroup.map_subtype_le J'
  have hJ : J ∈ Ω := mem_restrictFamily_iff.mp hJ'star.1
  have hstar : J ∈ omegaStarNbr Ω K :=
    omegaStarNbr_of_restrict hKY hJY (by rwa [hJ'eq])
  have hnbr : J ∉ omegaNbr Ω K := fun h =>
    hJ'nbr (by rw [← hJ'eq]; exact E187C.omegaNbr_subgroupOf_of hsyl hKY hJY hJ h)
  have hzK : IsUniqueInvolution K (zK' : G) := isUniqueInvolution_of_subgroupOf hzK' hKY
  have hzJ : IsUniqueInvolution J (zJ' : G) :=
    isUniqueInvolution_of_subgroupOf (by rwa [hJ'eq]) hJY
  obtain ⟨g, hg, hgK⟩ := hA J hstar hnbr _ _ hzK hzJ
  set Z' : Subgroup Y := Subgroup.closure ({zK', zJ'} : Set Y) with hZ'
  have hZ : Z'.map Y.subtype = Subgroup.closure ({(zK' : G), (zJ' : G)} : Set G) :=
    map_closure_pair_subtype zK' zJ'
  have hZY : Subgroup.closure ({(zK' : G), (zJ' : G)} : Set G) ≤ Y := by
    rw [← hZ]; exact Subgroup.map_subtype_le _
  have hgY : g ∈ Y := by
    have : pairNormalizers K J (zK' : G) (zJ' : G) ≤ Y := by
      unfold pairNormalizers
      exact sup_le (inf_le_left.trans hKY) (inf_le_left.trans hJY)
    exact this hg
  have hN : ∀ {A : Subgroup G}, A ≤ Y →
      (A ⊓ Subgroup.normalizer ((Subgroup.closure ({(zK' : G), (zJ' : G)} : Set G) :
        Subgroup G) : Set G)).subgroupOf Y ≤
        A.subgroupOf Y ⊓ Subgroup.normalizer ((Z' : Subgroup Y) : Set Y) := by
    intro A hAY x hx
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hx
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mpr hx.1, ?_⟩
    have := (mem_normalizer_subgroupOf_iff hZY).mp hx.2
    rwa [← hZ, subgroupOf_map_subtype'] at this
  have hAY : K ⊓ Subgroup.normalizer ((Subgroup.closure ({(zK' : G), (zJ' : G)} : Set G) :
      Subgroup G) : Set G) ≤ Y := inf_le_left.trans hKY
  have hBY : J ⊓ Subgroup.normalizer ((Subgroup.closure ({(zK' : G), (zJ' : G)} : Set G) :
      Subgroup G) : Set G) ≤ Y := inf_le_left.trans hJY
  have hmem : (⟨g, hgY⟩ : Y) ∈ (pairNormalizers K J (zK' : G) (zJ' : G)).subgroupOf Y :=
    Subgroup.mem_subgroupOf.mpr hg
  have hmem' : (⟨g, hgY⟩ : Y) ∈ pairNormalizers (K.subgroupOf Y) J' zK' zJ' := by
    have h1 := hmem
    unfold pairNormalizers at h1
    rw [Subgroup.subgroupOf_sup hAY hBY] at h1
    have h2 := hN (A := K) hKY
    have h3 := hN (A := J) hJY
    rw [hJ'eq] at h3
    exact sup_le_sup h2 h3 h1
  refine ⟨⟨g, hgY⟩, hmem', ?_⟩
  rw [conjSub_subgroupOf Y ⟨g, hgY⟩ K]
  show (conjSub g K).subgroupOf Y = J'
  rw [hgK]
  exact hJ'eq

theorem AEmpty.restrict [Finite G] (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) {Y K : Subgroup G}
    (hKY : K ≤ Y) (hA : AEmpty Ω K) : AEmpty (restrictFamily Ω Y) (K.subgroupOf Y) :=
  E187C.AEmpty.restrict_of (fun hJ hT hTJ => hΩ.isSylow2In_of_mem_RSet_of_le hp hJ hT hTJ) hKY hA

end CFSG.ClassicalInvolution.Asc77
