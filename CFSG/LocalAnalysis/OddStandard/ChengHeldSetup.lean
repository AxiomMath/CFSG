module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldDefs
public import CFSG.LocalAnalysis.ComponentInitial.StandardBasics
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.OddStandard.ChengHeld

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

theorem eq_of_orderOf_two_of_isCyclic {X : Subgroup G} (hX : IsCyclic X) {a b : G}
    (ha : a ∈ X) (hb : b ∈ X) (ha2 : orderOf a = 2) (hb2 : orderOf b = 2) : a = b := by
  have := Fintype.ofFinite X
  have hx : orderOf (⟨a, ha⟩ : X) = 2 := by rwa [Subgroup.orderOf_mk]
  have hy : orderOf (⟨b, hb⟩ : X) = 2 := by rwa [Subgroup.orderOf_mk]
  have h := IsCyclic.card_orderOf_eq_totient (hx ▸ orderOf_dvd_card : 2 ∣ Fintype.card X)
  rw [Nat.totient_two] at h
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp h
  have hxa : (⟨a, ha⟩ : X) ∈ ({c} : Finset X) :=
    hc ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
  have hya : (⟨b, hb⟩ : X) ∈ ({c} : Finset X) :=
    hc ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩
  rw [Finset.mem_singleton] at hxa hya
  exact congrArg Subtype.val (hxa.trans hya.symm)

omit [Finite G] in
theorem mul_mul_inv_mem_centralizer {m c : G} (hm : m ∈ normalizer (A : Set G))
    (hc : c ∈ centralizer (A : Set G)) : m * c * m⁻¹ ∈ centralizer (A : Set G) := by
  rw [mem_centralizer_iff] at hc ⊢
  intro l hl
  have hl' : m⁻¹ * l * m⁻¹⁻¹ ∈ A := (mem_normalizer_iff.mp (inv_mem hm) l).mp hl
  rw [inv_inv] at hl'
  have h1 := hc _ hl'
  calc l * (m * c * m⁻¹) = m * ((m⁻¹ * l * m) * c) * m⁻¹ := by group
    _ = m * (c * (m⁻¹ * l * m)) * m⁻¹ := by rw [h1]
    _ = m * c * m⁻¹ * l := by group

omit [Finite G] in
theorem isPGroup_two_sup_zpowers {u v : G} (huv : u * v = v * u) (hu2 : orderOf u = 2)
    (hv2 : orderOf v = 2) : IsPGroup 2 (zpowers u ⊔ zpowers v : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpu : IsPGroup 2 (zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu2, pow_one])
  have hpv : IsPGroup 2 (zpowers v) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hv2, pow_one])
  have hle : zpowers u ≤ centralizer (zpowers v : Set G) := by
    rw [zpowers_le, mem_centralizer_iff]
    rintro x ⟨k, rfl⟩
    exact (((Commute.zpow_right (show Commute u v from huv) k)).eq).symm
  exact hpu.to_sup_of_normal_right' hpv (hle.trans (centralizer_le_normalizer _))

omit [Finite G] in
theorem exists_mul_of_mem_sup_of_le_centralizer {H K : Subgroup G}
    (hHK : H ≤ centralizer (K : Set G)) {x : G} (hx : x ∈ H ⊔ K) :
    ∃ a ∈ H, ∃ b ∈ K, x = a * b := by
  have := Subgroup.coe_mul_of_left_le_normalizer_right H K
    (hHK.trans (centralizer_le_normalizer _))
  have hx' : x ∈ ((H : Set G) * (K : Set G)) := by
    rw [← this]
    exact hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  exact ⟨a, ha, b, hb, rfl⟩

theorem exists_sylow_of_isSylowOf_top {X : Subgroup G} (h : IsSylowOf 2 X (⊤ : Subgroup G)) :
    ∃ S : Sylow 2 G, (S : Subgroup G) = X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hp, hdvd⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp h
  rw [Subgroup.relIndex_top_right] at hdvd
  exact ⟨hp.toSylow hdvd, rfl⟩

theorem isSylowOf_top_of_sylow (S : Sylow 2 G) :
    IsSylowOf 2 (S : Subgroup G) (⊤ : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨le_top, S.isPGroup', ?_⟩
  rw [Subgroup.relIndex_top_right]
  exact S.not_dvd_index

omit [Finite G] in
theorem exists_isSylowOf_of_le {K Y : Subgroup G} (hY : IsPGroup 2 Y) (hYK : Y ≤ K) :
    ∃ P : Subgroup G, IsSylowOf 2 P K ∧ Y ≤ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := (hY.comap_subtype (K := K)).exists_le_sylow
  exact ⟨(Q : Subgroup K).map K.subtype, ⟨Q, rfl⟩,
    fun y hy => ⟨⟨y, hYK hy⟩, hQ (mem_subgroupOf.mpr hy), rfl⟩⟩

theorem exists_mem_normalizer_of_lt {X T : Subgroup G} (hT : IsPGroup 2 T) (hXT : X ≤ T)
    (hne : X ≠ T) : ∃ g ∈ T, g ∈ normalizer (X : Set G) ∧ g ∉ X := by
  have hI : X.subgroupOf T < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => hne (le_antisymm hXT fun x hx => ?_)
    have hx' : (⟨x, hx⟩ : T) ∈ X.subgroupOf T := by
      rw [htop]
      trivial
    exact mem_subgroupOf.mp hx'
  have : Group.IsNilpotent T := hT.isNilpotent
  have hnc : NormalizerCondition T := Group.normalizerCondition_of_isNilpotent (G := T)
  obtain ⟨x, hxN, hxnot⟩ := IsConcreteLE.exists_of_lt (hnc _ hI)
  have hgN : (x : G) ∈ normalizer (X : Set G) := by
    have hxsub : x ∈ (normalizer (X : Set G)).subgroupOf T := by
      rw [subgroupOf_normalizer_eq hXT]
      exact hxN
    exact mem_subgroupOf.mp hxsub
  exact ⟨x, x.2, hgN, fun hx => hxnot (mem_subgroupOf.mpr hx)⟩

theorem isSylowOf_top_of_normalizer {X : Subgroup G}
    (hX : IsSylowOf 2 X (normalizer (X : Set G))) : IsSylowOf 2 X (⊤ : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hXT⟩ := hX.isPGroup.exists_le_sylow
  by_cases hne : X = (T : Subgroup G)
  · rw [hne]
    exact isSylowOf_top_of_sylow T
  · obtain ⟨g, hgT, hgN, hgX⟩ := exists_mem_normalizer_of_lt T.isPGroup' hXT hne
    have heq := hX.eq_of_le (le_inf hXT le_normalizer) inf_le_right
      (T.isPGroup'.to_inf_left (K := normalizer (X : Set G)))
    exact absurd (heq ▸ (mem_inf.mpr ⟨hgT, hgN⟩) : g ∈ X) hgX

theorem isSylowOf_map {K H : Type*} [Group K] [Finite K] [Group H] {P L : Subgroup K}
    (h : IsSylowOf 2 P L) (f : K →* H) : IsSylowOf 2 (P.map f) (L.map f) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, rfl⟩ := h
  refine ⟨Q.mapSurjective (f.subgroupMap_surjective L), ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem fuse_of_weaklyClosed_of_centralizes {P E : Subgroup G}
    (hP : IsSylowOf 2 P (⊤ : Subgroup G)) (hE : E ≤ P)
    (hwc : ∀ g : G, E.map (MulAut.conj g).toMonoidHom ≤ P →
      E.map (MulAut.conj g).toMonoidHom = E)
    {x y : G} (hx : x ∈ centralizer (E : Set G)) (hy : y ∈ centralizer (E : Set G))
    (hxy : IsConj x y) : ∃ n ∈ normalizer (E : Set G), n⁻¹ * x * n = y := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hxy
  have hED : E ≤ centralizer ({y} : Set G) := fun e he => by
    rw [mem_centralizer_singleton_iff]
    exact mem_centralizer_iff.mp hy e he
  have hE₁D : E.map (MulAut.conj c).toMonoidHom ≤ centralizer ({y} : Set G) := by
    rintro _ ⟨e, he, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have h1 : e * x = x * e := mem_centralizer_iff.mp hx e he
    show c * e * c⁻¹ * y = y * (c * e * c⁻¹)
    rw [← hc]
    calc c * e * c⁻¹ * (c * x * c⁻¹) = c * (e * x) * c⁻¹ := by group
      _ = c * (x * e) * c⁻¹ := by rw [h1]
      _ = c * x * c⁻¹ * (c * e * c⁻¹) := by group
  have hEp : IsPGroup 2 E := hP.isPGroup.to_le hE
  obtain ⟨T₁, hT₁, hET₁⟩ := exists_isSylowOf_of_le hEp hED
  obtain ⟨T₂, hT₂, hE₁T₂⟩ := exists_isSylowOf_of_le (hEp.map (MulAut.conj c).toMonoidHom) hE₁D
  obtain ⟨k, hkD, hk⟩ := hT₁.exists_mem_conj hT₂
  obtain ⟨T, hT₁T⟩ := hT₁.isPGroup.exists_le_sylow
  obtain ⟨k', -, hk'⟩ := hP.exists_mem_conj (isSylowOf_top_of_sylow T)
  have hTP : ∀ z ∈ T₁, k'⁻¹ * z * k' ∈ P := fun z hz => (hk' z).mp (hT₁T hz)
  have h1 : k' ∈ normalizer (E : Set G) := by
    have := hwc k'⁻¹ (by
      rintro _ ⟨e, he, rfl⟩
      have h3 := hTP e (hET₁ he)
      simpa [MulAut.conj_apply] using h3)
    have h2 := (mem_normalizer_iff_map_conj_eq).mpr this
    simpa using inv_mem h2
  have h2 : k'⁻¹ * (k⁻¹ * c) ∈ normalizer (E : Set G) := by
    have := hwc (k'⁻¹ * (k⁻¹ * c)) (by
      rintro _ ⟨e, he, rfl⟩
      have h3 : c * e * c⁻¹ ∈ T₂ := hE₁T₂ ⟨e, he, rfl⟩
      have h4 := hTP _ ((hk _).mp h3)
      have e1 : (MulAut.conj (k'⁻¹ * (k⁻¹ * c))) e =
          k'⁻¹ * (k⁻¹ * (c * e * c⁻¹) * k) * k' := by
        simp only [MulAut.conj_apply]
        group
      show (MulAut.conj (k'⁻¹ * (k⁻¹ * c))) e ∈ P
      rw [e1]
      exact h4)
    exact (mem_normalizer_iff_map_conj_eq).mpr this
  have h5 : k⁻¹ * c ∈ normalizer (E : Set G) := by
    have := mul_mem h1 h2
    simpa using this
  refine ⟨(k⁻¹ * c)⁻¹, inv_mem h5, ?_⟩
  have hky : k * y = y * k := mem_centralizer_singleton_iff.mp hkD
  calc (k⁻¹ * c)⁻¹⁻¹ * x * (k⁻¹ * c)⁻¹ = k⁻¹ * (c * x * c⁻¹) * k := by group
    _ = k⁻¹ * y * k := by rw [hc]
    _ = y := by
      calc k⁻¹ * y * k = k⁻¹ * (y * k) := by group
        _ = k⁻¹ * (k * y) := by rw [hky]
        _ = y := by group

theorem fuse_of_weaklyClosed {P E : Subgroup G}
    (hP : IsSylowOf 2 P (⊤ : Subgroup G)) (hE : E ≤ P)
    (hwc : ∀ g : G, E.map (MulAut.conj g).toMonoidHom ≤ P →
      E.map (MulAut.conj g).toMonoidHom = E)
    {x y : G} (hx : x ∈ E ∧ x ∈ centralizer (E : Set G))
    (hy : y ∈ E ∧ y ∈ centralizer (E : Set G)) (hxy : IsConj x y) :
    ∃ n ∈ normalizer (E : Set G), n⁻¹ * x * n = y :=
  fuse_of_weaklyClosed_of_centralizes hP hE hwc hx.2 hy.2 hxy

theorem Hyp.isCyclic_of_isPGroup (h : Hyp G A) {T : Subgroup G}
    (hT : T ≤ centralizer (A : Set G)) (h2 : IsPGroup 2 T) : IsCyclic T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2' : IsPGroup 2 (T.subgroupOf (centralizer (A : Set G))) := h2.comap_subtype
  obtain ⟨R, hR⟩ := h2'.exists_le_sylow
  have hc := h.cyclic R
  have hc' : IsCyclic ((T.subgroupOf (centralizer (A : Set G))).subgroupOf
      (R : Subgroup (centralizer (A : Set G)))) := inferInstance
  have e1 := Subgroup.subgroupOfEquivOfLe hR
  have hc2 : IsCyclic (T.subgroupOf (centralizer (A : Set G))) :=
    isCyclic_of_surjective e1.toMonoidHom e1.surjective
  have e2 := Subgroup.subgroupOfEquivOfLe hT
  exact isCyclic_of_surjective e2.toMonoidHom e2.surjective

theorem Hyp.eq_of_involutions (h : Hyp G A) {u v : G} (hu : u ∈ centralizer (A : Set G))
    (hv : v ∈ centralizer (A : Set G)) (huv : u * v = v * u) (hu2 : orderOf u = 2)
    (hv2 : orderOf v = 2) : u = v := by
  have hp := isPGroup_two_sup_zpowers huv hu2 hv2
  have hC : (zpowers u ⊔ zpowers v : Subgroup G) ≤ centralizer (A : Set G) :=
    sup_le (zpowers_le.mpr hu) (zpowers_le.mpr hv)
  exact eq_of_orderOf_two_of_isCyclic (h.isCyclic_of_isPGroup hC hp)
    (mem_sup_left (mem_zpowers u)) (mem_sup_right (mem_zpowers v)) hu2 hv2

theorem Hyp.of_one_cyclic {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (hS : StandardSetting G A) (h34 : LieModel (A ⧸ center A) .PSL 3 2 2)
    (hev : Even (Nat.card (center A))) (R : Sylow 2 (centralizer (A : Set G)))
    (hc : IsCyclic (R : Subgroup (centralizer (A : Set G)))) : Hyp G A :=
  ⟨hS, h34, hev, fun S' => ((Sylow.equiv R S').isCyclic).1 hc⟩

theorem Hyp.exists_datum (h : Hyp G A) : Nonempty (Datum A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center A) 2
    (even_iff_two_dvd.mp h.even)
  obtain ⟨X, hX⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 (normalizer (A : Set G))
  refine ⟨⟨((z : A) : G), (z : A).2, ?_, ?_, X, hX⟩⟩
  · rw [mem_centralizer_iff]
    intro a ha
    exact congrArg Subtype.val ((mem_center_iff.mp z.2) ⟨a, ha⟩)
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hz

namespace Datum

variable (d : Datum A)

theorem centralizer_q (h : Hyp G A) :
    centralizer ({d.q} : Set G) = normalizer (A : Set G) := by
  refine le_antisymm
    (CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality
      h.setting.standard d.q_cent d.q_ord).1 fun m hm => ?_
  have hq' : m * d.q * m⁻¹ ∈ centralizer (A : Set G) := mul_mul_inv_mem_centralizer hm d.q_cent
  have hcomm : d.q * (m * d.q * m⁻¹) = (m * d.q * m⁻¹) * d.q :=
    mem_centralizer_iff.mp hq' d.q d.q_mem
  have hord : orderOf (m * d.q * m⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, d.q_ord]
  have heq := h.eq_of_involutions d.q_cent hq' hcomm d.q_ord hord
  rw [mem_centralizer_singleton_iff]
  calc m * d.q = (m * d.q * m⁻¹) * m := by group
    _ = d.q * m := by rw [← heq]

theorem q_mem_X (h : Hyp G A) : d.q ∈ d.X ∧ d.X ≤ centralizer ({d.q} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcq := d.centralizer_q h
  have hXN : d.X ≤ normalizer (A : Set G) := d.X_sylow.le
  rw [← hcq] at hXN
  refine ⟨?_, hXN⟩
  obtain ⟨Q, hQ⟩ := d.X_sylow
  let n0 : normalizer (A : Set G) := ⟨d.q, le_normalizer d.q_mem⟩
  have hn0 : n0 ∈ center (normalizer (A : Set G)) := by
    rw [mem_center_iff]
    intro y
    apply Subtype.ext
    have hy : (y : G) ∈ centralizer ({d.q} : Set G) := by rw [hcq]; exact y.2
    exact mem_centralizer_singleton_iff.mp hy
  have hpg : IsPGroup 2 (zpowers n0) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    have h1 : orderOf n0 = orderOf d.q := by
      rw [← Subgroup.orderOf_coe]
    rw [h1, d.q_ord]
  have : (zpowers n0).Normal := Subgroup.normal_of_le_center (zpowers_le.mpr hn0)
  have hle := hpg.le_sylow_of_normal Q (mem_zpowers n0)
  rw [← hQ]
  exact ⟨n0, hle, rfl⟩

theorem q_mem_S (h : Hyp G A) : d.q ∈ d.S := ⟨(d.q_mem_X h).1, d.q_mem⟩

theorem q_mem_Q (h : Hyp G A) : d.q ∈ d.Q := ⟨(d.q_mem_X h).1, d.q_cent⟩

theorem eq_q_of_mem_centralizer (h : Hyp G A) {z : G} (hz : z ∈ centralizer (A : Set G))
    (hz2 : orderOf z = 2) : z = d.q :=
  h.eq_of_involutions hz d.q_cent (mem_centralizer_iff.mp hz d.q d.q_mem).symm hz2 d.q_ord

theorem X_sylow_G (h : Hyp G A)
    (hfix : ∀ n ∈ normalizer (d.X : Set G), n⁻¹ * d.q * n = d.q) :
    IsSylowOf 2 d.X (⊤ : Subgroup G) := by
  refine isSylowOf_top_of_normalizer (d.X_sylow.of_le le_normalizer ?_)
  intro n hn
  rw [← d.centralizer_q h, mem_centralizer_singleton_iff]
  calc n * d.q = n * (n⁻¹ * d.q * n) := by rw [hfix n hn]
    _ = d.q * n := by group

theorem fixes_q_of_unique_central_involution (h : Hyp G A)
    (hu : ∀ z ∈ d.X, (∀ x ∈ d.X, x * z = z * x) → orderOf z = 2 → z = d.q) :
    ∀ n ∈ normalizer (d.X : Set G), n⁻¹ * d.q * n = d.q := by
  intro n hn
  obtain ⟨hqX, hXc⟩ := d.q_mem_X h
  have hqc : ∀ x ∈ d.X, x * d.q = d.q * x := fun x hx =>
    mem_centralizer_singleton_iff.mp (hXc hx)
  have hn' := mem_normalizer_iff''.mp hn
  have hn'' := mem_normalizer_iff.mp hn
  refine hu _ ((hn' d.q).mp hqX) (fun x hx => ?_) ?_
  · have hx' : n * x * n⁻¹ ∈ d.X := (hn'' x).mp hx
    have := hqc _ hx'
    calc x * (n⁻¹ * d.q * n) = n⁻¹ * ((n * x * n⁻¹) * d.q) * n := by group
      _ = n⁻¹ * (d.q * (n * x * n⁻¹)) * n := by rw [this]
      _ = n⁻¹ * d.q * n * x := by group
  · rw [show n⁻¹ * d.q * n = (MulAut.conj n⁻¹) d.q by simp, MulEquiv.orderOf_eq,
      d.q_ord]

theorem exists_conj_config (h : Hyp G A) {z : G} (hz : IsConj d.q z) :
    ∃ g : G, g⁻¹ * d.q * g = z ∧ ∀ x ∈ d.X, x * z = z * x → g * x * g⁻¹ ∈ d.X := by
  obtain ⟨c₀, hc₀⟩ := isConj_iff.mp hz
  have hqz : d.q = c₀⁻¹ * z * c₀ := by rw [← hc₀]; group
  have hcq := d.centralizer_q h
  set Y : Subgroup G := d.X ⊓ centralizer ({z} : Set G) with hY
  have hYp : IsPGroup 2 Y := d.X_sylow.isPGroup.to_inf_left
  have hY₁N : Y.map (MulAut.conj c₀⁻¹).toMonoidHom ≤ normalizer (A : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← hcq, mem_centralizer_singleton_iff]
    have hyz : y * z = z * y := mem_centralizer_singleton_iff.mp hy.2
    show c₀⁻¹ * y * c₀⁻¹⁻¹ * d.q = d.q * (c₀⁻¹ * y * c₀⁻¹⁻¹)
    rw [hqz]
    calc c₀⁻¹ * y * c₀⁻¹⁻¹ * (c₀⁻¹ * z * c₀) = c₀⁻¹ * (y * z) * c₀ := by group
      _ = c₀⁻¹ * (z * y) * c₀ := by rw [hyz]
      _ = c₀⁻¹ * z * c₀ * (c₀⁻¹ * y * c₀⁻¹⁻¹) := by group
  obtain ⟨X', hX', hYX'⟩ := exists_isSylowOf_of_le (hYp.map (MulAut.conj c₀⁻¹).toMonoidHom) hY₁N
  obtain ⟨k, hkN, hk⟩ := d.X_sylow.exists_mem_conj hX'
  have hkq : k * d.q = d.q * k := by
    have : k ∈ centralizer ({d.q} : Set G) := by rw [hcq]; exact hkN
    exact mem_centralizer_singleton_iff.mp this
  refine ⟨k⁻¹ * c₀⁻¹, ?_, fun x hx hxz => ?_⟩
  · calc (k⁻¹ * c₀⁻¹)⁻¹ * d.q * (k⁻¹ * c₀⁻¹) = c₀ * (k * d.q * k⁻¹) * c₀⁻¹ := by group
      _ = c₀ * d.q * c₀⁻¹ := by rw [hkq]; group
      _ = z := hc₀
  · have hxY : x ∈ Y := ⟨hx, mem_centralizer_singleton_iff.mpr hxz⟩
    have h1 : c₀⁻¹ * x * c₀⁻¹⁻¹ ∈ X' := hYX' ⟨x, hxY, rfl⟩
    have h2 := (hk _).mp h1
    have : k⁻¹ * (c₀⁻¹ * x * c₀⁻¹⁻¹) * k = k⁻¹ * c₀⁻¹ * x * (k⁻¹ * c₀⁻¹)⁻¹ := by group
    rw [this] at h2
    exact h2

end Datum

end CFSG.OddStandard.ChengHeld
