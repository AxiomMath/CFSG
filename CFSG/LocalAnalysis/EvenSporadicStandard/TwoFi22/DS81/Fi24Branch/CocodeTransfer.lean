module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeXE

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup MulAction
open scoped commutatorElement

variable {G : Type} [Group G] {E : Subgroup G} {t : G}

@[expose] def preS (T : Subgroup (MulAut ↥E)) : Subgroup G :=
  (T.comap (S44.actN E)).map (normalizer (E : Set G)).subtype

theorem mem_preS {T : Subgroup (MulAut ↥E)} {x : G} :
    x ∈ preS T ↔ ∃ h : x ∈ normalizer (E : Set G), S44.actN E ⟨x, h⟩ ∈ T := by
  simp only [preS, Subgroup.mem_map, Subgroup.mem_comap]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨x, h⟩, hx, rfl⟩

theorem mem_preS_iff_of_mem {T : Subgroup (MulAut ↥E)} {x : G} (hx : x ∈ normalizer (E : Set G)) :
    x ∈ preS T ↔ S44.actN E ⟨x, hx⟩ ∈ T :=
  ⟨fun h => by obtain ⟨_, h'⟩ := mem_preS.1 h; exact h', fun h => mem_preS.2 ⟨hx, h⟩⟩

theorem preS_le_normalizer (T : Subgroup (MulAut ↥E)) : preS T ≤ normalizer (E : Set G) :=
  fun _ hx => (mem_preS.1 hx).1

theorem preS_le_Nrm (T : Subgroup (MulAut ↥E)) : preS T ≤ Nrm E := preS_le_normalizer T

theorem preS_mono {T T' : Subgroup (MulAut ↥E)} (h : T ≤ T') : preS T ≤ preS T' := by
  intro x hx
  obtain ⟨hxN, hxT⟩ := mem_preS.1 hx
  exact mem_preS.2 ⟨hxN, h hxT⟩

theorem preS_inf (T T' : Subgroup (MulAut ↥E)) : preS (T ⊓ T') = preS T ⊓ preS T' := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxN, hxT⟩ := mem_preS.1 hx
    exact ⟨mem_preS.2 ⟨hxN, hxT.1⟩, mem_preS.2 ⟨hxN, hxT.2⟩⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨hxN, hx1⟩ := mem_preS.1 h1
    exact mem_preS.2 ⟨hxN, hx1, (mem_preS_iff_of_mem hxN).1 h2⟩

theorem preS_XE : preS (S44.XE E) = Nrm E := by
  ext x
  exact ⟨fun hx => (mem_preS.1 hx).1, fun hx => mem_preS.2 ⟨hx, ⟨⟨x, hx⟩, rfl⟩⟩⟩

theorem preS_XE_inf (T : Subgroup (MulAut ↥E)) : preS (S44.XE E ⊓ T) = Nrm E ⊓ preS T := by
  rw [preS_inf, preS_XE]

theorem mem_E_iff_actN_eq_one (hCE : centralizer (E : Set G) = E) {x : G}
    (hx : x ∈ normalizer (E : Set G)) : x ∈ E ↔ S44.actN E ⟨x, hx⟩ = 1 := by
  have h := S44.mem_ker_actN_iff_mem_centralizer (E := E) (n := ⟨x, hx⟩)
  rw [MonoidHom.mem_ker, hCE] at h
  exact h.symm

theorem E_le_preS (hCE : centralizer (E : Set G) = E) (T : Subgroup (MulAut ↥E)) :
    E ≤ preS T := by
  intro x hx
  have hxN : x ∈ normalizer (E : Set G) := le_normalizer hx
  have h1 := (mem_E_iff_actN_eq_one hCE hxN).1 hx
  exact mem_preS.2 ⟨hxN, by rw [h1]; exact one_mem T⟩

theorem preS_bot (hCE : centralizer (E : Set G) = E) : preS (⊥ : Subgroup (MulAut ↥E)) = E := by
  refine le_antisymm (fun x hx => ?_) (E_le_preS hCE _)
  obtain ⟨hxN, hx1⟩ := mem_preS.1 hx
  exact (mem_E_iff_actN_eq_one hCE hxN).2 (Subgroup.mem_bot.1 hx1)

theorem exists_mem_preS_actN {T : Subgroup (MulAut ↥E)} (hT : T ≤ S44.XE E) {g : MulAut ↥E}
    (hg : g ∈ T) : ∃ y : ↥(normalizer (E : Set G)), (y : G) ∈ preS T ∧ S44.actN E y = g := by
  obtain ⟨y, rfl⟩ := hT hg
  exact ⟨y, mem_preS.2 ⟨y.2, hg⟩, rfl⟩

theorem map_actN_preS {T : Subgroup (MulAut ↥E)} (hT : T ≤ S44.XE E) :
    ((preS T).subgroupOf (normalizer (E : Set G))).map (S44.actN E) = T := by
  ext g
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (mem_preS_iff_of_mem y.2).1 hy
  · intro hg
    obtain ⟨y, hy, rfl⟩ := exists_mem_preS_actN hT hg
    exact ⟨y, hy, rfl⟩

theorem preS_le_preS_iff {T T' : Subgroup (MulAut ↥E)} (hT : T ≤ S44.XE E) :
    preS T ≤ preS T' ↔ T ≤ T' := by
  refine ⟨fun h g hg => ?_, preS_mono⟩
  obtain ⟨y, hy, rfl⟩ := exists_mem_preS_actN hT hg
  exact (mem_preS_iff_of_mem y.2).1 (h hy)

theorem card_preS_eq (hCE : centralizer (E : Set G) = E) {T : Subgroup (MulAut ↥E)}
    (hT : T ≤ S44.XE E) : Nat.card ↥(preS T) = Nat.card ↥T * Nat.card ↥E := by
  have h := S44.card_image_mul hCE (preS_le_normalizer T) (E_le_preS hCE T)
  rw [map_actN_preS hT] at h
  exact h.symm

theorem card_preS (hm : M24Out G E t) {T : Subgroup (MulAut ↥E)} (hT : T ≤ S44.XE E) :
    Nat.card ↥(preS T) = 2 ^ 11 * Nat.card ↥T := by
  rw [card_preS_eq hm.centralizer_eq hT, hm.card_E, mul_comm]

theorem mem_of_actN_eq (hCE : centralizer (E : Set G) = E) {S : Subgroup G} (hES : E ≤ S)
    {c : ↥(normalizer (E : Set G))} (hc : (c : G) ∈ S) {x : G}
    (hx : x ∈ normalizer (E : Set G)) (h : S44.actN E c = S44.actN E ⟨x, hx⟩) : x ∈ S := by
  have hker : c⁻¹ * ⟨x, hx⟩ ∈ (S44.actN E).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  rw [S44.ker_actN_eq hCE, mem_subgroupOf] at hker
  have h' : (c : G)⁻¹ * x ∈ E := hker
  have hxeq : x = (c : G) * ((c : G)⁻¹ * x) := by group
  rw [hxeq]
  exact S.mul_mem hc (hES h')

theorem exists_T (hCE : centralizer (E : Set G) = E) {S : Subgroup G} (hES : E ≤ S)
    (hSN : S ≤ normalizer (E : Set G)) :
    ∃ T : Subgroup (MulAut ↥E), T ≤ S44.XE E ∧ S = preS T := by
  refine ⟨(S.subgroupOf (normalizer (E : Set G))).map (S44.actN E), Subgroup.map_le_range _ _, ?_⟩
  ext x
  constructor
  · intro hx
    exact mem_preS.2 ⟨hSN hx, ⟨⟨x, hSN hx⟩, hx, rfl⟩⟩
  · intro hx
    obtain ⟨hxN, y, hy, hyx⟩ := mem_preS.1 hx
    exact mem_of_actN_eq hCE hES hy hxN hyx

theorem commutator_mem_E_iff (hCE : centralizer (E : Set G) = E) {r p : G}
    (hr : r ∈ normalizer (E : Set G)) (hp : p ∈ normalizer (E : Set G)) :
    r * p * r⁻¹ * p⁻¹ ∈ E ↔
      S44.actN E ⟨r, hr⟩ * S44.actN E ⟨p, hp⟩ = S44.actN E ⟨p, hp⟩ * S44.actN E ⟨r, hr⟩ := by
  have hc : r * p * r⁻¹ * p⁻¹ ∈ normalizer (E : Set G) :=
    mul_mem (mul_mem (mul_mem hr hp) (inv_mem hr)) (inv_mem hp)
  rw [mem_E_iff_actN_eq_one hCE hc]
  have h1 : (⟨r * p * r⁻¹ * p⁻¹, hc⟩ : ↥(normalizer (E : Set G))) =
      ⟨r, hr⟩ * ⟨p, hp⟩ * ⟨r, hr⟩⁻¹ * ⟨p, hp⟩⁻¹ := rfl
  rw [h1, map_mul, map_mul, map_mul, map_inv, map_inv, ← commutatorElement_def,
    commutatorElement_eq_one_iff_mul_comm]

theorem commutator_mem_preS_iff {S : Subgroup (MulAut ↥E)} {a r : G}
    (ha : a ∈ normalizer (E : Set G)) (hr : r ∈ normalizer (E : Set G)) :
    a * r * a⁻¹ * r⁻¹ ∈ preS S ↔
      S44.actN E ⟨a, ha⟩ * S44.actN E ⟨r, hr⟩ * (S44.actN E ⟨a, ha⟩)⁻¹ *
        (S44.actN E ⟨r, hr⟩)⁻¹ ∈ S := by
  have hc : a * r * a⁻¹ * r⁻¹ ∈ normalizer (E : Set G) :=
    mul_mem (mul_mem (mul_mem ha hr) (inv_mem ha)) (inv_mem hr)
  rw [mem_preS_iff_of_mem hc]
  have h1 : (⟨a * r * a⁻¹ * r⁻¹, hc⟩ : ↥(normalizer (E : Set G))) =
      ⟨a, ha⟩ * ⟨r, hr⟩ * ⟨a, ha⟩⁻¹ * ⟨r, hr⟩⁻¹ := rfl
  rw [h1, map_mul, map_mul, map_mul, map_inv, map_inv]

theorem pow_mem_E_iff (hCE : centralizer (E : Set G) = E) {x : G}
    (hx : x ∈ normalizer (E : Set G)) (n : ℕ) :
    x ^ n ∈ E ↔ S44.actN E ⟨x, hx⟩ ^ n = 1 := by
  rw [mem_E_iff_actN_eq_one hCE (pow_mem hx n)]
  have h1 : (⟨x ^ n, pow_mem hx n⟩ : ↥(normalizer (E : Set G))) = ⟨x, hx⟩ ^ n := rfl
  rw [h1, map_pow]

theorem orderOf_actN_eq_three (hm : M24Out G E t) {r : G} (hr : r ∈ normalizer (E : Set G))
    (h3 : orderOf r = 3) : orderOf (S44.actN E ⟨r, hr⟩) = 3 := by
  have hr3 : r ^ 3 = 1 := by rw [← h3]; exact pow_orderOf_eq_one r
  have h1 : S44.actN E ⟨r, hr⟩ ^ 3 = 1 :=
    (pow_mem_E_iff hm.centralizer_eq hr 3).1 (by rw [hr3]; exact one_mem E)
  have h2 : S44.actN E ⟨r, hr⟩ ≠ 1 := by
    intro h
    have hrE : r ∈ E := (mem_E_iff_actN_eq_one hm.centralizer_eq hr).2 h
    have hsq := hm.E_sq r hrE
    have hr1 : r = 1 := by
      have : r = r ^ 3 * (r ^ 2)⁻¹ := by group
      rw [this, hr3, hsq]
      simp
    rw [hr1, orderOf_one] at h3
    exact absurd h3 (by norm_num)
  exact orderOf_eq_prime h1 h2

theorem invUnder_preS_iff {T : Subgroup (MulAut ↥E)} (hT : T ≤ S44.XE E) {U : Subgroup G}
    (hU : U ≤ E) :
    InvUnder (preS T) U ↔ ∀ g ∈ T, ∀ u ∈ U.subgroupOf E, g u ∈ U.subgroupOf E := by
  constructor
  · intro h g hg u hu
    obtain ⟨y, hy, rfl⟩ := exists_mem_preS_actN hT hg
    exact h y hy u hu
  · intro h n hn u hu
    obtain ⟨hnN, hnT⟩ := mem_preS.1 hn
    exact h _ hnT ⟨u, hU hu⟩ hu

theorem invUnder_preS_preS_iff {T S : Subgroup (MulAut ↥E)} (hT : T ≤ S44.XE E)
    (hS : S ≤ S44.XE E) :
    InvUnder (preS T) (preS S) ↔ ∀ g ∈ T, ∀ s ∈ S, g * s * g⁻¹ ∈ S := by
  constructor
  · intro h g hg s hs
    obtain ⟨y, hy, rfl⟩ := exists_mem_preS_actN hT hg
    obtain ⟨u, hu, rfl⟩ := exists_mem_preS_actN hS hs
    have h1 := h y hy u hu
    have hmem : (y : G) * u * (y : G)⁻¹ ∈ normalizer (E : Set G) :=
      mul_mem (mul_mem y.2 u.2) (inv_mem y.2)
    have h2 := (mem_preS_iff_of_mem hmem).1 h1
    have h3 : (⟨(y : G) * u * (y : G)⁻¹, hmem⟩ : ↥(normalizer (E : Set G))) = y * u * y⁻¹ := rfl
    rwa [h3, map_mul, map_mul, map_inv] at h2
  · intro h n hn u hu
    obtain ⟨hnN, hnT⟩ := mem_preS.1 hn
    obtain ⟨huN, huS⟩ := mem_preS.1 hu
    have hmem : n * u * n⁻¹ ∈ normalizer (E : Set G) := mul_mem (mul_mem hnN huN) (inv_mem hnN)
    refine (mem_preS_iff_of_mem hmem).2 ?_
    have h3 : (⟨n * u * n⁻¹, hmem⟩ : ↥(normalizer (E : Set G))) =
        ⟨n, hnN⟩ * ⟨u, huN⟩ * ⟨n, hnN⟩⁻¹ := rfl
    rw [h3, map_mul, map_mul, map_inv]
    exact h _ hnT _ huS

theorem map_subgroupOf_subtype {U : Subgroup G} (hU : U ≤ E) :
    (U.subgroupOf E).map E.subtype = U :=
  Subgroup.map_subgroupOf_eq_of_le hU

theorem eq_map_subtype_iff {U : Subgroup G} (hU : U ≤ E) (W : Subgroup ↥E) :
    U = W.map E.subtype ↔ U.subgroupOf E = W := by
  constructor
  · rintro rfl
    exact Subgroup.comap_map_eq_self_of_injective E.subtype_injective W
  · rintro rfl
    exact (map_subgroupOf_subtype hU).symm

theorem eq_bot_iff_subgroupOf_eq_bot {U : Subgroup G} (hU : U ≤ E) :
    U = ⊥ ↔ U.subgroupOf E = ⊥ := by
  rw [← eq_map_subtype_iff hU ⊥, Subgroup.map_bot]

theorem eq_self_iff_subgroupOf_eq_top {U : Subgroup G} (hU : U ≤ E) :
    U = E ↔ U.subgroupOf E = ⊤ := by
  rw [← eq_map_subtype_iff hU ⊤, Subgroup.map_top, Subgroup.range_subtype]

theorem eq_zpowers_iff_subgroupOf_eq_zpowers {U : Subgroup G} (hU : U ≤ E) {z : G} (hz : z ∈ E) :
    U = zpowers z ↔ U.subgroupOf E = zpowers (⟨z, hz⟩ : ↥E) := by
  rw [← eq_map_subtype_iff hU, MonoidHom.map_zpowers]
  rfl

theorem card_eq_card_subgroupOf {U : Subgroup G} (hU : U ≤ E) :
    Nat.card ↥U = Nat.card ↥(U.subgroupOf E) := by
  conv_lhs => rw [← map_subgroupOf_subtype hU]
  exact Subgroup.card_map_of_injective E.subtype_injective

theorem commutator_E_preS (hm : M24Out G E t) {T : Subgroup (MulAut ↥E)} (hT : T ≤ S44.XE E) :
    ⁅E, preS T⁆ = (@Quasithin.commV ↥E (commGroupOfM24Out hm) T).map E.subtype := by
  letI := commGroupOfM24Out hm
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro e he p hp
    obtain ⟨hpN, hpT⟩ := mem_preS.1 hp
    set g : MulAut ↥E := S44.actN E ⟨p, hpN⟩ with hg
    refine ⟨(⟨e, he⟩ : ↥E) * (g ⟨e, he⟩)⁻¹, ?_, ?_⟩
    · have hw : (⟨e, he⟩ : ↥E) * (g ⟨e, he⟩)⁻¹ = g (⟨e, he⟩⁻¹) * (⟨e, he⟩⁻¹)⁻¹ := by
        rw [map_inv, inv_inv, mul_comm]
      rw [hw]
      exact Subgroup.subset_closure ⟨g, hpT, ⟨e, he⟩⁻¹, rfl⟩
    · show e * (p * e * p⁻¹)⁻¹ = e * p * e⁻¹ * p⁻¹
      group
  · rw [Subgroup.map_le_iff_le_comap, Quasithin.commV, Subgroup.closure_le]
    rintro _ ⟨g, hg, v, rfl⟩
    obtain ⟨y, hy, rfl⟩ := exists_mem_preS_actN hT hg
    have h1 : ⁅(v : G), (y : G)⁆ ∈ ⁅E, preS T⁆ := Subgroup.commutator_mem_commutator v.2 hy
    have h2 := inv_mem h1
    have h3 : ((S44.actN E y v * v⁻¹ : ↥E) : G) = ((y : G) * v * (y : G)⁻¹) * (v : G)⁻¹ := rfl
    show ((S44.actN E y v * v⁻¹ : ↥E) : G) ∈ ⁅E, preS T⁆
    rw [h3]
    convert h2 using 1
    rw [commutatorElement_def]
    group

theorem commutator_E_preS_eq_zpowers_iff (hm : M24Out G E t) {T : Subgroup (MulAut ↥E)}
    (hT : T ≤ S44.XE E) {z : G} (hz : z ∈ E) :
    ⁅E, preS T⁆ = zpowers z ↔
      @Quasithin.commV ↥E (commGroupOfM24Out hm) T = zpowers (⟨z, hz⟩ : ↥E) := by
  have hz' : zpowers z = (zpowers (⟨z, hz⟩ : ↥E)).map E.subtype := by
    rw [MonoidHom.map_zpowers]
    rfl
  rw [commutator_E_preS hm hT, hz']
  exact (Subgroup.map_injective E.subtype_injective).eq_iff

theorem commutator_preS_subgroupOf (T : Subgroup (MulAut ↥E)) :
    (⁅preS T, preS T⁆).subgroupOf (normalizer (E : Set G)) =
      ⁅(preS T).subgroupOf (normalizer (E : Set G)),
        (preS T).subgroupOf (normalizer (E : Set G))⁆ := by
  have h : ⁅preS T, preS T⁆ = (⁅(preS T).subgroupOf (normalizer (E : Set G)),
      (preS T).subgroupOf (normalizer (E : Set G))⁆).map (normalizer (E : Set G)).subtype := by
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le (preS_le_normalizer T)]
  rw [h]
  exact Subgroup.comap_map_eq_self_of_injective (normalizer (E : Set G)).subtype_injective _

theorem map_actN_commutator_preS {T : Subgroup (MulAut ↥E)} (hT : T ≤ S44.XE E) :
    ((⁅preS T, preS T⁆).subgroupOf (normalizer (E : Set G))).map (S44.actN E) = ⁅T, T⁆ := by
  rw [commutator_preS_subgroupOf, Subgroup.map_commutator, map_actN_preS hT]

theorem commutator_self_le (S : Subgroup G) : ⁅S, S⁆ ≤ S :=
  Subgroup.commutator_le.2 fun _ ha _ hb =>
    S.mul_mem (S.mul_mem (S.mul_mem ha hb) (S.inv_mem ha)) (S.inv_mem hb)

theorem commutator_preS_eq_iff (hCE : centralizer (E : Set G) = E) {T : Subgroup (MulAut ↥E)}
    (hT : T ≤ S44.XE E) :
    ⁅preS T, preS T⁆ = preS T ↔ ⁅T, T⁆ = T ∧ E ≤ ⁅preS T, preS T⁆ := by
  constructor
  · intro h
    refine ⟨?_, by rw [h]; exact E_le_preS hCE T⟩
    rw [← map_actN_commutator_preS hT, h, map_actN_preS hT]
  · rintro ⟨h1, h2⟩
    refine le_antisymm (commutator_self_le _) fun s hs => ?_
    have hsN := preS_le_normalizer T hs
    have hsT : S44.actN E ⟨s, hsN⟩ ∈ ⁅T, T⁆ := by
      rw [h1]
      exact (mem_preS_iff_of_mem hsN).1 hs
    rw [← map_actN_commutator_preS hT] at hsT
    obtain ⟨c, hc, hcs⟩ := hsT
    exact mem_of_actN_eq hCE h2 hc hsN hcs

theorem commutator_preS_eq_of (hm : M24Out G E t) {T : Subgroup (MulAut ↥E)} (hT : T ≤ S44.XE E)
    (h1 : ⁅T, T⁆ = T) (h2 : @Quasithin.commV ↥E (commGroupOfM24Out hm) T = ⊤) :
    ⁅preS T, preS T⁆ = preS T := by
  refine (commutator_preS_eq_iff hm.centralizer_eq hT).2 ⟨h1, ?_⟩
  have h3 := commutator_E_preS hm hT
  rw [h2, Subgroup.map_top, Subgroup.range_subtype] at h3
  calc E = ⁅E, preS T⁆ := h3.symm
    _ ≤ ⁅preS T, preS T⁆ := Subgroup.commutator_mono_left (E_le_preS hm.centralizer_eq T)

theorem mem_map_E_subtype_iff {W : Subgroup ↥E} {h : G} :
    h ∈ W.map E.subtype ↔ ∃ hE : h ∈ E, (⟨h, hE⟩ : ↥E) ∈ W := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.2, hw⟩
  · rintro ⟨hE, hw⟩
    exact ⟨⟨h, hE⟩, hw, rfl⟩

theorem mem_normalizer_map_E_subtype_iff {W : Subgroup ↥E} {y : G}
    (hy : y ∈ normalizer (E : Set G)) :
    y ∈ normalizer ((W.map E.subtype : Subgroup G) : Set G) ↔
      ∀ u : ↥E, S44.actN E ⟨y, hy⟩ u ∈ W ↔ u ∈ W := by
  have hact : ∀ u : ↥E, ((S44.actN E ⟨y, hy⟩ u : ↥E) : G) = y * u * y⁻¹ := fun u => rfl
  constructor
  · intro h u
    have h1 := mem_normalizer_iff.1 h (u : G)
    rw [mem_map_E_subtype_iff, mem_map_E_subtype_iff] at h1
    constructor
    · intro hu
      have h2 : ∃ hE : y * (u : G) * y⁻¹ ∈ E, (⟨y * (u : G) * y⁻¹, hE⟩ : ↥E) ∈ W :=
        ⟨(S44.actN E ⟨y, hy⟩ u).2, hu⟩
      obtain ⟨hE, hu'⟩ := h1.2 h2
      exact hu'
    · intro hu
      obtain ⟨hE, hu'⟩ := h1.1 ⟨u.2, hu⟩
      exact hu'
  · intro h
    refine mem_normalizer_iff.2 fun x => ?_
    by_cases hxE : x ∈ E
    · have h1 := h ⟨x, hxE⟩
      rw [mem_map_E_subtype_iff, mem_map_E_subtype_iff]
      constructor
      · rintro ⟨_, hx⟩
        exact ⟨(S44.actN E ⟨y, hy⟩ ⟨x, hxE⟩).2, h1.2 hx⟩
      · rintro ⟨_, hx⟩
        exact ⟨hxE, h1.1 hx⟩
    · have hyx : y * x * y⁻¹ ∉ E := fun hh => hxE ((mem_normalizer_iff.1 hy x).2 hh)
      constructor
      · intro hx
        exact absurd (mem_map_E_subtype_iff.1 hx).1 hxE
      · intro hx
        exact absurd (mem_map_E_subtype_iff.1 hx).1 hyx

theorem preS_stabilizer {x : G} (hx : x ∈ E) :
    preS (stabilizer (MulAut ↥E) (⟨x, hx⟩ : ↥E)) = Nrm E ⊓ centralizer ({x} : Set G) := by
  ext y
  rw [Subgroup.mem_inf, mem_centralizer_singleton_iff]
  constructor
  · intro hy
    obtain ⟨hyN, hyS⟩ := mem_preS.1 hy
    refine ⟨hyN, ?_⟩
    have h1 : y * x * y⁻¹ = x := congrArg Subtype.val (MulAction.mem_stabilizer_iff.1 hyS)
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1
  · rintro ⟨hyN, hy⟩
    refine mem_preS.2 ⟨hyN, MulAction.mem_stabilizer_iff.2 (Subtype.ext ?_)⟩
    show y * x * y⁻¹ = x
    rw [mul_inv_eq_iff_eq_mul]
    exact hy

theorem Nrm_inf_centralizer_eq_preS (hm : M24Out G E t) {x : G} (hx : x ∈ E) :
    Nrm E ⊓ centralizer ({x} : Set G) =
      preS (S44.XE E ⊓ @Quasithin.centSub ↥E (commGroupOfM24Out hm)
        (zpowers (⟨x, hx⟩ : ↥E))) := by
  rw [preS_XE_inf, centSub_zpowers_eq_stabilizer, preS_stabilizer hx, ← inf_assoc, inf_idem]

theorem CNz_eq_preS (hm : M24Out G E t) {z : G} (hz : z ∈ E) :
    CNz E z = preS (S44.XE E ⊓ @Quasithin.centSub ↥E (commGroupOfM24Out hm)
      (zpowers (⟨z, hz⟩ : ↥E))) :=
  Nrm_inf_centralizer_eq_preS hm hz

theorem CNz_inf_centralizer_eq_preS (hm : M24Out G E t) {x z : G} (hx : x ∈ E) (hz : z ∈ E) :
    CNz E z ⊓ centralizer ({x} : Set G) =
      preS (S44.XE E ⊓ @Quasithin.centSub ↥E (commGroupOfM24Out hm) (zpowers (⟨z, hz⟩ : ↥E)) ⊓
        @Quasithin.centSub ↥E (commGroupOfM24Out hm) (zpowers (⟨x, hx⟩ : ↥E))) := by
  rw [preS_inf, ← CNz_eq_preS hm hz, centSub_zpowers_eq_stabilizer hm, preS_stabilizer hx,
    ← inf_assoc, inf_eq_left.2 (CNz_le_Nrm E z)]

theorem preS_stabSub (hm : M24Out G E t) (W : Subgroup ↥E) :
    preS (@Quasithin.stabSub ↥E (commGroupOfM24Out hm) W) =
      Nrm E ⊓ normalizer ((W.map E.subtype : Subgroup G) : Set G) := by
  letI := commGroupOfM24Out hm
  ext y
  constructor
  · intro hy
    obtain ⟨hyN, hyS⟩ := mem_preS.1 hy
    exact ⟨hyN, (mem_normalizer_map_E_subtype_iff hyN).2 (Quasithin.mem_stabSub.1 hyS)⟩
  · rintro ⟨hyN, hy⟩
    exact mem_preS.2 ⟨hyN, Quasithin.mem_stabSub.2 ((mem_normalizer_map_E_subtype_iff hyN).1 hy)⟩

theorem Vtz_eq_map {x y : G} (hx : x ∈ E) (hy : y ∈ E) :
    Vtz x y = (closure {(⟨x, hx⟩ : ↥E), ⟨y, hy⟩} : Subgroup ↥E).map E.subtype := by
  rw [MonoidHom.map_closure, Set.image_pair]
  rfl

theorem Nrm_inf_Jg_eq_preS (hm : M24Out G E t) {x y : G} (hx : x ∈ E) (hy : y ∈ E) :
    Nrm E ⊓ Jg x y =
      preS (S44.XE E ⊓ @Quasithin.stabSub ↥E (commGroupOfM24Out hm)
        (closure {(⟨x, hx⟩ : ↥E), ⟨y, hy⟩})) := by
  rw [preS_XE_inf, preS_stabSub hm, ← Vtz_eq_map hx hy, ← inf_assoc, inf_idem]
  rfl

theorem conj_mem_normClass {x y n : G} (hn : n ∈ normalizer (E : Set G))
    (hy : y ∈ normClass E x) : n * y * n⁻¹ ∈ normClass E x := by
  obtain ⟨m, hmN, rfl⟩ := hy
  exact ⟨n * m, mul_mem hn hmN, by group⟩

theorem mem_Vtz_cases {t z : G} (ht : t * t = 1) (hz : z * z = 1) (hc : t * z = z * t) {w : G}
    (hw : w ∈ Vtz t z) : w = 1 ∨ w = t ∨ w = z ∨ w = t * z := by
  have e1 : t * (t * z) = z := by rw [← mul_assoc, ht, one_mul]
  have e2 : z * (t * z) = t := by rw [hc, ← mul_assoc, hz, one_mul]
  have e3 : t * z * t = z := by rw [hc, mul_assoc, ht, mul_one]
  have e4 : t * z * z = t := by rw [mul_assoc, hz, mul_one]
  have e5 : t * z * (t * z) = 1 := by rw [← mul_assoc, e3, hz]
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  | one => exact Or.inl rfl
  | mul x y _ _ hx hy =>
    rcases hx with h | h | h | h <;> rcases hy with h' | h' | h' | h' <;> rw [h, h']
    · exact Or.inl (one_mul 1)
    · exact Or.inr (Or.inl (one_mul t))
    · exact Or.inr (Or.inr (Or.inl (one_mul z)))
    · exact Or.inr (Or.inr (Or.inr (one_mul _)))
    · exact Or.inr (Or.inl (mul_one t))
    · exact Or.inl ht
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact Or.inr (Or.inr (Or.inl e1))
    · exact Or.inr (Or.inr (Or.inl (mul_one z)))
    · exact Or.inr (Or.inr (Or.inr hc.symm))
    · exact Or.inl hz
    · exact Or.inr (Or.inl e2)
    · exact Or.inr (Or.inr (Or.inr (mul_one _)))
    · exact Or.inr (Or.inr (Or.inl e3))
    · exact Or.inr (Or.inl e4)
    · exact Or.inl e5
  | inv x _ hx =>
    rcases hx with h | h | h | h <;> rw [h]
    · exact Or.inl inv_one
    · exact Or.inr (Or.inl (inv_eq_iff_mul_eq_one.2 ht))
    · exact Or.inr (Or.inr (Or.inl (inv_eq_iff_mul_eq_one.2 hz)))
    · exact Or.inr (Or.inr (Or.inr (inv_eq_iff_mul_eq_one.2 e5)))

theorem Nrm_inf_Jg_le_CNz (hm : M24Out G E t) {z : G} (hz : IsZ E t z) :
    Nrm E ⊓ Jg t z ≤ CNz E z := by
  intro n hn
  obtain ⟨hnN, hnJ⟩ := Subgroup.mem_inf.1 hn
  have htE : t ∈ E := hm.t_mem
  have ht2 : t * t = 1 := by rw [← pow_two]; exact hm.E_sq t htE
  have hz2 : z * z = 1 := by rw [← pow_two]; exact hm.E_sq z hz.1
  have hc : t * z = z * t := m24Out_E_comm hm t htE z hz.1
  have hzV : z ∈ Vtz t z := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hw : n * z * n⁻¹ ∈ Vtz t z := (mem_normalizer_iff.1 hnJ z).1 hzV
  have hclass : ∀ y, y ∈ normClass E t → n⁻¹ * y * n ∈ normClass E t := fun y hy => by
    simpa only [inv_inv] using conj_mem_normClass (inv_mem hnN) hy
  have hz' : n⁻¹ * (n * z * n⁻¹) * n = z := by group
  refine mem_CNz.2 ⟨hnN, ?_⟩
  have hfix : n * z * n⁻¹ = z := by
    rcases mem_Vtz_cases ht2 hz2 hc hw with h | h | h | h
    · rw [h] at hz'
      exact absurd (by rw [← hz']; group) hz.2.1
    · rw [h] at hz'
      exact absurd (hz' ▸ hclass t ⟨1, one_mem _, by group⟩) hz.2.2.1
    · exact h
    · rw [h] at hz'
      exact absurd (hz' ▸ hclass _ hz.2.2.2) hz.2.2.1
  calc n * z = n * z * n⁻¹ * n := by group
    _ = z * n := by rw [hfix]

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
