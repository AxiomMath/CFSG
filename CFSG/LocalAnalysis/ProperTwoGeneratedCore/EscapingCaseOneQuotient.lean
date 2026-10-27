module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherEscapingRankTwo

public section

namespace CFSG.ProperTwoGeneratedCore.Assembly

open CFSG.Open

section Notation

variable {G : Type*} [Group G]

abbrev EscapingQuotient (x : G) :=
  Subgroup.centralizer ({x} : Set G) ⧸ pPrimeCore 2 (Subgroup.centralizer ({x} : Set G))

abbrev escapingMk (x : G) : Subgroup.centralizer ({x} : Set G) →* EscapingQuotient x :=
  QuotientGroup.mk' _

abbrev escapingSelf (x : G) : Subgroup.centralizer ({x} : Set G) :=
  ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

abbrev escapingBar (x : G) : EscapingQuotient x :=
  escapingMk x (escapingSelf x)

abbrev escapingImage (H : Subgroup G) (x : G) : Subgroup (EscapingQuotient x) :=
  (H.subgroupOf (Subgroup.centralizer ({x} : Set G))).map (escapingMk x)

end Notation

section OddQuotient

variable {K : Type*} [Group K] {N : Subgroup K} [N.Normal]

theorem orderOf_pow_card_eq_two (hN : Odd (Nat.card N)) {c : K}
    (hc : orderOf (QuotientGroup.mk' N c) = 2) :
    orderOf (c ^ Nat.card N) = 2 ∧
      QuotientGroup.mk' N (c ^ Nat.card N) = QuotientGroup.mk' N c := by
  have hsq : QuotientGroup.mk' N c ^ 2 = 1 := by rw [← hc, pow_orderOf_eq_one]
  have hc2 : c ^ 2 ∈ N := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_pow]
    exact hsq
  have himage : QuotientGroup.mk' N (c ^ Nat.card N) = QuotientGroup.mk' N c := by
    obtain ⟨k, hk⟩ := hN
    rw [map_pow, hk, pow_succ, pow_mul, hsq, one_pow, one_mul]
  refine ⟨orderOf_eq_prime ?_ ?_, himage⟩
  · have h1 : (⟨c ^ 2, hc2⟩ : N) ^ Nat.card N = 1 := pow_card_eq_one'
    have h2 := congrArg Subtype.val h1
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h2
    rw [← pow_mul, mul_comm, pow_mul, h2]
  · intro h1
    have h3 := congrArg (QuotientGroup.mk' N) h1
    rw [himage, map_one] at h3
    rw [h3, orderOf_one] at hc
    exact absurd hc (by decide)

theorem exists_involution_lift (hN : Odd (Nat.card N)) {y : K ⧸ N} (hy : orderOf y = 2) :
    ∃ c : K, orderOf c = 2 ∧ QuotientGroup.mk' N c = y := by
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective N y
  exact ⟨_, orderOf_pow_card_eq_two hN hy⟩

theorem orderOf_mk_eq_two (hN : Odd (Nat.card N)) {a : K} (ha : orderOf a = 2) :
    orderOf (QuotientGroup.mk' N a) = 2 := by
  refine orderOf_eq_prime (by rw [← map_pow, ← ha, pow_orderOf_eq_one, map_one]) ?_
  intro h1
  have haN : a ∈ N := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply]
    exact h1
  have hdvd : orderOf a ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N haN
  rw [ha] at hdvd
  exact (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr hdvd)

theorem exists_conj_of_mk_eq (hN : Odd (Nat.card N)) {a b : K} (ha : orderOf a = 2)
    (hb : orderOf b = 2) (hab : QuotientGroup.mk' N a = QuotientGroup.mk' N b) :
    ∃ n ∈ N, n⁻¹ * a * n = b := by
  have haa : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  have hbb : b * b = 1 := by rw [← pow_two, ← hb, pow_orderOf_eq_one]
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  set n₀ := a⁻¹ * b with hn₀
  have hn₀N : n₀ ∈ N := QuotientGroup.eq.mp hab
  have hconj : a * n₀ * a⁻¹ = n₀⁻¹ := by
    rw [hn₀, mul_inv_rev, hbinv, inv_inv, hainv, ← mul_assoc, haa, one_mul]
  set c := n₀ ^ ((Nat.card N + 1) / 2) with hc
  have hcc : c * c = n₀ := by
    obtain ⟨k, hk⟩ := hN
    have hdiv : (Nat.card N + 1) / 2 = k + 1 := by omega
    have h1 : (⟨n₀, hn₀N⟩ : N) ^ Nat.card N = 1 := pow_card_eq_one'
    have h2 := congrArg Subtype.val h1
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h2
    rw [hc, hdiv, ← pow_add, show k + 1 + (k + 1) = Nat.card N + 1 by omega, pow_succ, h2,
      one_mul]
  have hac : a * c * a⁻¹ = c⁻¹ := by rw [hc, ← conj_pow, hconj, inv_pow]
  refine ⟨c, N.pow_mem hn₀N _, ?_⟩
  calc c⁻¹ * a * c = (a * c * a⁻¹) * a * c := by rw [hac]
    _ = a * (c * c) := by group
    _ = b := by rw [hcc, hn₀, ← mul_assoc, mul_inv_cancel, one_mul]

theorem isConj_of_isConj_mk (hN : Odd (Nat.card N)) {a b : K} (ha : orderOf a = 2)
    (hb : orderOf b = 2) (h : IsConj (QuotientGroup.mk' N a) (QuotientGroup.mk' N b)) :
    IsConj a b := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective N c
  have ha' : orderOf (m * a * m⁻¹) = 2 := by
    rw [← ha]
    simpa only [MulAut.conj_apply] using (MulAut.conj m).orderOf_eq a
  obtain ⟨n, -, hn⟩ := exists_conj_of_mk_eq hN ha' hb (by rw [← hc, map_mul, map_mul, map_inv])
  refine isConj_iff.mpr ⟨n⁻¹ * m, ?_⟩
  rw [← hn]
  group

theorem map_centralizer_eq (hN : Odd (Nat.card N)) {a : K} (ha : orderOf a = 2) :
    (Subgroup.centralizer ({a} : Set K)).map (QuotientGroup.mk' N) =
      Subgroup.centralizer ({QuotientGroup.mk' N a} : Set (K ⧸ N)) := by
  apply le_antisymm
  · rintro _ ⟨m, hm, rfl⟩
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp hm]
  · intro y hy
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective N y
    rw [Subgroup.mem_centralizer_singleton_iff] at hy
    have ha' : orderOf (m⁻¹ * a * m) = 2 := by
      rw [← ha]
      simpa only [MulAut.conj_apply, inv_inv] using (MulAut.conj m⁻¹).orderOf_eq a
    obtain ⟨n, hnN, hn⟩ := exists_conj_of_mk_eq hN ha ha' (by
      rw [map_mul, map_mul, map_inv, mul_assoc, ← hy, ← mul_assoc, inv_mul_cancel, one_mul])
    refine ⟨m * n⁻¹, ?_, ?_⟩
    · refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      calc m * n⁻¹ * a = m * (n⁻¹ * a * n) * n⁻¹ := by group
        _ = a * (m * n⁻¹) := by rw [hn]; group
    · have hn1 : QuotientGroup.mk' N n = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hnN
      rw [map_mul, map_inv, hn1, inv_one, mul_one]

theorem exists_commuting_involution_lift (hN : Odd (Nat.card N)) {a : K} (ha : orderOf a = 2)
    {y : K ⧸ N} (hy : orderOf y = 2) (hya : Commute y (QuotientGroup.mk' N a)) :
    ∃ b : K, orderOf b = 2 ∧ Commute b a ∧ QuotientGroup.mk' N b = y := by
  have hmem : y ∈ (Subgroup.centralizer ({a} : Set K)).map (QuotientGroup.mk' N) := by
    rw [map_centralizer_eq hN ha, Subgroup.mem_centralizer_singleton_iff]
    exact hya.eq
  obtain ⟨c, hc, rfl⟩ := hmem
  obtain ⟨hord, himage⟩ := orderOf_pow_card_eq_two hN hy
  refine ⟨c ^ Nat.card N, hord, ?_, himage⟩
  exact (Commute.pow_left (Subgroup.mem_centralizer_singleton_iff.mp hc) _)

theorem eq_of_mk_eq_of_commute (hN : Odd (Nat.card N)) {a b : K}
    (hcomm : ∀ n ∈ N, Commute a n) (haa : a * a = 1) (hbb : b * b = 1)
    (hab : QuotientGroup.mk' N a = QuotientGroup.mk' N b) : a = b := by
  set n := a⁻¹ * b with hn
  have hnN : n ∈ N := QuotientGroup.eq.mp hab
  have hb : b = a * n := by rw [hn, ← mul_assoc, mul_inv_cancel, one_mul]
  have hnn : n * n = 1 := by
    have h := hbb
    rw [hb, mul_assoc, ← mul_assoc n a n, ← (hcomm n hnN).eq, mul_assoc, ← mul_assoc a a,
      haa, one_mul] at h
    exact h
  have h1 : orderOf n ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hnn)
  have h2 : orderOf n ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hnN
  have hcop : Nat.Coprime 2 (Nat.card N) := Nat.coprime_two_left.mpr hN
  have h3 : orderOf n = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  rw [orderOf_eq_one_iff] at h3
  rw [hb, h3, mul_one]

end OddQuotient

section Centralizer

variable {G : Type} [Group G] [Finite G]

theorem escaping_oddCore_odd (x : G) :
    Odd (Nat.card (pPrimeCore 2 (Subgroup.centralizer ({x} : Set G)))) :=
  Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2))

theorem escaping_exists_lift (x : G) {y : EscapingQuotient x} (hy : orderOf y = 2) :
    ∃ c : Subgroup.centralizer ({x} : Set G), orderOf c = 2 ∧ escapingMk x c = y :=
  exists_involution_lift (escaping_oddCore_odd x) hy

theorem escaping_orderOf_mk (x : G) {a : Subgroup.centralizer ({x} : Set G)}
    (ha : orderOf a = 2) : orderOf (escapingMk x a) = 2 :=
  orderOf_mk_eq_two (escaping_oddCore_odd x) ha

theorem escaping_conj_of_mk_eq (x : G) {a b : Subgroup.centralizer ({x} : Set G)}
    (ha : orderOf a = 2) (hb : orderOf b = 2) (hab : escapingMk x a = escapingMk x b) :
    ∃ n ∈ pPrimeCore 2 (Subgroup.centralizer ({x} : Set G)), n⁻¹ * a * n = b :=
  exists_conj_of_mk_eq (escaping_oddCore_odd x) ha hb hab

theorem escaping_isConj_of_isConj_mk (x : G) {a b : Subgroup.centralizer ({x} : Set G)}
    (ha : orderOf a = 2) (hb : orderOf b = 2) (h : IsConj (escapingMk x a) (escapingMk x b)) :
    IsConj a b :=
  isConj_of_isConj_mk (escaping_oddCore_odd x) ha hb h

theorem escaping_map_centralizer (x : G) {a : Subgroup.centralizer ({x} : Set G)}
    (ha : orderOf a = 2) :
    (Subgroup.centralizer ({a} : Set (Subgroup.centralizer ({x} : Set G)))).map (escapingMk x) =
      Subgroup.centralizer ({escapingMk x a} : Set (EscapingQuotient x)) :=
  map_centralizer_eq (escaping_oddCore_odd x) ha

theorem escaping_exists_commuting_lift (x : G) {a : Subgroup.centralizer ({x} : Set G)}
    (ha : orderOf a = 2) {y : EscapingQuotient x} (hy : orderOf y = 2)
    (hya : Commute y (escapingMk x a)) :
    ∃ b : Subgroup.centralizer ({x} : Set G), orderOf b = 2 ∧ Commute b a ∧ escapingMk x b = y :=
  exists_commuting_involution_lift (escaping_oddCore_odd x) ha hy hya

theorem escaping_eq_of_mk_eq_bar {x : G} (hx : x * x = 1) {y : Subgroup.centralizer ({x} : Set G)}
    (hy : y * y = 1) (hyx : escapingMk x y = escapingBar x) : (y : G) = x := by
  have hcomm : ∀ n ∈ pPrimeCore 2 (Subgroup.centralizer ({x} : Set G)),
      Commute (escapingSelf x) n := fun n _ =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp n.property).symm
  have h := eq_of_mk_eq_of_commute (escaping_oddCore_odd x) hcomm (Subtype.ext hx) hy hyx.symm
  exact (congrArg Subtype.val h).symm

end Centralizer

section Escaping

variable {G : Type} [Group G] [Finite G]

structure EscapingQuotientData (H : Subgroup G) (x : G) : Prop where
  mem : x ∈ H
  order : orderOf x = 2
  oddCore_le : pPrimeCore 2 (Subgroup.centralizer ({x} : Set G)) ≤
    H.subgroupOf (Subgroup.centralizer ({x} : Set G))
  image_ne_top : escapingImage H x ≠ ⊤
  sylow : ∃ U : Sylow 2 (EscapingQuotient x),
    (U : Subgroup (EscapingQuotient x)) ≤ escapingImage H x ∧
      properTwoGenCoreGamma (U : Subgroup (EscapingQuotient x)) 2 ≤ escapingImage H x
  oddCore_eq_bot : pPrimeCore 2 (EscapingQuotient x) = ⊥
  bar_mem_center : escapingBar x ∈ Subgroup.center (EscapingQuotient x)
  bar_order : orderOf (escapingBar x) = 2
  bar_mem_twoCore : escapingBar x ∈ pCore 2 (EscapingQuotient x)
  twoCore_rank : CFSG.Open.pRank 2 (pCore 2 (EscapingQuotient x)) = 1
  layer_ne_bot : layer (EscapingQuotient x) ≠ ⊥
  rank : 3 ≤ twoRank (EscapingQuotient x)

theorem escapingQuotientData {S : Sylow 2 G} {H : Subgroup G} (hset : CoreSetting G S H)
    {x : G} (hxH : x ∈ H) (hx : orderOf x = 2)
    (hesc : ¬ Subgroup.centralizer ({x} : Set G) ≤ H) : EscapingQuotientData H x := by
  let : Group.IsPerfect G := hset.isPerfect
  have hG : 3 ≤ twoRank G := by
    rw [← sylow_two_rank_eq S]
    exact hset.rank
  obtain ⟨T⟩ : Nonempty (Sylow 2 ↥(H ⊓ Subgroup.centralizer ({x} : Set G))) := inferInstance
  obtain ⟨U, -, -, -, hfacts⟩ := perfect_proper_core_escaping_centralizer_structure hG S H
    hset.proper hset.sylow_le hset.core_le x hxH hx hesc T
  obtain ⟨-, hRJ, hJHM, -, -, hJbar, hHbar, hUbar, -, hrank, hodd, hcenter, horder, hcore,
    hcoreRank, -, hlayer⟩ := hfacts
  exact ⟨hxH, hx, hRJ.trans hJHM, hHbar.ne, ⟨_, hUbar, hJbar⟩, hodd, hcenter, horder, hcore,
    hcoreRank, hlayer, hrank⟩

variable {H : Subgroup G} {x : G}

namespace EscapingQuotientData

theorem mk_mem_image_iff (hq : EscapingQuotientData H x) (a : Subgroup.centralizer ({x} : Set G)) :
    escapingMk x a ∈ escapingImage H x ↔ (a : G) ∈ H := by
  rw [← Subgroup.mem_comap, Subgroup.comap_map_eq_self (by
    rw [QuotientGroup.ker_mk']
    exact hq.oddCore_le)]
  exact Subgroup.mem_subgroupOf

theorem bar_mem_image (hq : EscapingQuotientData H x) : escapingBar x ∈ escapingImage H x :=
  (hq.mk_mem_image_iff _).mpr hq.mem

theorem commute_bar (hq : EscapingQuotientData H x) (y : EscapingQuotient x) :
    Commute y (escapingBar x) :=
  Subgroup.mem_center_iff.mp hq.bar_mem_center y

theorem normalizer_le (hq : EscapingQuotientData H x) (D : Subgroup (EscapingQuotient x))
    (hDH : D ≤ escapingImage H x) (hD : 2 ≤ CFSG.Open.pRank 2 D) :
    Subgroup.normalizer (D : Set (EscapingQuotient x)) ≤ escapingImage H x := by
  obtain ⟨U, hUH, hcore⟩ := hq.sylow
  exact two_generated_core_subgroup_normalizer_le U _ hUH hcore D hDH hD

theorem centralizer_le (hq : EscapingQuotientData H x) (D : Subgroup (EscapingQuotient x))
    (hDH : D ≤ escapingImage H x) (hD : 2 ≤ CFSG.Open.pRank 2 D) :
    Subgroup.centralizer (D : Set (EscapingQuotient x)) ≤ escapingImage H x :=
  (Subgroup.centralizer_le_normalizer _).trans (hq.normalizer_le D hDH hD)

theorem involution_centralizer_le (hq : EscapingQuotientData H x) {y : EscapingQuotient x}
    (hyH : y ∈ escapingImage H x) (hy : orderOf y = 2) (hne : y ≠ escapingBar x) :
    Subgroup.centralizer ({y} : Set (EscapingQuotient x)) ≤ escapingImage H x := by
  set D := Subgroup.closure ({y, escapingBar x} : Set (EscapingQuotient x)) with hD
  have hyD : y ∈ D := Subgroup.subset_closure (Set.mem_insert _ _)
  have hbD : escapingBar x ∈ D := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hDH : D ≤ escapingImage H x := by
    rw [hD, Subgroup.closure_le]
    rintro w (rfl | rfl)
    · exact hyH
    · exact hq.bar_mem_image
  have hrank : 2 ≤ CFSG.Open.pRank 2 D :=
    two_le_pRank_of_commuting_involutions hyD hbD hy hq.bar_order hne (hq.commute_bar y)
  refine le_trans ?_ (hq.centralizer_le D hDH hrank)
  intro c hc
  rw [hD, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  rintro w (rfl | rfl)
  · exact (Subgroup.mem_centralizer_singleton_iff.mp hc).symm
  · exact (hq.commute_bar c).eq.symm

theorem eq_bar_of_mem_inf_conj (hq : EscapingQuotientData H x) {m y : EscapingQuotient x}
    (hm : m ∉ escapingImage H x)
    (hy : y ∈ escapingImage H x ⊓ (escapingImage H x).conjBy m⁻¹) (hy2 : orderOf y = 2) :
    y = escapingBar x := by
  obtain ⟨U, hUH, hcore⟩ := hq.sylow
  by_contra hne
  have hlt := conjugate_intersection_rank_lt U (escapingImage H x) (k := 2) (by decide) hUH
    hcore m hm
  have hbar : escapingBar x ∈ escapingImage H x ⊓ (escapingImage H x).conjBy m⁻¹ := by
    refine ⟨hq.bar_mem_image, Subgroup.mem_map.mpr ⟨escapingBar x, hq.bar_mem_image, ?_⟩⟩
    change m⁻¹ * escapingBar x * m⁻¹⁻¹ = escapingBar x
    rw [inv_inv, (hq.commute_bar m⁻¹).eq, mul_assoc, inv_mul_cancel, mul_one]
  have h2 := two_le_pRank_of_commuting_involutions hy hbar hy2 hq.bar_order hne
    (hq.commute_bar y)
  omega

theorem eq_bar_of_conj_mem (hq : EscapingQuotientData H x) {m y : EscapingQuotient x}
    (hm : m ∉ escapingImage H x) (hy : y ∈ escapingImage H x)
    (hym : m * y * m⁻¹ ∈ escapingImage H x) (hy2 : orderOf y = 2) : y = escapingBar x := by
  refine hq.eq_bar_of_mem_inf_conj hm ⟨hy, Subgroup.mem_map.mpr ⟨_, hym, ?_⟩⟩ hy2
  change m⁻¹ * (m * y * m⁻¹) * m⁻¹⁻¹ = y
  group

theorem mem_image_of_conj_mem (hq : EscapingQuotientData H x) {m y : EscapingQuotient x}
    (hy : y ∈ escapingImage H x) (hy2 : orderOf y = 2) (hne : y ≠ escapingBar x)
    (hym : m⁻¹ * y * m ∈ escapingImage H x) : m ∈ escapingImage H x := by
  by_contra hm
  have hm' : m⁻¹ ∉ escapingImage H x := fun h => hm (by simpa using (escapingImage H x).inv_mem h)
  exact hne (hq.eq_bar_of_conj_mem hm' hy (by simpa using hym) hy2)

end EscapingQuotientData

theorem exists_isConj_mk_ne_bar (hsimple : IsSimpleGroup G) (hnonab : ∃ a b : G, a * b ≠ b * a)
    {x : G} (hx : orderOf x = 2) :
    ∃ v : Subgroup.centralizer ({x} : Set G), IsConj x (v : G) ∧ orderOf (v : G) = 2 ∧
      escapingMk x v ≠ escapingBar x := by
  obtain ⟨g, hgc, hgne⟩ := exists_conj_commute_ne hsimple hnonab hx
  have hv : g * x * g⁻¹ ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hgc
  have hvx : orderOf (g * x * g⁻¹) = 2 := by
    rw [← hx]
    simpa only [MulAut.conj_apply] using (MulAut.conj g).orderOf_eq x
  refine ⟨⟨_, hv⟩, isConj_iff.mpr ⟨g, rfl⟩, hvx, fun h => hgne ?_⟩
  have hxx : x * x = 1 := by rw [← pow_two, ← hx, pow_orderOf_eq_one]
  refine escaping_eq_of_mk_eq_bar hxx (Subtype.ext ?_) h
  change g * x * g⁻¹ * (g * x * g⁻¹) = 1
  rw [← pow_two, ← hvx, pow_orderOf_eq_one]

end Escaping

end CFSG.ProperTwoGeneratedCore.Assembly
