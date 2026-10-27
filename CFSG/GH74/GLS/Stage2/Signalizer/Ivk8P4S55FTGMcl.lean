module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55FTGMclPerm
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4Inv2
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714AltAut
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.Stage2.Local.Basic
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55FTGQuot
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8YCfgAct
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Sec
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

namespace FTG

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.ABGLocalTools CFSG.GH74.GLS.IVK.Proofs2

theorem card_dvd_sixteen_of_aut {Y : Type} [Group Y] (e : Y ≃* alternatingGroup (Fin 7))
    {E : Subgroup (MulAut Y)} (hE : IsPGroup 2 ↥E) : Nat.card E ∣ 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfin : Finite Y := Finite.of_equiv _ e.symm.toEquiv
  have hA : Nat.card (MulAut Y) = 5040 := by
    rw [Nat.card_congr (altAutEquiv (by norm_num) e).toEquiv, Nat.card_perm, Nat.card_fin]
    decide
  have : Finite (MulAut Y) := Nat.finite_of_card_ne_zero (by rw [hA]; norm_num)
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card.mp hE)
  have hd : 2 ^ a ∣ 2 ^ 4 * 315 := by
    rw [← ha, show (2 : ℕ) ^ 4 * 315 = 5040 by norm_num, ← hA]
    exact Subgroup.card_subgroup_dvd_card E
  have hc : Nat.Coprime (2 ^ a) 315 := Nat.Coprime.pow_left a (by norm_num)
  rw [ha]
  exact hc.dvd_of_dvd_mul_right hd

theorem two_pow_seven_dvd_card_S {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}
    (hctx : Stage2Ctx G z Kind.mcl S) : 2 ^ 7 ∣ Nat.card S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd := hctx.data
  cases hd with
  | mcl h =>
    obtain ⟨n, hn, hS1⟩ := h
    obtain ⟨-, hZ, ⟨eC⟩⟩ := hS1.cover
    have hAn : 2 ^ 6 ∣ Nat.card (alternatingGroup (Fin n)) := by
      rcases hn with rfl | rfl <;> rw [nat_card_alternatingGroup, Nat.card_fin] <;> decide
    have hCb : 2 ^ 7 ∣ Nat.card (CentralizerBar z) := by
      have h1 := Subgroup.card_mul_index (center (CentralizerBar z))
      rw [hZ, Subgroup.index_eq_card, Nat.card_congr eC.toEquiv] at h1
      rw [← h1, pow_succ, mul_comm (2 ^ 6) 2]
      exact Nat.mul_dvd_mul_left 2 hAn
    have hC : 2 ^ 7 ∣ Nat.card (centralizer ({z} : Set G)) :=
      hCb.trans (Subgroup.card_quotient_dvd_card _)
    obtain ⟨Q, hQ⟩ := hctx.sylow
    rw [← hQ, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    exact Q.pow_dvd_card_of_pow_dvd_card hC

variable {G : Type} [Group G] [Finite G]

theorem mk_injOn_of_two {H : Subgroup G} {A : Subgroup ↥H} (hA : IsPGroup 2 ↥A) {x y : ↥H}
    (hx : x ∈ A) (hy : y ∈ A)
    (h : QuotientGroup.mk' (pPrimeCore 2 ↥H) x = QuotientGroup.mk' (pPrimeCore 2 ↥H) y) :
    x = y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm : x⁻¹ * y ∈ pPrimeCore 2 ↥H := by
    rw [← QuotientGroup.eq]
    exact h
  have hmA : x⁻¹ * y ∈ A := mul_mem (inv_mem hx) hy
  have hodd : Odd (Nat.card ↥(pPrimeCore 2 ↥H)) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  obtain ⟨a, ha⟩ := hA ⟨_, hmA⟩
  have h1 : orderOf (⟨x⁻¹ * y, hm⟩ : ↥(pPrimeCore 2 ↥H)) ∣ 2 ^ a := by
    apply orderOf_dvd_of_pow_eq_one
    exact Subtype.ext (congrArg (fun w : ↥A => (w : ↥H)) ha)
  have h2 := orderOf_dvd_natCard (⟨x⁻¹ * y, hm⟩ : ↥(pPrimeCore 2 ↥H))
  have hcop : Nat.Coprime (2 ^ a) (Nat.card ↥(pPrimeCore 2 ↥H)) :=
    Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hodd)
  have h3 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2
  have h4 : (⟨x⁻¹ * y, hm⟩ : ↥(pPrimeCore 2 ↥H)) = 1 := orderOf_eq_one_iff.mp h3
  have h5 : x⁻¹ * y = 1 := congrArg Subtype.val h4
  exact (inv_mul_eq_one.mp h5)

theorem sbar_card {H S : Subgroup G} (hSH : S ≤ H) (hS : IsPGroup 2 ↥S) :
    Nat.card ↥(barIn H S) = Nat.card S := by
  have hA : IsPGroup 2 ↥(S.subgroupOf H) :=
    hS.of_equiv (Subgroup.subgroupOfEquivOfLe hSH).symm
  let f : ↥(S.subgroupOf H) →* HBar H :=
    (QuotientGroup.mk' (pPrimeCore 2 ↥H)).comp (S.subgroupOf H).subtype
  have hf : Function.Injective f := fun x y h =>
    Subtype.ext (mk_injOn_of_two hA x.2 y.2 h)
  have hr : f.range = barIn H S := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  rw [← hr, Nat.card_congr (MonoidHom.ofInjective hf).toEquiv.symm,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSH).toEquiv]

theorem sbar_sylow {H S : Subgroup G} (hSH : S ≤ H) (hS : IsSylowOf 2 S ⊤) :
    IsSylowOf 2 (barIn H S) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSH' : IsSylowOf 2 S H := hS.of_le hSH le_top
  rw [isSylowOf_iff] at hSH' ⊢
  obtain ⟨-, hp, hdvd⟩ := hSH'
  refine ⟨le_top, ?_, ?_⟩
  · exact (hp.of_equiv (Subgroup.subgroupOfEquivOfLe hSH).symm).map _
  · rw [Subgroup.relIndex_top_right]
    intro h2
    apply hdvd
    exact h2.trans (Subgroup.index_map_dvd (S.subgroupOf H) (QuotientGroup.mk'_surjective _))

theorem card_alt_seven_dvd {J : Type} [Group J] (eJ : (J ⧸ center J) ≃* alternatingGroup (Fin 7)) :
    Nat.card (J ⧸ center J) = 2520 := by
  rw [Nat.card_congr eJ.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem four_dvd_card_R1 {z : G} {S : Subgroup G} (hctx : Stage2Ctx G z Kind.mcl S)
    {H : Subgroup G} (hSH : S ≤ H) {J : Subgroup (HBar H)} (hJ : IsComponent J)
    (eJ : (↥J ⧸ center ↥J) ≃* alternatingGroup (Fin 7)) :
    4 ∣ Nat.card ↥(barIn H S ⊓ centralizer (J : Set (HBar H))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Sb, hSb⟩ : ∃ Sb, Sb = barIn H S := ⟨_, rfl⟩
  rw [← hSb]
  have hS2 : IsPGroup 2 ↥S := hctx.sylow_top.isPGroup
  have hcard : Nat.card Sb = Nat.card S := hSb ▸ sbar_card hSH hS2
  have h128 : 2 ^ 7 ∣ Nat.card Sb := hcard ▸ two_pow_seven_dvd_card_S hctx
  have hSyl : IsSylowOf 2 Sb ⊤ := hSb ▸ sbar_sylow hSH hctx.sylow_top
  have hSb2 : IsPGroup 2 ↥Sb := hSyl.isPGroup
  have hT0 : IsSylowOf 2 (Sb ⊓ J) J := YCfg.isSylowOf_inf_isSubnormal_top hSyl hJ.2
  have h8J : 2 ^ 3 ∣ Nat.card J := by
    have h1 := Subgroup.card_mul_index (center ↥J)
    rw [Subgroup.index_eq_card, card_alt_seven_dvd eJ] at h1
    rw [← h1]
    exact Dvd.dvd.mul_left (by norm_num) _
  have h8 : 2 ^ 3 ∣ Nat.card ↥(Sb ⊓ J) := by
    obtain ⟨Q, hQ⟩ := hT0
    rw [← hQ, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    exact Q.pow_dvd_card_of_pow_dvd_card h8J
  have hperf : Group.IsPerfect ↥J := hJ.1.1
  by_cases hN : Sb ≤ normalizer (J : Set (HBar H))
  · let f : ↥Sb →* MulAut (↥J ⧸ center ↥J) := (YCfg.yAct J).comp (Subgroup.inclusion hN)
    have hker : f.ker = (centralizer (J : Set (HBar H))).subgroupOf Sb := by
      ext s
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      exact YCfg.yAct_eq_one_iff J _
    have hrange : Nat.card f.range ∣ 16 :=
      card_dvd_sixteen_of_aut eJ (hSb2.of_surjective f.rangeRestrict f.rangeRestrict_surjective)
    have h1 := Subgroup.card_mul_index f.ker
    rw [Subgroup.index_ker, hker] at h1
    have hR : Nat.card ↥((centralizer (J : Set (HBar H))).subgroupOf Sb) =
        Nat.card ↥(Sb ⊓ centralizer (J : Set (HBar H))) := by
      rw [← Subgroup.card_map_of_injective Sb.subtype_injective,
        Subgroup.subgroupOf_map_subtype, inf_comm]
    rw [hR] at h1
    rw [← h1] at h128
    have h3 : 2 ^ 3 * 16 ∣ Nat.card ↥(Sb ⊓ centralizer (J : Set (HBar H))) * 16 := by
      have h4 := h128.trans (Nat.mul_dvd_mul_left
        (Nat.card ↥(Sb ⊓ centralizer (J : Set (HBar H)))) hrange)
      norm_num at h4 ⊢
      exact h4
    have h2 := Nat.dvd_of_mul_dvd_mul_right (by norm_num : 0 < 16) h3
    exact Nat.dvd_trans (by norm_num : 4 ∣ 2 ^ 3) h2
  · obtain ⟨s, hs, hsN⟩ := Set.not_subset.mp hN
    set J' : Subgroup (HBar H) := J.map (MulAut.conj s).toMonoidHom with hJ'def
    have hJ' : IsComponent J' := CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj s) hJ
    have hne : J' ≠ J := fun h => hsN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
    rcases CFSG.LocalCores.distinct_components_commute hJ' hJ with h | h
    · exact absurd h hne
    · have hJ'C : J' ≤ centralizer (J : Set (HBar H)) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
      have hle : (Sb ⊓ J).map (MulAut.conj s).toMonoidHom ≤
          Sb ⊓ centralizer (J : Set (HBar H)) := by
        rintro _ ⟨x, ⟨hxS, hxJ⟩, rfl⟩
        refine ⟨?_, hJ'C ⟨x, hxJ, rfl⟩⟩
        show s * x * s⁻¹ ∈ Sb
        exact mul_mem (mul_mem hs hxS) (inv_mem hs)
      have hc : Nat.card ↥((Sb ⊓ J).map (MulAut.conj s).toMonoidHom) = Nat.card ↥(Sb ⊓ J) :=
        Subgroup.card_map_of_injective (MulAut.conj s).injective
      have hd := Subgroup.card_dvd_of_le hle
      rw [hc] at hd
      exact (Nat.dvd_trans (by norm_num : 4 ∣ 2 ^ 3) h8).trans hd

theorem exists_u_r {B : Type*} [Group B] [Finite B] {R1 : Subgroup B}
    (h4 : 4 ∣ Nat.card R1) :
    ∃ u ∈ R1, ∃ r ∈ R1, orderOf u = 2 ∧ r ∉ zpowers u ∧ r ^ 2 ∈ zpowers u ∧ r * u = u * r := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 2 (n := 2) (G := ↥R1)
    (by simpa using h4)
  obtain ⟨u, r, hu, hr, hr2, hur⟩ := exists_pair_of_card_four (Q := ↥K) (by rw [hK]; norm_num)
  refine ⟨((u : ↥R1) : B), (u : ↥R1).2, ((r : ↥R1) : B), (r : ↥R1).2, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hu
  · intro hmem
    apply hr
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine Subgroup.mem_zpowers_iff.mpr ⟨m, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    simpa using hm
  · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hr2
    refine Subgroup.mem_zpowers_iff.mpr ⟨m, ?_⟩
    have := congrArg (fun w : ↥K => ((w : ↥R1) : B)) hm
    simpa using this
  · have := congrArg (fun w : ↥K => ((w : ↥R1) : B)) hur
    simpa using this

theorem eq_one_of_two_elem {K : Type*} [Group K] [Finite K] {N : Subgroup K}
    (hN : Odd (Nat.card N)) {x : K} (hx : x ∈ N) {a : ℕ} (ha : x ^ (2 ^ a) = 1) : x = 1 := by
  have h1 : orderOf (⟨x, hx⟩ : ↥N) ∣ 2 ^ a :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using ha))
  have h2 := orderOf_dvd_natCard (⟨x, hx⟩ : ↥N)
  have hcop : Nat.Coprime (2 ^ a) (Nat.card N) :=
    Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hN)
  have h3 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2
  exact congrArg Subtype.val (orderOf_eq_one_iff.mp h3)

theorem false_of_mcl_alt7 {z : G} {S : Subgroup G} (hctx : Stage2Ctx G z Kind.mcl S)
    {H : Subgroup G} (hSH : S ≤ H) {J : Subgroup (HBar H)} (hJ : IsComponent J)
    (eJ : (↥J ⧸ center ↥J) ≃* alternatingGroup (Fin 7)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd := hctx.data
  cases hd with
  | mcl hS =>
  obtain ⟨n, hn, hS1⟩ := hS
  obtain ⟨-, hCZ, ⟨eC⟩⟩ := hS1.cover
  obtain ⟨u0, hu0, r0, hr0, hu2, hrn, hr2, hur⟩ :=
    exists_u_r (four_dvd_card_R1 hctx hSH hJ eJ)
  have hS2 : IsPGroup 2 ↥S := hctx.sylow_top.isPGroup
  have hA : IsPGroup 2 ↥(S.subgroupOf H) :=
    hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSH).symm
  set q : ↥H →* HBar H := QuotientGroup.mk' (pPrimeCore 2 ↥H) with hq
  obtain ⟨ut, hutS, hut⟩ := hu0.1
  obtain ⟨rt, hrtS, hrt⟩ := hr0.1
  have hinj : ∀ {x y : ↥H}, x ∈ S.subgroupOf H → y ∈ S.subgroupOf H → q x = q y → x = y :=
    fun hx hy h => mk_injOn_of_two hA hx hy h
  have hu0sq : u0 ^ 2 = 1 := by
    have := pow_orderOf_eq_one u0
    rwa [hu2] at this
  have hut2 : ut ^ 2 = 1 :=
    hinj (pow_mem hutS 2) (one_mem _) (by rw [map_pow, hut, hu0sq, map_one])
  have hut1 : ut ≠ 1 := by
    intro h
    rw [h, map_one] at hut
    rw [← hut, orderOf_one] at hu2
    norm_num at hu2
  have hcomm : rt * ut = ut * rt :=
    hinj (mul_mem hrtS hutS) (mul_mem hutS hrtS) (by rw [map_mul, map_mul, hut, hrt, hur])
  have hrtn : rt ∉ zpowers ut := by
    intro h
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h
    apply hrn
    exact Subgroup.mem_zpowers_iff.mpr ⟨m, by rw [← hut, ← map_zpow, hm, hrt]⟩
  have hrt2 : rt ^ 2 ∈ zpowers ut := by
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hr2
    refine Subgroup.mem_zpowers_iff.mpr ⟨m, hinj (zpow_mem hutS m) (pow_mem hrtS 2) ?_⟩
    rw [map_zpow, map_pow, hut, hrt, hm]
  set R : Subgroup ↥H := zpowers ut ⊔ zpowers rt with hRdef
  have hRS : R ≤ S.subgroupOf H :=
    sup_le (Subgroup.zpowers_le.mpr hutS) (Subgroup.zpowers_le.mpr hrtS)
  have hR2 : IsPGroup 2 ↥R := hA.to_le hRS
  have hodd : Odd (Nat.card ↥(pPrimeCore 2 ↥H)) :=
    Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hcen := centralizer_map_mk_eq (pPrimeCore 2 ↥H) hodd R hR2
  have hRmap : R.map q = zpowers u0 ⊔ zpowers r0 := by
    rw [hRdef, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers, hut, hrt]
  have hJR : J ≤ centralizer ((R.map q : Subgroup (HBar H)) : Set (HBar H)) := by
    rw [hRmap, Subgroup.le_centralizer_iff]
    exact sup_le (Subgroup.zpowers_le.mpr hu0.2) (Subgroup.zpowers_le.mpr hr0.2)
  rw [hcen] at hJR
  set X0 : Subgroup ↥H := centralizer (R : Set ↥H) ⊓ J.comap q with hX0
  have hX0J : ∀ j ∈ J, ∃ x : ↥X0, q x = j := by
    intro j hj
    obtain ⟨w, hw, hwj⟩ := hJR hj
    exact ⟨⟨w, hw, by show q w ∈ J; rw [hwj]; exact hj⟩, hwj⟩
  set t : G := (ut : G) with ht
  have ht2 : orderOf t = 2 := by
    rw [ht, Subgroup.orderOf_coe]
    exact orderOf_eq_prime hut2 hut1
  obtain ⟨c0, hc0⟩ := isConj_iff.mp (hS1.one_class z t hctx.orderOf_z ht2)
  have hκmem : ∀ w : G, w ∈ centralizer ({t} : Set G) → c0⁻¹ * w * c0 ∈ Cen z := by
    intro w hw
    rw [Subgroup.mem_centralizer_singleton_iff] at hw ⊢
    rw [← hc0] at hw
    calc c0⁻¹ * w * c0 * z = c0⁻¹ * (w * (c0 * z * c0⁻¹)) * c0 := by group
      _ = c0⁻¹ * ((c0 * z * c0⁻¹) * w) * c0 := by rw [hw]
      _ = z * (c0⁻¹ * w * c0) := by group
  let κ : ↥(centralizer ({t} : Set G)) →* ↥(Cen z) :=
    { toFun := fun w => ⟨c0⁻¹ * w * c0, hκmem w w.2⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp [mul_assoc] }
  have hκv : ∀ w, ((κ w : ↥(Cen z)) : G) = c0⁻¹ * w * c0 := fun _ => rfl
  have hκinj : Function.Injective κ := by
    intro x y h
    have := congrArg Subtype.val h
    simp only [hκv] at this
    exact Subtype.ext (by simpa using this)
  set bar : ↥(Cen z) →* CentralizerBar z := QuotientGroup.mk' (pPrimeCore 2 ↥(Cen z)) with hbar
  let ψ : ↥(centralizer ({t} : Set G)) →* alternatingGroup (Fin n) :=
    eC.toMonoidHom.comp ((QuotientGroup.mk' (center (CentralizerBar z))).comp (bar.comp κ))
  have hψ1 : ∀ w, ψ w = 1 ↔ bar (κ w) ∈ center (CentralizerBar z) := by
    intro w
    show eC (QuotientGroup.mk (bar (κ w))) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hzC : z ∈ Cen z := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hz2G : z ^ 2 = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hctx.orderOf_z] at this
  have hz2 : (⟨z, hzC⟩ : ↥(Cen z)) ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hz2G)
  set zb : CentralizerBar z := bar ⟨z, hzC⟩ with hzb
  have hzb_cen : zb ∈ center (CentralizerBar z) := by
    rw [Subgroup.mem_center_iff]
    intro v
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective v
    rw [hzb]
    show (QuotientGroup.mk y : CentralizerBar z) * QuotientGroup.mk ⟨z, hzC⟩ =
      QuotientGroup.mk ⟨z, hzC⟩ * QuotientGroup.mk y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp y.2)
  have hoddC : Odd (Nat.card ↥(pPrimeCore 2 ↥(Cen z))) :=
    Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hzb1 : zb ≠ 1 := by
    intro h
    have hm : (⟨z, hzC⟩ : ↥(Cen z)) ∈ pPrimeCore 2 ↥(Cen z) :=
      (QuotientGroup.eq_one_iff _).mp h
    have h1 := eq_one_of_two_elem hoddC hm (a := 1) (by rw [pow_one]; exact hz2)
    have h2 : z = 1 := congrArg Subtype.val h1
    have := hctx.orderOf_z
    rw [h2, orderOf_one] at this
    norm_num at this
  have hZeq : center (CentralizerBar z) = zpowers zb := by
    symm
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzb_cen)
    rw [hCZ, Nat.card_zpowers]
    have hzb2 : zb ^ 2 = 1 := by rw [hzb, ← map_pow, hz2, map_one]
    have := orderOf_eq_prime hzb2 hzb1
    rw [this]
  have hker2 : ∀ w : ↥(centralizer ({t} : Set G)), ψ w = 1 → ∀ a : ℕ, w ^ (2 ^ a) = 1 →
      (w : G) = 1 ∨ (w : G) = t := by
    intro w hw a ha
    rw [hψ1, hZeq] at hw
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hzb2 : zb ^ 2 = 1 := by rw [hzb, ← map_pow, hz2, map_one]
    have hzbo : orderOf zb = 2 := orderOf_eq_prime hzb2 hzb1
    have hm2 : zb ^ m = 1 ∨ zb ^ m = zb := by
      rw [← zpow_mod_orderOf, hzbo]
      rcases Int.emod_two_eq_zero_or_one m with h0 | h1
      · left
        rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h0, zpow_zero]
      · right
        rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h1, zpow_one]
    have hκa : (κ w) ^ (2 ^ a) = 1 := by rw [← map_pow, ha, map_one]
    rcases hm2 with h | h
    · left
      rw [h] at hm
      have hk : κ w ∈ pPrimeCore 2 ↥(Cen z) := (QuotientGroup.eq_one_iff _).mp hm.symm
      have := eq_one_of_two_elem hoddC hk hκa
      have hw1 : w = 1 := hκinj (by rw [this, map_one])
      rw [hw1]
      rfl
    · right
      rw [h] at hm
      have hk : κ w * (⟨z, hzC⟩ : ↥(Cen z))⁻¹ ∈ pPrimeCore 2 ↥(Cen z) := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
        change bar (κ w) * (bar ⟨z, hzC⟩)⁻¹ = 1
        rw [← hm, mul_inv_cancel]
      have hcz : κ w * (⟨z, hzC⟩ : ↥(Cen z)) = (⟨z, hzC⟩ : ↥(Cen z)) * κ w :=
        Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (κ w).2)
      have hpow : (κ w * (⟨z, hzC⟩ : ↥(Cen z))⁻¹) ^ (2 ^ (a + 1)) = 1 := by
        have hc' : Commute (κ w) ((⟨z, hzC⟩ : ↥(Cen z))⁻¹) :=
          (Commute.inv_right hcz)
        have e1 : (κ w) ^ (2 ^ (a + 1)) = 1 := by rw [pow_succ, pow_mul, hκa, one_pow]
        have e2 : ((⟨z, hzC⟩ : ↥(Cen z))⁻¹) ^ (2 ^ (a + 1)) = 1 := by
          rw [pow_succ, mul_comm, pow_mul, inv_pow, hz2, inv_one, one_pow]
        rw [hc'.mul_pow, e1, e2, one_mul]
      have h1 := eq_one_of_two_elem hoddC hk hpow
      have h2 : κ w = ⟨z, hzC⟩ := mul_inv_eq_one.mp h1
      have h3 := congrArg Subtype.val h2
      rw [hκv] at h3
      calc (w : G) = c0 * (c0⁻¹ * w * c0) * c0⁻¹ := by group
        _ = c0 * z * c0⁻¹ := by rw [h3]
        _ = t := hc0
  have htC : t ∈ centralizer ({t} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hrC : (rt : G) ∈ centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val hcomm
  set tt : ↥(centralizer ({t} : Set G)) := ⟨t, htC⟩ with htt
  set rr : ↥(centralizer ({t} : Set G)) := ⟨(rt : G), hrC⟩ with hrr
  set c : alternatingGroup (Fin n) := ψ rr with hc
  have hψt : ψ tt = 1 := by
    rw [hψ1]
    have : κ tt = ⟨z, hzC⟩ := Subtype.ext (by
      rw [hκv]
      show c0⁻¹ * t * c0 = z
      rw [← hc0]
      group)
    rw [this]
    exact hzb_cen
  obtain ⟨a, ha⟩ := hS2 ⟨(rt : G), hrtS⟩
  have hrr2a : rr ^ (2 ^ a) = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow]
    have := congrArg Subtype.val ha
    rwa [Subgroup.coe_pow] at this)
  have hc1 : c ≠ 1 := by
    intro h
    rcases hker2 rr h a hrr2a with h1 | h1
    · apply hrtn
      have : rt = 1 := Subtype.ext h1
      rw [this]
      exact one_mem _
    · apply hrtn
      have : rt = ut := Subtype.ext h1
      rw [this]
      exact Subgroup.mem_zpowers ut
  have hc2 : c * c = 1 := by
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hrt2
    have hrr2 : rr ^ 2 = tt ^ m := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_zpow]
      show (rt : G) ^ 2 = (ut : G) ^ m
      rw [← Subgroup.coe_pow, ← Subgroup.coe_zpow, hm])
    rw [← pow_two, hc, ← map_pow, hrr2, map_zpow, hψt, one_zpow]
  have hX0C : ∀ x : ↥X0, ((x : ↥H) : G) ∈ centralizer ({t} : Set G) := by
    intro x
    have hu : ut ∈ R := Subgroup.mem_sup_left (Subgroup.mem_zpowers ut)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp x.2.1 ut hu).symm
  let ιX : ↥X0 →* ↥(centralizer ({t} : Set G)) :=
    { toFun := fun x => ⟨((x : ↥H) : G), hX0C x⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hιX : Function.Injective ιX := fun x y h => by
    have := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext this)
  let ψX : ↥X0 →* alternatingGroup (Fin n) := ψ.comp ιX
  have hcX : ∀ x : ↥X0, ψX x * c = c * ψX x := by
    intro x
    have hr : rt ∈ R := Subgroup.mem_sup_right (Subgroup.mem_zpowers rt)
    have h1 := Subgroup.mem_centralizer_iff.mp x.2.1 rt hr
    have h2 : ιX x * rr = rr * ιX x := Subtype.ext (by
      have := congrArg Subtype.val h1.symm
      exact this)
    show ψ (ιX x) * ψ rr = ψ rr * ψ (ιX x)
    rw [← map_mul, ← map_mul, h2]
  let qX : ↥X0 →* ↥J := (q.comp X0.subtype).codRestrict J (fun x => x.2.2)
  have hqX : Function.Surjective qX := by
    intro j
    obtain ⟨x, hx⟩ := hX0J j j.2
    exact ⟨x, Subtype.ext hx⟩
  let φ1 : ↥X0 →* alternatingGroup (Fin 7) :=
    eJ.toMonoidHom.comp ((QuotientGroup.mk' (center ↥J)).comp qX)
  have hφ1 : Function.Surjective φ1 :=
    eJ.surjective.comp ((QuotientGroup.mk'_surjective _).comp hqX)
  have hkerψ : Nat.card ψ.ker ∣ 2 * Nat.card ↥(pPrimeCore 2 ↥(Cen z)) := by
    have hle : ψ.ker.map κ ≤ (center (CentralizerBar z)).comap bar := by
      rintro _ ⟨w, hw, rfl⟩
      exact (hψ1 w).mp hw
    have h1 := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective hκinj,
      card_comap_center (QuotientGroup.mk'_surjective (pPrimeCore 2 ↥(Cen z))), hCZ,
      QuotientGroup.ker_mk'] at h1
    exact h1
  have hkX : Nat.card ψX.ker ∣ Nat.card ψ.ker := by
    have hkerX : ψX.ker.map ιX ≤ ψ.ker := by
      rintro _ ⟨x, hx, rfl⟩
      exact hx
    have := Subgroup.card_dvd_of_le hkerX
    rwa [Subgroup.card_map_of_injective hιX] at this
  have hcard7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hle1 : ψX.ker ≤ φ1.ker := by
    have hnorm : (ψX.ker.map φ1).Normal := (MonoidHom.normal_ker ψX).map φ1 hφ1
    have hs : IsSimpleGroup (alternatingGroup (Fin 7)) :=
      alternatingGroup.isSimpleGroup (by norm_num)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (ψX.ker.map φ1) with h | h
    · exact (Subgroup.map_eq_bot_iff _).mp h
    · exfalso
      have h1 : Nat.card (alternatingGroup (Fin 7)) ∣ Nat.card ψX.ker := by
        have := Subgroup.card_map_dvd ψX.ker φ1
        rwa [h, Subgroup.card_top] at this
      rw [hcard7] at h1
      have h4 : 4 ∣ 2 * Nat.card ↥(pPrimeCore 2 ↥(Cen z)) :=
        (Nat.dvd_trans (by norm_num : 4 ∣ 2520) h1).trans (hkX.trans hkerψ)
      obtain ⟨j, hj⟩ := hoddC
      rw [hj] at h4
      omega
  have hXc : 2520 ≤ Nat.card ψX.range := by
    have e1 := Subgroup.card_mul_index ψX.ker
    rw [Subgroup.index_ker] at e1
    have e2 := Subgroup.card_mul_index φ1.ker
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hφ1, Subgroup.card_top, hcard7] at e2
    have hle := Subgroup.card_le_of_le hle1
    by_contra hlt
    push Not at hlt
    have := Nat.mul_lt_mul_of_le_of_lt hle hlt (Nat.card_pos (α := ↥φ1.ker))
    rw [e1, e2] at this
    exact lt_irrefl _ this
  have hXlt : Nat.card ψX.range < 2520 := by
    have hle : ψX.range.map (alternatingGroup (Fin n)).subtype ≤
        centralizer ({(c : Equiv.Perm (Fin n))} : Set (Equiv.Perm (Fin n))) := by
      rintro _ ⟨y, ⟨x, rfl⟩, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (hcX x)
    have h1 := Subgroup.card_le_of_le hle
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)] at h1
    have hn9 : n ≤ 9 := by rcases hn with rfl | rfl <;> norm_num
    refine lt_of_le_of_lt h1 (card_centralizer_lt_of_even_involution hn9 ?_ ?_ ?_)
    · exact congrArg Subtype.val hc2
    · intro h
      exact hc1 (Subtype.ext h)
    · exact Equiv.Perm.mem_alternatingGroup.mp c.2
  omega

end FTG

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
