module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.KStructure
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.ExtraspecialSub

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.TwoFi22
open scoped commutatorElement

variable {G : Type} [Group G]

theorem eq_one_or_eq_of_mem_zpowers_two {w x : G} (hw : orderOf w = 2) (hx : x ∈ zpowers w) :
    x = 1 ∨ x = w := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
  rw [← zpow_mod_orderOf, hw]
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · left
    rw [show ((2 : ℕ) : ℤ) = 2 from rfl, hk, zpow_zero]
  · right
    rw [show ((2 : ℕ) : ℤ) = 2 from rfl, hk, zpow_one]

theorem isPGroup_zpowers_two {w : G} (hw : orderOf w = 2) : IsPGroup 2 (zpowers w) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hw, pow_one])

theorem O2In_le (H : Subgroup G) : O2In H ≤ H := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem self_mem_O2In_centZ {z : G} (hz : orderOf z = 2) : z ∈ O2In (centZ z) :=
  le_O2In (V := zpowers z) (H := centZ z) (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))
    inferInstance (isPGroup_zpowers_two hz) (mem_zpowers z)

theorem center_O2In_centZ [Finite G] {z : G} (hz : orderOf z = 2)
    (hext : IsExtraspecialPGroup 2 ↥(O2In (centZ z))) :
    (center ↥(O2In (centZ z))).map (O2In (centZ z)).subtype = zpowers z := by
  have hzQ : z ∈ O2In (centZ z) := self_mem_O2In_centZ hz
  have hzc : (⟨z, hzQ⟩ : ↥(O2In (centZ z))) ∈ center ↥(O2In (centZ z)) := by
    rw [mem_center_iff]
    intro g
    have hg : (g : G) ∈ centZ z := O2In_le _ g.2
    exact Subtype.ext (mem_centralizer_singleton_iff.1 hg)
  have hle : zpowers z ≤ (center ↥(O2In (centZ z))).map (O2In (centZ z)).subtype := by
    rw [zpowers_le]
    exact ⟨_, hzc, rfl⟩
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [Subgroup.card_map_of_injective (O2In (centZ z)).subtype_injective, hext.2.2.2,
    Nat.card_zpowers, hz]

theorem factorization_two_pow_mul {a m : ℕ} (hm : ¬ 2 ∣ m) (hm0 : m ≠ 0) :
    (2 ^ a * m).factorization 2 = a := by
  rw [Nat.factorization_mul (pow_ne_zero _ (by norm_num)) hm0]
  simp [Nat.Prime.factorization_pow Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd hm]

theorem pCore_eq_of_quotient_simple {K : Type} [Group K] [Finite K] {N' : Subgroup K}
    (hn : N'.Normal) (h2 : IsPGroup 2 N') {S : Type} [Group S] (hSs : IsSimpleGroup S)
    (e : K ⧸ N' ≃* S) (hS : ¬ IsPGroup 2 S) : CFSG.pCore 2 K = N' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ (le_sSup ⟨hn, h2⟩)
  have : IsSimpleGroup (K ⧸ N') := @MulEquiv.isSimpleGroup _ _ _ _ hSs e
  have : ((CFSG.pCore 2 K).map (QuotientGroup.mk' N')).Normal :=
    Subgroup.Normal.map CFSG.pCore_normal _ (QuotientGroup.mk'_surjective N')
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 K).map (QuotientGroup.mk' N'))
    with hb | ht
  · rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hb
    exact hb
  · exfalso
    apply hS
    have hp : IsPGroup 2 (K ⧸ N') := by
      refine (CFSG.pCore_isPGroup (p := 2) (G := K)).of_surjective
        ((QuotientGroup.mk' N').comp (CFSG.pCore 2 K).subtype) ?_
      intro y
      have hy : y ∈ (CFSG.pCore 2 K).map (QuotientGroup.mk' N') := by rw [ht]; exact mem_top y
      obtain ⟨x, hx, rfl⟩ := hy
      exact ⟨⟨x, hx⟩, rfl⟩
    exact hp.of_equiv e


@[expose] noncomputable def centralizerEquivInf' {H : Subgroup G} {z : G} (hz : z ∈ H) :
    centralizer ({(⟨z, hz⟩ : ↥H)} : Set ↥H) ≃* ↥(H ⊓ centZ z) where
  toFun y := ⟨((y : H) : G), (y : H).2, mem_centralizer_singleton_iff.2
    (congrArg Subtype.val (mem_centralizer_singleton_iff.1 y.2))⟩
  invFun x := ⟨⟨(x : G), x.2.1⟩, by
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext (mem_centralizer_singleton_iff.1 x.2.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem map_centralizer_mk_subtype {H : Subgroup G} {z : G} (hz : z ∈ H) :
    (centralizer ({(⟨z, hz⟩ : ↥H)} : Set ↥H)).map H.subtype = H ⊓ centZ z := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, mem_centralizer_singleton_iff.2
      (congrArg Subtype.val (mem_centralizer_singleton_iff.1 hy))⟩
  · rintro ⟨hxH, hxz⟩
    refine ⟨⟨x, hxH⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    exact Subtype.ext (mem_centralizer_singleton_iff.1 hxz)

theorem map_O2In_centralizer_mk {H : Subgroup G} {z : G} (hz : z ∈ H) :
    (O2In (centralizer ({(⟨z, hz⟩ : ↥H)} : Set ↥H))).map H.subtype = O2In (H ⊓ centZ z) := by
  let α := centralizerEquivInf' hz
  have hα := CFSG.pCore_map_iso 2 α
  have hcomp : H.subtype.comp (centralizer ({(⟨z, hz⟩ : ↥H)} : Set ↥H)).subtype =
      (H ⊓ centZ z).subtype.comp α.toMonoidHom := rfl
  unfold O2In
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hα]

structure LocalDatum (G : Type) [Group G] [Finite G] (t z : G) : Prop where
  order_t : orderOf t = 2
  order_z : orderOf z = 2
  ne : z ≠ t
  comm : z * t = t * z
  ext : IsExtraspecialPGroup 2 ↥(O2In (centZ z))
  card_Q : Nat.card (O2In (centZ z)) = 2 ^ 25
  t_mem : t ∈ O2In (centZ z)
  shape : ∃ (N' : Subgroup ↥(centZ t ⊓ centZ z)) (_ : N'.Normal), Nat.card N' = 2 ^ 24 ∧
    Nonempty (↥(centZ t ⊓ centZ z) ⧸ N' ≃* Carrier .Co2)
  two_part : (Nat.card (centZ t)).factorization 2 = 42
  irreducible : ∀ W : Subgroup G, t ∈ W → z ∈ W → W ≤ O2In (centZ z) ⊓ centZ t →
    (∀ g ∈ centZ t ⊓ centZ z, ∀ w ∈ W, g * w * g⁻¹ ∈ W) →
    (∀ n ∈ W, n = 1 ∨ n = t ∨ n = z ∨ n = t * z) ∨ W = O2In (centZ z) ⊓ centZ t
  nonsplit : t ∈ ⁅O2In (centZ z) ⊓ centZ t, centZ t ⊓ centZ z⁆

section Main

variable [Finite G] {t z : G}

theorem LocalDatum.mem_centZ (h : LocalDatum G t z) : z ∈ centZ t :=
  mem_centralizer_singleton_iff.2 h.comm

theorem self_mem_centZ' (t : G) : t ∈ centZ t := mem_centralizer_singleton_iff.2 rfl

theorem LocalDatum.localAt_localR0 (h : LocalDatum G t z) :
    LocalAt ↥(centZ t) ⟨t, self_mem_centZ' t⟩ ⟨z, h.mem_centZ⟩ ∧
      LocalR0 ↥(centZ t) ⟨t, self_mem_centZ' t⟩ ⟨z, h.mem_centZ⟩ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht2 := h.order_t
  have hz2 := h.order_z
  have hzX := h.mem_centZ
  have htX := self_mem_centZ' t
  have hQz : O2In (centZ z) ≤ centZ z := O2In_le _
  have hZQ := center_O2In_centZ hz2 h.ext
  have htz : t ∉ (center ↥(O2In (centZ z))).map (O2In (centZ z)).subtype := by
    rw [hZQ]
    intro hmem
    rcases eq_one_or_eq_of_mem_zpowers_two hz2 hmem with h1 | h1
    · rw [h1, orderOf_one] at ht2
      omega
    · exact h.ne h1.symm
  obtain ⟨E, hEQ, hEext, hQE, hZQE, hZE, hdisj, hCE⟩ :=
    exists_centralizer_eq_prod_subgroup h.ext (by rw [h.card_Q]; norm_num) h.t_mem ht2 htz
  have hEcard : Nat.card E = 2 ^ 23 := by
    have h4 : 4 * Nat.card E = 4 * 2 ^ 23 := by
      rw [← hQE, h.card_Q]
      norm_num
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h4
  have hNE : O2In (centZ z) ⊓ centZ t = E ⊔ zpowers t := by rw [inf_comm]; exact hCE
  have hZEz : (center ↥E).map E.subtype = zpowers z := hZE.trans hZQ
  obtain ⟨N', hN'n, hN'card, ⟨eK⟩⟩ := h.shape
  have hN'2 : IsPGroup 2 N' := IsPGroup.of_card (n := 24) hN'card
  have hCo2 : ¬ IsPGroup 2 Co2 := by
    intro hp
    rw [IsPGroup.iff_card] at hp
    obtain ⟨n, hn⟩ := hp
    have h3 : 3 ∣ 2 ^ n := by
      rw [← hn, CFSG.Sporadic.Co2.card_Co2]
      norm_num
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  have hpC : CFSG.pCore 2 ↥(centZ t ⊓ centZ z) = N' :=
    pCore_eq_of_quotient_simple hN'n hN'2 CFSG.Sporadic.Co2.isSimpleGroup_Co2 eK hCo2
  have hO2K : O2In (centZ t ⊓ centZ z) = N'.map (centZ t ⊓ centZ z).subtype := by
    unfold O2In
    rw [hpC]
  have hO2card : Nat.card (O2In (centZ t ⊓ centZ z)) = 2 ^ 24 := by
    rw [hO2K, Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hN'card]
  have hNK : O2In (centZ z) ⊓ centZ t ≤ centZ t ⊓ centZ z := fun x hx => ⟨hx.2, hQz hx.1⟩
  have hNn : ((O2In (centZ z) ⊓ centZ t).subgroupOf (centZ t ⊓ centZ z)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    obtain ⟨hnQ, hnt⟩ := hn
    have hgz : (g : G) ∈ centZ z := g.2.2
    have hgt : (g : G) ∈ centZ t := g.2.1
    show (g : G) * (n : G) * (g : G)⁻¹ ∈ O2In (centZ z) ⊓ centZ t
    refine ⟨?_, (centZ t).mul_mem ((centZ t).mul_mem hgt hnt) ((centZ t).inv_mem hgt)⟩
    have := (normal_subgroupOf_O2In (centZ z)).conj_mem ⟨(n : G), hQz hnQ⟩
      (by rw [mem_subgroupOf]; exact hnQ) ⟨(g : G), hgz⟩
    exact this
  have hNp : IsPGroup 2 (O2In (centZ z) ⊓ centZ t : Subgroup G) :=
    (isPGroup_O2In _).to_le inf_le_left
  have hNle : O2In (centZ z) ⊓ centZ t ≤ O2In (centZ t ⊓ centZ z) := le_O2In hNK hNn hNp
  have hEN : E ≤ O2In (centZ z) ⊓ centZ t := by rw [hNE]; exact le_sup_left
  have htE : t ∉ E := by
    intro htE
    have := Subgroup.disjoint_def.1 hdisj htE (mem_zpowers t)
    rw [this, orderOf_one] at ht2
    omega
  have htN : t ∈ O2In (centZ z) ⊓ centZ t := ⟨h.t_mem, htX⟩
  have hNO : O2In (centZ t ⊓ centZ z) = O2In (centZ z) ⊓ centZ t := by
    symm
    refine Subgroup.eq_of_le_of_card_ge hNle ?_
    obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le hEN
    have hdvd : Nat.card (O2In (centZ z) ⊓ centZ t : Subgroup G) ∣ 2 ^ 24 :=
      hO2card ▸ Subgroup.card_dvd_of_le hNle
    rw [hc, hEcard] at hdvd
    have hc2 : c ∣ 2 := by
      have : 2 ^ 23 * c ∣ 2 ^ 23 * 2 := by simpa [pow_succ] using hdvd
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
    rcases (Nat.dvd_prime Nat.prime_two).1 hc2 with h1 | h1
    · exfalso
      rw [h1, mul_one] at hc
      have := Subgroup.eq_of_le_of_card_ge hEN (le_of_eq hc)
      exact htE (this ▸ htN)
    · rw [hO2card, hc, h1, hEcard]
      norm_num
  have hEX : E ≤ centZ t := fun x hx => (hEN hx).2
  have hCmap : (centralizer ({(⟨z, hzX⟩ : ↥(centZ t))} : Set ↥(centZ t))).map (centZ t).subtype =
      centZ t ⊓ centZ z := map_centralizer_mk_subtype hzX
  have hO2map : (O2In (centralizer ({(⟨z, hzX⟩ : ↥(centZ t))} : Set ↥(centZ t)))).map
      (centZ t).subtype = O2In (centZ z) ⊓ centZ t :=
    (map_O2In_centralizer_mk hzX).trans hNO
  have hKcard : Nat.card ↥(centZ t ⊓ centZ z) = 2 ^ 24 * 42305421312000 := by
    have hco : Nat.card (Carrier .Co2) = 42305421312000 := CFSG.Sporadic.Co2.card_Co2
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N', Nat.card_congr eK.toEquiv,
      hco, hN'card, mul_comm]
  have hzEE : z ∈ ⁅E, E⁆ := by
    have h1 : (commutator ↥E).map E.subtype = ⁅E, E⁆ := by
      rw [_root_.commutator_def, Subgroup.map_commutator]
      simp only [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [← h1, hEext.2.1, hZEz]
    exact mem_zpowers z
  have hNKle : ⁅O2In (centZ z) ⊓ centZ t, centZ t ⊓ centZ z⁆ ≤ ⁅E, centZ t ⊓ centZ z⁆ := by
    rw [Subgroup.commutator_le]
    intro n hn k hk
    have hzE : zpowers t ≤ centralizer (E : Set G) := by
      rw [zpowers_le]
      rw [mem_centralizer_iff]
      intro e he
      exact mem_centralizer_singleton_iff.1 (hEX he)
    rw [hNE] at hn
    obtain ⟨e, he, s, hs, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hzE hn
    have hsk : s * k * s⁻¹ = k := by
      obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hs
      have hkt : t * k = k * t := (mem_centralizer_singleton_iff.1 hk.1).symm
      have : (t ^ m) * k = k * t ^ m := (Commute.zpow_left (show Commute t k from hkt) m).eq
      rw [this, mul_assoc, mul_inv_cancel, mul_one]
    have : ⁅e * s, k⁆ = ⁅e, k⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      calc e * s * k * (e * s)⁻¹ * k⁻¹ = e * (s * k * s⁻¹) * e⁻¹ * k⁻¹ := by group
        _ = e * k * e⁻¹ * k⁻¹ := by rw [hsk]
    rw [this]
    exact Subgroup.commutator_mem_commutator he hk
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_centralizer_singleton_iff.1 g.2)
  · exact (Subgroup.orderOf_mk t htX).trans ht2
  · exact fun hcon => h.ne (congrArg Subtype.val hcon)
  · exact (Subgroup.orderOf_mk z hzX).trans hz2
  · have hc1 : Nat.card ↥(centralizer ({(⟨z, hzX⟩ : ↥(centZ t))} : Set ↥(centZ t))) =
        Nat.card ↥(centZ t ⊓ centZ z) := Nat.card_congr (centralizerEquivInf' hzX).toEquiv
    rw [hc1, hKcard, h.two_part, show 2 ^ 24 * 42305421312000 = 2 ^ 42 * 161382375 by norm_num]
    exact factorization_two_pow_mul (by norm_num) (by norm_num)
  · refine (Subgroup.mem_map_iff_mem (centZ t).subtype_injective).1 ?_
    rw [Subgroup.map_commutator, hO2map]
    exact Subgroup.commutator_mono hEN hEN hzEE
  · refine ⟨(QuotientGroup.congr _ _ (centralizerEquivInf' hzX) (CFSG.pCore_map_iso 2 _)).trans
      ((QuotientGroup.quotientMulEquivOfEq hpC).trans eK)⟩
  · refine ⟨E.subgroupOf (centZ t), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      rw [mem_subgroupOf] at hx
      rw [mem_centralizer_singleton_iff]
      exact Subtype.ext (mem_centralizer_singleton_iff.1 (hQz (hEQ hx)))
    · exact RankThree.PartOne.Torsion37.isExtraspecialPGroup_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe hEX).symm hEext
    · exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEX).toEquiv).trans hEcard
    · apply Subgroup.map_injective (centZ t).subtype_injective
      rw [Subgroup.map_map, MonoidHom.map_zpowers]
      have hcomp : (centZ t).subtype.comp (E.subgroupOf (centZ t)).subtype =
          E.subtype.comp (Subgroup.subgroupOfEquivOfLe hEX).toMonoidHom := rfl
      rw [hcomp, ← Subgroup.map_map, RankThree.PartOne.Torsion37.center_map_mulEquiv]
      exact hZEz
    · apply Subgroup.map_injective (centZ t).subtype_injective
      rw [hO2map, Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hEX, MonoidHom.map_zpowers]
      exact hNE
    · rw [Subgroup.disjoint_def]
      intro x hx hx'
      have h1 : (x : G) ∈ E := mem_subgroupOf.1 hx
      have h2 : (x : G) ∈ zpowers t := by
        obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hx'
        exact ⟨k, by rw [← hk]; rfl⟩
      exact Subtype.ext (Subgroup.disjoint_def.1 hdisj h1 h2)
    · refine (Subgroup.mem_map_iff_mem (centZ t).subtype_injective).1 ?_
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hEX, hCmap]
      exact hNKle h.nonsplit
  · intro W hW1 hW2 hW3
    have hW1' : zpowers (⟨z, hzX⟩ : ↥(centZ t)) ≤ W := fun x hx => hW1 (mem_sup_left hx)
    have hW1'' : zpowers (⟨t, htX⟩ : ↥(centZ t)) ≤ W := fun x hx => hW1 (mem_sup_right hx)
    have ht' : t ∈ W.map (centZ t).subtype := ⟨⟨t, htX⟩, hW1'' (mem_zpowers _), rfl⟩
    have hz' : z ∈ W.map (centZ t).subtype := ⟨⟨z, hzX⟩, hW1' (mem_zpowers _), rfl⟩
    have hle : W.map (centZ t).subtype ≤ O2In (centZ z) ⊓ centZ t := by
      rw [← hO2map]
      exact Subgroup.map_mono hW2
    have hinv : ∀ g ∈ centZ t ⊓ centZ z, ∀ w ∈ W.map (centZ t).subtype,
        g * w * g⁻¹ ∈ W.map (centZ t).subtype := by
      intro g hg w hw
      rw [← hCmap] at hg
      obtain ⟨c, hc, rfl⟩ := hg
      obtain ⟨w₀, hw₀, rfl⟩ := hw
      exact ⟨c * w₀ * c⁻¹, hW3 c hc w₀ hw₀, rfl⟩
    rcases h.irreducible (W.map (centZ t).subtype) ht' hz' hle hinv with h1 | h1
    · left
      refine le_antisymm (fun w hw => ?_) hW1
      rcases h1 _ ⟨w, hw, rfl⟩ with h2 | h2 | h2 | h2
      · have : w = 1 := Subtype.ext h2
        rw [this]
        exact one_mem _
      · have : w = ⟨t, htX⟩ := Subtype.ext h2
        rw [this]
        exact mem_sup_right (mem_zpowers _)
      · have : w = ⟨z, hzX⟩ := Subtype.ext h2
        rw [this]
        exact mem_sup_left (mem_zpowers _)
      · have : w = ⟨t, htX⟩ * ⟨z, hzX⟩ := Subtype.ext h2
        rw [this]
        exact mul_mem (mem_sup_right (mem_zpowers _)) (mem_sup_left (mem_zpowers _))
    · right
      apply Subgroup.map_injective (centZ t).subtype_injective
      rw [h1, hO2map]

end Main

end CFSG.EvenSporadicStandard.TwoB
