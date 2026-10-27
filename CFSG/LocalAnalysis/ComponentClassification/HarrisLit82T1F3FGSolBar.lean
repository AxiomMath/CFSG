module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3FGSolTools
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1RowAltBar
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1RowAltImage
public import CFSG.ClassicalInvolution.Q3.Tight
public import CFSG.LieType.HighestRoot.CentLinearBasic
public import CFSG.Adapters.QiuzhenLegacy.FeitThompson.GroupAction.Quotient

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.F3FG

open CFSG Subgroup
open scoped MatrixGroups commutatorElement

@[expose] def barY (G : Type) [Group G] : Subgroup (G ⧸ pPrimeCore 2 G) :=
  (GH74.GLS.oPrimeResidual 2 G).map (QuotientGroup.mk' (pPrimeCore 2 G))

@[expose] def barZ (G : Type) [Group G] : Subgroup (G ⧸ pPrimeCore 2 G) :=
  (center ↥(barY G)).map (barY G).subtype

variable {G : Type} [Group G] [Finite G]

theorem mem_of_two_pow_of_odd_index {X : Type*} [Group X] (N : Subgroup X) [N.Normal]
    (hN : Odd N.index) {x : X} (hx : ∃ n : ℕ, x ^ 2 ^ n = 1) : x ∈ N := by
  obtain ⟨n, hn⟩ := hx
  have h1 : orderOf (QuotientGroup.mk x : X ⧸ N) ∣ 2 ^ n := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← QuotientGroup.mk_pow, hn, QuotientGroup.mk_one]
  have h2 : orderOf (QuotientGroup.mk x : X ⧸ N) ∣ N.index := orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ n) N.index := Nat.Coprime.pow_left n (Nat.coprime_two_left.2 hN)
  have h3 : orderOf (QuotientGroup.mk x : X ⧸ N) = 1 :=
    (hcop.coprime_dvd_left h1).eq_one_of_dvd h2
  exact (QuotientGroup.eq_one_iff x).1 (orderOf_eq_one_iff.1 h3)

theorem subsingleton_of_isPerfect_of_isSolvable {X : Type*} [Group X] [Group.IsPerfect X]
    [Group.IsSolvable X] : Subsingleton X := by
  obtain ⟨n, hn⟩ := (Group.isSolvable_def X).mp inferInstance
  have htop : ∀ k, derivedSeries X k = ⊤ := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [derivedSeries_succ, ih]
      exact Group.IsPerfect.commutator_eq_top
  rw [htop n] at hn
  refine ⟨fun a b => ?_⟩
  have ha : a ∈ (⊥ : Subgroup X) := hn ▸ mem_top a
  have hb : b ∈ (⊥ : Subgroup X) := hn ▸ mem_top b
  rw [mem_bot] at ha hb
  rw [ha, hb]

omit [Finite G] in
theorem barY_normal : (barY G).Normal :=
  (oPrimeResidual_two_normal (G := G)).map _ (QuotientGroup.mk'_surjective _)

theorem odd_index_barY : Odd (barY G).index := by
  have h := Subgroup.index_map_dvd (H := GH74.GLS.oPrimeResidual 2 G)
    (QuotientGroup.mk'_surjective (pPrimeCore 2 G))
  exact Odd.of_dvd_nat odd_index_oPrimeResidual_two h

theorem nonempty_barY_equiv :
    Nonempty (↥(GH74.GLS.oPrimeResidual 2 G) ⧸ pPrimeCore 2 ↥(GH74.GLS.oPrimeResidual 2 G) ≃*
      ↥(barY G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := GH74.GLS.oPrimeResidual 2 G with hYdef
  have hYn : Y.Normal := oPrimeResidual_two_normal
  set φ : ↥Y →* G ⧸ pPrimeCore 2 G := (QuotientGroup.mk' (pPrimeCore 2 G)).comp Y.subtype
    with hφ
  have hφk : φ.ker = pPrimeCore 2 ↥Y := by
    rw [CatalogueBHeldSmallCore.primeCore_subnormal_intersection 2 Y
      (Subgroup.Normal.isSubnormal hYn), hφ, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    rfl
  have hr : φ.range = barY G := by
    rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hφk.symm).trans
    (QuotientGroup.quotientKerEquivRange φ)).trans (MulEquiv.subgroupCongr hr)⟩

theorem isQuasisimple_barY (hY : IsTwoQuasisimple ↥(GH74.GLS.oPrimeResidual 2 G)) :
    IsQuasisimple ↥(barY G) := by
  obtain ⟨e⟩ := nonempty_barY_equiv (G := G)
  exact LocalCores.isQuasisimple_of_mulEquiv e hY.2

theorem pPrimeCore_barY : pPrimeCore 2 ↥(barY G) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := barY_normal (G := G)
  have h := CatalogueBHeldSmallCore.primeCore_subnormal_intersection 2 (barY G)
    (Subgroup.Normal.isSubnormal inferInstance)
  rw [h, pPrimeCore_quotient_pPrimeCore_eq_bot 2]
  exact Subgroup.bot_subgroupOf _

omit [Finite G] in
theorem mem_barZ_iff {x : G ⧸ pPrimeCore 2 G} :
    x ∈ barZ G ↔ x ∈ barY G ∧ ∀ y ∈ barY G, y * x = x * y := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨c.2, fun y hy => ?_⟩
    exact congrArg Subtype.val (mem_center_iff.mp hc ⟨y, hy⟩)
  · rintro ⟨hx, h⟩
    refine ⟨⟨x, hx⟩, mem_center_iff.mpr fun g => Subtype.ext (h g g.2), rfl⟩

omit [Finite G] in
theorem barZ_normal : (barZ G).Normal := by
  have := barY_normal (G := G)
  refine ⟨fun x hx g => ?_⟩
  rw [mem_barZ_iff] at hx ⊢
  refine ⟨(barY_normal).conj_mem x hx.1 g, fun y hy => ?_⟩
  have hy' : g⁻¹ * y * g ∈ barY G := by
    simpa using (barY_normal).conj_mem y hy g⁻¹
  have h1 := hx.2 _ hy'
  calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
    _ = g * x * g⁻¹ * y := by group

theorem isPGroup_barZ : IsPGroup 2 ↥(barZ G) :=
  (N36.center_isPGroup (pPrimeCore_barY (G := G))).map (barY G).subtype

theorem centralizer_barY_le :
    centralizer (barY G : Set (G ⧸ pPrimeCore 2 G)) ≤ barZ G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := barY_normal (G := G)
  have hc : ∀ x ∈ centralizer (barY G : Set (G ⧸ pPrimeCore 2 G)), x ∈ barY G → x ∈ barZ G :=
    fun x hx hxY => mem_barZ_iff.mpr ⟨hxY, fun y hy => mem_centralizer_iff.mp hx y hy⟩
  have hle := RowAlt.centralizer_le_of_odd_index (pPrimeCore_quotient_pPrimeCore_eq_bot 2)
    odd_index_barY (fun x hx hxY => by
      obtain ⟨k, hk⟩ := isPGroup_barZ (G := G) ⟨x, hc x hx hxY⟩
      exact ⟨k, congrArg Subtype.val hk⟩)
  exact fun x hx => hc x hx (hle hx)

theorem mem_barY_of_two_pow {x : G ⧸ pPrimeCore 2 G} (hx : ∃ n : ℕ, x ^ 2 ^ n = 1) :
    x ∈ barY G := by
  have := barY_normal (G := G)
  exact mem_of_two_pow_of_odd_index _ odd_index_barY hx

section L

variable {z : G} {L : Subgroup G}

omit [Finite G] in
theorem mk_mem_barY (hz : orderOf z = 2) : QuotientGroup.mk' (pPrimeCore 2 G) z ∈ barY G :=
  mem_map_of_mem _ (subset_closure ⟨1, by rw [pow_one, ← hz, pow_orderOf_eq_one]⟩)

theorem orderOf_mk_z (hz : orderOf z = 2) : orderOf (QuotientGroup.mk' (pPrimeCore 2 G) z) = 2 :=
  UnbalancedLayer.orderOf_mk_eq_two (odd_card_pPrimeCore_two G) hz

theorem barL_subnormal (hz : orderOf z = 2) (hL : IsSolvableTwoComponentIn L (centralizer {z})) :
    L.map (QuotientGroup.mk' (pPrimeCore 2 G)) ≤
        centralizer {QuotientGroup.mk' (pPrimeCore 2 G) z} ∧
      ((L.map (QuotientGroup.mk' (pPrimeCore 2 G))).subgroupOf
        (centralizer {QuotientGroup.mk' (pPrimeCore 2 G) z})).IsSubnormal := by
  set ρ := QuotientGroup.mk' (pPrimeCore 2 G) with hρ
  have htt : z * z = 1 := by rw [← sq, ← hz, pow_orderOf_eq_one]
  have hC := UnbalancedLayer.map_centralizer_eq (odd_card_pPrimeCore_two G) htt
  set C := centralizer ({z} : Set G)
  set Cb := centralizer ({ρ z} : Set (G ⧸ pPrimeCore 2 G))
  have hle : L.map ρ ≤ Cb := hC ▸ map_mono hL.1
  refine ⟨hle, ?_⟩
  let γ : ↥C →* ↥Cb :=
    (ρ.comp C.subtype).codRestrict Cb (fun c => hC ▸ mem_map_of_mem ρ c.2)
  have hγs : Function.Surjective γ := by
    rintro ⟨y, hy⟩
    rw [← hC] at hy
    obtain ⟨c, hc, rfl⟩ := hy
    exact ⟨⟨c, hc⟩, rfl⟩
  have h1 := Subgroup.IsSubnormal.map hγs hL.2.1
  convert h1 using 1
  ext ⟨y, hy⟩
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨⟨l, hL.1 hl⟩, hl, rfl⟩
  · rintro ⟨c, hc, hcy⟩
    exact ⟨c, hc, congrArg Subtype.val hcy⟩

theorem nonempty_barL_equiv (eL : ↥L ⧸ pPrimeCore 2 ↥L ≃* SL(2, ZMod 3)) :
    Nonempty (↥(L.map (QuotientGroup.mk' (pPrimeCore 2 G))) ⧸
      pPrimeCore 2 ↥(L.map (QuotientGroup.mk' (pPrimeCore 2 G))) ≃* SL(2, ZMod 3)) := by
  obtain ⟨eLb⟩ := GSThmB.OddQuot.nonempty_pPrimeCore_equiv_of_surjective
    ((QuotientGroup.mk' (pPrimeCore 2 G)).subgroupMap L) (MonoidHom.subgroupMap_surjective _ _)
    (RowAlt.not_two_dvd_card_ker_bar L)
  exact ⟨eLb.symm.trans eL⟩

theorem mul_self_eq_one_of_orderOf {X : Type*} [Group X] {x : X} (h : orderOf x = 2) :
    x * x = 1 := by
  have h1 := pow_orderOf_eq_one x
  rw [h, sq] at h1
  exact h1

theorem false_of_mem_pPrimeCore {X : Type} [Group X] [Finite X] {w : X}
    (hO : w ∈ pPrimeCore 2 X) (hw : orderOf w = 2) : False := by
  have h1 := Subgroup.orderOf_dvd_natCard _ hO
  rw [hw] at h1
  exact (Nat.not_even_iff_odd.mpr (odd_card_pPrimeCore_two _)) (even_iff_two_dvd.mpr h1)

theorem false_of_mk_mem_barZ (hY : IsTwoQuasisimple ↥(GH74.GLS.oPrimeResidual 2 G))
    (hz : orderOf z = 2) (hL : IsSolvableTwoComponentIn L (centralizer {z}))
    (eL : ↥L ⧸ pPrimeCore 2 ↥L ≃* SL(2, ZMod 3))
    (hc : QuotientGroup.mk' (pPrimeCore 2 G) z ∈ barZ G) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ := QuotientGroup.mk' (pPrimeCore 2 G) with hρ
  set Cb := centralizer ({ρ z} : Set (G ⧸ pPrimeCore 2 G))
  obtain ⟨hLC, hLs⟩ := barL_subnormal hz hL
  obtain ⟨eLb⟩ := nonempty_barL_equiv eL
  have hYC : barY G ≤ Cb := fun y hy => by
    rw [mem_centralizer_singleton_iff]
    exact (mem_barZ_iff.mp hc).2 y hy
  have hq := isQuasisimple_barY hY
  have := barY_normal (G := G)
  have hK : IsComponent ((barY G).subgroupOf Cb) :=
    ⟨LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hYC).symm hq,
      (Subgroup.Normal.subgroupOf inferInstance Cb).isSubnormal⟩
  rcases LocalCores.component_subnormal_subgroup hK hLs with hle | hcomm
  ·
    have hYL : barY G ≤ L.map ρ := fun y hy => by
      have h1 : (⟨y, hYC hy⟩ : Cb) ∈ (barY G).subgroupOf Cb := hy
      exact hle h1
    set Lb := L.map ρ
    set π : ↥Lb →* SL(2, ZMod 3) := eLb.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥Lb))
    set Yb := (barY G).subgroupOf Lb
    have : Group.IsPerfect ↥Yb :=
      (LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hYL).symm hq).1
    set P := Yb.map π
    have : Group.IsPerfect ↥P :=
      Group.IsPerfect.ofSurjective (f := π.subgroupMap Yb) (MonoidHom.subgroupMap_surjective _ _)
    have : Group.IsSolvable SL(2, ZMod 3) := ClassicalInvolution.Q3.isSolvable_sl2Three
    have : Group.IsSolvable ↥P := subgroup_solvable_of_solvable P
    have hPs := subsingleton_of_isPerfect_of_isSolvable (X := ↥P)
    have hzY : (⟨ρ z, hYL (mk_mem_barY hz)⟩ : ↥Lb) ∈ Yb := mk_mem_barY hz
    have hπz : π ⟨ρ z, hYL (mk_mem_barY hz)⟩ = 1 :=
      congrArg Subtype.val (Subsingleton.elim (⟨_, mem_map_of_mem π hzY⟩ : ↥P) 1)
    have hO : (⟨ρ z, hYL (mk_mem_barY hz)⟩ : ↥Lb) ∈ pPrimeCore 2 ↥Lb := by
      have h1 : eLb (QuotientGroup.mk ⟨ρ z, hYL (mk_mem_barY hz)⟩) = 1 := hπz
      rwa [map_eq_one_iff _ eLb.injective, QuotientGroup.eq_one_iff] at h1
    exact false_of_mem_pPrimeCore hO (by rw [Subgroup.orderOf_mk]; exact orderOf_mk_z hz)
  ·
    have hLZ : L.map ρ ≤ barZ G := by
      intro x hx
      apply centralizer_barY_le
      rw [mem_centralizer_iff]
      intro y hy
      have h1 : ⁅(⟨y, hYC hy⟩ : Cb), ⟨x, hLC hx⟩⁆ ∈
          ⁅(barY G).subgroupOf Cb, (L.map ρ).subgroupOf Cb⁆ :=
        Subgroup.commutator_mem_commutator hy hx
      rw [hcomm, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact congrArg Subtype.val h1
    have h2 : IsPGroup 2 ↥(L.map ρ) := isPGroup_barZ.to_le hLZ
    have hcard : Nat.card ↥(L.map ρ) = Nat.card ↥(pPrimeCore 2 ↥(L.map ρ)) * 24 := by
      rw [card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥(L.map ρ)),
        Nat.card_congr eLb.toEquiv, card_specialLinearGroup_two_zmod_three, mul_comm]
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h2
    have h3 : 3 ∣ 2 ^ k := by
      rw [← hk, hcard]
      exact Dvd.dvd.mul_left (by norm_num) _
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)

theorem barL_inf_barZ (hz : orderOf z = 2) (hzL : z ∈ L)
    (eL : ↥L ⧸ pPrimeCore 2 ↥L ≃* SL(2, ZMod 3))
    (hnc : QuotientGroup.mk' (pPrimeCore 2 G) z ∉ barZ G) :
    L.map (QuotientGroup.mk' (pPrimeCore 2 G)) ⊓ barZ G = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ := QuotientGroup.mk' (pPrimeCore 2 G) with hρ
  obtain ⟨eLb⟩ := nonempty_barL_equiv eL
  set Lb := L.map ρ
  set π : ↥Lb →* SL(2, ZMod 3) := eLb.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥Lb))
  have hker : ∀ w : ↥Lb, π w = 1 → w ∈ pPrimeCore 2 ↥Lb := by
    intro w hw
    have h1 : eLb (QuotientGroup.mk w) = 1 := hw
    rwa [map_eq_one_iff _ eLb.injective, QuotientGroup.eq_one_iff] at h1
  have hinv : ∀ w : ↥Lb, orderOf w = 2 → π w = -1 := by
    intro w hw
    have hw2 := pow_orderOf_eq_one w
    rw [hw] at hw2
    have hww : π w * π w = 1 := by rw [← map_mul, ← sq, hw2, map_one]
    rcases LieType.HighestRoot.eq_one_or_neg_one_of_mul_self_SL23 _ hww with h | h
    · exact (false_of_mem_pPrimeCore (hker w h) hw).elim
    · exact h
  rw [eq_bot_iff]
  intro x hx
  by_contra hx1
  have hP : IsPGroup 2 ↥(Lb ⊓ barZ G) := isPGroup_barZ.to_le inf_le_right
  have h2 : 2 ∣ Nat.card ↥(Lb ⊓ barZ G) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
    rcases k with _ | k
    · exfalso
      rw [pow_zero, Subgroup.card_eq_one] at hk
      exact hx1 (by rw [hk] at hx; exact hx)
    · rw [hk, pow_succ]
      exact dvd_mul_left 2 _
  obtain ⟨⟨w, hw'⟩, hw⟩ := exists_prime_orderOf_dvd_card' 2 h2
  rw [Subgroup.orderOf_mk] at hw
  have hwL : w ∈ Lb := hw'.1
  have hwZ : w ∈ barZ G := hw'.2
  have hzLb : ρ z ∈ Lb := mem_map_of_mem ρ hzL
  have h1 : π ⟨w, hwL⟩ = -1 := hinv _ (by rw [Subgroup.orderOf_mk]; exact hw)
  have h2' : π ⟨ρ z, hzLb⟩ = -1 := hinv _ (by rw [Subgroup.orderOf_mk]; exact orderOf_mk_z hz)
  have h3 : π (⟨w, hwL⟩ * ⟨ρ z, hzLb⟩) = 1 := by
    rw [map_mul, h1, h2']
    decide
  have hO := hker _ h3
  have hcomm : w * ρ z = ρ z * w := ((mem_barZ_iff.mp hwZ).2 (ρ z) (mk_mem_barY hz)).symm
  have hsq : (⟨w, hwL⟩ * ⟨ρ z, hzLb⟩ : ↥Lb) ^ 2 = 1 := by
    apply Subtype.ext
    have hw2 : w * w = 1 := mul_self_eq_one_of_orderOf hw
    have hz2 : ρ z * ρ z = 1 := mul_self_eq_one_of_orderOf (orderOf_mk_z hz)
    calc ((⟨w, hwL⟩ * ⟨ρ z, hzLb⟩ : ↥Lb) ^ 2 : G ⧸ pPrimeCore 2 G)
        = w * ρ z * (w * ρ z) := by simp [sq]
      _ = (w * w) * (ρ z * ρ z) := by
          rw [show w * ρ z * (w * ρ z) = w * (ρ z * w) * ρ z by group, ← hcomm]; group
      _ = 1 := by rw [hw2, hz2, one_mul]
  have hone : (⟨w, hwL⟩ * ⟨ρ z, hzLb⟩ : ↥Lb) = 1 := by
    by_contra hne
    exact false_of_mem_pPrimeCore hO (orderOf_eq_prime hsq hne)
  have hwz : w = ρ z := by
    have := congrArg Subtype.val hone
    simp only [Subgroup.coe_mul, OneMemClass.coe_one] at this
    have hz2 : ρ z * ρ z = 1 := mul_self_eq_one_of_orderOf (orderOf_mk_z hz)
    calc w = w * ρ z * ρ z := by rw [mul_assoc, hz2, mul_one]
      _ = ρ z := by rw [this, one_mul]
  exact hnc (hwz ▸ hwZ)

theorem barL_le_centralizer (hz : orderOf z = 2)
    (hL : IsSolvableTwoComponentIn L (centralizer {z})) (hzL : z ∈ L)
    (eL : ↥L ⧸ pPrimeCore 2 ↥L ≃* SL(2, ZMod 3))
    (hnc : QuotientGroup.mk' (pPrimeCore 2 G) z ∉ barZ G) :
    L.map (QuotientGroup.mk' (pPrimeCore 2 G)) ≤
      centralizer (barZ G : Set (G ⧸ pPrimeCore 2 G)) := by
  set ρ := QuotientGroup.mk' (pPrimeCore 2 G) with hρ
  obtain ⟨hLC, hLs⟩ := barL_subnormal hz hL
  have hinf := barL_inf_barZ hz hzL eL hnc
  set Cb := centralizer ({ρ z} : Set (G ⧸ pPrimeCore 2 G))
  have hZC : barZ G ≤ Cb := fun w hw => by
    rw [mem_centralizer_singleton_iff]
    exact ((mem_barZ_iff.mp hw).2 (ρ z) (mk_mem_barY hz)).symm
  have := barZ_normal (G := G)
  have hN : ((barZ G).subgroupOf Cb).Normal := Subgroup.Normal.subgroupOf inferInstance Cb
  have hN2 : IsPGroup 2 ↥((barZ G).subgroupOf Cb) :=
    isPGroup_barZ.of_equiv (subgroupOfEquivOfLe hZC).symm
  have hAN : (L.map ρ).subgroupOf Cb ⊓ (barZ G).subgroupOf Cb = ⊥ := by
    rw [eq_bot_iff]
    rintro ⟨y, hy⟩ ⟨h1, h2⟩
    have : y ∈ L.map ρ ⊓ barZ G := ⟨h1, h2⟩
    rw [hinf, mem_bot] at this
    exact (Subgroup.mem_bot).mpr (Subtype.ext this)
  intro x hx
  rw [mem_centralizer_iff]
  intro w hw
  obtain ⟨a, ha, b, hb, rfl, ⟨k, hk⟩, hbo⟩ := exists_two_mul_odd x
  have haY : a ∈ barY G := mem_barY_of_two_pow ⟨k, hk⟩
  have hwa : w * a = a * w := ((mem_barZ_iff.mp hw).2 a haY).symm
  have hbL : b ∈ L.map ρ := (zpowers_le.mpr hx) hb
  have hwb : w * b = b * w := by
    have h1 := commute_of_subnormal hLs hN hN2 hAN (y := ⟨b, hLC hbL⟩) hbL
      (by rwa [Subgroup.orderOf_mk]) ⟨w, hZC hw⟩ hw
    exact congrArg Subtype.val h1
  calc w * (a * b) = a * (w * b) := by rw [← mul_assoc, hwa, mul_assoc]
    _ = a * b * w := by rw [hwb, mul_assoc]

end L

end CFSG.ComponentClassification.HarrisLit.T1.F3FG
