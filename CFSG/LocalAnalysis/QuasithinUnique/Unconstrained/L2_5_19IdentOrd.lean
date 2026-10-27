module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentFam
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdOrders
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2pFacts
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6A312Ord

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint CFSG.QuasithinUnique.Ch1
open scoped commutatorElement

section KType

variable {G : Type} [Group G] [Finite G]

theorem isKType_simple
    {K : Subgroup G} (hK : IsKType K) :
    IsSimpleGroup ↥K ∧ ∃ a b : ↥K, a * b ≠ b * a := by
  rcases hK with hK | hK | hK
  · obtain ⟨p, hp, h7, hm⟩ := hK
    have h := l2pFacts ↥K (Or.inl ⟨p, hp, h7, hm⟩)
    exact ⟨h.simple, h.nonabelian⟩
  · have h := l2pFacts ↥K (Or.inr hK)
    exact ⟨h.simple, h.nonabelian⟩
  · obtain ⟨e⟩ := hK
    have : IsSimpleGroup (alternatingGroup (Fin 6)) :=
      alternatingGroup.isSimpleGroup (by norm_num [Nat.card_eq_fintype_card])
    have hs : IsSimpleGroup ↥K := e.isSimpleGroup
    refine ⟨hs, ?_⟩
    by_contra hnc
    push Not at hnc
    let _ : CommGroup ↥K := { (inferInstance : Group ↥K) with mul_comm := fun a b => hnc a b }
    have hp := IsSimpleGroup.prime_card (α := ↥K)
    have h360 : Nat.card ↥K = 360 := by
      rw [Nat.card_congr e.toEquiv]
      exact card_alternatingGroup_six
    rw [h360] at hp
    exact absurd hp (by norm_num)

omit [Finite G] in
theorem isKType_card {K : Subgroup G} (hK : IsKType K) :
    Nat.card ↥K = 168 ∨ Nat.card ↥K = 360 ∨
      ∃ p : ℕ, IsFermatOrMersenne p ∧ 7 < p ∧ p * (p * p - 1) = 2 * Nat.card ↥K := by
  rcases hK with ⟨p, hp, h7, hm⟩ | hK | ⟨e⟩
  · exact Or.inr (Or.inr ⟨p, hp, h7, card_of_l2p hp.1 (by omega) hm⟩)
  · exact Or.inl (card_of_psl_three_two hK)
  · obtain ⟨e⟩ := e
    exact Or.inr (Or.inl (by rw [Nat.card_congr e.toEquiv]; exact card_alternatingGroup_six))

end KType

section Setting

variable {G : Type} [Group G] [Finite G] {X K : Subgroup G} {t : G}

omit [Finite G] in
theorem IdentSetting.K_le (hs : IdentSetting X K t) : K ≤ X := hs.comp.1.trans inf_le_left

omit [Finite G] in
theorem IdentSetting.K_le_cent (hs : IdentSetting X K t) :
    K ≤ Subgroup.centralizer ({t} : Set G) := hs.comp.1.trans inf_le_right

omit [Finite G] in
theorem IdentSetting.perfect_K (hs : IdentSetting X K t) : ⁅K, K⁆ = K := by
  have h1 := Subgroup.isPerfect_iff.mp hs.comp.2.1.1
  have h2 := congrArg (Subgroup.map (X ⊓ Subgroup.centralizer ({t} : Set G)).subtype) h1
  rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hs.comp.1] at h2

omit [Finite G] in
theorem IdentSetting.center_eq_bot_of_simple (hs : IdentSetting X K t) (hsimple : IsSimpleGroup ↥X) :
    Subgroup.center ↥X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥X) with h | h
  · exact h
  · exfalso
    obtain ⟨-, -, a, b, hab⟩ := hs.quasi
    have : Subsingleton (↥X ⧸ Subgroup.center ↥X) := by
      rw [h]
      exact QuotientGroup.subsingleton_quotient_top
    exact hab (Subsingleton.elim _ _)

theorem center_eq_bot_of_simple_nonab {H : Type*} [Group H] [IsSimpleGroup H]
    (hnc : ∃ a b : H, a * b ≠ b * a) : Subgroup.center H = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center H) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    have : a ∈ Subgroup.center H := by rw [h]; exact Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.mp this b).symm

theorem IdentSetting.inf_center
    (hs : IdentSetting X K t) (hK : IsKType K) :
    K.subgroupOf X ⊓ Subgroup.center ↥X = ⊥ := by
  obtain ⟨hsimple, a, b, hab⟩ := isKType_simple hK
  let e : ↥(K.subgroupOf X) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hs.K_le
  have : IsSimpleGroup ↥(K.subgroupOf X) := e.isSimpleGroup
  have hnc : ∃ a b : ↥(K.subgroupOf X), a * b ≠ b * a :=
    ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by rw [map_mul, map_mul]; exact h))⟩
  have hc := center_eq_bot_of_simple_nonab hnc
  rw [eq_bot_iff]
  intro k hk
  have hkc : (⟨k, hk.1⟩ : ↥(K.subgroupOf X)) ∈ Subgroup.center ↥(K.subgroupOf X) := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext ((Subgroup.mem_center_iff.mp hk.2) (y : ↥X))
  rw [hc, Subgroup.mem_bot] at hkc
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val hkc

theorem IdentSetting.injective_quot
    (hs : IdentSetting X K t) (hK : IsKType K) :
    Function.Injective
      ((QuotientGroup.mk' (Subgroup.center ↥X)).comp (K.subgroupOf X).subtype) := by
  rw [injective_iff_map_eq_one]
  intro k hk
  have hkZ : (k : ↥X) ∈ Subgroup.center ↥X := (QuotientGroup.eq_one_iff _).mp hk
  have := hs.inf_center hK
  have h1 : (k : ↥X) ∈ K.subgroupOf X ⊓ Subgroup.center ↥X := ⟨k.2, hkZ⟩
  rw [this, Subgroup.mem_bot] at h1
  exact Subtype.ext h1

theorem IdentSetting.card_dvd
    (hs : IdentSetting X K t) (hK : IsKType K) :
    Nat.card ↥K ∣ Nat.card (↥X ⧸ Subgroup.center ↥X) := by
  have h := Subgroup.card_dvd_of_injective _ (hs.injective_quot hK)
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hs.K_le).toEquiv] at h

@[expose] def IdentSetting.conjAut (hs : IdentSetting X K t) : ↥X ≃* ↥X where
  toFun y := ⟨t⁻¹ * y * t, by
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (X : Set G)).inv_mem hs.tN)
      (y : G)).mp y.2
    simpa using this⟩
  invFun y := ⟨t * y * t⁻¹, (Subgroup.mem_normalizer_iff.mp hs.tN (y : G)).mp y.2⟩
  left_inv y := Subtype.ext (by simp [mul_assoc])
  right_inv y := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

omit [Finite G] in
theorem IdentSetting.coe_conjAut (hs : IdentSetting X K t) (y : ↥X) :
    ((hs.conjAut y : ↥X) : G) = t⁻¹ * y * t := rfl

omit [Finite G] in
theorem IdentSetting.conjAut_conjAut (hs : IdentSetting X K t) (y : ↥X) :
    hs.conjAut (hs.conjAut y) = y := by
  apply Subtype.ext
  have ht : t⁻¹ = t := inv_eq_of_mul_eq_one_right hs.sq
  rw [coe_conjAut, coe_conjAut, ht]
  calc t * (t * (y : G) * t) * t = (t * t) * (y : G) * (t * t) := by group
    _ = y := by rw [hs.sq]; group

omit [Finite G] in
theorem IdentSetting.conjAut_of_mem_cent (hs : IdentSetting X K t) {y : ↥X}
    (hy : (y : G) ∈ Subgroup.centralizer ({t} : Set G)) : hs.conjAut y = y := by
  apply Subtype.ext
  have hkt : (y : G) * t = t * (y : G) := Subgroup.mem_centralizer_singleton_iff.mp hy
  rw [coe_conjAut, mul_assoc, hkt, ← mul_assoc, inv_mul_cancel, one_mul]

omit [Finite G] in
theorem IdentSetting.conjAut_of_mem_K (hs : IdentSetting X K t) {y : ↥X} (hy : (y : G) ∈ K) :
    hs.conjAut y = y :=
  hs.conjAut_of_mem_cent (hs.K_le_cent hy)

@[expose] def IdentSetting.quotAut (hs : IdentSetting X K t) :
    (↥X ⧸ Subgroup.center ↥X) ≃* (↥X ⧸ Subgroup.center ↥X) :=
  QuotientGroup.congr _ _ hs.conjAut (Subgroup.map_center_eq hs.conjAut)

omit [Finite G] in
theorem IdentSetting.quotAut_mk (hs : IdentSetting X K t) (y : ↥X) :
    hs.quotAut (QuotientGroup.mk y) = QuotientGroup.mk (hs.conjAut y) := rfl

omit [Finite G] in
theorem IdentSetting.false_of_comm_central (hs : IdentSetting X K t)
    (h : ∀ y : ↥X, hs.conjAut y * y⁻¹ ∈ Subgroup.center ↥X) : False := by
  set Zbig : Subgroup G := (Subgroup.center ↥X).map X.subtype with hZbig
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right hs.sq
  have hid : ∀ x : G, (t⁻¹ * x * t * x⁻¹)⁻¹ = ⁅x, t⁆ := by
    intro x
    rw [commutatorElement_def]
    simp only [mul_inv_rev, inv_inv, htinv, mul_assoc]
  have hcomm_t : ∀ x ∈ X, ⁅x, t⁆ ∈ Zbig := by
    intro x hx
    refine ⟨((hs.conjAut ⟨x, hx⟩ * ⟨x, hx⟩⁻¹)⁻¹ : ↥X), Subgroup.inv_mem _ (h ⟨x, hx⟩), ?_⟩
    rw [← hid x]
    simp only [Subgroup.coe_subtype, Subgroup.coe_inv, Subgroup.coe_mul, coe_conjAut]
  have hX_le : X ≤ Zbig := by
    rw [← hs.comm]
    refine Subgroup.commutator_le.mpr fun x hx g hg => ?_
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    rcases Int.even_or_odd' n with ⟨m, rfl | rfl⟩
    · have : t ^ (2 * m) = 1 := by
        rw [zpow_mul]
        have : t ^ (2 : ℤ) = 1 := by
          rw [zpow_two]
          exact hs.sq
        rw [this, one_zpow]
      rw [this, commutatorElement_one_right]
      exact Zbig.one_mem
    · have : t ^ (2 * m + 1) = t := by
        rw [zpow_add, zpow_mul, zpow_one]
        have : t ^ (2 : ℤ) = 1 := by
          rw [zpow_two]
          exact hs.sq
        rw [this, one_zpow, one_mul]
      rw [this]
      exact hcomm_t x hx
  have hcent : Subgroup.center ↥X = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨c, hc, hcy⟩ := hX_le y.2
    have : c = y := Subtype.ext hcy
    rw [← this]
    exact hc
  obtain ⟨-, -, a, b, hab⟩ := hs.quasi
  have : Subsingleton (↥X ⧸ Subgroup.center ↥X) := by
    rw [hcent]
    exact QuotientGroup.subsingleton_quotient_top
  exact hab (Subsingleton.elim _ _)

theorem IdentSetting.card_lt
    (hs : IdentSetting X K t) (hK : IsKType K) :
    Nat.card ↥K < Nat.card (↥X ⧸ Subgroup.center ↥X) := by
  have hinj := hs.injective_quot hK
  have hle : Nat.card ↥(K.subgroupOf X) ≤ Nat.card (↥X ⧸ Subgroup.center ↥X) :=
    Nat.card_le_card_of_injective _ hinj
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hs.K_le).toEquiv]
  refine lt_of_le_of_ne hle fun heq => ?_
  have hbij := hinj.bijective_of_nat_card_le heq.ge
  have hdec : ∀ x : ↥X, ∃ k : ↥(K.subgroupOf X), ∃ z ∈ Subgroup.center ↥X, x = (k : ↥X) * z := by
    intro x
    obtain ⟨k, hk⟩ := hbij.2 (QuotientGroup.mk x)
    refine ⟨k, (k : ↥X)⁻¹ * x, ?_, by group⟩
    have : QuotientGroup.mk (k : ↥X) = (QuotientGroup.mk x : ↥X ⧸ Subgroup.center ↥X) := hk
    exact (QuotientGroup.eq.mp this)
  refine hs.false_of_comm_central fun y => ?_
  obtain ⟨k, z, hz, rfl⟩ := hdec y
  have hkc : hs.conjAut (k : ↥X) = (k : ↥X) := hs.conjAut_of_mem_K k.2
  have hzc : hs.conjAut z ∈ Subgroup.center ↥X := by
    rw [← Subgroup.map_center_eq hs.conjAut]
    exact Subgroup.mem_map_of_mem _ hz
  have hw : hs.conjAut z * z⁻¹ ∈ Subgroup.center ↥X :=
    Subgroup.mul_mem _ hzc (Subgroup.inv_mem _ hz)
  have key : hs.conjAut ((k : ↥X) * z) * ((k : ↥X) * z)⁻¹ = hs.conjAut z * z⁻¹ := by
    rw [map_mul, hkc, mul_inv_rev]
    have hc := Subgroup.mem_center_iff.mp hw (k : ↥X)
    calc (k : ↥X) * hs.conjAut z * (z⁻¹ * (k : ↥X)⁻¹)
        = (k : ↥X) * (hs.conjAut z * z⁻¹) * (k : ↥X)⁻¹ := by group
      _ = hs.conjAut z * z⁻¹ := by rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  rw [key]
  exact hw

theorem seventeen_le_of_isFermatOrMersenne {p : ℕ} (hp : IsFermatOrMersenne p) (h7 : 7 < p) :
    17 ≤ p := by
  obtain ⟨hpp, ⟨k, hk⟩ | ⟨k, hk2, hk⟩⟩ := hp
  ·
    by_contra hlt
    have hk2 : 2 ^ 2 ^ k < 16 := by omega
    have hk1 : k < 2 := by
      by_contra hk'
      have h2k : 4 ≤ 2 ^ k := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      have : 2 ^ 4 ≤ 2 ^ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h2k
      omega
    interval_cases k <;> omega
  ·
    by_contra hlt
    have hpos : 0 < 2 ^ k := pow_pos (by norm_num) k
    have hk4 : k < 5 := by
      by_contra hk5
      have : 2 ^ 5 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases k <;> first | omega | exact absurd hpp (by rw [hk]; norm_num)

theorem IdentSetting.false_of_dvd
    (hs : IdentSetting X K t) (hK : IsKType K) {N : ℕ} (hNpos : 0 < N)
    (hN : Nat.card (↥X ⧸ Subgroup.center ↥X) ∣ N) (h168 : ¬ (168 ∣ N ∧ 168 < N))
    (h360 : ¬ (360 ∣ N ∧ 360 < N))
    (hp : ∀ p : ℕ, 17 ≤ p → ¬ (p * (p * p - 1) ∣ 2 * N ∧ p * (p * p - 1) < 2 * N)) : False := by
  have hd := (hs.card_dvd hK).trans hN
  have hlt : Nat.card ↥K < N := lt_of_lt_of_le (hs.card_lt hK) (Nat.le_of_dvd hNpos hN)
  rcases isKType_card hK with h | h | ⟨p, hFM, h7, hpk⟩
  · rw [h] at hd hlt
    exact h168 ⟨hd, hlt⟩
  · rw [h] at hd hlt
    exact h360 ⟨hd, hlt⟩
  · refine hp p (seventeen_le_of_isFermatOrMersenne hFM h7) ⟨?_, ?_⟩
    · rw [hpk]
      exact Nat.mul_dvd_mul_left 2 hd
    · rw [hpk]
      omega

end Setting

section Leaves

open Ident

theorem le_mul_pred_sq {p : ℕ} (hp : 17 ≤ p) : 4896 ≤ p * (p * p - 1) :=
  Nat.mul_le_mul hp (Nat.sub_le_sub_right (Nat.mul_le_mul hp hp) 1)

theorem isKType_card_ge {G : Type} [Group G] {K : Subgroup G} (hK : IsKType K) :
    168 ≤ Nat.card ↥K := by
  rcases isKType_card hK with h | h | ⟨p, hFM, h7, hpk⟩
  · omega
  · omega
  · have := le_mul_pred_sq (seventeen_le_of_isFermatOrMersenne hFM h7)
    omega

theorem IsA6.card_eq {G : Type} [Group G] {K : Subgroup G} (hK : IsA6 K) : Nat.card ↥K = 360 := by
  obtain ⟨e⟩ := hK
  rw [Nat.card_congr e.toEquiv]
  exact card_alternatingGroup_six

theorem IsL32.card_eq {G : Type} [Group G] {K : Subgroup G} (hK : IsL32 K) : Nat.card ↥K = 168 :=
  card_of_psl_three_two hK

theorem IsL2pBig.card_ge {G : Type} [Group G] {K : Subgroup G} (hK : IsL2pBig K) :
    2448 ≤ Nat.card ↥K := by
  obtain ⟨p, hp, h7, hm⟩ := hK
  have h := card_of_l2p hp.1 (by omega) hm
  have := le_mul_pred_sq (seventeen_le_of_isFermatOrMersenne hp h7)
  omega

theorem tabIdentFor_alt6
    : TabIdentFor @FamAlt6 := by
  intro G _ _ X K t hs hX
  exfalso
  obtain ⟨⟨φ⟩, -⟩ := hX
  have hcard : Nat.card (↥X ⧸ Subgroup.center ↥X) = 360 := by
    rw [Nat.card_congr φ.toEquiv]
    exact card_alternatingGroup_six
  refine hs.false_of_dvd hs.ktype (N := 360) (by norm_num) (by rw [hcard]) (by norm_num)
    (by norm_num) ?_
  rintro p hp ⟨-, hlt⟩
  have := le_mul_pred_sq hp
  omega

theorem tabIdentFor_a6Simple
    : TabIdentFor @FamA6Simple := by
  intro G _ _ X K t hs hX
  obtain ⟨hsimple, ⟨e⟩⟩ := hX
  have hc : Subgroup.center ↥X = ⊥ := hs.center_eq_bot_of_simple hsimple
  refine tabIdentFor_alt6 G X K t hs ⟨⟨?_⟩, Or.inl ?_⟩
  · exact ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).trans e
  · rw [hc]
    exact Subgroup.card_bot

theorem tabIdentFor_l3Two
    : TabIdentFor @FamL3Two := by
  intro G _ _ X K t hs hX
  exfalso
  have hcard : Nat.card ↥X = 168 := card_of_psl_three_two hX.2
  have hdvd : Nat.card (↥X ⧸ Subgroup.center ↥X) ∣ 168 := by
    rw [← hcard]
    exact Subgroup.card_quotient_dvd_card _
  refine hs.false_of_dvd hs.ktype (N := 168) (by norm_num) hdvd (by norm_num) (by norm_num) ?_
  rintro p hp ⟨-, hlt⟩
  have := le_mul_pred_sq hp
  omega

theorem tabIdentFor_l33
    : TabIdentFor @FamL33 := by
  intro G _ _ X K t hs hX
  exfalso
  have hcard : Nat.card ↥X = 5616 := Unc25G2.A312Sub.card_psl_three_three hX
  have hdvd : Nat.card (↥X ⧸ Subgroup.center ↥X) ∣ 5616 := by
    rw [← hcard]
    exact Subgroup.card_quotient_dvd_card _
  refine hs.false_of_dvd hs.ktype (N := 5616) (by norm_num) hdvd (by norm_num) (by norm_num) ?_
  rintro p hp ⟨hd, hlt⟩
  have h1 : p ≤ 22 := by
    by_contra h
    have h23 : 23 ≤ p := by omega
    have : 23 * (23 * 23 - 1) ≤ p * (p * p - 1) :=
      Nat.mul_le_mul h23 (Nat.sub_le_sub_right (Nat.mul_le_mul h23 h23) 1)
    omega
  interval_cases p <;> omega

end Leaves

end CFSG.QuasithinUnique.Id2519
