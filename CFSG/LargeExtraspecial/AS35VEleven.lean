module

public import CFSG.LargeExtraspecial.AS35VPbarB
public import CFSG.GroupTheory.OddInversion
public import CFSG.LargeExtraspecial.OrthoF2Pairs57
public import CFSG.LargeExtraspecial.S12Five

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module CFSG.RankThree.OrthogonalInvolutions CFSG.OddInversion
open Setting (orderOf_eq_two_of_isTypeA' mem_normalizer_of_conj_le)

namespace AS35V

theorem oddCore_eq_top_of_odd {K : Type*} [Group K] (h : Odd (Nat.card K)) :
    CFSG.oddCore K = ⊤ :=
  eq_top_iff.mpr (le_sSup ⟨Subgroup.normal_top, by rwa [Subgroup.card_top]⟩)

theorem odd_card_of_isPGroup_three {Γ : Type*} [Group Γ] {X : Subgroup Γ} [Finite X]
    (hX : IsPGroup 3 X) : Odd (Nat.card X) := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨k, hk⟩ := hX.exists_card_eq
  rw [hk]
  exact Odd.pow (by decide)

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem pow_three_of_inverted {τ j : S.O} (hτ : IsTypeA S.q (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) 2)
    (hodd : Odd (orderOf j)) (hj : τ * j * τ⁻¹ = j⁻¹) : j ^ 3 = 1 := by
  by_cases hj1 : j = 1
  · rw [hj1, one_pow]
  have hle : (zpowers j).map S.O.subtype ≤ TauCeti.QuadraticMap.orthogonalGroup S.q := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hodd' : Odd (Nat.card ((zpowers j).map S.O.subtype)) := by
    rwa [card_map_of_injective (subtype_injective _), Nat.card_zpowers]
  have hinv : ∀ x ∈ (zpowers j).map S.O.subtype,
      (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) * x * (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)⁻¹ = x⁻¹ := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hy
    have e : τ * j ^ m * τ⁻¹ = (j ^ m)⁻¹ := by rw [← conj_zpow, hj, inv_zpow]
    have e' := congrArg Subtype.val e
    simpa using e'
  have h3 := (orderOf_eq_three_of_inverted S.q_nondegenerate hτ hle hodd' hinv
    (x := (j : S.Qt ≃ₗ[ZMod 2] S.Qt)) ⟨j, mem_zpowers j, rfl⟩
    (fun e => hj1 (Subtype.ext e))).1
  rw [Subgroup.orderOf_coe] at h3
  rw [← h3]
  exact pow_orderOf_eq_one j

theorem card_le_three_of_inverts {τ : S.O} (hτ : IsTypeA S.q (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) 2)
    {A : Subgroup S.O} (hodd : Odd (Nat.card A)) (hinv : ∀ x ∈ A, τ * x * τ⁻¹ = x⁻¹) :
    Nat.card A ≤ 3 := by
  have hle : A.map S.O.subtype ≤ TauCeti.QuadraticMap.orthogonalGroup S.q := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have h := aschbacher_5_7 S.q_nondegenerate hτ hle
    (by rwa [card_map_of_injective (subtype_injective _)]) (by
      rintro _ ⟨y, hy, rfl⟩
      have e' := congrArg Subtype.val (hinv y hy)
      simpa using e')
  rwa [card_map_of_injective (subtype_injective _)] at h

theorem exists_fixed_mul_inverted {τ : S.O} (hτ : orderOf τ = 2) {X : Subgroup S.O}
    (hodd : Odd (Nat.card X)) (hN : τ ∈ normalizer (X : Set S.O)) {x : S.O} (hx : x ∈ X) :
    ∃ c ∈ X, c * τ = τ * c ∧ ∃ j ∈ X, τ * j * τ⁻¹ = j⁻¹ ∧ x = c * j := by
  obtain ⟨⟨c, j⟩, ⟨hc, hj⟩, hcj⟩ := (fixed_mul_inverted_bijOn hodd hτ hN).surjOn hx
  obtain ⟨hcX, hcC⟩ := mem_inf.mp hc
  exact ⟨c, hcX, mem_centralizer_singleton_iff.mp hcC, j, hj.1, hj.2, hcj.symm⟩

namespace PbarFacts

variable {τ : S.O} {P : Subgroup S.O}

theorem card_centralizer_le (h : PbarFacts S τ P)
    (h58 : ∀ Y : Subgroup S.O, Y ≤ S.Mbar → (∀ y ∈ Y, y * τ = τ * y) →
      (∀ p ∈ P, ∀ y ∈ Y, p * y * p⁻¹ ∈ Y) → CFSG.oddCore Y ⊔ CFSG.layer Y = ⊤ → Nat.card Y ≤ 3)
    {X : Subgroup S.O} (hXM : X ≤ S.Mbar) (hodd : Odd (Nat.card X))
    (hPX : ∀ p ∈ P, ∀ x ∈ X, p * x * p⁻¹ ∈ X) :
    Nat.card (X ⊓ centralizer ({τ} : Set S.O) : Subgroup S.O) ≤ 3 := by
  have hodd' : Odd (Nat.card (X ⊓ centralizer ({τ} : Set S.O) : Subgroup S.O)) :=
    Odd.of_dvd_nat hodd (card_dvd_of_le inf_le_left)
  refine h58 _ (inf_le_left.trans hXM) (fun y hy => mem_centralizer_singleton_iff.mp hy.2)
    (fun p hp y hy => mem_inf.mpr ⟨hPX p hp y hy.1, ?_⟩)
    (by rw [oddCore_eq_top_of_odd hodd', top_sup_eq])
  rw [mem_centralizer_singleton_iff]
  have hy := mem_centralizer_singleton_iff.mp hy.2
  have hpτ := h.commute hp
  have hpτ' : p⁻¹ * τ = τ * p⁻¹ := h.commute (P.inv_mem hp)
  calc p * y * p⁻¹ * τ = p * y * (p⁻¹ * τ) := by group
    _ = p * (y * τ) * p⁻¹ := by rw [hpτ']; group
    _ = p * τ * y * p⁻¹ := by rw [hy]; group
    _ = τ * (p * y * p⁻¹) := by rw [hpτ]; group

theorem false_of_inverts_subgroup (h : PbarFacts S τ P) {A : Subgroup S.O}
    (hodd : Odd (Nat.card A)) (hPA : ∀ p ∈ P, ∀ x ∈ A, p * x * p⁻¹ ∈ A)
    (hinv : ∀ x ∈ A, τ * x * τ⁻¹ = x⁻¹) {a : S.O} (ha : a ∈ A) (ha1 : a ≠ 1) : False := by
  have hA3 := card_le_three_of_inverts h.typeA hodd hinv
  have hoa : Odd (orderOf a) := Odd.of_dvd_nat hodd (A.orderOf_dvd_natCard ha)
  have ha3 : a ^ 3 = 1 := pow_three_of_inverted h.typeA hoa (hinv a ha)
  have hAz : zpowers a = A := by
    refine eq_of_le_of_card_ge (zpowers_le.mpr ha) ?_
    rw [Nat.card_zpowers, orderOf_eq_three_of_pow ha3 ha1]
    exact hA3
  refine h.false_of_inverts ha3 ha1 (fun p hp => ?_) (hinv a ha)
  rw [hAz]
  exact hPA p hp a ha

theorem exists_zeta (h : PbarFacts S τ P)
    (h58 : ∀ Y : Subgroup S.O, Y ≤ S.Mbar → (∀ y ∈ Y, y * τ = τ * y) →
      (∀ p ∈ P, ∀ y ∈ Y, p * y * p⁻¹ ∈ Y) → CFSG.oddCore Y ⊔ CFSG.layer Y = ⊤ → Nat.card Y ≤ 3)
    {X : Subgroup S.O} (hXM : X ≤ S.Mbar) (hX3 : IsPGroup 3 X)
    (hPX : ∀ p ∈ P, ∀ x ∈ X, p * x * p⁻¹ ∈ X) (hτX : ∃ x ∈ X, τ * x ≠ x * τ) :
    ∃ ζ ∈ X, ζ ≠ 1 ∧ ζ ^ 3 = 1 ∧ ζ * τ = τ * ζ ∧
      (∀ c ∈ X, c * τ = τ * c → c ∈ zpowers ζ) ∧ ∀ x ∈ X, ζ * x = x * ζ := by
  have hodd : Odd (Nat.card X) := odd_card_of_isPGroup_three hX3
  have hτ2 : orderOf τ = 2 := orderOf_eq_two_of_isTypeA' h.typeA
  have hτN : τ ∈ normalizer (X : Set S.O) := mem_normalizer_of_conj_le (hPX τ h.mem)
    (hPX τ⁻¹ (P.inv_mem h.mem))
  set C : Subgroup S.O := X ⊓ centralizer ({τ} : Set S.O) with hC
  have hC3 : Nat.card C ≤ 3 := h.card_centralizer_le h58 hXM hodd hPX
  have hCodd : Odd (Nat.card C) := Odd.of_dvd_nat hodd (card_dvd_of_le inf_le_left)
  have hmemC : ∀ {c : S.O}, c ∈ X → c * τ = τ * c → c ∈ C := fun hc hcτ =>
    ⟨hc, mem_centralizer_singleton_iff.mpr hcτ⟩
  obtain ⟨x₀, hx₀, hx₀τ⟩ := hτX
  obtain ⟨ζ, hζC, hζ1⟩ : ∃ ζ ∈ C, ζ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hinv : ∀ x ∈ X, τ * x * τ⁻¹ = x⁻¹ := by
      intro x hx
      obtain ⟨c, hc, hcτ, j, -, hj, rfl⟩ := exists_fixed_mul_inverted hτ2 hodd hτN hx
      rw [hcon c (hmemC hc hcτ), one_mul]
      exact hj
    refine h.false_of_inverts_subgroup hodd hPX hinv hx₀ fun e => hx₀τ ?_
    rw [e, mul_one, one_mul]
  have hζX : ζ ∈ X := hζC.1
  have hζτ : ζ * τ = τ * ζ := mem_centralizer_singleton_iff.mp hζC.2
  have hCcard : Nat.card C = 3 := by
    have h1 : Nat.card C ≠ 1 := by
      intro e
      exact hζ1 (by
        have := (Subgroup.card_eq_one.mp e)
        rw [this] at hζC
        exact (mem_bot.mp hζC))
    rcases hCodd with ⟨k, hk⟩
    omega
  have hζ3 : ζ ^ 3 = 1 := by
    have := pow_card_eq_one' (G := C) (x := ⟨ζ, hζC⟩)
    rw [hCcard] at this
    exact congrArg Subtype.val this
  have hCz : zpowers ζ = C := by
    refine eq_of_le_of_card_ge (zpowers_le.mpr hζC) ?_
    rw [Nat.card_zpowers, orderOf_eq_three_of_pow hζ3 hζ1, hCcard]
  refine ⟨ζ, hζX, hζ1, hζ3, hζτ, fun c hc hcτ => hCz ▸ hmemC hc hcτ, ?_⟩
  set Z : Subgroup S.O := (center X).map X.subtype with hZ
  have hZX : Z ≤ X := map_subtype_le _
  have hmemZ : ∀ {w : S.O}, w ∈ Z ↔ w ∈ X ∧ ∀ x ∈ X, w * x = x * w := by
    intro w
    constructor
    · rintro ⟨w', hw', rfl⟩
      refine ⟨w'.2, fun x hx => ?_⟩
      exact (congrArg Subtype.val (mem_center_iff.mp hw' ⟨x, hx⟩)).symm
    · rintro ⟨hw, hwc⟩
      refine ⟨⟨w, hw⟩, mem_center_iff.mpr fun x => Subtype.ext (hwc x x.2).symm, rfl⟩
  have hPZ : ∀ p ∈ P, ∀ w ∈ Z, p * w * p⁻¹ ∈ Z := by
    intro p hp w hw
    obtain ⟨hwX, hwc⟩ := hmemZ.mp hw
    refine hmemZ.mpr ⟨hPX p hp w hwX, fun x hx => ?_⟩
    have hx' : p⁻¹ * x * p⁻¹⁻¹ ∈ X := hPX p⁻¹ (P.inv_mem hp) x hx
    have e := hwc _ hx'
    calc p * w * p⁻¹ * x = p * (w * (p⁻¹ * x * p⁻¹⁻¹)) * p⁻¹ := by group
      _ = p * ((p⁻¹ * x * p⁻¹⁻¹) * w) * p⁻¹ := by rw [e]
      _ = x * (p * w * p⁻¹) := by group
  have hZodd : Odd (Nat.card Z) := Odd.of_dvd_nat hodd (card_dvd_of_le hZX)
  have hτZ : τ ∈ normalizer (Z : Set S.O) := mem_normalizer_of_conj_le (hPZ τ h.mem)
    (hPZ τ⁻¹ (P.inv_mem h.mem))
  obtain ⟨w, hwZ, hwτ, hw1⟩ : ∃ w ∈ Z, w * τ = τ * w ∧ w ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hinv : ∀ w ∈ Z, τ * w * τ⁻¹ = w⁻¹ := by
      intro w hw
      obtain ⟨c, hc, hcτ, j, -, hj, rfl⟩ := exists_fixed_mul_inverted hτ2 hZodd hτZ hw
      rw [hcon c hc hcτ, one_mul]
      exact hj
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    have hXnt : Nontrivial X := ⟨⟨⟨x₀, hx₀⟩, 1, fun e => hx₀τ (by
      rw [show x₀ = 1 from congrArg Subtype.val e, mul_one, one_mul])⟩⟩
    have hZnt := hX3.center_nontrivial
    obtain ⟨w₀, hw₀⟩ := exists_ne (1 : center X)
    refine h.false_of_inverts_subgroup hZodd hPZ hinv (a := ((w₀ : X) : S.O))
      ⟨w₀, w₀.2, rfl⟩ fun e => hw₀ (Subtype.ext (Subtype.ext e))
  have hwz : w ∈ zpowers ζ := hCz ▸ hmemC (hZX hwZ) hwτ
  have hζw : ζ ∈ zpowers w := by
    rcases eq_one_or_eq_or_eq_inv_of_mem_zpowers hζ3 hwz with e | e | e
    · exact absurd e hw1
    · rw [e]
      exact mem_zpowers ζ
    · rw [e, ← inv_inv ζ]
      exact inv_mem (mem_zpowers ζ⁻¹)
  have hζZ : ζ ∈ Z := (zpowers_le.mpr hwZ) hζw
  exact (hmemZ.mp hζZ).2

theorem mem_zpowers_of_commute (h : PbarFacts S τ P) {X : Subgroup S.O}
    (hodd : Odd (Nat.card X)) {j k : S.O} (hj : j ∈ X) (hk : k ∈ X) (hj1 : j ≠ 1)
    (hjk : j * k = k * j) (hτj : τ * j * τ⁻¹ = j⁻¹) (hτk : τ * k * τ⁻¹ = k⁻¹) :
    k ∈ zpowers j := by
  set A : Subgroup S.O := closure {j, k} with hA
  have hcomm : ({j, k} : Set S.O).Pairwise Commute := by
    intro a ha b hb _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact Commute.refl _
    · exact hjk
    · exact hjk.symm
    · exact Commute.refl _
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
    have := Subgroup.isMulCommutative_closure hcomm
    intro x hx y hy
    exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : A) ⟨y, hy⟩)
  have hAX : A ≤ X := by
    rw [hA, closure_le]
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact hj
    · exact hk
  have hAodd : Odd (Nat.card A) := Odd.of_dvd_nat hodd (card_dvd_of_le hAX)
  have hinv : ∀ x ∈ A, τ * x * τ⁻¹ = x⁻¹ := by
    intro x hx
    induction hx using closure_induction with
    | mem a ha =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl
      · exact hτj
      · exact hτk
    | one => simp
    | mul a b ha hb iha ihb =>
      calc τ * (a * b) * τ⁻¹ = (τ * a * τ⁻¹) * (τ * b * τ⁻¹) := by group
        _ = a⁻¹ * b⁻¹ := by rw [iha, ihb]
        _ = (a * b)⁻¹ := by rw [mul_inv_rev, hAc _ (inv_mem ha) _ (inv_mem hb)]
    | inv a ha iha => rw [show τ * a⁻¹ * τ⁻¹ = (τ * a * τ⁻¹)⁻¹ by group, iha]
  have hA3 := card_le_three_of_inverts h.typeA hAodd hinv
  have hjA : j ∈ A := subset_closure (by simp)
  have hoj : Odd (orderOf j) := Odd.of_dvd_nat hodd (X.orderOf_dvd_natCard hj)
  have hj3 : j ^ 3 = 1 := pow_three_of_inverted h.typeA hoj hτj
  have hAz : zpowers j = A := by
    refine eq_of_le_of_card_ge (zpowers_le.mpr hjA) ?_
    rw [Nat.card_zpowers, orderOf_eq_three_of_pow hj3 hj1]
    exact hA3
  rw [hAz]
  exact subset_closure (by simp)

theorem conj_commute (h : PbarFacts S τ P) {p y : S.O} (hp : p ∈ P) (hy : y * τ = τ * y) :
    p * y * p⁻¹ * τ = τ * (p * y * p⁻¹) := by
  have hpτ := h.commute hp
  have hpτ' : p⁻¹ * τ = τ * p⁻¹ := h.commute (P.inv_mem hp)
  calc p * y * p⁻¹ * τ = p * y * (p⁻¹ * τ) := by group
    _ = p * (y * τ) * p⁻¹ := by rw [hpτ']; group
    _ = p * τ * y * p⁻¹ := by rw [hy]; group
    _ = τ * (p * y * p⁻¹) := by rw [hpτ]; group

theorem conj_inverted (h : PbarFacts S τ P) {p j : S.O} (hp : p ∈ P)
    (hj : τ * j * τ⁻¹ = j⁻¹) : τ * (p * j * p⁻¹) * τ⁻¹ = (p * j * p⁻¹)⁻¹ := by
  have hpτ := h.commute hp
  calc τ * (p * j * p⁻¹) * τ⁻¹ = (τ * p) * j * (τ * p)⁻¹ := by group
    _ = (p * τ) * j * (p * τ)⁻¹ := by rw [hpτ]
    _ = p * (τ * j * τ⁻¹) * p⁻¹ := by group
    _ = (p * j * p⁻¹)⁻¹ := by rw [hj]; group

theorem fiveEleven (h : PbarFacts S τ P)
    (h58 : ∀ Y : Subgroup S.O, Y ≤ S.Mbar → (∀ y ∈ Y, y * τ = τ * y) →
      (∀ p ∈ P, ∀ y ∈ Y, p * y * p⁻¹ ∈ Y) → CFSG.oddCore Y ⊔ CFSG.layer Y = ⊤ → Nat.card Y ≤ 3)
    {X : Subgroup S.O} (hXM : X ≤ S.Mbar) (hX3 : IsPGroup 3 X)
    (hPX : ∀ p ∈ P, ∀ x ∈ X, p * x * p⁻¹ ∈ X) (hτX : ∃ x ∈ X, τ * x ≠ x * τ) :
    S.width ≤ 3 ∧ Nat.card (X ⊓ centralizer ({τ} : Set S.O) : Subgroup S.O) = 3 := by
  obtain ⟨ζ, hζX, hζ1, hζ3, hζτ, hCz, hζc⟩ := h.exists_zeta h58 hXM hX3 hPX hτX
  have hodd := odd_card_of_isPGroup_three hX3
  have hτ2 : orderOf τ = 2 := orderOf_eq_two_of_isTypeA' h.typeA
  have hτN : τ ∈ normalizer (X : Set S.O) := mem_normalizer_of_conj_le (hPX τ h.mem)
    (hPX τ⁻¹ (P.inv_mem h.mem))
  have hτi : τ⁻¹ = τ := h.inv_eq
  have hzc : ∀ c ∈ zpowers ζ, ∀ x ∈ X, c * x = x * c := by
    intro c hc x hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
    exact (Commute.zpow_left (hζc x hx) k).eq
  have hzX : ∀ c ∈ zpowers ζ, c ∈ X := fun c hc => (zpowers_le.mpr hζX) hc
  have hcτ : ∀ c ∈ zpowers ζ, τ * c * τ⁻¹ = c := by
    intro c hc
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
    rw [← conj_zpow, show τ * ζ * τ⁻¹ = ζ by rw [← hζτ]; group]
  have hPζ : ∀ p ∈ P, p * ζ = ζ * p := fun p hp =>
    h.commute_of_normalizes (hXM hζX) hζτ hζ3
      (fun q hq => hCz _ (hPX q hq ζ hζX) (h.conj_commute hq hζτ)) hp
  have hPc : ∀ p ∈ P, ∀ c ∈ zpowers ζ, p * c = c * p := by
    intro p hp c hc
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
    exact (Commute.zpow_right (hPζ p hp) k).eq
  have hdec : ∀ x ∈ X, ∃ c ∈ zpowers ζ, ∃ j ∈ X, τ * j * τ⁻¹ = j⁻¹ ∧ x = c * j := by
    intro x hx
    obtain ⟨c, hc, hcτ', j, hj, hjτ, rfl⟩ := exists_fixed_mul_inverted hτ2 hodd hτN hx
    exact ⟨c, hCz c hc hcτ', j, hj, hjτ, rfl⟩
  have hkey : ∀ c ∈ zpowers ζ, ∀ j ∈ X, τ * j * τ⁻¹ = j⁻¹ →
      τ * (c * j) * τ⁻¹ = (c * j)⁻¹ → c = 1 := by
    intro c hc j hj hτj hτcj
    have e : τ * (c * j) * τ⁻¹ = c * j⁻¹ := by
      rw [show τ * (c * j) * τ⁻¹ = (τ * c * τ⁻¹) * (τ * j * τ⁻¹) by group, hcτ c hc, hτj]
    have e2 : (c * j)⁻¹ = c⁻¹ * j⁻¹ := by
      rw [mul_inv_rev, hzc c⁻¹ (inv_mem hc) j⁻¹ (X.inv_mem hj)]
    have e3 : c = c⁻¹ := mul_right_cancel (e.symm.trans (hτcj.trans e2))
    have hcc : c * c = 1 := by
      calc c * c = c * c⁻¹ := by rw [← e3]
        _ = 1 := mul_inv_cancel c
    have hc3 : c ^ 3 = 1 := by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ3, one_zpow]
    calc c = c ^ 3 := by rw [pow_succ, pow_two, hcc, one_mul]
      _ = 1 := hc3
  have hτx : ∀ x ∈ X, ∃ c ∈ zpowers ζ, τ * x * τ⁻¹ = c * x⁻¹ := by
    intro x hx
    obtain ⟨c, hc, j, hj, hτj, rfl⟩ := hdec x hx
    refine ⟨c * c, (zpowers ζ).mul_mem hc hc, ?_⟩
    have e2 : (c * j)⁻¹ = c⁻¹ * j⁻¹ := by
      rw [mul_inv_rev, hzc c⁻¹ (inv_mem hc) j⁻¹ (X.inv_mem hj)]
    calc τ * (c * j) * τ⁻¹ = (τ * c * τ⁻¹) * (τ * j * τ⁻¹) := by group
      _ = c * j⁻¹ := by rw [hcτ c hc, hτj]
      _ = c * c * (c⁻¹ * j⁻¹) := by group
      _ = c * c * (c * j)⁻¹ := by rw [e2]
  have hcomm : ∀ a ∈ X, ∀ b ∈ X, a * b * a⁻¹ * b⁻¹ ∈ zpowers ζ := by
    intro a ha b hb
    obtain ⟨c₁, hc₁, e₁⟩ := hτx (a⁻¹ * b⁻¹) (X.mul_mem (X.inv_mem ha) (X.inv_mem hb))
    obtain ⟨c₂, hc₂, e₂⟩ := hτx a⁻¹ (X.inv_mem ha)
    obtain ⟨c₃, hc₃, e₃⟩ := hτx b⁻¹ (X.inv_mem hb)
    have e : c₁ * (b * a) = c₂ * c₃ * (a * b) := by
      calc c₁ * (b * a) = c₁ * (a⁻¹ * b⁻¹)⁻¹ := by group
        _ = τ * (a⁻¹ * b⁻¹) * τ⁻¹ := e₁.symm
        _ = (τ * a⁻¹ * τ⁻¹) * (τ * b⁻¹ * τ⁻¹) := by group
        _ = c₂ * a⁻¹⁻¹ * (c₃ * b⁻¹⁻¹) := by rw [e₂, e₃]
        _ = c₂ * (a * c₃) * b := by rw [inv_inv, inv_inv]; group
        _ = c₂ * c₃ * (a * b) := by rw [← hzc c₃ hc₃ a ha]; group
    have e' : a * b * a⁻¹ * b⁻¹ = (c₂ * c₃)⁻¹ * c₁ := by
      calc a * b * a⁻¹ * b⁻¹ = (c₂ * c₃)⁻¹ * (c₂ * c₃ * (a * b)) * (b * a)⁻¹ := by group
        _ = (c₂ * c₃)⁻¹ * (c₁ * (b * a)) * (b * a)⁻¹ := by rw [e]
        _ = (c₂ * c₃)⁻¹ * c₁ := by group
    rw [e']
    exact (zpowers ζ).mul_mem (inv_mem ((zpowers ζ).mul_mem hc₂ hc₃)) hc₁
  have hW5a : ∀ j ∈ X, j ≠ 1 → τ * j * τ⁻¹ = j⁻¹ → ∀ p ∈ P, p * j * p⁻¹ = j → p = 1 := by
    intro j hj hj1 hτj p hp hpj
    have hoj := Odd.of_dvd_nat hodd (X.orderOf_dvd_natCard hj)
    refine h.eq_one_of_commute (pow_three_of_inverted h.typeA hoj hτj) hj1 hτj hp ?_
    calc p * j = (p * j * p⁻¹) * p := by group
      _ = j * p := by rw [hpj]
  have hW5b : ∀ j ∈ X, j ≠ 1 → τ * j * τ⁻¹ = j⁻¹ → ∀ p ∈ P, p * j * p⁻¹ = j⁻¹ → p = τ := by
    intro j hj hj1 hτj p hp hpj
    have h1 : p * τ * j * (p * τ)⁻¹ = j := by
      calc p * τ * j * (p * τ)⁻¹ = p * (τ * j * τ⁻¹) * p⁻¹ := by group
        _ = (p * j * p⁻¹)⁻¹ := by rw [hτj]; group
        _ = j := by rw [hpj, inv_inv]
    have h2 := hW5a j hj hj1 hτj (p * τ) (P.mul_mem hp h.mem) h1
    rw [← hτi]
    exact eq_inv_of_mul_eq_one_left h2
  have hinv : ∀ p ∈ P, p * p = 1 → p = 1 ∨ p = τ := by
    intro p hp hpp
    by_contra hcon
    push Not at hcon
    obtain ⟨hp1, hpτ⟩ := hcon
    have hpi : p⁻¹ = p := inv_eq_of_mul_eq_one_right hpp
    obtain ⟨x₀, hx₀, hx₀τ⟩ := hτX
    obtain ⟨c₀, hc₀, j₀, hj₀, hτj₀, rfl⟩ := hdec x₀ hx₀
    have hj₀1 : j₀ ≠ 1 := by
      rintro rfl
      apply hx₀τ
      have := hcτ c₀ hc₀
      rw [mul_one]
      calc τ * c₀ = (τ * c₀ * τ⁻¹) * τ := by group
        _ = c₀ * τ := by rw [this]
    obtain ⟨x', hx'⟩ : ∃ x', x' = p * j₀ * p⁻¹ := ⟨_, rfl⟩
    have hx'X : x' ∈ X := hx' ▸ hPX p hp j₀ hj₀
    have hτx' : τ * x' * τ⁻¹ = x'⁻¹ := hx' ▸ h.conj_inverted hp hτj₀
    have hpx' : p * x' * p⁻¹ = j₀ := by
      rw [hx']
      calc p * (p * j₀ * p⁻¹) * p⁻¹ = (p * p) * j₀ * (p⁻¹ * p⁻¹) := by group
        _ = j₀ := by rw [hpp, hpi, hpp]; group
    obtain ⟨c, hc, ju, hju, hτju, hueq⟩ := hdec (j₀ * x') (X.mul_mem hj₀ hx'X)
    obtain ⟨c₁, hc₁⟩ : ∃ c₁, c₁ = x' * j₀ * x'⁻¹ * j₀⁻¹ := ⟨_, rfl⟩
    have hc₁z : c₁ ∈ zpowers ζ := hc₁ ▸ hcomm x' hx'X j₀ hj₀
    have hpju : p * ju * p⁻¹ = c₁ * ju := by
      have e1 : p * (j₀ * x') * p⁻¹ = c * (p * ju * p⁻¹) := by
        rw [hueq]
        calc p * (c * ju) * p⁻¹ = (p * c) * ju * p⁻¹ := by group
          _ = c * (p * ju * p⁻¹) := by rw [hPc p hp c hc]; group
      have e2 : p * (j₀ * x') * p⁻¹ = c₁ * (c * ju) := by
        calc p * (j₀ * x') * p⁻¹ = (p * j₀ * p⁻¹) * (p * x' * p⁻¹) := by group
          _ = c₁ * (j₀ * x') := by rw [← hx', hpx', hc₁]; group
          _ = c₁ * (c * ju) := by rw [hueq]
      have hcc : c₁ * c = c * c₁ := hzc c₁ hc₁z c (hzX c hc)
      have e3 : c * (p * ju * p⁻¹) = c * (c₁ * ju) := by
        rw [← e1, e2, ← mul_assoc, hcc, mul_assoc]
      exact mul_left_cancel e3
    have hc₁1 : c₁ = 1 := hkey c₁ hc₁z ju hju hτju (by rw [← hpju]; exact h.conj_inverted hp hτju)
    rw [hc₁1, one_mul] at hpju
    have hju1 : ju = 1 := by
      by_contra hju1
      exact hp1 (hW5a ju hju hju1 hτju p hp hpju)
    rw [hju1, mul_one] at hueq
    have hx'eq : x' = c * j₀⁻¹ := by
      calc x' = j₀⁻¹ * (j₀ * x') := by group
        _ = j₀⁻¹ * c := by rw [hueq]
        _ = c * j₀⁻¹ := (hzc c hc j₀⁻¹ (X.inv_mem hj₀)).symm
    have hτj₀' : τ * j₀⁻¹ * τ⁻¹ = j₀⁻¹⁻¹ := by
      rw [show τ * j₀⁻¹ * τ⁻¹ = (τ * j₀ * τ⁻¹)⁻¹ by group, hτj₀]
    have hc1 : c = 1 := hkey c hc j₀⁻¹ (X.inv_mem hj₀) hτj₀' (by rw [← hx'eq]; exact hτx')
    rw [hc1, one_mul] at hx'eq
    exact hpτ (hW5b j₀ hj₀ hj₀1 hτj₀ p hp (hx' ▸ hx'eq))
  refine ⟨h.width_le_three hinv, ?_⟩
  have hCeq : X ⊓ centralizer ({τ} : Set S.O) = zpowers ζ := by
    refine le_antisymm (fun c hc => hCz c hc.1 (mem_centralizer_singleton_iff.mp hc.2)) ?_
    exact zpowers_le.mpr ⟨hζX, mem_centralizer_singleton_iff.mpr hζτ⟩
  rw [hCeq, Nat.card_zpowers, orderOf_eq_three_of_pow hζ3 hζ1]

end PbarFacts

end AS35V

end CFSG.LargeExtraspecial
