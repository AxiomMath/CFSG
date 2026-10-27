module

public import CFSG.GH74.Uniqueness.SU.SU4Quot
public import CFSG.GH74.Uniqueness.SU.KI1r3Struct

public section

namespace CFSG.GH74.Uniqueness.SU.K.R4

open Subgroup CFSG CFSG.GH74.Uniqueness.SU CFSG.GH74.Uniqueness.SU.K.R3

section Group

variable {H : Type} [Group H]

theorem eq_one_of_coprime_two_power {G : Type*} [Group G] (z : G) {n : ℕ} (hn : Nat.Coprime 2 n)
    (hz : orderOf z ∣ n) (j : ℕ) (hj : orderOf z = 2 ^ j) : z = 1 := by
  have h1 : Nat.Coprime (2 ^ j) n := Nat.Coprime.pow_left j hn
  rw [hj] at hz
  have h2 : 2 ^ j = 1 := Nat.Coprime.eq_one_of_dvd h1 hz
  have h3 : orderOf z = 1 := by rw [hj, h2]
  exact orderOf_eq_one_iff.1 h3

theorem normalizer_oddCore_eq_bot (P : Subgroup H) (hP2 : IsPGroup 2 P)
    (hC : centralizer (P : Set H) ≤ P) (W : Subgroup ↥(normalizer (P : Set H))) [W.Normal]
    (hW : Nat.Coprime 2 (Nat.card W)) : W = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  rw [Subgroup.mem_bot]
  have hwN := w.2
  have hordW : ∀ z ∈ W, orderOf z ∣ Nat.card W := fun z hz => by
    have := orderOf_dvd_natCard (⟨z, hz⟩ : W)
    rwa [Subgroup.orderOf_mk] at this
  have hmain : ∀ z ∈ W, (z : H) ∈ P → z = 1 := by
    intro z hz hzP
    obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.1 hP2 ⟨(z : H), hzP⟩
    refine eq_one_of_coprime_two_power z hW (hordW z hz) j ?_
    calc orderOf z = orderOf (z : H) := (Subgroup.orderOf_coe z).symm
      _ = orderOf (⟨(z : H), hzP⟩ : P) := (Subgroup.orderOf_mk _ hzP).symm
      _ = 2 ^ j := hj
  have hcomm : ∀ p ∈ P, p * (w : H) = (w : H) * p := by
    intro p hp
    have hpN : p ∈ normalizer (P : Set H) := Subgroup.le_normalizer hp
    have hW1 : w * ⟨p, hpN⟩ * w⁻¹ * ⟨p, hpN⟩⁻¹ ∈ W := by
      have h1 : ⟨p, hpN⟩ * w⁻¹ * ⟨p, hpN⟩⁻¹ ∈ W :=
        Subgroup.Normal.conj_mem inferInstance _ (W.inv_mem hw) ⟨p, hpN⟩
      have : w * ⟨p, hpN⟩ * w⁻¹ * ⟨p, hpN⟩⁻¹ = w * (⟨p, hpN⟩ * w⁻¹ * ⟨p, hpN⟩⁻¹) := by group
      rw [this]
      exact W.mul_mem hw h1
    have hP1 : ((w * ⟨p, hpN⟩ * w⁻¹ * ⟨p, hpN⟩⁻¹ : ↥(normalizer (P : Set H))) : H) ∈ P := by
      have h1 : (w : H) * p * (w : H)⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.1 hwN p).1 hp
      have : ((w * ⟨p, hpN⟩ * w⁻¹ * ⟨p, hpN⟩⁻¹ : ↥(normalizer (P : Set H))) : H) =
          ((w : H) * p * (w : H)⁻¹) * p⁻¹ := rfl
      rw [this]
      exact P.mul_mem h1 (P.inv_mem hp)
    have h1 := hmain _ hW1 hP1
    have h2 : (w : H) * p * (w : H)⁻¹ * p⁻¹ = 1 := congrArg Subtype.val h1
    have h3 : (w : H) * p * (w : H)⁻¹ = p := mul_inv_eq_one.1 h2
    calc p * (w : H) = ((w : H) * p * (w : H)⁻¹) * (w : H) := by rw [h3]
      _ = (w : H) * p := by group
  have hwC : (w : H) ∈ centralizer (P : Set H) := Subgroup.mem_centralizer_iff.2 hcomm
  exact hmain w hw (hC hwC)

theorem normalizer_center_eq_bot (P : Subgroup H) (hC : centralizer (P : Set H) ≤ P)
    (hy : ∃ y ∈ normalizer (P : Set H), ∀ z ∈ P, y * z * y⁻¹ = z → z = 1) :
    center ↥(normalizer (P : Set H)) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hzC : (z : H) ∈ centralizer (P : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have := Subgroup.mem_center_iff.1 hz ⟨p, Subgroup.le_normalizer hp⟩
    exact congrArg Subtype.val this
  have hzP : (z : H) ∈ P := hC hzC
  obtain ⟨y, hyN, hy⟩ := hy
  have h1 : y * (z : H) = (z : H) * y :=
    congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨y, hyN⟩)
  have h2 : y * (z : H) * y⁻¹ = z := mul_inv_eq_iff_eq_mul.2 h1
  exact Subtype.ext (hy z hzP h2)

end Group

section Finite

variable {H : Type} [Group H] [Finite H]

theorem two_le_pRank_centralizer_inf (P : Subgroup H) (hP2 : IsPGroup 2 P) (hPne : P ≠ ⊥)
    (x : H) (hx : x * x = 1) (hxP : x ∉ P) (hxn : ∀ s ∈ P, x * s * x⁻¹ ∈ P)
    (N : Subgroup H) (hPN : P ≤ N) (hxN : x ∈ N) :
    2 ≤ Open.pRank 2 (centralizer ({x} : Set H) ⊓ N) := by
  obtain ⟨u, huP, hu1, hu2, hxu⟩ := exists_fixed_involution hP2 hPne hx hxn
  have hxzu : x ∉ zpowers u := fun hx' => hxP (Subgroup.zpowers_le.2 huP hx')
  have hcomm : u * x = x * u := by
    calc u * x = x * u * x⁻¹ * x := by rw [hxu]
      _ = x * u := by group
  obtain ⟨hel, hcard⟩ := SU1.isElemAbelian_card_sup_zpowers Nat.prime_two (a := u) (y := x)
    (by rw [pow_two]; exact hu2) (by rw [pow_two]; exact hx) hu1 hxzu hcomm
  have hle : zpowers u ⊔ zpowers x ≤ centralizer ({x} : Set H) ⊓ N := by
    refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
    · exact Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 hcomm, hPN huP⟩
    · exact Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 rfl, hxN⟩
  exact SU1.le_pRank (p := 2) (by norm_num) hle hel hcard

end Finite

theorem Cfg.normalizer_two {H : Type} [Group H] [Finite H] {T : Sylow 2 H} {x : H}
    (h : Cfg H T x) (h4 : 4 ≤ Open.twoRank H) (P : Subgroup H) (hP2 : IsPGroup 2 P)
    (hPne : P ≠ ⊥) (hTN : (T : Subgroup H) ≤ normalizer (P : Set H)) (hxP : x ∉ P)
    (hC : centralizer (P : Set H) ≤ P)
    (hy : ∃ y ∈ normalizer (P : Set H), ∀ z ∈ P, y * z * y⁻¹ = z → z = 1) :
    Cfg ↥(normalizer (P : Set H)) (T.subtype hTN) ⟨x, hTN h.xT⟩ ∧
      4 ≤ Open.twoRank ↥(normalizer (P : Set H)) ∧
      fittingSubgroup ↥(normalizer (P : Set H)) ≠ ⊥ ∧
      P.subgroupOf (normalizer (P : Set H)) ≤ fittingSubgroup ↥(normalizer (P : Set H)) := by
  classical
  have hPN : P ≤ normalizer (P : Set H) := Subgroup.le_normalizer
  have hxN : x ∈ normalizer (P : Set H) := hTN h.xT
  have hxx := h.mul_self_x
  have h4N : 4 ≤ Open.twoRank ↥(normalizer (P : Set H)) := by
    have h1 := SU4.pRank_map_of_injective (normalizer (P : Set H)).subtype
      (normalizer (P : Set H)).subtype_injective (⊤ : Subgroup ↥(normalizer (P : Set H)))
    rw [Subgroup.map_top, Subgroup.range_subtype] at h1
    have h2 : Open.twoRank ↥(normalizer (P : Set H)) = Open.pRank 2 (normalizer (P : Set H)) :=
      h1.symm
    have h3 : Open.pRank 2 (T : Subgroup H) ≤ Open.pRank 2 (normalizer (P : Set H)) :=
      SU1.pRank_mono (p := 2) (by norm_num) hTN
    rw [CFSG.ProperTwoGeneratedCore.sylow_two_rank_eq T] at h3
    omega
  have hP'n : (P.subgroupOf (normalizer (P : Set H))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPN).2 le_rfl
  have hP'2 : IsPGroup 2 (P.subgroupOf (normalizer (P : Set H))) := hP2.comap_subtype
  have hP'fit : P.subgroupOf (normalizer (P : Set H)) ≤ fittingSubgroup ↥(normalizer (P : Set H)) :=
    le_sSup ⟨hP'n, hP'2.isNilpotent⟩
  have hfit : fittingSubgroup ↥(normalizer (P : Set H)) ≠ ⊥ := by
    intro hbot
    apply hPne
    rw [eq_bot_iff]
    intro p hp
    have h1 : (⟨p, hPN hp⟩ : ↥(normalizer (P : Set H))) ∈
        P.subgroupOf (normalizer (P : Set H)) := hp
    have h2 := hP'fit h1
    rw [hbot, Subgroup.mem_bot] at h2
    have : p = 1 := congrArg Subtype.val h2
    rw [this]
    exact Subgroup.one_mem _
  have hcrk : Open.pRank 2 (centralizer ({(⟨x, hxN⟩ : ↥(normalizer (P : Set H)))} :
      Set ↥(normalizer (P : Set H)))) = 2 := by
    have hmap : (centralizer ({(⟨x, hxN⟩ : ↥(normalizer (P : Set H)))} :
        Set ↥(normalizer (P : Set H)))).map (normalizer (P : Set H)).subtype =
        centralizer ({x} : Set H) ⊓ normalizer (P : Set H) := by
      ext a
      simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
        Subgroup.coe_subtype]
      constructor
      · rintro ⟨c, hc, rfl⟩
        exact ⟨congrArg Subtype.val hc, c.2⟩
      · rintro ⟨hc, ha⟩
        exact ⟨⟨a, ha⟩, Subtype.ext hc, rfl⟩
    have h1 := SU4.pRank_map_of_injective (normalizer (P : Set H)).subtype
      (normalizer (P : Set H)).subtype_injective (centralizer ({(⟨x, hxN⟩ :
        ↥(normalizer (P : Set H)))} : Set ↥(normalizer (P : Set H))))
    rw [hmap] at h1
    rw [← h1]
    have hxn : ∀ s ∈ P, x * s * x⁻¹ ∈ P := fun s hs =>
      (Subgroup.mem_normalizer_iff.1 hxN s).1 hs
    have hlow := two_le_pRank_centralizer_inf P hP2 hPne x hxx hxP hxn
      (normalizer (P : Set H)) hPN hxN
    have hup : Open.pRank 2 (centralizer ({x} : Set H) ⊓ normalizer (P : Set H)) ≤
        Open.pRank 2 (centralizer ({x} : Set H)) :=
      SU1.pRank_mono (p := 2) (by norm_num) inf_le_left
    have := h.crk
    omega
  refine ⟨⟨?_, by omega, normalizer_center_eq_bot P hC hy, ?_, ?_, hcrk⟩, h4N,
    hfit, hP'fit⟩
  · exact (pPrimeCore_eq_bot_iff).2 fun W hW hWc => by
      have := hW
      exact normalizer_oddCore_eq_bot P hP2 hC W hWc
  · exact Subgroup.mem_subgroupOf.2 h.xT
  · rw [Subgroup.orderOf_mk]
    exact h.x2

end CFSG.GH74.Uniqueness.SU.K.R4
