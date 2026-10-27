module

public import CFSG.GH74.Constrained
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Closed
public import CFSG.LocalAnalysis.ComponentInitial.EmptyLayerCharTwo

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem eq_one_of_odd_orderOf_of_mem {Y : Type*} [Group Y] {P : Subgroup Y}
    (hP : IsPGroup 2 P) {a : Y} (hao : Odd (orderOf a)) (haP : a ∈ P) : a = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨a, haP⟩
  have h1 : a ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  have h2 : orderOf a ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
  have h3 : Nat.Coprime (orderOf a) (2 ^ k) := (Nat.coprime_two_right.mpr hao).pow_right k
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd h3 h2)

theorem odd_orderOf_of_mem_odd {X : Type*} [Group X] [Finite X] {D : Subgroup X}
    (hD : Odd (Nat.card D)) {d : X} (hd : d ∈ D) : Odd (orderOf d) := by
  have h1 : orderOf (⟨d, hd⟩ : D) ∣ Nat.card D := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at h1
  exact Odd.of_dvd_nat hD h1

theorem odd_le_pPrimeCore_of_twoConstrained {X : Type} [Group X] [Finite X]
    (hAB : IG_11_7) (hX : IsTwoConstrained X) {D : Subgroup X} (hD : Odd (Nat.card D))
    {z : X}
    (hz : orderOf z = 2) (hDz : D ≤ centralizer ({z} : Set X))
    (hn : ∀ x ∈ centralizer ({z} : Set X), ∀ d ∈ D, x * d * x⁻¹ ∈ D) :
    D ≤ pPrimeCore 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := pPrimeCore 2 X with hO
  set π : X →* X ⧸ O := QuotientGroup.mk' O with hπ
  set P : Subgroup (X ⧸ O) := pCore 2 (X ⧸ O) with hP
  have hPp : IsPGroup 2 P := pCore_isPGroup
  have hPn : P.Normal := pCore_normal
  have hz2 : z ^ 2 = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz] at this
  have hDodd : ∀ d ∈ D, Odd (orderOf d) := fun d hd => odd_orderOf_of_mem_odd hD hd
  set A : Subgroup (X ⧸ O) := D.map π with hA
  set B : Subgroup (X ⧸ O) := zpowers (π z) with hB
  have hBp : IsPGroup 2 B := by
    have hy : (π z) ^ (2 ^ 1) = 1 := by
      rw [pow_one, ← map_pow, hz2, map_one]
    rintro ⟨g, hg⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy, one_zpow]
  have hAcop : Nat.Coprime 2 (Nat.card A) := by
    have h1 : Nat.card A ∣ Nat.card D :=
      Subgroup.card_dvd_of_surjective (π.subgroupMap_surjective D)
    exact Nat.coprime_two_left.mpr (Odd.of_dvd_nat hD h1)
  have hAN : A ≤ normalizer (P : Set (X ⧸ O)) := fun a _ => by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    exact ⟨fun hy => hPn.conj_mem y hy a, fun hy => by
      have := hPn.conj_mem _ hy a⁻¹
      simpa [mul_assoc] using this⟩
  have hBN : B ≤ normalizer (P : Set (X ⧸ O)) := fun a _ => by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    exact ⟨fun hy => hPn.conj_mem y hy a, fun hy => by
      have := hPn.conj_mem _ hy a⁻¹
      simpa [mul_assoc] using this⟩
  have hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
    rintro _ ⟨d, hd, rfl⟩ b hb
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hc : Commute (π d) (π z) := by
      have := mem_centralizer_singleton_iff.mp (hDz hd)
      exact congrArg π this
    exact (hc.zpow_right n).eq
  have hfix : A ≤ centralizer ((P ⊓ centralizer (B : Set (X ⧸ O)) : Subgroup (X ⧸ O)) :
      Set (X ⧸ O)) := by
    rintro _ ⟨d, hd, rfl⟩
    rw [mem_centralizer_iff]
    intro w hw
    have hwz : w ∈ centralizer ({π z} : Set (X ⧸ O)) := by
      rw [mem_centralizer_singleton_iff]
      exact (mem_centralizer_iff.mp hw.2 (π z) (mem_zpowers _)).symm
    rw [hπ, centralizer_involution_pPrimeCore_quotient_eq_map hz] at hwz
    obtain ⟨x, hx, rfl⟩ := hwz
    have hxP : π x ∈ P := hw.1
    have hc : x * d * x⁻¹ * d⁻¹ ∈ D := D.mul_mem (hn x hx d hd) (D.inv_mem hd)
    have hcodd : Odd (orderOf (π (x * d * x⁻¹ * d⁻¹))) :=
      Odd.of_dvd_nat (hDodd _ hc) (orderOf_map_dvd π _)
    have hcP : π (x * d * x⁻¹ * d⁻¹) ∈ P := by
      have : π (x * d * x⁻¹ * d⁻¹) = π x * (π d * (π x)⁻¹ * (π d)⁻¹) := by
        simp only [map_mul, map_inv]; group
      rw [this]
      exact P.mul_mem hxP (hPn.conj_mem _ (P.inv_mem hxP) (π d))
    have h1 : π (x * d * x⁻¹ * d⁻¹) = 1 := eq_one_of_odd_orderOf_of_mem hPp hcodd hcP
    simp only [map_mul, map_inv] at h1
    have h2 : π x * π d = π d * π x := by
      have := mul_inv_eq_one.mp h1
      calc π x * π d = π x * π d * (π x)⁻¹ * π x := by group
        _ = π d * π x := by rw [this]
    exact h2
  have key := hAB (X ⧸ O) 2 Nat.prime_two A B P hPp hBp hAcop hAN hBN hcomm hfix
  intro d hd
  have h1 : π d ∈ P := hX (key ⟨d, hd, rfl⟩)
  have h2 : π d = 1 :=
    eq_one_of_odd_orderOf_of_mem hPp (Odd.of_dvd_nat (hDodd d hd) (orderOf_map_dvd π d)) h1
  exact (QuotientGroup.eq_one_iff d).mp h2

theorem pPrimeCoreOf_norm {G : Type} [Group G] {H : Subgroup G} {m : G} (hm : m ∈ H) {x : G}
    (hx : x ∈ pPrimeCoreOf 2 H) : m * x * m⁻¹ ∈ pPrimeCoreOf 2 H := by
  obtain ⟨x', hx', rfl⟩ := hx
  exact ⟨⟨m, hm⟩ * x' * ⟨m, hm⟩⁻¹, (pPrimeCore_normal (p := 2) (G := ↥H)).conj_mem x' hx' ⟨m, hm⟩,
    by simp⟩

theorem le_normalizer_pPrimeCoreOf {G : Type} [Group G] (H : Subgroup G) :
    H ≤ normalizer (pPrimeCoreOf 2 H : Set G) := fun m hm => by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  exact ⟨fun hy => pPrimeCoreOf_norm hm hy, fun hy => by
    have := pPrimeCoreOf_norm (H.inv_mem hm) hy
    simpa [mul_assoc] using this⟩

theorem odd_card_pPrimeCoreOf' {G : Type} [Group G] [Finite G] (H : Subgroup G) :
    Odd (Nat.card ↥(pPrimeCoreOf 2 H)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : Nat.card ↥(pPrimeCoreOf 2 H) = Nat.card ↥(pPrimeCore 2 ↥H) :=
    Subgroup.card_map_of_injective H.subtype_injective
  rw [h1]
  exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥H))

theorem isTwoConstrained_of_pLayerOf_eq_bot {G : Type} [Group G] [Finite G] {M : Subgroup G}
    (h : pLayerOf 2 M = ⊥) : IsTwoConstrained ↥M := by
  refine isTwoConstrained_of_layer_eq_bot (sSup_eq_bot.2 fun K hK => ?_)
  obtain ⟨L, hL, hmap⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.exists_isPComponent_of_isComponent 2 hK
  have hJ : IsPCompIn 2 M (L.map M.subtype) :=
    ⟨Subgroup.map_subtype_le L, by
      rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
      exact hL⟩
  have hle : L.map M.subtype ≤ pLayerOf 2 M := le_sSup hJ
  rw [h, le_bot_iff] at hle
  have hL0 : L = ⊥ := (Subgroup.map_eq_bot_iff_of_injective L M.subtype_injective).1 hle
  rw [← hmap, hL0, Subgroup.map_bot]

theorem pPrimeCoreOf_map_subtype {G : Type} [Group G] {M : Subgroup G} (L : Subgroup ↥M) :
    pPrimeCoreOf 2 (L.map M.subtype) = (pPrimeCoreOf 2 L).map M.subtype := by
  let e : ↥L ≃* ↥(L.map M.subtype) :=
    Subgroup.equivMapOfInjective L M.subtype M.subtype_injective
  have h1 := pPrimeCore_map_iso 2 e
  unfold pPrimeCoreOf
  rw [← h1, Subgroup.map_map, Subgroup.map_map]
  congr 1

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S2
