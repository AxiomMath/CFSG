module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3Delta5Six
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3SporRows

public section

namespace CFSG.QuasithinUnique.A5.G3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def J4Normalizer3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSporadic .J4 X → ∀ P N : Subgroup X, Nat.card P = 3 →
    N ≤ Subgroup.normalizer (P : Set X) → ¬ 2 ^ 16 ∣ Nat.card N

theorem map_subtype_le_normalizer {X : Type} [Group X] {Y : Subgroup X} {P M : Subgroup ↥Y}
    (h : M ≤ Subgroup.normalizer (P : Set ↥Y)) :
    M.map Y.subtype ≤ Subgroup.normalizer ((P.map Y.subtype : Subgroup X) : Set X) := by
  rintro _ ⟨m, hm, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hm' := Subgroup.mem_normalizer_iff.mp (h hm)
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨m * p * m⁻¹, (hm' p).mp hp, by simp⟩
  · rintro ⟨p, hp, hpx⟩
    have hxe : x = (m : X)⁻¹ * (p : X) * (m : X) := by
      have : (p : X) = (m : X) * x * (m : X)⁻¹ := hpx
      rw [this]
      group
    have hxY : x ∈ Y := by
      rw [hxe]
      exact Y.mul_mem (Y.mul_mem (Y.inv_mem m.2) p.2) m.2
    have hxP : (⟨x, hxY⟩ : ↥Y) ∈ P := by
      rw [hm' ⟨x, hxY⟩]
      have : m * ⟨x, hxY⟩ * m⁻¹ = p := by
        apply Subtype.ext
        have : (p : X) = (m : X) * x * (m : X)⁻¹ := hpx
        simpa using this.symm
      rw [this]
      exact hp
    exact ⟨⟨x, hxY⟩, hxP, rfl⟩

theorem exists_normalizer_dvd {X : Type} [Group X] [Finite X] {T B : Subgroup X}
    (hT : IsSylowTwoOf T ⊤) (hcard : Nat.card T = 2 ^ 21) (hD : IsDelta5Group ↥B)
    (hTB : T ≤ Subgroup.normalizer (B : Set X)) :
    ∃ P N : Subgroup X, Nat.card P = 3 ∧ N ≤ Subgroup.normalizer (P : Set X) ∧
      2 ^ 16 ∣ Nat.card N := by
  classical
  obtain ⟨j, hj1, hj2, hnorm, hq⟩ := delta5_sup_data hT hD hTB
  have hj : j = 15 := by
    have h2 : 2 ^ (6 + j) = 2 ^ 21 := by rw [← hj1, hcard]
    have := Nat.pow_right_injective (le_refl 2) h2
    omega
  subst hj
  have hBY : B ≤ B ⊔ T := le_sup_left
  have : (B.subgroupOf (B ⊔ T)).Normal := hnorm
  obtain ⟨y, u, hy3, hu, hu1, hyu⟩ := hD.exists_three_comm
  have hu2sq : u ^ 2 = 1 := by
    have h0 : (⟨u, hu⟩ : ↥(CFSG.pCore 2 ↥B)) * ⟨u, hu⟩ = 1 := hD.mul_self_eq_one ⟨u, hu⟩
    have := congrArg Subtype.val h0
    simpa [sq] using this
  have hord_u : orderOf u = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime hu2sq hu1
  let ι : ↥B →* ↥(B ⊔ T) := Subgroup.inclusion hBY
  have hι : Function.Injective ι := Subgroup.inclusion_injective hBY
  have hy'3 : orderOf (ι y) = 3 := (orderOf_injective ι hι y).trans hy3
  have hu'2 : orderOf (ι u) = 2 := (orderOf_injective ι hι u).trans hord_u
  have hcomm : Commute (ι y) (ι u) := by
    show ι y * ι u = ι u * ι y
    rw [← map_mul, ← map_mul, hyu]
  set P : Subgroup ↥(B ⊔ T) := Subgroup.zpowers (ι y) with hP
  have hP3 : Nat.card P = 3 := by rw [hP, Nat.card_zpowers, hy'3]
  have hPN : P ≤ B.subgroupOf (B ⊔ T) :=
    (Subgroup.zpowers_le).mpr (show ι y ∈ B.subgroupOf (B ⊔ T) from y.2)
  have hPgrp : IsPGroup 3 ↥P := IsPGroup.of_card (n := 1) (by rw [hP3]; norm_num)
  have hindex : ¬ 3 ∣ P.index := by
    have h1 := Subgroup.index_mul_card P
    rw [hP3, hj2] at h1
    omega
  let P₃ : Sylow 3 ↥(B ⊔ T) := hPgrp.toSylow hindex
  have hFr : Subgroup.normalizer (P : Set ↥(B ⊔ T)) ⊔ B.subgroupOf (B ⊔ T) = ⊤ :=
    Sylow.normalizer_sup_eq_top' P₃ hPN
  set M : Subgroup ↥(B ⊔ T) := Subgroup.normalizer (P : Set ↥(B ⊔ T)) with hM
  have hrel : (B.subgroupOf (B ⊔ T)).relIndex M = 2 ^ 15 := by
    have h1 := Subgroup.relIndex_sup_right (H := M) (K := B.subgroupOf (B ⊔ T))
    rw [hFr, Subgroup.relIndex_top_right] at h1
    rw [← h1]
    exact hq
  have hMcard : Nat.card M = Nat.card ((B.subgroupOf (B ⊔ T)).subgroupOf M) * 2 ^ 15 := by
    rw [← hrel]
    exact (Subgroup.card_mul_index ((B.subgroupOf (B ⊔ T)).subgroupOf M)).symm
  have huC : ι u ∈ Subgroup.centralizer (P : Set ↥(B ⊔ T)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact (hcomm.zpow_left k).eq
  have huM : ι u ∈ M := Subgroup.centralizer_le_normalizer (P : Set ↥(B ⊔ T)) huC
  have h2 : 2 ∣ Nat.card ((B.subgroupOf (B ⊔ T)).subgroupOf M) := by
    let x : ↥((B.subgroupOf (B ⊔ T)).subgroupOf M) := ⟨⟨ι u, huM⟩, u.2⟩
    have hx : orderOf x = 2 := by
      rw [← Subgroup.orderOf_coe x, ← Subgroup.orderOf_coe (x : ↥M)]
      exact hu'2
    rw [← hx]
    exact orderOf_dvd_natCard x
  refine ⟨P.map (B ⊔ T).subtype, M.map (B ⊔ T).subtype, ?_,
    map_subtype_le_normalizer (le_refl M), ?_⟩
  · rw [Subgroup.card_map_of_injective (B ⊔ T).subtype_injective, hP3]
  · rw [Subgroup.card_map_of_injective (B ⊔ T).subtype_injective, hMcard]
    obtain ⟨c, hc⟩ := h2
    exact ⟨c, by rw [hc]; ring⟩

theorem a314J4NoDelta5_of_normalizer
    (h : J4Normalizer3) : A314J4NoDelta5 := by
  intro G _ _ Λ B T hΛ hT hBΛ hTB hD
  obtain ⟨e⟩ := hΛ
  have hT' : IsSylowTwoOf (T.subgroupOf Λ) (⊤ : Subgroup ↥Λ) := isSylowTwoOf_top_subgroupOf hT
  have hD' : IsDelta5Group ↥(B.subgroupOf Λ) :=
    hD.of_equiv (Subgroup.subgroupOfEquivOfLe hBΛ).symm
  have hTB' : T.subgroupOf Λ ≤ Subgroup.normalizer ((B.subgroupOf Λ : Subgroup ↥Λ) : Set ↥Λ) :=
    subgroupOf_le_normalizer hTB
  have hΛcard : Nat.card ↥Λ = 2 ^ 21 * 41377816699065 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.J4.card_J4.trans (by norm_num)
  have hTcard : Nat.card ↥(T.subgroupOf Λ) = 2 ^ 21 :=
    card_eq_of_isSylowTwoOf hT' (by norm_num) hΛcard
  obtain ⟨P, N, hP3, hN, hdvd⟩ := exists_normalizer_dvd hT' hTcard hD' hTB'
  exact h ↥Λ ⟨e⟩ P N hP3 hN hdvd

end CFSG.QuasithinUnique.A5.G3
