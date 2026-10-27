module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3Delta5

public section

namespace CFSG.QuasithinUnique.A5.G3

open Equiv CFSG.QuasithinUnique CFSG.Quasithin CFSG.Open

theorem IsDelta5Group.exists_three_comm {B : Type} [Group B] [Finite B] (hD : IsDelta5Group B) :
    ∃ y u : B, orderOf y = 3 ∧ u ∈ CFSG.pCore 2 B ∧ u ≠ 1 ∧ y * u = u * y := by
  classical
  have hcard := hD.card
  obtain ⟨α, β, hαs, hαk, hβb, hβe⟩ := hD
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := B) 3 (by rw [hcard]; norm_num)
  have hy3 : y ^ 3 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have hynot : y ∉ CFSG.pCore 2 B := by
    intro hy_mem
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (G := B) (p := 2)) ⟨y, hy_mem⟩
    have h2 : y ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    have hdvd : 3 ∣ 2 ^ k := hy ▸ orderOf_dvd_of_pow_eq_one h2
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
    omega
  have hyne : α y ≠ 1 := fun h1 => hynot (by rw [← hαk]; exact h1)
  obtain ⟨w, hwe, hwn, hwfix⟩ := fixed_vector_of_order_three
    ((α y : alternatingGroup (Fin 5)) : Perm (Fin 5))
    (Equiv.Perm.mem_alternatingGroup.mp (α y).2) (fun h => hyne (Subtype.ext h))
    (by
      have := congrArg Subtype.val (show (α y) ^ 3 = 1 by rw [← map_pow, hy3, map_one])
      simpa using this)
  obtain ⟨u, hu⟩ := hβb.2 (Multiplicative.ofAdd
    (⟨w, (Delta5.mem_evenWeight_iff w).2 hwe⟩ : evenWeight 5))
  have hmem : y * (u : B) * y⁻¹ ∈ CFSG.pCore 2 B :=
    (CFSG.pCore_normal (G := B) (p := 2)).conj_mem _ u.2 y
  set u2 : ↥(CFSG.pCore 2 B) := ⟨y * u * y⁻¹, hmem⟩ with hu2
  have h2 : β u2 = β u := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    funext i
    have := hβe y u u2 rfl i
    rw [this, hu]
    simpa using hwfix i
  have h3 : u2 = u := hβb.1 h2
  have hcomm : y * (u : B) * y⁻¹ = u := congrArg Subtype.val h3
  have hu1 : (u : B) ≠ 1 := by
    intro h
    have hu1' : u = 1 := Subtype.ext h
    rw [hu1', map_one] at hu
    apply hwn
    have := congrArg (fun z => ((Multiplicative.toAdd z : evenWeight 5) :
      Fin 5 → ZMod 2)) hu
    simpa using this.symm
  exact ⟨y, u, hy, u.2, hu1, mul_inv_eq_iff_eq_mul.mp hcomm⟩

theorem IsDelta5Group.exists_orderOf_six {B : Type} [Group B] [Finite B] (hD : IsDelta5Group B) :
    ∃ g : B, orderOf g = 6 := by
  have hsq := hD.mul_self_eq_one
  obtain ⟨y, u, hy, hu, hu1, hyu⟩ := hD.exists_three_comm
  have hu' : (⟨u, hu⟩ : ↥(CFSG.pCore 2 B)) * ⟨u, hu⟩ = 1 := hsq ⟨u, hu⟩
  have hu2sq : u ^ 2 = 1 := by
    have := congrArg Subtype.val hu'
    simpa [sq] using this
  have hord_u : orderOf u = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime hu2sq hu1
  refine ⟨y * u, ?_⟩
  rw [(show Commute y u from hyu).orderOf_mul_eq_mul_orderOf_of_coprime
    (by rw [hy, hord_u]; norm_num), hy, hord_u]

theorem delta5_sup_data {X : Type} [Group X] [Finite X] {T B : Subgroup X}
    (hT : IsSylowTwoOf T ⊤) (hD : IsDelta5Group ↥B)
    (hTB : T ≤ Subgroup.normalizer (B : Set X)) :
    ∃ j : ℕ, Nat.card ↥T = 2 ^ (6 + j) ∧ Nat.card ↥(B ⊔ T) = 2 ^ j * 960 ∧
      (B.subgroupOf (B ⊔ T)).Normal ∧
      Nat.card (↥(B ⊔ T) ⧸ B.subgroupOf (B ⊔ T)) = 2 ^ j := by
  classical
  have h960 : Nat.card ↥B = 960 := hD.card
  set Y : Subgroup X := B ⊔ T with hY
  have hBY : B ≤ Y := le_sup_left
  have hTY : T ≤ Y := le_sup_right
  have hYN : Y ≤ Subgroup.normalizer (B : Set X) := sup_le Subgroup.le_normalizer hTB
  set N : Subgroup ↥Y := B.subgroupOf Y with hN
  have hNn : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hBY).mpr hYN
  have hTp : IsPGroup 2 ↥(T.subgroupOf Y) :=
    hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTY).symm
  have hsup : N ⊔ T.subgroupOf Y = ⊤ := by
    rw [hN, ← Subgroup.subgroupOf_sup hBY hTY, ← hY, Subgroup.subgroupOf_self]
  have hsurj : Function.Surjective ((QuotientGroup.mk' N).comp (T.subgroupOf Y).subtype) := by
    rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, Subgroup.range_subtype]
    have h1 : (N ⊔ T.subgroupOf Y).map (QuotientGroup.mk' N) = ⊤ := by
      rw [hsup]
      exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq] at h1
    exact h1
  have hQp : IsPGroup 2 (↥Y ⧸ N) := IsPGroup.of_surjective (hTp) _ hsurj
  obtain ⟨j, hj⟩ := hQp.exists_card_eq
  have hNcard : Nat.card N = 960 := by
    rw [hN, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBY).toEquiv, h960]
  have hYcard : Nat.card ↥Y = 2 ^ j * 960 := by
    rw [← hj, ← hNcard]
    exact (Subgroup.card_eq_card_quotient_mul_card_subgroup N)
  have ht2Y : Nat.card ↥T ∣ Nat.card ↥Y := Subgroup.card_dvd_of_le hTY
  obtain ⟨s, hs⟩ := hT.2.1.exists_card_eq
  have hid : 2 ^ j * 960 = 2 ^ (6 + j) * 15 := by rw [pow_add]; ring
  have hsj : s = 6 + j := by
    have h1 : 2 ^ s ∣ 2 ^ (6 + j) * 15 := by
      rw [← hs, ← hid, ← hYcard]
      exact ht2Y
    have h2 : 2 ^ s ∣ 2 ^ (6 + j) :=
      Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_left s (by norm_num : Nat.Coprime 2 15))
        h1
    have h3 : s ≤ 6 + j := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h2
    have h4 : 2 ^ (6 + j) ∣ Nat.card X := by
      have h5 : 2 ^ (6 + j) ∣ Nat.card ↥Y := by
        rw [hYcard, show 2 ^ (6 + j) = 2 ^ j * 64 by rw [pow_add]; ring]
        exact mul_dvd_mul_left _ (by norm_num)
      exact h5.trans (Subgroup.card_subgroup_dvd_card Y)
    have hidx : Nat.card X = Nat.card ↥T * T.index := (Subgroup.card_mul_index T).symm
    have hodd : ¬ 2 ∣ T.index := by
      have h1 : (T.subgroupOf (⊤ : Subgroup X)).index = T.index := Subgroup.relIndex_top_right T
      have := hT.2.2
      rwa [h1] at this
    have hcop : Nat.Coprime (2 ^ (6 + j)) T.index :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
    have h6 : 2 ^ (6 + j) ∣ 2 ^ s := by
      rw [hidx, hs] at h4
      exact hcop.dvd_of_dvd_mul_right h4
    have h7 : 6 + j ≤ s := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h6
    omega
  refine ⟨j, by rw [hs, hsj], hYcard, hNn, ?_⟩
  rw [← hj]

end CFSG.QuasithinUnique.A5.G3
