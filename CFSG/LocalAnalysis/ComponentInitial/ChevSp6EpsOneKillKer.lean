module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneKillSylowBase

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne

open Subgroup

section Kernel

variable {G : Type*} [Group G] {Jh E : Subgroup G}

@[expose] def kerSub (hEJ : E ≤ Jh) : Subgroup G where
  carrier := {x | x ∈ normalizer (Jh : Set G) ∧ ∀ j ∈ Jh, x * j * x⁻¹ * j⁻¹ ∈ E}
  mul_mem' := by
    rintro x y ⟨hxN, hx⟩ ⟨hyN, hy⟩
    refine ⟨mul_mem hxN hyN, fun j hj => ?_⟩
    have he := hy j hj
    have hxe : x * (y * j * y⁻¹ * j⁻¹) * x⁻¹ ∈ E := by
      have h1 := hx _ (hEJ he)
      have : x * (y * j * y⁻¹ * j⁻¹) * x⁻¹ =
          x * (y * j * y⁻¹ * j⁻¹) * x⁻¹ * (y * j * y⁻¹ * j⁻¹)⁻¹ * (y * j * y⁻¹ * j⁻¹) := by
        group
      rw [this]
      exact mul_mem h1 he
    have : x * y * j * (x * y)⁻¹ * j⁻¹ =
        x * (y * j * y⁻¹ * j⁻¹) * x⁻¹ * (x * j * x⁻¹ * j⁻¹) := by group
    rw [this]
    exact mul_mem hxe (hx j hj)
  one_mem' := ⟨one_mem _, fun j _ => by simp⟩
  inv_mem' := by
    rintro x ⟨hxN, hx⟩
    refine ⟨inv_mem hxN, fun j hj => ?_⟩
    have hm : x⁻¹ * j * x ∈ Jh := by
      have := (mem_normalizer_iff.1 (inv_mem hxN) j).1 hj
      simpa using this
    have h1 := inv_mem (hx _ hm)
    have : x⁻¹ * j * x⁻¹⁻¹ * j⁻¹ = (x * (x⁻¹ * j * x) * x⁻¹ * (x⁻¹ * j * x)⁻¹)⁻¹ := by group
    rw [this]
    exact h1

@[expose] def extSub (K : Subgroup G) {z : G} (hzK : ∀ x ∈ K, z * x * z⁻¹ ∈ K)
    (hz2 : z * z = 1) : Subgroup G where
  carrier := {x | x ∈ K ∨ x * z ∈ K}
  mul_mem' := by
    have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
    have hconj : ∀ y ∈ K, z⁻¹ * y * z ∈ K := fun y hy => by
      have := hzK y hy
      rw [hzi] at this
      rw [hzi]
      exact this
    rintro x y (hx | hx) (hy | hy)
    · exact Or.inl (mul_mem hx hy)
    · exact Or.inr (by rw [mul_assoc]; exact mul_mem hx hy)
    · refine Or.inr ?_
      have : x * y * z = (x * z) * (z⁻¹ * y * z) := by group
      rw [this]
      exact mul_mem hx (hconj y hy)
    · refine Or.inl ?_
      have : x * y = (x * z) * (z⁻¹ * (y * z) * z) * (z⁻¹ * z⁻¹) := by group
      rw [this, show z⁻¹ * z⁻¹ = 1 by rw [hzi, hz2], mul_one]
      exact mul_mem hx (hconj _ hy)
  one_mem' := Or.inl (one_mem _)
  inv_mem' := by
    have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
    rintro x (hx | hx)
    · exact Or.inl (inv_mem hx)
    · refine Or.inr ?_
      have : x⁻¹ * z = z * (x * z)⁻¹ * z⁻¹ := by rw [hzi]; group
      rw [this]
      exact hzK _ (inv_mem hx)

theorem card_extSub (K : Subgroup G) {z : G} (hzK : ∀ x ∈ K, z * x * z⁻¹ ∈ K)
    (hz2 : z * z = 1) (hz : z ∉ K) : Nat.card (extSub K hzK hz2) = 2 * Nat.card K := by
  have hKY : K ≤ extSub K hzK hz2 := fun x hx => Or.inl hx
  have hzY : z ∈ extSub K hzK hz2 := Or.inr (by rw [hz2]; exact one_mem _)
  have hidx : (K.subgroupOf (extSub K hzK hz2)).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨z, hzY⟩, fun b => ?_⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    rcases b.2 with hb | hb
    · exact Or.inr ⟨hb, fun hbz => hz (by
        have := mul_mem (inv_mem hb) hbz
        rwa [← mul_assoc, inv_mul_cancel, one_mul] at this)⟩
    · exact Or.inl ⟨hb, fun hb' => hz (by
        have := mul_mem (inv_mem hb') hb
        rwa [← mul_assoc, inv_mul_cancel, one_mul] at this)⟩
  rw [← Subgroup.card_mul_index (K.subgroupOf (extSub K hzK hz2)), hidx,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKY).toEquiv, mul_comm]

theorem card_le_of_kernel [Finite G] {D : Subgroup G} {z : G} (hEJ : E ≤ Jh)
    (hcomm : ∀ x ∈ Jh, ∀ y ∈ Jh, x * y * x⁻¹ * y⁻¹ ∈ E)
    (hJ2 : IsPGroup 2 Jh) (hD : Jh ⊔ zpowers z = D) (hcardD : Nat.card D = 2 * Nat.card Jh)
    (hzJ : z ∈ normalizer (Jh : Set G)) (hz2 : z * z = 1) (hzE : ∀ e ∈ E, z * e * z⁻¹ ∈ E)
    (hzK : ∃ j ∈ Jh, z * j * z⁻¹ * j⁻¹ ∉ E)
    (hker : ∀ x ∈ normalizer (Jh : Set G), x ∈ normalizer (D : Set G) →
      (∀ j ∈ Jh, x * j * x⁻¹ * j⁻¹ ∈ E) → x ∈ Jh)
    {P : Subgroup G} (hP : IsPGroup 2 P) (hPK : P ≤ kerSub hEJ) :
    Nat.card P ≤ Nat.card Jh := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := kerSub hEJ with hKdef
  have hzKK : ∀ x ∈ K, z * x * z⁻¹ ∈ K := by
    rintro x ⟨hxN, hx⟩
    refine ⟨mul_mem (mul_mem hzJ hxN) (inv_mem hzJ), fun j hj => ?_⟩
    have hj' : z⁻¹ * j * z ∈ Jh := by
      have := (mem_normalizer_iff.1 (inv_mem hzJ) j).1 hj
      simpa using this
    have := hzE _ (hx _ hj')
    have e : z * x * z⁻¹ * j * (z * x * z⁻¹)⁻¹ * j⁻¹ =
        z * (x * (z⁻¹ * j * z) * x⁻¹ * (z⁻¹ * j * z)⁻¹) * z⁻¹ := by group
    rw [e]
    exact this
  have hzK' : z ∉ K := by
    rintro ⟨-, hz⟩
    obtain ⟨j, hj, hjE⟩ := hzK
    exact hjE (hz j hj)
  have hJK : Jh ≤ K := fun j hj => ⟨Jh_le_X hj, fun j' hj' => hcomm j hj j' hj'⟩
  have hKY : K ≤ extSub K hzKK hz2 := fun x hx => Or.inl hx
  have hzY : z ∈ extSub K hzKK hz2 := Or.inr (by rw [hz2]; exact one_mem _)
  have hDY : D ≤ extSub K hzKK hz2 := hD ▸ sup_le (hJK.trans hKY) (zpowers_le.2 hzY)
  have hD2 : IsPGroup 2 D := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hJ2
    exact IsPGroup.of_card (n := k + 1) (by rw [hcardD, hk, pow_succ, mul_comm])
  obtain ⟨R, hR⟩ := (hD2.comap_of_injective (extSub K hzKK hz2).subtype
    (Subgroup.subtype_injective _)).exists_le_sylow
  have hR'2 : IsPGroup 2 ((R : Subgroup (extSub K hzKK hz2)).map (extSub K hzKK hz2).subtype) :=
    R.2.map _
  have hDR : D ≤ (R : Subgroup (extSub K hzKK hz2)).map (extSub K hzKK hz2).subtype :=
    fun d hd => ⟨⟨d, hDY hd⟩, hR (Subgroup.mem_comap.2 hd), rfl⟩
  refine Nat.le_of_not_lt fun hlt => ?_
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hP
  have hPK' : 2 ^ a ∣ Nat.card K := ha ▸ Subgroup.card_dvd_of_le hPK
  have hdvd : 2 ^ (a + 1) ∣ Nat.card (extSub K hzKK hz2) := by
    rw [card_extSub K hzKK hz2 hzK', pow_succ, mul_comm]
    exact Nat.mul_dvd_mul_left 2 hPK'
  have hRc : 2 ^ (a + 1) ∣ Nat.card R := R.pow_dvd_card_of_pow_dvd_card hdvd
  have hR'c : Nat.card ((R : Subgroup (extSub K hzKK hz2)).map (extSub K hzKK hz2).subtype) =
      Nat.card R := Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
  have h1 : 2 ^ (a + 1) ≤
      Nat.card ((R : Subgroup (extSub K hzKK hz2)).map (extSub K hzKK hz2).subtype) :=
    hR'c ▸ Nat.le_of_dvd Nat.card_pos hRc
  have hlt' : Nat.card D <
      Nat.card ((R : Subgroup (extSub K hzKK hz2)).map (extSub K hzKK hz2).subtype) := by
    rw [hcardD]
    calc 2 * Nat.card Jh < 2 * 2 ^ a := by rw [← ha]; omega
      _ = 2 ^ (a + 1) := by ring
      _ ≤ _ := h1
  have hDlt : D < (R : Subgroup (extSub K hzKK hz2)).map (extSub K hzKK hz2).subtype :=
    lt_of_le_of_ne hDR fun h => by rw [h] at hlt'; exact lt_irrefl _ hlt'
  obtain ⟨n, hnR, hnN, hnD⟩ := exists_mem_normalizer_not_mem_of_lt hR'2 hDlt
  have hnY : n ∈ extSub K hzKK hz2 := by
    obtain ⟨y, -, rfl⟩ := hnR
    exact y.2
  have hzD : z ∈ D := hD ▸ mem_sup_right (mem_zpowers z)
  rcases hnY with hnK | hnzK
  · exact hnD (hD ▸ mem_sup_left (hker n hnK.1 hnN hnK.2))
  · have hnzN : n * z ∈ normalizer (D : Set G) := mul_mem hnN (Jh_le_X hzD)
    have hJ := hker (n * z) hnzK.1 hnzN hnzK.2
    apply hnD
    have e : n = (n * z) * z⁻¹ := by group
    rw [e]
    exact mul_mem (hD ▸ mem_sup_left hJ) (inv_mem hzD)

end Kernel

end CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne
