module

public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Core
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Squares

public section

namespace CFSG.QuasithinUnique.DoubleA3

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem mem_zpowers_iff_of_sq_eq_one {z u : G} (hz : z ^ 2 = 1) :
    u ∈ Subgroup.zpowers z ↔ u = 1 ∨ u = z := by
  constructor
  · rintro ⟨k, rfl⟩
    show z ^ k = 1 ∨ z ^ k = z
    have h2 : z ^ (2 * (k / 2)) = 1 := by
      rw [zpow_mul]
      have : z ^ (2 : ℤ) = 1 := by exact_mod_cast hz
      rw [this, one_zpow]
    have hk' : k = 2 * (k / 2) + k % 2 := by omega
    have hk : z ^ k = z ^ (k % 2) := by
      conv_lhs => rw [hk']
      rw [zpow_add, h2, one_mul]
    rw [hk]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left; rw [h]; simp
    · right; rw [h]; simp
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact Subgroup.mem_zpowers _

theorem mem_or_mul_inv_mem_of_index_two {K : Type*} [Group K] {H : Subgroup K}
    (hH : H.index = 2) {a : K} (ha : a ∉ H) (b : K) : b ∈ H ∨ b * a⁻¹ ∈ H := by
  obtain ⟨a', ha'⟩ := Subgroup.index_eq_two_iff.mp hH
  by_cases hb : b ∈ H
  · exact Or.inl hb
  · right
    have h1 : a * a' ∈ H := by
      rcases ha' a with ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · exact absurd h ha
    have h2 : b * a' ∈ H := by
      rcases ha' b with ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · exact absurd h hb
    have : b * a⁻¹ = (b * a') * (a * a')⁻¹ := by group
    rw [this]
    exact H.mul_mem h2 (H.inv_mem h1)

theorem exists_central_of_normal [Finite G] {U B : Subgroup G}
    (hUbot : U ≠ ⊥) (hUB : U ≤ B) (hBN : B ≤ normalizer (U : Set G)) (hB2 : IsPGroup 2 B) :
    ∃ z ∈ U, z ≠ 1 ∧ ∀ y ∈ B, y * z = z * y := by
  classical
  have hnil : Group.IsNilpotent B := hB2.isNilpotent
  let H : Subgroup B := U.subgroupOf B
  have hHn : H.Normal := ⟨fun n hn g => by
    have hn' : (n : G) ∈ U := hn
    exact (Subgroup.mem_normalizer_iff.mp (hBN g.2) (n : G)).mp hn'⟩
  have hH0 : H ≠ ⊥ := by
    intro h
    apply hUbot
    rw [eq_bot_iff]
    intro u hu
    have : (⟨u, hUB hu⟩ : B) ∈ H := hu
    rw [h] at this
    have h1 : (⟨u, hUB hu⟩ : B) = 1 := this
    have h2 : u = 1 := congrArg Subtype.val h1
    rw [h2]; exact one_mem _
  have hne : H ⊓ Subgroup.center B ≠ ⊥ := Group.IsNilpotent.inf_center_ne_bot_of_normal hH0
  obtain ⟨⟨w, hwH, hwc⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  refine ⟨(w : G), hwH, ?_, ?_⟩
  · intro h
    apply hw1
    apply Subtype.ext
    apply Subtype.ext
    exact h
  · intro y hy
    have := Subgroup.mem_center_iff.mp hwc ⟨y, hy⟩
    exact congrArg Subtype.val this

theorem card_eq_card_mul_relIndex_of_le [Finite G] {H K : Subgroup G} (h : H ≤ K) :
    Nat.card K = Nat.card H * H.relIndex K := by
  rw [Subgroup.relIndex]
  have := Subgroup.card_mul_index (H.subgroupOf K)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv] at this
  exact this.symm

theorem klein_structure [Finite G] {U B : Subgroup G}
    (hU4 : Nat.card U = 4) (hU2 : ∀ a ∈ U, a ^ 2 = 1)
    (hUB : U ≤ B) (hBN : B ≤ normalizer (U : Set G)) (hB2 : IsPGroup 2 B)
    (hnt : ¬ B ≤ centralizer (U : Set G)) :
    ∃ z ∈ U, z ≠ 1 ∧ (B ⊓ centralizer (U : Set G)).relIndex B = 2 ∧
      U ⊓ centralizer (B : Set G) = zpowers z ∧ ⁅U, B⁆ = zpowers z ∧
      (∀ y ∈ B, y ∉ centralizer (U : Set G) → ∀ u ∈ U, (u ∈ zpowers z ↔ u * y = y * u)) := by
  classical
  have hUbot : U ≠ ⊥ := by
    intro h; rw [h, Subgroup.card_bot] at hU4; omega
  obtain ⟨z, hzU, hz1, hzc⟩ := exists_central_of_normal hUbot hUB hBN hB2
  have hz2 : z ^ 2 = 1 := hU2 z hzU
  have hzz : z * z = 1 := by simpa [pow_two] using hz2
  have hzmem : ∀ u : G, u ∈ Subgroup.zpowers z ↔ u = 1 ∨ u = z :=
    fun u => mem_zpowers_iff_of_sq_eq_one hz2
  have hzle : Subgroup.zpowers z ≤ U := (Subgroup.zpowers_le).mpr hzU
  have hord : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  have hcz : Nat.card (Subgroup.zpowers z) = 2 := by rw [Nat.card_zpowers, hord]
  have hrel : (Subgroup.zpowers z).relIndex U = 2 := by
    have := card_eq_card_mul_relIndex_of_le hzle
    rw [hU4, hcz] at this
    omega
  have hex : ∃ a ∈ U, a ∉ Subgroup.zpowers z := by
    by_contra hcon
    have hle : U ≤ Subgroup.zpowers z := fun u hu => by
      by_contra h; exact hcon ⟨u, hu, h⟩
    have := (Subgroup.relIndex_eq_one (H := Subgroup.zpowers z) (K := U)).mpr hle
    omega
  obtain ⟨a, haU, haz⟩ := hex
  have ha2 : a ^ 2 = 1 := hU2 a haU
  have hainv : a⁻¹ = a := by
    have : a * a = 1 := by simpa [pow_two] using ha2
    exact inv_eq_of_mul_eq_one_right this
  have hUdesc : ∀ u ∈ U, u = 1 ∨ u = z ∨ u = a ∨ u = z * a := by
    intro u hu
    have hidx : ((Subgroup.zpowers z).subgroupOf U).index = 2 := hrel
    have hanot : (⟨a, haU⟩ : U) ∉ (Subgroup.zpowers z).subgroupOf U := haz
    rcases mem_or_mul_inv_mem_of_index_two hidx hanot ⟨u, hu⟩ with h | h
    · have h' : u ∈ Subgroup.zpowers z := h
      rcases (hzmem u).mp h' with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
    · have h' : u * a⁻¹ ∈ Subgroup.zpowers z := h
      rw [hainv] at h'
      rcases (hzmem (u * a)).mp h' with h1 | h1
      · right; right; left
        have := mul_eq_one_iff_eq_inv.mp h1
        rw [this, hainv]
      · right; right; right
        have := eq_mul_inv_of_mul_eq h1
        rw [this, hainv]
  have hza_ne : z * a ≠ a := by
    intro h
    apply hz1
    have : z * a = 1 * a := by rw [h, one_mul]
    exact mul_right_cancel this
  have hact : ∀ y ∈ B, y * a * y⁻¹ = a ∨ y * a * y⁻¹ = z * a := by
    intro y hy
    have hyaU : y * a * y⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (hBN hy) a).mp haU
    have hyz : y * z = z * y := hzc y hy
    rcases hUdesc _ hyaU with h | h | h | h
    · exfalso
      apply haz
      have : a = 1 := by
        calc a = y⁻¹ * (y * a * y⁻¹) * y := by group
          _ = 1 := by rw [h]; group
      rw [this]; exact one_mem _
    · exfalso
      apply haz
      have : a = z := by
        calc a = y⁻¹ * (y * a * y⁻¹) * y := by group
          _ = y⁻¹ * z * y := by rw [h]
          _ = y⁻¹ * (z * y) := by rw [mul_assoc]
          _ = y⁻¹ * (y * z) := by rw [hyz]
          _ = z := by group
      rw [this]; exact Subgroup.mem_zpowers z
    · exact Or.inl h
    · exact Or.inr h
  have hcent : ∀ y ∈ B, y ∈ centralizer (U : Set G) ↔ y * a * y⁻¹ = a := by
    intro y hy
    have hyz : y * z = z * y := hzc y hy
    constructor
    · intro h
      have h1 : a * y = y * a := Subgroup.mem_centralizer_iff.mp h a haU
      calc y * a * y⁻¹ = a * y * y⁻¹ := by rw [h1]
        _ = a := by group
    · intro h
      have h1 : y * a = a * y := by
        calc y * a = (y * a * y⁻¹) * y := by group
          _ = a * y := by rw [h]
      refine Subgroup.mem_centralizer_iff.mpr (fun u hu => ?_)
      rcases hUdesc u hu with rfl | rfl | rfl | rfl
      · simp
      · exact hyz.symm
      · exact h1.symm
      · calc z * a * y = z * (a * y) := by group
          _ = z * (y * a) := by rw [h1]
          _ = (z * y) * a := by group
          _ = (y * z) * a := by rw [hyz]
          _ = y * (z * a) := by group
  have hnc : ∀ y ∈ B, y ∉ centralizer (U : Set G) → y * a * y⁻¹ = z * a := by
    intro y hy hyn
    rcases hact y hy with h | h
    · exact absurd ((hcent y hy).mpr h) hyn
    · exact h
  have hcommU : ∀ y ∈ B, ∀ u ∈ U, (u = a ∨ u = z * a) → u * y = y * u →
      y ∈ centralizer (U : Set G) := by
    intro y hy u hu hua huy
    have hyz : y * z = z * y := hzc y hy
    rw [hcent y hy]
    have h1 : a * y = y * a := by
      rcases hua with rfl | rfl
      · exact huy
      · have : z * (a * y) = z * (y * a) := by
          calc z * (a * y) = z * a * y := by group
            _ = y * (z * a) := huy
            _ = (y * z) * a := by group
            _ = (z * y) * a := by rw [hyz]
            _ = z * (y * a) := by group
        exact mul_left_cancel this
    calc y * a * y⁻¹ = a * y * y⁻¹ := by rw [← h1]
      _ = a := by group
  obtain ⟨y₀, hy₀B, hy₀n⟩ : ∃ y ∈ B, y ∉ centralizer (U : Set G) := by
    by_contra hcon
    apply hnt
    intro y hy
    by_contra h
    exact hcon ⟨y, hy, h⟩
  have h0 : y₀ * a * y₀⁻¹ = z * a := hnc y₀ hy₀B hy₀n
  have hrelQ : (B ⊓ centralizer (U : Set G)).relIndex B = 2 := by
    show ((B ⊓ centralizer (U : Set G)).subgroupOf B).index = 2
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨y₀, hy₀B⟩, fun b => ?_⟩
    have hbB : (b : G) ∈ B := b.2
    have hbz : (b : G) * z = z * b := hzc b hbB
    have hmem : ∀ c : B, c ∈ (B ⊓ centralizer (U : Set G)).subgroupOf B ↔
        (c : G) ∈ centralizer (U : Set G) := by
      intro c
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => h.2, fun h => ⟨c.2, h⟩⟩
    have hcoe : ((b * ⟨y₀, hy₀B⟩ : B) : G) = (b : G) * y₀ := rfl
    rw [hmem, hmem, hcoe]
    have hprod : (b : G) * y₀ * a * ((b : G) * y₀)⁻¹ =
        z * ((b : G) * a * (b : G)⁻¹) := by
      calc (b : G) * y₀ * a * ((b : G) * y₀)⁻¹
          = (b : G) * (y₀ * a * y₀⁻¹) * (b : G)⁻¹ := by group
        _ = (b : G) * (z * a) * (b : G)⁻¹ := by rw [h0]
        _ = ((b : G) * z) * a * (b : G)⁻¹ := by group
        _ = (z * (b : G)) * a * (b : G)⁻¹ := by rw [hbz]
        _ = z * ((b : G) * a * (b : G)⁻¹) := by group
    rcases hact b hbB with hb | hb
    · refine Or.inr ⟨(hcent b hbB).mpr hb, fun h => ?_⟩
      have := (hcent _ (B.mul_mem hbB hy₀B)).mp h
      rw [hprod, hb] at this
      exact hza_ne this
    · refine Or.inl ⟨?_, fun h => ?_⟩
      · refine (hcent _ (B.mul_mem hbB hy₀B)).mpr ?_
        rw [hprod, hb]
        calc z * (z * a) = (z * z) * a := by group
          _ = a := by rw [hzz, one_mul]
      · have := (hcent b hbB).mp h
        rw [hb] at this
        exact hza_ne this
  have hCUB : U ⊓ centralizer (B : Set G) = Subgroup.zpowers z := by
    apply le_antisymm
    · rintro u ⟨huU, huC⟩
      have key : ∀ y ∈ B, y * u = u * y := fun y hy => Subgroup.mem_centralizer_iff.mp huC y hy
      rcases hUdesc u huU with rfl | rfl | rfl | rfl
      · exact one_mem _
      · exact Subgroup.mem_zpowers _
      · exact absurd (hcommU y₀ hy₀B _ huU (Or.inl rfl) (key y₀ hy₀B).symm) hy₀n
      · exact absurd (hcommU y₀ hy₀B _ huU (Or.inr rfl) (key y₀ hy₀B).symm) hy₀n
    · intro u hu
      refine ⟨hzle hu, ?_⟩
      rcases (hzmem u).mp hu with rfl | rfl
      · exact one_mem _
      · exact Subgroup.mem_centralizer_iff.mpr (fun h hh => hzc h hh)
  have hcommA : ∀ y ∈ B, y ∉ centralizer (U : Set G) → ⁅a, y⁆ = z⁻¹ := by
    intro y hy hyn
    rw [commutatorElement_def]
    calc a * y * a⁻¹ * y⁻¹ = a * (y * a * y⁻¹)⁻¹ := by group
      _ = a * (z * a)⁻¹ := by rw [hnc y hy hyn]
      _ = z⁻¹ := by group
  have hcomm : ⁅U, B⁆ = Subgroup.zpowers z := by
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro u hu y hy
      by_cases hyc : y ∈ centralizer (U : Set G)
      · have h1 : u * y = y * u := Subgroup.mem_centralizer_iff.mp hyc u hu
        rw [commutatorElement_def, h1]
        have : y * u * u⁻¹ * y⁻¹ = 1 := by group
        rw [this]; exact one_mem _
      · have hyz : y * z = z * y := hzc y hy
        have hya := hnc y hy hyc
        rcases hUdesc u hu with rfl | rfl | rfl | rfl
        · rw [commutatorElement_def]
          have : (1 : G) * y * 1⁻¹ * y⁻¹ = 1 := by group
          rw [this]; exact one_mem _
        · rw [commutatorElement_def, ← hyz]
          have : y * u * u⁻¹ * y⁻¹ = 1 := by group
          rw [this]; exact one_mem _
        · rw [hcommA y hy hyc]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers z)
        · rw [commutatorElement_def]
          have hya' : y * (z * a) * y⁻¹ = a := by
            calc y * (z * a) * y⁻¹ = (y * z) * a * y⁻¹ := by group
              _ = (z * y) * a * y⁻¹ := by rw [hyz]
              _ = z * (y * a * y⁻¹) := by group
              _ = z * (z * a) := by rw [hya]
              _ = (z * z) * a := by group
              _ = a := by rw [hzz, one_mul]
          have : z * a * y * (z * a)⁻¹ * y⁻¹ = z := by
            calc z * a * y * (z * a)⁻¹ * y⁻¹
                = (z * a) * (y * (z * a) * y⁻¹)⁻¹ := by group
              _ = (z * a) * a⁻¹ := by rw [hya']
              _ = z := by group
          rw [this]; exact Subgroup.mem_zpowers z
    · rw [Subgroup.zpowers_le]
      have h1 : ⁅a, y₀⁆ ∈ ⁅U, B⁆ := Subgroup.commutator_mem_commutator haU hy₀B
      rw [hcommA y₀ hy₀B hy₀n] at h1
      simpa using ⁅U, B⁆.inv_mem h1
  have hcenty : ∀ y ∈ B, y ∉ centralizer (U : Set G) → ∀ u ∈ U,
      (u ∈ Subgroup.zpowers z ↔ u * y = y * u) := by
    intro y hy hyn u hu
    have hyz : y * z = z * y := hzc y hy
    constructor
    · intro h
      rcases (hzmem u).mp h with rfl | rfl
      · simp
      · exact hyz.symm
    · intro h
      rcases hUdesc u hu with rfl | rfl | rfl | rfl
      · exact one_mem _
      · exact Subgroup.mem_zpowers _
      · exact absurd (hcommU y hy _ hu (Or.inl rfl) h) hyn
      · exact absurd (hcommU y hy _ hu (Or.inr rfl) h) hyn
  exact ⟨z, hzU, hz1, hrelQ, hCUB, hcomm, hcenty⟩

theorem rank1_of_klein [Finite G] {U B : Subgroup G}
    (hU4 : Nat.card U = 4) (hU2 : ∀ a ∈ U, a ^ 2 = 1)
    (hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a)
    (hUB : U ≤ B) (hBN : B ≤ normalizer (U : Set G)) (hB2 : IsPGroup 2 B)
    (hnt : ¬ B ≤ centralizer (U : Set G)) :
    ∃ z ∈ U, z ≠ 1 ∧ U ⊓ centralizer (B : Set G) = zpowers z ∧
      C5.Rank1 B (B ⊓ centralizer (U : Set G)) U (zpowers z) 2 := by
  obtain ⟨z, hzU, hz1, hrelQ, hCUB, hcomm, hcenty⟩ := klein_structure hU4 hU2 hUB hBN hB2 hnt
  have hz2 : z ^ 2 = 1 := hU2 z hzU
  have hzle : Subgroup.zpowers z ≤ U := (Subgroup.zpowers_le).mpr hzU
  have hord : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  have hcz : Nat.card (Subgroup.zpowers z) = 2 := by rw [Nat.card_zpowers, hord]
  refine ⟨z, hzU, hz1, hCUB, ?_⟩
  refine ⟨?_, inf_le_left, ?_, hBN, rfl, hzle, hrelQ, ?_, two_ne_zero, ?_, hcomm, hUab⟩
  · exact le_inf hUB (fun u hu => Subgroup.mem_centralizer_iff.mpr (fun h hh => hUab h hh u hu))
  · intro g hg
    exact C5.mem_normalizer_inf (Subgroup.le_normalizer hg)
      (C5.mem_normalizer_centralizer (hBN hg))
  · have := card_eq_card_mul_relIndex_of_le hzle
    rw [hU4, hcz] at this
    omega
  · intro y hy hyQ u hu
    refine hcenty y hy (fun hc => hyQ ⟨hy, hc⟩) u hu

end CFSG.QuasithinUnique.DoubleA3
