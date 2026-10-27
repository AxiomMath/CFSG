module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalData
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Fusion

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

structure ThLocalIn (L S A B : Subgroup G) (z : G) : Prop where
  S_le : S ≤ L
  B_le : B ≤ L
  pgroup : IsPGroup 2 S
  maximal : ∀ Y : Subgroup G, Y ≤ L → IsPGroup 2 Y → S ≤ Y → Y ≤ S
  z_sq : z ^ 2 = 1
  z_ne_one : z ≠ 1
  z_mem : z ∈ S
  center_le : ∀ x ∈ S, (∀ y ∈ S, x * y = y * x) → x ∈ zpowers z
  mem_A_iff : ∀ x, x ∈ A ↔ x ∈ S ∧ ∀ s₁ ∈ S, ∀ s₂ ∈ S, ∀ s₃ ∈ S, ∀ s₄ ∈ S,
    ⁅⁅⁅⁅x, s₁⁆, s₂⁆, s₃⁆, s₄⁆ = 1
  A_comm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x
  A_sq : ∀ x ∈ A, x ^ 2 = 1
  A_card : Nat.card A = 16
  z_mem_A : z ∈ A
  mem_B_iff : ∀ x ∈ L, (x ∈ B ↔ ∀ a ∈ A, x * a = a * x)
  B_card : Nat.card B = 2 ^ 9
  trans : ∀ a ∈ A, a ≠ 1 → ∃ n ∈ L, (∀ x ∈ A, n * x * n⁻¹ ∈ A) ∧ n * z * n⁻¹ = a
  surj : ∀ f : G → G, (∀ a ∈ A, f a ∈ A) → (∀ a ∈ A, ∀ b ∈ A, f (a * b) = f a * f b) →
    (∀ a ∈ A, ∀ b ∈ A, f a = f b → a = b) → ∃ n ∈ L, ∀ a ∈ A, n * a * n⁻¹ = f a

theorem ThLocalWitness.toLocalIn {L : Subgroup G} {S₀ A₀ B₀ : Subgroup ↥L} {z₀ : ↥L}
    (W : ThLocalWitness S₀ A₀ B₀ z₀) :
    ThLocalIn L (S₀.map L.subtype) (A₀.map L.subtype) (B₀.map L.subtype) (z₀ : G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmem : ∀ K : Subgroup ↥L, ∀ x : G, x ∈ K.map L.subtype ↔ ∃ h : x ∈ L, (⟨x, h⟩ : L) ∈ K :=
    fun K x => by
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.2, hy⟩
      · rintro ⟨h, hx⟩
        exact ⟨⟨x, h⟩, hx, rfl⟩
  have hcomm : ∀ a b : ↥L, ((⁅a, b⁆ : ↥L) : G) = ⁅(a : G), (b : G)⁆ := fun a b =>
    map_commutatorElement L.subtype a b
  refine ⟨Subgroup.map_subtype_le _, Subgroup.map_subtype_le _, W.pgroup.map _, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Y hYL hY hle
    have hker : IsPGroup 2 L.subtype.ker := by
      rw [Subgroup.ker_subtype]
      exact IsPGroup.of_card (n := 0) (by simp)
    have hY' : IsPGroup 2 (Y.comap L.subtype) := IsPGroup.comap_of_ker_isPGroup hY _ hker
    have hle' : S₀ ≤ Y.comap L.subtype := fun x hx => hle ⟨x, hx, rfl⟩
    have heq := (W.pgroup.toSylow W.index_odd).is_maximal' hY' hle'
    intro y hy
    have hy' : (⟨y, hYL hy⟩ : L) ∈ Y.comap L.subtype := hy
    rw [heq] at hy'
    exact ⟨_, hy', rfl⟩
  · simpa using congrArg Subtype.val W.z_sq
  · exact fun h => W.z_ne_one (Subtype.ext h)
  · exact (hmem S₀ _).2 ⟨z₀.2, by simpa using W.z_mem⟩
  · intro x hx hc
    obtain ⟨hxL, hx0⟩ := (hmem _ _).1 hx
    have h1 : (⟨x, hxL⟩ : L) ∈ zpowers z₀ := by
      refine W.center_le _ hx0 fun y hy =>
        Subtype.ext (hc y ((hmem _ _).2 ⟨y.2, by simpa using hy⟩))
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h1
    exact Subgroup.mem_zpowers_iff.2 ⟨k, by simpa using congrArg Subtype.val hk⟩
  · intro x
    constructor
    · intro hx
      obtain ⟨hxL, hx0⟩ := (hmem _ _).1 hx
      obtain ⟨hxS, hx4⟩ := (W.mem_A_iff _).1 hx0
      refine ⟨(hmem _ _).2 ⟨hxL, hxS⟩, fun s₁ hs₁ s₂ hs₂ s₃ hs₃ s₄ hs₄ => ?_⟩
      obtain ⟨h1, h1'⟩ := (hmem _ _).1 hs₁
      obtain ⟨h2, h2'⟩ := (hmem _ _).1 hs₂
      obtain ⟨h3, h3'⟩ := (hmem _ _).1 hs₃
      obtain ⟨h4, h4'⟩ := (hmem _ _).1 hs₄
      have := congrArg Subtype.val (hx4 _ h1' _ h2' _ h3' _ h4')
      rw [hcomm, hcomm, hcomm, hcomm] at this
      simpa using this
    · rintro ⟨hxS, hx4⟩
      obtain ⟨hxL, hx0⟩ := (hmem _ _).1 hxS
      refine (hmem _ _).2 ⟨hxL, (W.mem_A_iff _).2 ⟨hx0, fun s₁ hs₁ s₂ hs₂ s₃ hs₃ s₄ hs₄ => ?_⟩⟩
      have := hx4 (s₁ : G) ((hmem _ _).2 ⟨s₁.2, by simpa using hs₁⟩) (s₂ : G)
        ((hmem _ _).2 ⟨s₂.2, by simpa using hs₂⟩) (s₃ : G) ((hmem _ _).2 ⟨s₃.2, by simpa using hs₃⟩)
        (s₄ : G) ((hmem _ _).2 ⟨s₄.2, by simpa using hs₄⟩)
      refine Subtype.ext ?_
      rw [hcomm, hcomm, hcomm, hcomm]
      simpa using this
  · intro x hx y hy
    obtain ⟨hxL, hx0⟩ := (hmem _ _).1 hx
    obtain ⟨hyL, hy0⟩ := (hmem _ _).1 hy
    exact congrArg Subtype.val (W.A_comm _ hx0 _ hy0)
  · intro x hx
    obtain ⟨hxL, hx0⟩ := (hmem _ _).1 hx
    simpa using congrArg Subtype.val (W.A_sq _ hx0)
  · rw [Subgroup.card_map_of_injective L.subtype_injective]
    exact W.A_card
  · exact (hmem A₀ _).2 ⟨z₀.2, by simpa using W.z_mem_A⟩
  · intro x hxL
    constructor
    · intro hx a ha
      obtain ⟨hxL', hx0⟩ := (hmem _ _).1 hx
      obtain ⟨haL, ha0⟩ := (hmem _ _).1 ha
      exact congrArg Subtype.val ((W.mem_B_iff _).1 hx0 _ ha0)
    · intro h
      refine (hmem _ _).2 ⟨hxL, (W.mem_B_iff _).2 fun a ha => Subtype.ext ?_⟩
      exact h (a : G) ((hmem _ _).2 ⟨a.2, by simpa using ha⟩)
  · rw [Subgroup.card_map_of_injective L.subtype_injective]
    exact W.B_card
  · intro a ha ha1
    obtain ⟨haL, ha0⟩ := (hmem _ _).1 ha
    obtain ⟨n, hn1, hn2⟩ := W.trans ⟨a, haL⟩ ha0 (fun h => ha1 (congrArg Subtype.val h))
    refine ⟨(n : G), n.2, fun x hx => ?_, by simpa using congrArg Subtype.val hn2⟩
    obtain ⟨hxL, hx0⟩ := (hmem _ _).1 hx
    exact (hmem _ _).2 ⟨(n * ⟨x, hxL⟩ * n⁻¹).2, hn1 _ hx0⟩
  · intro f hf1 hf2 hf3
    classical
    let f' : ↥L → ↥L := fun y => if h : f (y : G) ∈ L then ⟨f (y : G), h⟩ else 1
    have hf'val : ∀ a : ↥L, a ∈ A₀ → (f' a : G) = f (a : G) := fun a ha => by
      have h := hf1 (a : G) ((hmem _ _).2 ⟨a.2, by simpa using ha⟩)
      obtain ⟨hfL, -⟩ := (hmem _ _).1 h
      simp [f', hfL]
    obtain ⟨n, hn⟩ := W.surj f'
      (fun a ha => by
        have h := hf1 (a : G) ((hmem _ _).2 ⟨a.2, by simpa using ha⟩)
        obtain ⟨hfL, h0⟩ := (hmem _ _).1 h
        have : f' a = ⟨f (a : G), hfL⟩ := Subtype.ext (hf'val a ha)
        rw [this]
        exact h0)
      (fun a ha b hb => by
        apply Subtype.ext
        have hab : a * b ∈ A₀ := A₀.mul_mem ha hb
        rw [hf'val _ hab, Subgroup.coe_mul, Subgroup.coe_mul, hf'val _ ha, hf'val _ hb]
        exact hf2 _ ((hmem _ _).2 ⟨a.2, by simpa using ha⟩) _
          ((hmem _ _).2 ⟨b.2, by simpa using hb⟩))
      (fun a ha b hb hab => by
        apply Subtype.ext
        have h1 : f (a : G) = f (b : G) := by rw [← hf'val a ha, ← hf'val b hb, hab]
        exact hf3 _ ((hmem _ _).2 ⟨a.2, by simpa using ha⟩) _
          ((hmem _ _).2 ⟨b.2, by simpa using hb⟩) h1)
    refine ⟨(n : G), n.2, fun a ha => ?_⟩
    obtain ⟨haL, ha0⟩ := (hmem _ _).1 ha
    have := congrArg Subtype.val (hn ⟨a, haL⟩ ha0)
    rw [hf'val _ ha0] at this
    simpa using this

theorem zpow_eq_one_or_self {z : G} (hz : z ^ 2 = 1) (k : ℤ) : z ^ k = 1 ∨ z ^ k = z := by
  have h1 : z ^ k = z ^ (k % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 2]
    rw [zpow_add, zpow_mul]
    have : z ^ (2 : ℤ) = 1 := by exact_mod_cast hz
    rw [this, one_zpow, mul_one]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [h1, h, zpow_zero]
  · right
    rw [h1, h, zpow_one]

section

variable {L S A B : Subgroup G} {z : G}

theorem ThLocalIn.isThSylow (W : ThLocalIn L S A B z) : IsThSylow L S :=
  ⟨W.S_le, W.pgroup, W.maximal, fun x hx hc => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (W.center_le x hx hc)
    rcases zpow_eq_one_or_self W.z_sq k with h | h
    · rw [h, one_pow]
    · rw [h, W.z_sq]⟩

theorem ThLocalIn.z_central [Finite G] (W : ThLocalIn L S A B z) :
    ∀ y ∈ S, z * y = y * z := by
  have : Nontrivial ↥S := ⟨⟨⟨z, W.z_mem⟩, 1, fun h => W.z_ne_one (congrArg Subtype.val h)⟩⟩
  have : Nontrivial (Subgroup.center ↥S) := W.pgroup.center_nontrivial
  obtain ⟨w, hw⟩ := exists_ne (1 : Subgroup.center ↥S)
  have hwc : ∀ y ∈ S, (w.1.1 : G) * y = y * w.1.1 := fun y hy =>
    (congrArg Subtype.val (Subgroup.mem_center_iff.1 w.2 ⟨y, hy⟩)).symm
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (W.center_le _ w.1.2 hwc)
  have hw1 : (w.1.1 : G) ≠ 1 := fun h => hw (Subtype.ext (Subtype.ext h))
  have hwz : (w.1.1 : G) = z := by
    rcases zpow_eq_one_or_self W.z_sq k with h | h
    · exact absurd (hk.symm.trans h) hw1
    · exact hk.symm.trans h
  intro y hy
  have := hwc y hy
  rwa [hwz] at this

end

end CFSG.EvenSporadicStandard.ThStd
