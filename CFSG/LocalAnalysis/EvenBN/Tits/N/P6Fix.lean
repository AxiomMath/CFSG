module

public import CFSG.Open.LocalVocabulary
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P6Comm

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P6

open Subgroup CFSG.Open

variable {G : Type*} [Group G]

theorem mem_sup_zpowers_iff {P : Subgroup G} {u : G} (hu : u * u = 1)
    (hn : ∀ p ∈ P, u * p * u⁻¹ ∈ P) {x : G} : x ∈ P ⊔ zpowers u ↔ x ∈ P ∨ x * u ∈ P := by
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  let K : Subgroup G :=
    { carrier := {x | x ∈ P ∨ x * u ∈ P}
      one_mem' := Or.inl P.one_mem
      mul_mem' := by
        rintro x y (hx | hx) (hy | hy)
        · exact Or.inl (P.mul_mem hx hy)
        · exact Or.inr (by rw [mul_assoc]; exact P.mul_mem hx hy)
        · right
          have h1 : u * y * u⁻¹ ∈ P := hn y hy
          have : x * y * u = (x * u) * (u * y * u⁻¹) := by
            rw [huinv, show x * u * (u * y * u) = x * (u * u) * y * u by group, hu, mul_one]
          rw [this]
          exact P.mul_mem hx h1
        · left
          have h1 : u * (y * u) * u⁻¹ ∈ P := hn _ hy
          have : x * y = (x * u) * (u * (y * u) * u⁻¹) := by
            rw [huinv]
            calc x * y = x * (u * u) * y * (u * u) := by rw [hu]; group
              _ = x * u * (u * (y * u) * u) := by group
          rw [this]
          exact P.mul_mem hx h1
      inv_mem' := by
        rintro x (hx | hx)
        · exact Or.inl (P.inv_mem hx)
        · right
          have h1 := hn _ (P.inv_mem hx)
          have : x⁻¹ * u = u * (x * u)⁻¹ * u⁻¹ := by rw [huinv]; group
          rw [this]
          exact h1 }
  have hK : P ⊔ zpowers u = K := by
    apply le_antisymm
    · refine sup_le (fun x hx => Or.inl hx) ?_
      rw [zpowers_le]
      right
      rw [hu]
      exact P.one_mem
    · rintro x (hx | hx)
      · exact mem_sup_left hx
      · have : x = (x * u) * u := by rw [mul_assoc, hu, mul_one]
        rw [this]
        exact mul_mem (mem_sup_left hx) (mem_sup_right (mem_zpowers u))
  rw [hK]
  rfl

theorem card_sup_zpowers [Finite G] {P : Subgroup G} {u : G} (hu : u * u = 1)
    (hn : ∀ p ∈ P, u * p * u⁻¹ ∈ P) (huP : u ∉ P) :
    Nat.card ↥(P ⊔ zpowers u) = 2 * Nat.card P := by
  classical
  have hdisj : Disjoint (P : Set G) ((fun x => x * u) '' (P : Set G)) := by
    rw [Set.disjoint_left]
    rintro x hx ⟨y, hy, rfl⟩
    have : u = y⁻¹ * (y * u) := by group
    exact huP (this ▸ P.mul_mem (P.inv_mem hy) hx)
  have hunion : ((P ⊔ zpowers u : Subgroup G) : Set G) =
      (P : Set G) ∪ (fun x => x * u) '' (P : Set G) := by
    ext x
    rw [SetLike.mem_coe, mem_sup_zpowers_iff hu hn, Set.mem_union, SetLike.mem_coe]
    refine or_congr Iff.rfl ⟨fun h => ⟨x * u, h, by
      show x * u * u = x
      rw [mul_assoc, hu, mul_one]⟩, ?_⟩
    rintro ⟨y, hy, rfl⟩
    show y * u * u ∈ P
    rw [mul_assoc, hu, mul_one]
    exact hy
  have hinj : Set.InjOn (fun x => x * u) (P : Set G) := fun x _ y _ h => mul_right_cancel h
  have h1 : Nat.card ↥(P ⊔ zpowers u) = ((P ⊔ zpowers u : Subgroup G) : Set G).ncard :=
    Nat.card_coe_set_eq _
  have h2 : Nat.card ↥P = (P : Set G).ncard := Nat.card_coe_set_eq _
  rw [h1, hunion, Set.ncard_union_eq hdisj, hinj.ncard_image, h2]
  ring

theorem eq_of_card_two {W : Subgroup G} (hW : Nat.card W = 2) {a b : G} (ha : a ∈ W) (hb : b ∈ W)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  obtain ⟨x, y, hxy, hset⟩ := Nat.card_eq_two_iff.1 hW
  have hall : ∀ w : ↥W, w = x ∨ w = y := fun w => by
    have : w ∈ ({x, y} : Set ↥W) := by rw [hset]; exact Set.mem_univ w
    simpa using this
  have ha' : (⟨a, ha⟩ : ↥W) ≠ ⟨1, W.one_mem⟩ := fun h => ha1 (congrArg Subtype.val h)
  have hb' : (⟨b, hb⟩ : ↥W) ≠ ⟨1, W.one_mem⟩ := fun h => hb1 (congrArg Subtype.val h)
  have key : (⟨a, ha⟩ : ↥W) = ⟨b, hb⟩ := by
    rcases hall ⟨a, ha⟩ with h1 | h1 <;> rcases hall ⟨b, hb⟩ with h2 | h2 <;>
      rcases hall ⟨1, W.one_mem⟩ with h3 | h3 <;> first | exact h1.trans h2.symm | (exfalso; aesop)
  exact congrArg Subtype.val key

theorem comm_of_card_two {W : Subgroup G} (hW : Nat.card W = 2) {w g : G} (hw : w ∈ W)
    (hw1 : w ≠ 1) (hg : g * w * g⁻¹ ∈ W) : g * w = w * g := by
  have h1 : g * w * g⁻¹ ≠ 1 := fun h => hw1 (by
    have : w = g⁻¹ * (g * w * g⁻¹) * g := by group
    rw [this, h]; group)
  have h2 := eq_of_card_two hW hg hw h1 hw1
  calc g * w = g * w * g⁻¹ * g := by group
    _ = w * g := by rw [h2]

end CFSG.LocalAnalysis.EvenBN.Tits.N.P6
