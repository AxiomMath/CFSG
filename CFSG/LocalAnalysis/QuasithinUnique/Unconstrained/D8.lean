module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Basic

public section

namespace CFSG.QuasithinUnique.D8

open DihedralGroup CFSG.Open

@[expose] def w1 : Finset (DihedralGroup 4) := {1, r 2, sr 0, sr 2}

@[expose] def w2 : Finset (DihedralGroup 4) := {1, r 2, sr 1, sr 3}

theorem w1_mul : ∀ a ∈ w1, ∀ b ∈ w1, a * b ∈ w1 := by decide
theorem w1_inv : ∀ a ∈ w1, a⁻¹ ∈ w1 := by decide
theorem w2_mul : ∀ a ∈ w2, ∀ b ∈ w2, a * b ∈ w2 := by decide
theorem w2_inv : ∀ a ∈ w2, a⁻¹ ∈ w2 := by decide
theorem w1_comm : ∀ a ∈ w1, ∀ b ∈ w1, a * b = b * a := by decide
theorem w2_comm : ∀ a ∈ w2, ∀ b ∈ w2, a * b = b * a := by decide
theorem w1_sq : ∀ a ∈ w1, a * a = 1 := by decide
theorem w2_sq : ∀ a ∈ w2, a * a = 1 := by decide
theorem w1_card : w1.card = 4 := by decide
theorem w2_card : w2.card = 4 := by decide

set_option maxRecDepth 100000 in
theorem classification : ∀ F : Finset (DihedralGroup 4), F.card = 4 → (1 ∈ F) →
    (∀ x ∈ F, ∀ y ∈ F, x * y ∈ F) → (∀ x ∈ F, x * x = 1) → F = w1 ∨ F = w2 := by
  decide

@[expose] def subgroupOfFinset (F : Finset (DihedralGroup 4)) (h1 : 1 ∈ F)
    (hm : ∀ a ∈ F, ∀ b ∈ F, a * b ∈ F) (hi : ∀ a ∈ F, a⁻¹ ∈ F) : Subgroup (DihedralGroup 4) where
  carrier := ↑F
  mul_mem' {a b} ha hb := by simpa using hm a (by simpa using ha) b (by simpa using hb)
  one_mem' := by simpa using h1
  inv_mem' {a} ha := by simpa using hi a (by simpa using ha)

@[expose] def W1 : Subgroup (DihedralGroup 4) := subgroupOfFinset w1 (by decide) w1_mul w1_inv

@[expose] def W2 : Subgroup (DihedralGroup 4) := subgroupOfFinset w2 (by decide) w2_mul w2_inv

theorem mem_W1 {x : DihedralGroup 4} : x ∈ W1 ↔ x ∈ w1 := Iff.rfl
theorem mem_W2 {x : DihedralGroup 4} : x ∈ W2 ↔ x ∈ w2 := Iff.rfl

theorem natCard_W1 : Nat.card W1 = 4 := by
  have h : Nat.card W1 = Nat.card (w1 : Set (DihedralGroup 4)) := rfl
  rw [h, Nat.card_coe_set_eq, Set.ncard_coe_finset, w1_card]

theorem natCard_W2 : Nat.card W2 = 4 := by
  have h : Nat.card W2 = Nat.card (w2 : Set (DihedralGroup 4)) := rfl
  rw [h, Nat.card_coe_set_eq, Set.ncard_coe_finset, w2_card]

theorem W1_ne_W2 : W1 ≠ W2 := by
  intro h
  have : (sr 0 : DihedralGroup 4) ∈ W1 := by rw [mem_W1]; decide
  rw [h, mem_W2] at this
  revert this
  decide

theorem eq_W1_or_W2 {W : Subgroup (DihedralGroup 4)} (hW2 : ∀ x ∈ W, x * x = 1)
    (hcard : Nat.card W = 4) : W = W1 ∨ W = W2 := by
  classical
  set F : Finset (DihedralGroup 4) := Finset.univ.filter (· ∈ W) with hF
  have hFcard' : F.card = Nat.card W := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hFcard : F.card = 4 := hFcard'.trans hcard
  have hmemF : ∀ x, x ∈ F ↔ x ∈ W := fun x => by simp [hF]
  rcases classification F hFcard ((hmemF 1).mpr W.one_mem)
      (fun x hx y hy => (hmemF _).mpr (W.mul_mem ((hmemF _).mp hx) ((hmemF _).mp hy)))
      (fun x hx => hW2 x ((hmemF _).mp hx)) with h | h
  · left
    ext x
    rw [← hmemF, h]
    exact Iff.rfl
  · right
    ext x
    rw [← hmemF, h]
    exact Iff.rfl

section Transfer

variable {G : Type} [Group G]

theorem exists_two_four_subgroups {X : Subgroup G} (e : ↥X ≃* DihedralGroup 4) :
    ∃ E₁ E₂ : Subgroup G, E₁ ≤ X ∧ E₂ ≤ X ∧ IsFourSubgroup E₁ ∧ IsFourSubgroup E₂ ∧ E₁ ≠ E₂ ∧
      ∀ E : Subgroup G, E ≤ X → IsFourSubgroup E → E = E₁ ∨ E = E₂ := by
  let img : Subgroup (DihedralGroup 4) → Subgroup G :=
    fun W => (W.map e.symm.toMonoidHom).map X.subtype
  have hcomp : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id _ := by ext x; simp
  have hcomp' : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id _ := by ext x; simp
  have hback : ∀ W : Subgroup (DihedralGroup 4),
      ((img W).subgroupOf X).map e.toMonoidHom = W := by
    intro W
    show Subgroup.map e.toMonoidHom (Subgroup.comap X.subtype
      (Subgroup.map X.subtype (Subgroup.map e.symm.toMonoidHom W))) = W
    rw [Subgroup.comap_map_eq_self_of_injective X.subtype_injective, Subgroup.map_map, hcomp',
      Subgroup.map_id]
  have himg_le : ∀ W, img W ≤ X := fun W => Subgroup.map_subtype_le _
  have hcard : ∀ W : Subgroup (DihedralGroup 4), Nat.card (img W) = Nat.card W := by
    intro W
    simp only [img]
    rw [Subgroup.card_map_of_injective X.subtype_injective,
      Subgroup.card_map_of_injective e.symm.injective]
  have hmem : ∀ (W : Subgroup (DihedralGroup 4)) (x : G),
      x ∈ img W ↔ ∃ w ∈ W, ((e.symm w : ↥X) : G) = x := by
    intro W x
    simp only [img, Subgroup.mem_map]
    constructor
    · rintro ⟨y, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨w, hw, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨e.symm w, ⟨w, hw, rfl⟩, rfl⟩
  have hfour : ∀ (W : Subgroup (DihedralGroup 4)), (∀ a ∈ W, ∀ b ∈ W, a * b = b * a) →
      (∀ a ∈ W, a * a = 1) → Nat.card W = 4 → IsFourSubgroup (img W) := by
    intro W hcomm hsq hc
    refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
    · obtain ⟨w₁, hw₁, ha⟩ := (hmem W a).mp a.2
      obtain ⟨w₂, hw₂, hb⟩ := (hmem W b).mp b.2
      apply Subtype.ext
      show (a : G) * b = b * a
      rw [← ha, ← hb]
      have := congrArg (fun z : DihedralGroup 4 => ((e.symm z : ↥X) : G)) (hcomm w₁ hw₁ w₂ hw₂)
      simpa using this
    · obtain ⟨w, hw, rfl⟩ := (hmem W x).mp hx
      have := congrArg (fun z : DihedralGroup 4 => ((e.symm z : ↥X) : G)) (hsq w hw)
      simpa [sq] using this
    · rw [hcard W, hc]
  have hsub : ∀ E : Subgroup G, E ≤ X → img ((E.subgroupOf X).map e.toMonoidHom) = E := by
    intro E hE
    have h1 : ((E.subgroupOf X).map e.toMonoidHom).map e.symm.toMonoidHom = E.subgroupOf X := by
      rw [Subgroup.map_map, hcomp, Subgroup.map_id]
    show Subgroup.map X.subtype (Subgroup.map e.symm.toMonoidHom
      (Subgroup.map e.toMonoidHom (E.subgroupOf X))) = E
    rw [h1, Subgroup.map_subgroupOf_eq_of_le hE]
  refine ⟨img W1, img W2, himg_le _, himg_le _,
    hfour W1 (fun a ha b hb => w1_comm a ha b hb) (fun a ha => w1_sq a ha) natCard_W1,
    hfour W2 (fun a ha b hb => w2_comm a ha b hb) (fun a ha => w2_sq a ha) natCard_W2,
    fun h => W1_ne_W2 ?_, ?_⟩
  · rw [← hback W1, ← hback W2, h]
  · intro E hE hE4
    have hW2 : ∀ x ∈ (E.subgroupOf X).map e.toMonoidHom, x * x = 1 := by
      rintro _ ⟨y, hy, rfl⟩
      have hyE : (y : G) ∈ E := hy
      have h2 : (y : G) ^ 2 = 1 := hE4.1.2 _ hyE
      have : y * y = 1 := Subtype.ext (by simpa [sq] using h2)
      rw [MulEquiv.coe_toMonoidHom, ← map_mul, this, map_one]
    have hWcard : Nat.card ((E.subgroupOf X).map e.toMonoidHom) = 4 := by
      rw [Subgroup.card_map_of_injective e.injective, ← hE4.2]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE).toEquiv
    rcases eq_W1_or_W2 hW2 hWcard with h | h
    · left
      rw [← hsub E hE, h]
    · right
      rw [← hsub E hE, h]

end Transfer

end CFSG.QuasithinUnique.D8
