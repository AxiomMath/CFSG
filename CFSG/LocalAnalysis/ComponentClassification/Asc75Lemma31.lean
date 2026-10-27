module

public import CFSG.LocalAnalysis.ComponentClassification.Asc75Lemma31Cases

public section

namespace CFSG.ComponentClassification.Asc75Lemma31

open Subgroup CFSG.Open CFSG.Goldschmidt CFSG.Goldschmidt.G2
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Hyp

variable {V X : Subgroup G} {y : G} (h : Hyp V X y)
include h

omit [Finite G] in
theorem comClosure_inf_le : comClosure V X y ⊓ centralizer ({y} : Set G) ≤ fixGrp V y :=
  le_inf (inf_le_left.trans h.comClosure_le) inf_le_right

theorem comClosure_eq_sup :
    comClosure V X y = (comClosure V X y ⊓ centralizer ({y} : Set G)) ⊔ comGrp V y := by
  refine le_antisymm (fun n hn => ?_) (sup_le inf_le_left comGrp_le_comClosure)
  obtain ⟨u, hu, w, hw, rfl⟩ := h.exists_mul (h.comClosure_le hn)
  have huN : u ∈ comClosure V X y := by
    simpa using mul_mem hn (inv_mem (comGrp_le_comClosure hw))
  exact mul_mem (mem_sup_left (mem_inf.mpr ⟨huN, (mem_inf.mp hu).2⟩)) (mem_sup_right hw)

theorem card_comClosure : Nat.card (comClosure V X y) =
    Nat.card (comClosure V X y ⊓ centralizer ({y} : Set G) : Subgroup G) *
      Nat.card (comGrp V y) := by
  conv_lhs => rw [h.comClosure_eq_sup]
  refine AS76b.card_sup_eq_mul
    (le_normalizer_of_le h.elem (inf_le_left.trans h.comClosure_le) h.comGrp_le) ?_
  rw [eq_bot_iff, ← h.inf_eq_bot]
  exact inf_le_inf_right _ h.comClosure_inf_le

theorem onanHyp_comClosure {x₀ : G} (hx₀ : x₀ ∈ X) (hU : conjSub x₀ (fixGrp V y) ≠ fixGrp V y)
    (hNU : comClosure V X y ⊓ centralizer ({y} : Set G) ≠ ⊥) : ONanHyp (comClosure V X y) X y where
  elem := ⟨⟨⟨fun a b => Subtype.ext (by
      have hab : (a : G) * b = b * a := congrArg Subtype.val
        (h.elem.1.is_comm.comm (⟨a, h.comClosure_le a.2⟩ : V) ⟨b, h.comClosure_le b.2⟩)
      exact hab)⟩⟩,
    fun v hv => h.elem.2 v (h.comClosure_le hv)⟩
  le := le_normalizer_comClosure
  irreducible := fun M hMN hMX => by
    by_cases hM : M = ⊥
    · exact Or.inl hM
    · exact Or.inr (le_antisymm hMN
        (h.comClosure_le_of_ne_bot hx₀ hU (hMN.trans h.comClosure_le) hMX hM))
  mem := h.mem
  odd := h.odd
  not_mem := fun hy => h.comGrp_ne_bot (by
    rw [eq_bot_iff, ← h.inf_eq_bot]
    intro w hw
    refine mem_inf.mpr ⟨mem_inf.mpr ⟨h.comGrp_le hw, ?_⟩, hw⟩
    rw [mem_centralizer_singleton_iff]
    exact mem_centralizer_iff.mp hy w (comGrp_le_comClosure hw))
  ne_bot := hNU
  trans := fun b hb c hc hb1 hc1 =>
    h.trans b (commutator_mono h.comClosure_le le_rfl hb) c
      (commutator_mono h.comClosure_le le_rfl hc) hb1 hc1
  ti := fun x hx hne => by
    have hNC : comClosure V X y ⊓ centralizer ({y} : Set G) = comClosure V X y ⊓ fixGrp V y :=
      le_antisymm (le_inf inf_le_left h.comClosure_inf_le) (inf_le_inf_left _ inf_le_right)
    rw [hNC] at hne ⊢
    have hxU : conjSub x (fixGrp V y) ≠ fixGrp V y := by
      intro h1
      apply hne
      rw [G2.conjSub_inf, conjSub_comClosure hx, h1]
    rw [eq_bot_iff, ← h.ti x hx hxU]
    exact inf_le_inf inf_le_right (conjSub_mono x inf_le_right)

theorem case_one
    (hI : ∀ X₀ : Subgroup G, X₀ ≤ X → X ⊓ centralizer (V : Set G) ≤ X₀ →
      (X₀.subgroupOf X).index ≠ 2)
    (hN : ∀ x ∈ X, conjSub x (fixGrp V y) = fixGrp V y →
      x⁻¹ * y * x ∈ zpowers y ⊔ centralizer (V : Set G))
    {x₀ : G} (hx₀ : x₀ ∈ X) (hU : conjSub x₀ (fixGrp V y) ≠ fixGrp V y)
    {x₁ : G} (hx₁ : x₁ ∈ X) (hW : conjSub x₁ (comGrp V y) ≠ comGrp V y) :
    Nat.card (fixGrp V y) = 2 ∧ Nat.card V = 8 := by
  have hNU : comClosure V X y ⊓ centralizer ({y} : Set G) ≠ ⊥ := by
    intro h0
    apply hW
    have hNW : comClosure V X y = comGrp V y := by
      rw [h.comClosure_eq_sup, h0, bot_sup_eq]
    rw [← hNW]
    exact conjSub_comClosure hx₁
  have hON := h.onanHyp_comClosure hx₀ hU hNU
  have hI' : ∀ X₀ : Subgroup G, X₀ ≤ X → X ⊓ centralizer (comClosure V X y : Set G) ≤ X₀ →
      (X₀.subgroupOf X).index ≠ 2 := fun X₀ h1 h2 =>
    hI X₀ h1 ((inf_le_inf_left X (centralizer_le fun v hv => h.comClosure_le hv)).trans h2)
  have hN' : ∀ x ∈ X, conjSub x (comClosure V X y ⊓ centralizer ({y} : Set G)) =
      comClosure V X y ⊓ centralizer ({y} : Set G) →
      x⁻¹ * y * x ∈ zpowers y ⊔ centralizer (comClosure V X y : Set G) := by
    intro x hx hxN
    have hxU : conjSub x (fixGrp V y) = fixGrp V y := by
      by_contra hne
      apply hNU
      rw [eq_bot_iff, ← h.ti x hx hne]
      refine le_inf h.comClosure_inf_le ?_
      rw [← hxN]
      exact conjSub_mono x h.comClosure_inf_le
    exact sup_le_sup_left (centralizer_le fun v hv => h.comClosure_le hv) _ (hN x hx hxU)
  obtain ⟨hN8, hNU2, -, -⟩ := G211 G (comClosure V X y) X y hON hI' hN'
  have htr := transitive_of_onanHyp hON hI' hN'
  have hW4 : Nat.card (comGrp V y) = 4 := by
    have := h.card_comClosure
    rw [hN8, hNU2] at this
    omega
  obtain ⟨⟨b₀, hb₀⟩, hb₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hNU
  have hb₀1' : b₀ ≠ 1 := fun h1 => hb₀1 (Subtype.ext h1)
  have hb₀U : b₀ ∈ fixGrp V y := h.comClosure_inf_le hb₀
  have hex : ∀ b : {b : comClosure V X y // b ≠ 1}, ∃ x ∈ X, x⁻¹ * b₀ * x = (b.1 : G) :=
    fun b => htr b₀ (mem_inf.mp hb₀).1 b.1 b.1.2 hb₀1' fun h1 => b.2 (Subtype.ext h1)
  choose xb hxbX hxb using hex
  have hti : ∀ b b' : {b : comClosure V X y // b ≠ 1}, b ≠ b' →
      conjSub (xb b) (fixGrp V y) ⊓ conjSub (xb b') (fixGrp V y) = ⊥ := by
    intro b b' hbb'
    refine h.conjSub_inf_conjSub (hxbX b) (hxbX b') fun h1 => hbb' ?_
    have hb'U : (b'.1 : G) ∈ conjSub (xb b) (fixGrp V y) := by
      rw [h1, ← hxb b']
      exact conj_mem_conjSub hb₀U
    rw [mem_conjSub] at hb'U
    have hmem : xb b * b'.1 * (xb b)⁻¹ ∈ comClosure V X y ⊓ centralizer ({y} : Set G) :=
      mem_inf.mpr ⟨(mem_normalizer_iff.mp (le_normalizer_comClosure (hxbX b)) (b'.1 : G)).mp
        b'.1.2, (mem_inf.mp hb'U).2⟩
    have h2 := eq_of_card_eq_two hNU2 hmem hb₀
      (conj_ne_one' fun h3 => b'.2 (Subtype.ext h3)) hb₀1'
    apply Subtype.ext
    apply Subtype.ext
    rw [← hxb b, ← h2]
    group
  obtain ⟨hle, -⟩ := card_mul_le (W := ⊥) bot_le
    (fun b : {b : comClosure V X y // b ≠ 1} => conjSub (xb b) (fixGrp V y)) hti
    (fun b => h.conjSub_le (hxbX b) inf_le_left) (fun b => inf_bot_eq _)
    (c := Nat.card (fixGrp V y)) (fun b => card_conjSub _ _)
  rw [card_ne_one, card_bot, hN8, h.card_eq, hW4] at hle
  have h7 : 7 * (Nat.card (fixGrp V y) - 1) ≤ Nat.card (fixGrp V y) * 4 - 1 := hle
  have hU2 : 2 ≤ Nat.card (fixGrp V y) := (Subgroup.one_lt_card_iff_ne_bot _).mpr h.ne_bot
  have hU2' : Nat.card (fixGrp V y) = 2 := by omega
  refine ⟨hU2', ?_⟩
  rw [h.card_eq, hU2', hW4]

end Hyp

theorem lemma31 {V X : Subgroup G} {y : G} (h : Hyp V X y)
    (hI : ∀ X₀ : Subgroup G, X₀ ≤ X → X ⊓ centralizer (V : Set G) ≤ X₀ →
      (X₀.subgroupOf X).index ≠ 2)
    (hN : ∀ x ∈ X, conjSub x (fixGrp V y) = fixGrp V y →
      x⁻¹ * y * x ∈ zpowers y ⊔ centralizer (V : Set G)) :
    (Nat.card (fixGrp V y) = 2 ∧ Nat.card V = 8) ∨
      (∀ x ∈ X, conjSub x (comGrp V y) = comGrp V y ∧ conjSub x (fixGrp V y) = fixGrp V y) ∨
      ((∀ x ∈ X, conjSub x (comGrp V y) = comGrp V y) ∧
        (∀ x ∈ X, ∀ x' ∈ X, conjSub x (fixGrp V y) ≠ fixGrp V y →
          conjSub x' (fixGrp V y) ≠ fixGrp V y →
          ∃ k : ℕ, conjSub (y ^ k) (conjSub x (fixGrp V y)) = conjSub x' (fixGrp V y)) ∧
        (∀ x ∈ X, conjSub x (fixGrp V y) ≠ fixGrp V y → ∀ k : ℕ,
          conjSub (y ^ k) (conjSub x (fixGrp V y)) = conjSub x (fixGrp V y) →
          y ^ k ∈ centralizer (V : Set G)) ∧
        ∀ v ∈ V, v ∉ comGrp V y ↔ ∃ x ∈ X, v ∈ conjSub x (fixGrp V y) ∧ v ≠ 1) := by
  by_cases hU : ∀ x ∈ X, conjSub x (fixGrp V y) = fixGrp V y
  · exact Or.inr (Or.inl fun x hx => ⟨h.conjSub_comGrp_eq hx (hN x hx (hU x hx)), hU x hx⟩)
  push Not at hU
  obtain ⟨x₀, hx₀, hx₀U⟩ := hU
  by_cases hW : ∀ x ∈ X, conjSub x (comGrp V y) = comGrp V y
  · obtain ⟨htr, hcov⟩ := h.case_three hW hx₀ hx₀U
    exact Or.inr (Or.inr ⟨hW, htr, fun x hx hxU k hk =>
      h.mem_centralizer_of_conjSub_eq hW hx hxU (npow_mem_zpowers y k) hk, hcov⟩)
  push Not at hW
  obtain ⟨x₁, hx₁, hx₁W⟩ := hW
  exact Or.inl (h.case_one hI hN hx₀ hx₀U hx₁ hx₁W)

end CFSG.ComponentClassification.Asc75Lemma31
