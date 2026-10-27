module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.Data.SetLike.Fintype
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree

open Subgroup

variable {G : Type*} [Group G]

theorem exists_minimal_normal [Finite G] [Nontrivial G] :
    ∃ S : Subgroup G, S.Normal ∧ S ≠ ⊥ ∧ ∀ L : Subgroup G, L.Normal → L ≤ S → L = ⊥ ∨ L = S := by
  have hne : ∃ S : Subgroup G, S.Normal ∧ S ≠ ⊥ := ⟨⊤, inferInstance, top_ne_bot⟩
  obtain ⟨S, ⟨hSn, hS0⟩, hmin⟩ := WellFounded.has_min (wellFounded_lt (α := Subgroup G))
    {S : Subgroup G | S.Normal ∧ S ≠ ⊥} hne
  refine ⟨S, hSn, hS0, fun L hL hLS => ?_⟩
  by_cases hL0 : L = ⊥
  · exact Or.inl hL0
  · right
    by_contra hne'
    exact hmin L ⟨hL, hL0⟩ (lt_of_le_of_ne hLS hne')

theorem not_dvd_card_sup_of_normal {A B : Subgroup G} [B.Normal] (hA : ¬ 3 ∣ Nat.card A)
    (hB : ¬ 3 ∣ Nat.card B) : ¬ 3 ∣ Nat.card ↥(A ⊔ B) := by
  have h1 : Nat.card B * (B.relIndex (A ⊔ B)) = Nat.card ↥(A ⊔ B) := by
    have := Subgroup.card_mul_index (B.subgroupOf (A ⊔ B))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv] at this
    exact this
  rw [← h1, Subgroup.relIndex_sup_right]
  have h2 : B.relIndex A ∣ Nat.card A := by
    have := Subgroup.card_mul_index (B.subgroupOf A)
    exact ⟨Nat.card ↥(B.subgroupOf A), by rw [← this, mul_comm]; rfl⟩
  intro h
  rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
  · exact hB h
  · exact hA (h.trans h2)

theorem not_dvd_card_iSup_of_normal [Finite G] {ι : Type*} (T : ι → Subgroup G)
    [∀ i, (T i).Normal] (h : ∀ i, ¬ 3 ∣ Nat.card (T i)) : ¬ 3 ∣ Nat.card ↥(⨆ i, T i) := by
  obtain ⟨W, ⟨hWn, hW3⟩, hWmax⟩ := Set.exists_max_image
    {W : Subgroup G | W.Normal ∧ ¬ 3 ∣ Nat.card W} (fun W : Subgroup G => Nat.card W)
    (Set.toFinite _) ⟨⊥, inferInstance, by simp⟩
  have hle : ∀ i, T i ≤ W := by
    intro i
    have hmem : W ⊔ T i ∈ {W : Subgroup G | W.Normal ∧ ¬ 3 ∣ Nat.card W} :=
      ⟨inferInstance, not_dvd_card_sup_of_normal hW3 (h i)⟩
    have h1 := hWmax _ hmem
    have h2 : W ⊔ T i = W := (Subgroup.eq_of_le_of_card_ge (le_sup_left) h1).symm
    exact h2 ▸ le_sup_right
  intro h3
  exact hW3 (h3.trans (Subgroup.card_dvd_of_le (iSup_le hle)))

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
