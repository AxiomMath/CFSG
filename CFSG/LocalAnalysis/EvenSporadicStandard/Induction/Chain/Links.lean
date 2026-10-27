module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chain.Order

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup Relation CFSG.EvenSporadicStandard.Solomon78

structure Sol78Links (H : Type) [Group H] (a : ℕ) (L T : ℕ → Subgroup H) (s : ℕ → H) : Prop where
  comp : ∀ i ≤ a, IsPGroup 2 (T i) ∧ IsCompIn (L i) (centralizer (T i : Set H))
  elem : ∀ i, 1 ≤ i → i ≤ a → IsPGroup 2 (zpowers (s i)) ∧ s i ∈ normalizer (T i : Set H) ∧
    s i ^ 2 ∈ T i ∧
      IsCompIn (L (i - 1)) (centralizer ((T i ⊔ zpowers (s i) : Subgroup H) : Set H))
  incl : ∀ i, 1 ≤ i → i ≤ a →
    L (i - 1) ≤ L i ⊔ (L i).map (MulAut.conj (s i)).toMonoidHom ∧
      L i ⊔ (L i).map (MulAut.conj (s i)).toMonoidHom =
        conjClosure (L (i - 1)) (layerIn (centralizer (T i : Set H)))
  link : ∀ i, 1 ≤ i → i ≤ a →
    Sol78Link5a (L i) (L (i - 1)) (s i) ∨ Sol78Link5b (L i) (L (i - 1)) (s i)

variable {H : Type} [Group H] {N : Subgroup H} {a b n : ℕ} {L T : ℕ → Subgroup H} {s : ℕ → H}

theorem Sol78Chain23.toLinks (h : Sol78Chain23 H N n L T s) : Sol78Links H n L T s :=
  ⟨h.comp, h.elem, h.incl, h.link⟩

theorem Sol78Links.mono (h : Sol78Links H a L T s) (hba : b ≤ a) : Sol78Links H b L T s :=
  ⟨fun i hi => h.comp i (hi.trans hba), fun i h1 hi => h.elem i h1 (hi.trans hba),
    fun i h1 hi => h.incl i h1 (hi.trans hba), fun i h1 hi => h.link i h1 (hi.trans hba)⟩

theorem Sol78Links.shift (h : Sol78Links H a L T s) (j : ℕ) (hj : j ≤ a) :
    Sol78Links H (a - j) (fun i => L (j + i)) (fun i => T (j + i)) (fun i => s (j + i)) := by
  refine ⟨fun i hi => h.comp (j + i) (by omega), ?_, ?_, ?_⟩
  · intro i hi1 hi
    have h1 : j + i - 1 = j + (i - 1) := by omega
    have := h.elem (j + i) (by omega) (by omega)
    rw [h1] at this
    exact this
  · intro i hi1 hi
    have h1 : j + i - 1 = j + (i - 1) := by omega
    have := h.incl (j + i) (by omega) (by omega)
    rw [h1] at this
    exact this
  · intro i hi1 hi
    have h1 : j + i - 1 = j + (i - 1) := by omega
    have := h.link (j + i) (by omega) (by omega)
    rw [h1] at this
    exact this

theorem Sol78Links.toChain (h : Sol78Links H n L T s) (hlast : L n = N)
    (hinj : ∀ i ≤ n, ∀ j ≤ n, L i = L j → i = j) : Sol78Chain23 H N n L T s :=
  ⟨hlast, hinj, h.comp, h.elem, h.incl, h.link⟩

section Order

variable [Finite H]

theorem Sol78Links.cqOrd_le_succ (h : Sol78Links H a L T s) {i : ℕ} (hi : 1 ≤ i) (hia : i ≤ a) :
    cqOrd (L (i - 1)) ≤ cqOrd (L i) :=
  link_cqOrd_le (h.incl i hi hia).1 (h.link i hi hia)

theorem Sol78Links.cqOrd_mono (h : Sol78Links H a L T s) {c d : ℕ} (hcd : c ≤ d)
    (hd : d ≤ a) : cqOrd (L c) ≤ cqOrd (L d) := by
  induction d, hcd using Nat.le_induction with
  | base => exact le_rfl
  | succ d hcd ih =>
    have := h.cqOrd_le_succ (i := d + 1) (by omega) hd
    simp only [Nat.add_sub_cancel] at this
    exact (ih (by omega)).trans this

theorem Sol78Links.link5a_of_cqOrd_eq (h : Sol78Links H a L T s) {i : ℕ} (hi : 1 ≤ i)
    (hia : i ≤ a) (heq : cqOrd (L (i - 1)) = cqOrd (L i)) (hne : L (i - 1) ≠ L i) :
    Sol78Link5a (L i) (L (i - 1)) (s i) :=
  CFSG.EvenSporadicStandard.Induction.link5a_of_cqOrd_eq
    (h.comp (i - 1) (by omega)).2.isQuasisimple (h.comp i hia).2.isQuasisimple
    (h.incl i hi hia).1 (h.link i hi hia) heq hne

end Order

@[expose] def concat {α : Type*} (a : ℕ) (f g : ℕ → α) : ℕ → α :=
  fun i => if i ≤ a then f i else g (i - a)

theorem concat_of_le {α : Type*} {a : ℕ} {f g : ℕ → α} {i : ℕ} (h : i ≤ a) :
    concat a f g i = f i := by
  simp [concat, h]

theorem concat_add_succ {α : Type*} (a : ℕ) (f g : ℕ → α) (k : ℕ) :
    concat a f g (a + (k + 1)) = g (k + 1) := by
  have h1 : ¬ (a + (k + 1) ≤ a) := by omega
  have h2 : a + (k + 1) - a = k + 1 := by omega
  simp [concat, h1, h2]

theorem concat_add {α : Type*} {a : ℕ} {f g : ℕ → α} (hjoin : g 0 = f a) (k : ℕ) :
    concat a f g (a + k) = g k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [Nat.add_zero, concat_of_le le_rfl, hjoin]
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    exact concat_add_succ a f g k

theorem Sol78Links.concat {L' T' : ℕ → Subgroup H} {s' : ℕ → H}
    (hL : Sol78Links H a L T s) (hL' : Sol78Links H b L' T' s') (hjoin : L' 0 = L a) :
    Sol78Links H (a + b) (concat a L L') (concat a T T') (concat a s s') := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    by_cases hia : i ≤ a
    · rw [concat_of_le hia, concat_of_le hia]
      exact hL.comp i hia
    · obtain ⟨k, rfl⟩ : ∃ k, i = a + (k + 1) := ⟨i - a - 1, by omega⟩
      rw [concat_add_succ, concat_add_succ]
      exact hL'.comp (k + 1) (by omega)
  · intro i hi1 hi
    by_cases hia : i ≤ a
    · rw [concat_of_le hia, concat_of_le hia, concat_of_le (show i - 1 ≤ a by omega)]
      exact hL.elem i hi1 hia
    · obtain ⟨k, rfl⟩ : ∃ k, i = a + (k + 1) := ⟨i - a - 1, by omega⟩
      have h1 : a + (k + 1) - 1 = a + k := by omega
      rw [concat_add_succ, concat_add_succ, h1, concat_add hjoin]
      exact hL'.elem (k + 1) (by omega) (by omega)
  · intro i hi1 hi
    by_cases hia : i ≤ a
    · rw [concat_of_le hia, concat_of_le hia, concat_of_le hia,
        concat_of_le (show i - 1 ≤ a by omega)]
      exact hL.incl i hi1 hia
    · obtain ⟨k, rfl⟩ : ∃ k, i = a + (k + 1) := ⟨i - a - 1, by omega⟩
      have h1 : a + (k + 1) - 1 = a + k := by omega
      rw [concat_add_succ, concat_add_succ, concat_add_succ, h1, concat_add hjoin]
      exact hL'.incl (k + 1) (by omega) (by omega)
  · intro i hi1 hi
    by_cases hia : i ≤ a
    · rw [concat_of_le hia, concat_of_le hia, concat_of_le (show i - 1 ≤ a by omega)]
      exact hL.link i hi1 hia
    · obtain ⟨k, rfl⟩ : ∃ k, i = a + (k + 1) := ⟨i - a - 1, by omega⟩
      have h1 : a + (k + 1) - 1 = a + k := by omega
      rw [concat_add_succ, concat_add_succ, h1, concat_add hjoin]
      exact hL'.link (k + 1) (by omega) (by omega)

end CFSG.EvenSporadicStandard.Induction
