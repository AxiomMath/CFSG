module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.Step

public section

namespace CFSG.EvenSporadicStandard.M12Std.Rbc

open Subgroup CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction

theorem forall_le_concat {α : Type*} {a b : ℕ} {f g : ℕ → α} {P : α → Prop}
    (hf : ∀ i ≤ a, P (f i)) (hg : ∀ i ≤ b, P (g i)) : ∀ i ≤ a + b, P (concat a f g i) := by
  intro i hi
  by_cases hia : i ≤ a
  · rw [concat_of_le hia]
    exact hf i hia
  · obtain ⟨k, rfl⟩ : ∃ k, i = a + (k + 1) := ⟨i - a - 1, by omega⟩
    rw [concat_add_succ]
    exact hg (k + 1) (by omega)

section TLinksConcat

variable {H : Type} [Group H] {a b : ℕ} {L T L' T' : ℕ → Subgroup H} {s s' : ℕ → H}

theorem TLinks.singleton {T₀ K : Subgroup H} (hT : IsPGroup 2 T₀)
    (hK : IsCompIn K (centralizer (T₀ : Set H))) :
    TLinks H 0 (fun _ => K) (fun _ => T₀) (fun _ => 1) := by
  refine ⟨fun i hi => ?_, fun i h1 hi => by omega, fun i h1 hi => by omega,
    fun i h1 hi => by omega⟩
  obtain rfl : i = 0 := by omega
  exact ⟨hT, hK⟩

theorem TLinks.append (h : TLinks H a L T s) (h' : TLinks H b L' T' s') (hjoin : L' 0 = L a) :
    TLinks H (a + b) (concat a L L') (concat a T T') (concat a s s') := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    by_cases hia : i ≤ a
    · rw [concat_of_le hia, concat_of_le hia]
      exact h.comp i hia
    · obtain ⟨k, rfl⟩ : ∃ k, i = a + (k + 1) := ⟨i - a - 1, by omega⟩
      rw [concat_add_succ, concat_add_succ]
      exact h'.comp (k + 1) (by omega)
  · intro i hi1 hi
    by_cases hia : i ≤ a
    · rw [concat_of_le hia, concat_of_le hia, concat_of_le (show i - 1 ≤ a by omega)]
      exact h.elem i hi1 hia
    · obtain ⟨k, rfl⟩ : ∃ k, i = a + (k + 1) := ⟨i - a - 1, by omega⟩
      have h1 : a + (k + 1) - 1 = a + k := by omega
      rw [concat_add_succ, concat_add_succ, h1, concat_add hjoin]
      exact h'.elem (k + 1) (by omega) (by omega)
  · intro i hi1 hi
    by_cases hia : i ≤ a
    · rw [concat_of_le hia, concat_of_le hia, concat_of_le hia,
        concat_of_le (show i - 1 ≤ a by omega)]
      exact h.incl i hi1 hia
    · obtain ⟨k, rfl⟩ : ∃ k, i = a + (k + 1) := ⟨i - a - 1, by omega⟩
      have h1 : a + (k + 1) - 1 = a + k := by omega
      rw [concat_add_succ, concat_add_succ, concat_add_succ, h1, concat_add hjoin]
      exact h'.incl (k + 1) (by omega) (by omega)
  · intro i hi1 hi
    by_cases hia : i ≤ a
    · rw [concat_of_le hia, concat_of_le hia, concat_of_le (show i - 1 ≤ a by omega)]
      exact h.link i hi1 hia
    · obtain ⟨k, rfl⟩ : ∃ k, i = a + (k + 1) := ⟨i - a - 1, by omega⟩
      have h1 : a + (k + 1) - 1 = a + k := by omega
      rw [concat_add_succ, concat_add_succ, h1, concat_add hjoin]
      exact h'.link (k + 1) (by omega) (by omega)

theorem TLinks.cut (h : TLinks H a L T s) {i j : ℕ} (hij : i < j) (hja : j ≤ a)
    (heq : L i = L j) :
    TLinks H (a - (j - i)) (concat i L fun k => L (k + j)) (concat i T fun k => T (k + j))
      (concat i s fun k => s (k + j)) := by
  have hjoin : (fun k => L (k + j)) 0 = L i := by simpa using heq.symm
  have h1 := (h.mono (show i ≤ a by omega)).append (h.shift j hja) hjoin
  rwa [show i + (a - j) = a - (j - i) by omega] at h1

theorem TLinks.exists_inj (h : TLinks H a L T s) :
    ∃ b ≤ a, ∃ L' T' s', TLinks H b L' T' s' ∧ L' 0 = L 0 ∧ L' b = L a ∧
      (∀ i ≤ b, ∀ j ≤ b, L' i = L' j → i = j) ∧
      (∀ i ≤ b, ∃ k ≤ a, L' i = L k ∧ T' i = T k) := by
  classical
  have hex : ∃ m, ∃ (L' T' : ℕ → Subgroup H) (s' : ℕ → H), TLinks H m L' T' s' ∧
      L' 0 = L 0 ∧ L' m = L a ∧ ∀ i ≤ m, ∃ k ≤ a, L' i = L k ∧ T' i = T k :=
    ⟨a, L, T, s, h, rfl, rfl, fun i hi => ⟨i, hi, rfl, rfl⟩⟩
  obtain ⟨L₁, T₁, s₁, h₁, h0, hlast, hmem⟩ := Nat.find_spec hex
  set m := Nat.find hex with hm
  refine ⟨m, Nat.find_min' hex ⟨L, T, s, h, rfl, rfl, fun i hi => ⟨i, hi, rfl, rfl⟩⟩,
    L₁, T₁, s₁, h₁, h0, hlast, ?_, hmem⟩
  by_contra hcon
  push Not at hcon
  have key : ∃ i j, i < j ∧ j ≤ m ∧ L₁ i = L₁ j := by
    obtain ⟨i, hi, j, hj, hij, hne⟩ := hcon
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact ⟨i, j, hlt, hj, hij⟩
    · exact ⟨j, i, hlt, hi, hij.symm⟩
  obtain ⟨i, j, hlt, hjm, hLij⟩ := key
  have hjoin : (fun k => L₁ (k + j)) 0 = L₁ i := by simpa using hLij.symm
  refine Nat.find_min hex (show m - (j - i) < m by omega)
    ⟨_, _, _, h₁.cut hlt hjm hLij, ?_, ?_, ?_⟩
  · rw [concat_of_le (Nat.zero_le i)]
    exact h0
  · rw [show m - (j - i) = i + (m - j) by omega, concat_add hjoin]
    simpa [Nat.sub_add_cancel hjm] using hlast
  · intro p hp
    by_cases hpi : p ≤ i
    · rw [concat_of_le hpi, concat_of_le hpi]
      exact hmem p (by omega)
    · obtain ⟨q, rfl⟩ : ∃ q, p = i + (q + 1) := ⟨p - i - 1, by omega⟩
      rw [concat_add_succ, concat_add_succ]
      exact hmem (q + 1 + j) (by omega)

theorem TLinks.exists_inj_last (h : TLinks H a L T s) (ha : 1 ≤ a)
    (hlast : ∀ i < a, L i ≠ L a) :
    ∃ b ≤ a, 1 ≤ b ∧ ∃ L' T' s', TLinks H b L' T' s' ∧ L' 0 = L 0 ∧ L' b = L a ∧
      L' (b - 1) = L (a - 1) ∧ (∀ i ≤ b, ∀ j ≤ b, L' i = L' j → i = j) ∧
      (∀ i ≤ b, ∃ k ≤ a, L' i = L k ∧ T' i = T k) := by
  obtain ⟨c, hc, L₁, T₁, s₁, h₁, h0, hcL, hinj, hmem⟩ :=
    (h.mono (show a - 1 ≤ a by omega)).exists_inj
  have hlink : TLinks H 1 (fun k => L (k + (a - 1))) (fun k => T (k + (a - 1)))
      (fun k => s (k + (a - 1))) := by
    have := h.shift (a - 1) (by omega)
    rwa [show a - (a - 1) = 1 by omega] at this
  have hjoin : (fun k => L (k + (a - 1))) 0 = L₁ c := by simpa using hcL.symm
  have hsucc : ∀ {α : Type} (f g : ℕ → α), concat c f g (c + 1) = g 1 :=
    fun f g => concat_add_succ c f g 0
  have hLc : ∀ i ≤ c, L₁ i ≠ L a := by
    intro i hi
    obtain ⟨k, hk, hk1, -⟩ := hmem i hi
    rw [hk1]
    exact hlast k (by omega)
  have hlastL : concat c L₁ (fun k => L (k + (a - 1))) (c + 1) = L a := by
    rw [hsucc]
    exact congrArg L (by omega)
  refine ⟨c + 1, by omega, by omega, _, _, _, h₁.append hlink hjoin, ?_, hlastL, ?_, ?_, ?_⟩
  · rw [concat_of_le (Nat.zero_le c)]
    exact h0
  · rw [Nat.add_sub_cancel, concat_of_le le_rfl]
    exact hcL
  · intro i hi j hj hij
    by_cases hic : i ≤ c <;> by_cases hjc : j ≤ c
    · rw [concat_of_le hic, concat_of_le hjc] at hij
      exact hinj i hic j hjc hij
    · obtain rfl : j = c + 1 := by omega
      rw [concat_of_le hic, hlastL] at hij
      exact absurd hij (hLc i hic)
    · obtain rfl : i = c + 1 := by omega
      rw [concat_of_le hjc, hlastL] at hij
      exact absurd hij.symm (hLc j hjc)
    · omega
  · intro i hi
    by_cases hic : i ≤ c
    · rw [concat_of_le hic, concat_of_le hic]
      obtain ⟨k, hk, hk1, hk2⟩ := hmem i hic
      exact ⟨k, by omega, hk1, hk2⟩
    · obtain rfl : i = c + 1 := by omega
      refine ⟨a, le_rfl, hlastL, ?_⟩
      rw [hsucc]
      exact congrArg T (by omega)

end TLinksConcat

section Chains

variable {G : Type} [Group G]

theorem TLinks.eq_bot_of_eq_top {a : ℕ} {L T : ℕ → Subgroup G} {s : ℕ → G}
    (hG : IsSimpleGroup G) (hna : ∃ x y : G, x * y ≠ y * x) (h : TLinks G a L T s) {i : ℕ}
    (hi : i ≤ a) (hL : L i = ⊤) : T i = ⊥ := by
  have hc := (h.comp i hi).2
  rw [hL] at hc
  have h2 := Subgroup.centralizer_eq_top_iff_subset.1 (top_le_iff.1 hc.1)
  rw [eq_bot_iff]
  intro x hx
  have := h2 hx
  rwa [center_eq_bot_of_isSimpleGroup hG hna] at this

theorem seq2_ne_bot {T₀ T₁ : Subgroup G} (h₀ : T₀ ≠ ⊥) (h₁ : T₁ ≠ ⊥) :
    ∀ i ≤ 1, seq2 T₀ T₁ i ≠ ⊥ := by
  intro i hi
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hi with rfl | rfl
  · simpa using h₀
  · simpa using h₁

variable [Finite G]

theorem chain_of_transGen_ltF {K X : Subgroup G} (h : Relation.TransGen LtF K X) :
    ∃ a L T s, TLinks G a L T s ∧ L 0 = K ∧ L a = X ∧ ∀ i ≤ a, T i ≠ ⊥ := by
  induction h with
  | single hlt =>
    obtain ⟨T₀, T₁, u, hT₀, hT₁, hl⟩ := tLinks_of_ltF hlt
    exact ⟨1, _, _, _, hl, by simp [seq2], by simp [seq2], seq2_ne_bot hT₀ hT₁⟩
  | tail _ hlt ih =>
    obtain ⟨a, L, T, s, hl, h0, ha, hT⟩ := ih
    obtain ⟨T₀, T₁, u, hT₀, hT₁, hl'⟩ := tLinks_of_ltF hlt
    refine ⟨a + 1, _, _, _, hl.append hl' (by simp [seq2, ha]), ?_, ?_,
      forall_le_concat (P := fun x => x ≠ ⊥) hT (seq2_ne_bot hT₀ hT₁)⟩
    · rw [concat_of_le (Nat.zero_le a)]
      exact h0
    · exact (concat_add_succ a L _ 0).trans (by simp [seq2])

end Chains

end CFSG.EvenSporadicStandard.M12Std.Rbc
