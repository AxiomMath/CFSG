module

public import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat

public section

namespace CFSG.AGLEmbeddingD2.HeisLinear

variable {m : ℕ}

@[expose] def RunIn (I : Set (Fin m)) (a n : ℕ) : Prop :=
  a + n ≤ m ∧ ∀ k : Fin m, a ≤ k.val → k.val < a + n → k ∈ I

theorem RunIn.mono {I : Set (Fin m)} {a n : ℕ} (h : RunIn I a n) {b n' : ℕ} (hb : a ≤ b)
    (hbn : b + n' ≤ a + n) : RunIn I b n' :=
  ⟨by have := h.1; omega, fun k hk1 hk2 => h.2 k (by omega) (by omega)⟩

open Classical in
noncomputable def blockIndex (I : Set (Fin m)) (b : Fin (m + 1)) : ℕ :=
  (Finset.univ.filter fun k : Fin m => k.val < b.val ∧ k ∉ I).card

theorem blockIndex_succ_of_mem {I : Set (Fin m)} {i : Fin m} (hi : i ∈ I) :
    blockIndex I i.succ = blockIndex I i.castSucc := by
  classical
  unfold blockIndex
  congr 1
  refine Finset.filter_congr fun k _ => ?_
  simp only [Fin.val_succ, Fin.val_castSucc]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h | h
    · exact h
    · exact absurd (Fin.ext h ▸ hi) h2
  · rintro ⟨h1, h2⟩
    exact ⟨by omega, h2⟩

theorem blockIndex_lt_of_not_mem {I : Set (Fin m)} {b b' : Fin (m + 1)} {k : Fin m} (hk : k ∉ I)
    (h1 : b.val ≤ k.val) (h2 : k.val < b'.val) : blockIndex I b < blockIndex I b' := by
  classical
  unfold blockIndex
  refine Finset.card_lt_card (Finset.ssubset_iff_of_subset ?_ |>.2 ⟨k, ?_, ?_⟩)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact ⟨by omega, hx.2⟩
  · simp [hk, h2]
  · simp [h1]

theorem card_blockIndex_le {I : Set (Fin m)} {n : ℕ} (hn : ¬ ∃ a, RunIn I a n) (c : ℕ) :
    Fintype.card {b : Fin (m + 1) // blockIndex I b = c} ≤ n := by
  classical
  rw [Fintype.card_subtype]
  by_contra hlt
  push Not at hlt
  set B := Finset.univ.filter fun b : Fin (m + 1) => blockIndex I b = c with hB
  have hne : B.Nonempty := Finset.card_pos.1 (by omega)
  set b₀ := B.min' hne with hb₀def
  have hb₀ : b₀ ∈ B := B.min'_mem hne
  by_cases hfar : ∃ b ∈ B, b₀.val + n ≤ b.val
  · obtain ⟨b, hb, hbn⟩ := hfar
    refine hn ⟨b₀.val, ?_, ?_⟩
    · have := b.isLt
      omega
    · intro k hk1 hk2
      by_contra hk
      have hlt' := blockIndex_lt_of_not_mem hk hk1 (by omega : k.val < b.val)
      simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and] at hb hb₀
      omega
  · push Not at hfar
    have hsub : B.image Fin.val ⊆ Finset.Ico b₀.val (b₀.val + n) := by
      intro x hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hx
      exact Finset.mem_Ico.2 ⟨Fin.le_def.1 (B.min'_le b hb), hfar b hb⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ Fin.val_injective, Nat.card_Ico] at this
    omega

theorem exists_orth_of_runIn {I : Set (Fin m)} {a : ℕ} (h : RunIn I a 5) :
    ∃ x ∈ I, ∃ y ∈ I, ∃ z ∈ I, x.val + 2 ≤ y.val ∧ y.val + 2 ≤ z.val := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨⟨a, by omega⟩, h2 _ (by simp) (by simp), ⟨a + 2, by omega⟩, h2 _ (by simp) (by simp),
    ⟨a + 4, by omega⟩, h2 _ (by simp) (by simp), by simp, by simp⟩

theorem exists_runs_of_runIn {I : Set (Fin m)} {a : ℕ} (h : RunIn I a 11) :
    ∃ x y z : ℕ, x + 4 ≤ y ∧ y + 4 ≤ z ∧ RunIn I x 3 ∧ RunIn I y 3 ∧ RunIn I z 3 :=
  ⟨a, a + 4, a + 8, by omega, by omega, h.mono le_rfl (by omega), h.mono (by omega) (by omega),
    h.mono (by omega) (by omega)⟩

theorem not_exists_runIn_four {I : Set (Fin m)} (hm : m ≤ 4) {j : Fin m} (hj : j ∉ I) :
    ¬ ∃ a, RunIn I a 4 := by
  rintro ⟨a, h1, h2⟩
  exact hj (h2 j (by omega) (by have := j.isLt; omega))

end CFSG.AGLEmbeddingD2.HeisLinear
