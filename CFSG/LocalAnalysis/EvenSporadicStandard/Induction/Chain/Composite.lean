module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chain.Links
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Stage3Defs

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup Relation CFSG.EvenSporadicStandard.Solomon78

variable {H : Type} [Group H] {N : Subgroup H}

section Composite

variable {n m r : ℕ} {L T : ℕ → Subgroup H} {s : ℕ → H} {P TP : ℕ → Subgroup H} {sP : ℕ → H}
  {U TU : ℕ → Subgroup H} {sU : ℕ → H}

@[expose] def compGen {α : Type*} (n b j₀ : ℕ) (f g u : ℕ → α) : ℕ → α :=
  concat (n - 2 + b) (concat (n - 2) f g) (fun i => u (j₀ + i))

theorem compGen_of_le {α : Type*} {n b j₀ i : ℕ} {f g u : ℕ → α} (hi : i ≤ n - 2) :
    compGen n b j₀ f g u i = f i := by
  rw [compGen, concat_of_le (by omega : i ≤ n - 2 + b), concat_of_le hi]

theorem compGen_P {α : Type*} {n b j₀ k : ℕ} {f g u : ℕ → α} (hjoin : g 0 = f (n - 2))
    (hk : k ≤ b) : compGen n b j₀ f g u (n - 2 + k) = g k := by
  rw [compGen, concat_of_le (by omega : n - 2 + k ≤ n - 2 + b), concat_add hjoin]

theorem compGen_U {α : Type*} {n b j₀ : ℕ} {f g u : ℕ → α} (hjoin : g 0 = f (n - 2))
    (hu : u j₀ = g b) (k : ℕ) : compGen n b j₀ f g u (n - 2 + b + k) = u (j₀ + k) := by
  rw [compGen]
  refine concat_add (f := concat (n - 2) f g) (g := fun i => u (j₀ + i)) ?_ k
  show u (j₀ + 0) = _
  rw [Nat.add_zero, concat_add hjoin, hu]

theorem compLinks (hn : 2 ≤ n) (h : Sol78Links H n L T s) (hP : Sol78Links H m P TP sP)
    (hU : Sol78Links H r U TU sU) (hP0 : P 0 = L (n - 2)) {b j₀ : ℕ} (hb : b ≤ m) (hj₀ : j₀ ≤ r)
    (hjoin : U j₀ = P b) :
    Sol78Links H (n - 2 + b + (r - j₀)) (compGen n b j₀ L P U) (compGen n b j₀ T TP TU)
      (compGen n b j₀ s sP sU) := by
  refine (((h.mono (show n - 2 ≤ n by omega)).concat (hP.mono hb) hP0).concat
    (hU.shift j₀ hj₀) ?_)
  show U (j₀ + 0) = _
  rw [Nat.add_zero, concat_add hP0, hjoin]

variable [Finite H]

theorem compChain_inj (hN : FStarSimple N) (hn : 2 ≤ n) (h : Sol78Chain23 H N n L T s)
    {M : Subgroup H}
    (hP : Sol78Chain23 H M m P TP sP) (hP0 : P 0 = L (n - 2))
    (hTP : ∀ i, 1 ≤ i → i ≤ m → TP i ≠ ⊥) (hU : Sol78Chain23 H N r U TU sU)
    {b j₀ : ℕ} (hb1 : 1 ≤ b) (hb : b ≤ m) (hj₀ : j₀ < r) (hjoin : U j₀ = P b)
    (hLU : ∀ a ≤ n - 2, ∀ j, j₀ ≤ j → j < r → L a ≠ U j)
    (hLP : ∀ a < n - 2, ∀ b', 1 ≤ b' → b' ≤ b → L a ≠ P b')
    (hPU : ∀ b', 1 ≤ b' → b' < b → ∀ j, j₀ + 1 ≤ j → j < r → P b' ≠ U j) :
    ∀ i ≤ n - 2 + b + (r - j₀), ∀ k ≤ n - 2 + b + (r - j₀),
      compGen n b j₀ L P U i = compGen n b j₀ L P U k → i = k := by
  have hPN : ∀ b', 1 ≤ b' → b' ≤ m → P b' ≠ N := by
    intro b' h1 h2 heq
    have hc := (hP.comp b' h2).2
    rw [heq] at hc
    exact hTP b' h1 h2 (hN.eq_bot_of_isCompIn hc)
  have hLN : ∀ a ≤ n - 2, a ≤ n → L a ≠ N := by
    intro a ha han heq
    have := h.inj a han n le_rfl (by rw [h.last]; exact heq)
    omega
  have hCL : ∀ i ≤ n - 2, compGen n b j₀ L P U i = L i := fun i hi => compGen_of_le hi
  have hCP : ∀ y ≤ b, compGen n b j₀ L P U (n - 2 + y) = P y := fun y hy => compGen_P hP0 hy
  have hCU : ∀ y, compGen n b j₀ L P U (n - 2 + b + y) = U (j₀ + y) := fun y =>
    compGen_U hP0 hjoin y
  have key : ∀ i ≤ n - 2 + b + (r - j₀), ∀ k ≤ n - 2 + b + (r - j₀), i ≤ k →
      compGen n b j₀ L P U i = compGen n b j₀ L P U k → i = k := by
    intro i hi k hk hik hCik
    rcases (show i ≤ n - 2 ∨ (n - 2 < i ∧ i ≤ n - 2 + b) ∨ n - 2 + b < i by omega) with
      hiL | ⟨hi1, hi2⟩ | hiU
    · rcases (show k ≤ n - 2 ∨ (n - 2 < k ∧ k ≤ n - 2 + b) ∨ n - 2 + b < k by omega) with
        hkL | ⟨hk1, hk2⟩ | hkU
      · rw [hCL i hiL, hCL k hkL] at hCik
        exact h.inj i (by omega) k (by omega) hCik
      · obtain ⟨y, rfl⟩ : ∃ y, k = n - 2 + y := ⟨k - (n - 2), by omega⟩
        rw [hCL i hiL, hCP y (by omega)] at hCik
        by_cases hin : i = n - 2
        · subst hin
          have h1 : P 0 = P y := by rw [hP0, hCik]
          have := hP.inj 0 (Nat.zero_le _) y (by omega) h1
          omega
        · exact absurd hCik (hLP i (by omega) y (by omega) (by omega))
      · obtain ⟨y, rfl⟩ : ∃ y, k = n - 2 + b + y := ⟨k - (n - 2 + b), by omega⟩
        rw [hCL i hiL, hCU y] at hCik
        by_cases hjr : j₀ + y = r
        · rw [hjr, hU.last] at hCik
          exact absurd hCik (hLN i hiL (by omega))
        · exact absurd hCik (hLU i hiL (j₀ + y) (by omega) (by omega))
    · obtain ⟨x, rfl⟩ : ∃ x, i = n - 2 + x := ⟨i - (n - 2), by omega⟩
      rcases (show (n - 2 < k ∧ k ≤ n - 2 + b) ∨ n - 2 + b < k by omega) with ⟨hk1, hk2⟩ | hkU
      · obtain ⟨y, rfl⟩ : ∃ y, k = n - 2 + y := ⟨k - (n - 2), by omega⟩
        rw [hCP x (by omega), hCP y (by omega)] at hCik
        have := hP.inj x (by omega) y (by omega) hCik
        omega
      · obtain ⟨y, rfl⟩ : ∃ y, k = n - 2 + b + y := ⟨k - (n - 2 + b), by omega⟩
        rw [hCP x (by omega), hCU y] at hCik
        by_cases hjr : j₀ + y = r
        · rw [hjr, hU.last] at hCik
          exact absurd hCik (hPN x (by omega) (by omega))
        · by_cases hxb : x = b
          · subst hxb
            have h1 : U j₀ = U (j₀ + y) := by rw [hjoin, hCik]
            have := hU.inj j₀ (by omega) (j₀ + y) (by omega) h1
            omega
          · exact absurd hCik (hPU x (by omega) (by omega) (j₀ + y) (by omega) (by omega))
    · obtain ⟨x, rfl⟩ : ∃ x, i = n - 2 + b + x := ⟨i - (n - 2 + b), by omega⟩
      obtain ⟨y, rfl⟩ : ∃ y, k = n - 2 + b + y := ⟨k - (n - 2 + b), by omega⟩
      rw [hCU x, hCU y] at hCik
      have := hU.inj (j₀ + x) (by omega) (j₀ + y) (by omega) hCik
      omega
  intro i hi k hk hCik
  rcases le_total i k with hik | hki
  · exact key i hi k hk hik hCik
  · exact (key k hk i hi hki hCik.symm).symm

theorem compChain_length_bound {IsK : GroupClass} (hN : FStarSimple N) (hn : 2 ≤ n)
    (h : Sol78Chain23 H N n L T s) (h0 : IsK ↥(L 0)) (hmax : ∀ k, IsKChain IsK N k → k ≤ n)
    {M : Subgroup H} (hP : Sol78Chain23 H M m P TP sP) (hP0 : P 0 = L (n - 2))
    (hTP : ∀ i, 1 ≤ i → i ≤ m → TP i ≠ ⊥) (hU : Sol78Chain23 H N r U TU sU)
    {b j₀ : ℕ} (hb1 : 1 ≤ b) (hb : b ≤ m) (hj₀ : j₀ < r) (hjoin : U j₀ = P b)
    (hLU : ∀ a ≤ n - 2, ∀ j, j₀ ≤ j → j < r → L a ≠ U j)
    (hLP : ∀ a < n - 2, ∀ b', 1 ≤ b' → b' ≤ b → L a ≠ P b')
    (hPU : ∀ b', 1 ≤ b' → b' < b → ∀ j, j₀ + 1 ≤ j → j < r → P b' ≠ U j) :
    b + (r - j₀) ≤ 2 := by
  have hinj := compChain_inj hN hn h hP hP0 hTP hU hb1 hb hj₀ hjoin hLU hLP hPU
  have hlinks := compLinks hn h.toLinks hP.toLinks hU.toLinks hP0 hb hj₀.le hjoin
  have hlast : compGen n b j₀ L P U (n - 2 + b + (r - j₀)) = N := by
    rw [compGen_U hP0 hjoin, Nat.add_sub_cancel' hj₀.le, hU.last]
  have hchain := hlinks.toChain hlast hinj
  have hK : IsKChain IsK N (n - 2 + b + (r - j₀)) :=
    ⟨_, _, _, hchain, by rw [compGen_of_le (Nat.zero_le _)]; exact h0⟩
  have := hmax _ hK
  omega

end Composite

end CFSG.EvenSporadicStandard.Induction
