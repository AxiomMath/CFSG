module

public import CFSG.HardMathSupport.Foote.Coordinator.AnisoCube.E6ThreeLines

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.AnisoCube

open CFSG.HardMathSupport.Malle.SeitzCube
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem not_mem_block_zero_one_of_neg_mem_radical
    {α : Fin Tag.E6.rank → ℤ}
    (h : -α ∈ parabolicRadicalRoots Tag.E6 (e6FrameLeviSet 0 ∪ e6FrameLeviSet 1)) :
    α ∉ e6BlockRoots 0 ∧ α ∉ e6BlockRoots 1 := by
  obtain ⟨-, -, k, hk, hk'⟩ := mem_parabolicRadicalRoots_iff.1 h
  exact not_mem_block_zero_one ⟨k, hk, fun hαk => hk' (by simp [hαk])⟩

theorem line_cases {p : ℕ} (_hp : p.Prime) (q : ℕ) {x y : ℕ} (hx : x < p) (hy : y < p)
    (hxy : x ≠ 0 ∨ y ≠ 0) :
    (¬ p ∣ x ∧ ∃ s : Fin 3, (y : ZMod p) = (x : ZMod p) * (q : ZMod p) ^ (s : ℕ)) ∨
    (¬ (p ∣ x ∧ p ∣ y) ∧
      (¬ p ∣ x → ∀ s : Fin 3, (y : ZMod p) ≠ (x : ZMod p) * (q : ZMod p) ^ (s : ℕ))) := by
  have hdvd : ∀ {n : ℕ}, n < p → (p ∣ n ↔ n = 0) := fun {n} hn =>
    ⟨fun h => Nat.eq_zero_of_dvd_of_lt h hn, fun h => h ▸ dvd_zero p⟩
  by_cases hpx : p ∣ x
  · right
    have hx0 : x = 0 := (hdvd hx).1 hpx
    have hy0 : y ≠ 0 := by
      rcases hxy with h | h
      · exact absurd hx0 h
      · exact h
    exact ⟨fun h => hy0 ((hdvd hy).1 h.2), fun h => absurd hpx h⟩
  · by_cases hs : ∃ s : Fin 3, (y : ZMod p) = (x : ZMod p) * (q : ZMod p) ^ (s : ℕ)
    · exact Or.inl ⟨hpx, hs⟩
    · exact Or.inr ⟨fun h => hpx h.1, fun _ s hs' => hs ⟨s, hs'⟩⟩

end CFSG.HardMathSupport.Foote.Coordinator.AnisoCube

end
