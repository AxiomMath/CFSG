module

public import CFSG.LocalAnalysis.GLTheoremA.S12.Compl123

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10

@[expose] def T167Idx (f : ℕ) : TauCeti.CFSGIndex → Prop := fun i =>
  (f = 1 ∧ ∃ n : ℕ, Odd n ∧ 5 ≤ n ∧ isLnA n 2 i) ∨
  (f = 1 ∧ ∃ n : ℕ, Even n ∧ 6 ≤ n ∧ isOmMA n 2 i) ∨
  (∃ n : ℕ, Odd n ∧ 3 ≤ n ∧ (f = 1 → 5 ≤ n) ∧ 1 ≤ f ∧ 3 ∣ 2 ^ f + 1 ∧ isOmPA n (2 ^ f) i)

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem type167J_three {J : Subgroup Ω} (h : Type167J 3 J) :
    ∃ f : ℕ, 1 ≤ f ∧ 3 ∣ 2 ^ f + 1 ∧ catalogIs (PSimple 3 J) (T167Idx f) := by
  rcases h with ⟨-, n, hn, hn5, hJ⟩ | ⟨-, n, hn, hn6, hJ⟩ | ⟨n, k, hn, hn3, hk5, hk, hpk, hJ⟩
  · obtain ⟨i, hi, hiso⟩ := hJ
    exact ⟨1, le_rfl, by norm_num, i, Or.inl ⟨rfl, n, hn, hn5, hi⟩, hiso⟩
  · obtain ⟨i, hi, hiso⟩ := hJ
    exact ⟨1, le_rfl, by norm_num, i, Or.inr (Or.inl ⟨rfl, n, hn, hn6, hi⟩), hiso⟩
  · obtain ⟨i, hi, hiso⟩ := hJ
    exact ⟨k, hk, hpk, i, Or.inr (Or.inr ⟨n, hn, hn3, hk5, hk, hpk, hi⟩), hiso⟩

end CFSG.LocalAnalysis.GLTheoremA.I167

end
