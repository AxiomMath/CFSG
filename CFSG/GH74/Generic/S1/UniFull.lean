module

public import CFSG.GH74.Generic.S1.UniGraphA
public import CFSG.GH74.Generic.S1.UniAdapted
public import CFSG.GH74.Generic.S1.UniClassify
public import CFSG.GH74.Generic.S1.UniGraph

public section

namespace CFSG.GH74.Generic.S1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Matrix
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.GH74.Generic.S1.Uni

theorem graphField_uni {F : Type} [Field F] [Finite F] {q : ℕ} (hF : Nat.card F = q ^ 2)
    (hq : q % 4 = 1) (α : MulAut ↥(StatedSU 4 q F)) (_hα : α * α = 1)
    (h : IsGraphFieldLike (StatedSU 4 q F) q α) :
    GoodFixedCentral False α ∨ IsExoticUni (StatedSU 4 q F) q α := by
  obtain ⟨p, f, hu, rfl, hp2⟩ := exists_unitaryFieldData hF hq
  obtain ⟨bar, g, hbar, ⟨c, hgc⟩, hαg⟩ := h
  have hbarEq : bar = (hu.bar : F →+* F) :=
    RingHom.ext fun x => (hbar x).trans (hu.bar_apply x).symm
  subst hbarEq
  obtain ⟨g', ε, hε, hu', hgg', hsym, hαg'⟩ := normalize_graph hu hp2 hq α hgc hαg
  rcases hε with rfl | rfl
  · by_cases hsq : ∃ u : F, u ^ (p ^ f + 1) = 1 ∧ u * u = (g' : Matrix (Fin 4) (Fin 4) F).det
    · left
      obtain ⟨P, hP1, hP2⟩ := adapted_sym hu hp2 hu' (by simpa using hgg') hsq
      exact goodFixedCentral_of_adapted hu hp2 hq α (ε := 1) (s := 1) (Or.inl rfl) one_ne_zero
        hαg' hP1 (by rw [one_smul]; exact hP2)
    · right
      exact ⟨hu.bar, g', fun x => hu.bar_apply x, hu', by simpa using hsym, hsq, hαg'⟩
  · left
    obtain ⟨P, s, hs, hP1, hP2⟩ := adapted_skew hu hp2 hu' hgg'
    exact goodFixedCentral_of_adapted hu hp2 hq α (ε := -1) (s := s) (Or.inr rfl) hs hαg' hP1 hP2

theorem classify_uni_full {F : Type} [Field F] [Finite F] {q : ℕ} (hF : Nat.card F = q ^ 2)
    (hq : q % 4 = 1) (α : MulAut ↥(StatedSU 4 q F)) (hα : α * α = 1)
    (hout : ∀ k : ↥(StatedSU 4 q F), α ≠ MulAut.conj k) :
    GoodFixedCentral False α ∨ IsReflection (StatedSU 4 q F) α ∨
      IsExoticUni (StatedSU 4 q F) q α := by
  rcases classify_uni hF hq α hα hout with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · rcases graphField_uni hF hq α hα h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inr h')

end CFSG.GH74.Generic.S1
