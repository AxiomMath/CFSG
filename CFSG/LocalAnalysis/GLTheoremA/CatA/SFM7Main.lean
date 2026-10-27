module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM7L48

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

@[expose] def I2017LieNoA7Omega : Prop :=
  ∀ (S : Type) [Group S] [Finite S],
    catalogIs S (onLie fun d => d = TauCeti.LieTypeIndex.twistedD 4 gfTwoPP) →
      ∀ T : Subgroup S, IsPGroup 2 T → T ≠ ⊥ → ∀ H : Subgroup S, H ≤ Subgroup.normalizer (T : Set S) →
        ¬ Nonempty (↥H ≃* ↥(alternatingGroup (Fin 7)))

theorem catalogIs_onLie_or {S : Type} [Group S] {P Q : TauCeti.LieTypeIndex → Prop}
    (h : catalogIs S (onLie fun d => P d ∨ Q d)) : catalogIs S (onLie P) ∨ catalogIs S (onLie Q) := by
  obtain ⟨i, hi, e⟩ := h
  cases i with
  | cyclic p k => exact hi.elim
  | alternating n k => exact hi.elim
  | sporadic s => exact hi.elim
  | lie j =>
    obtain ⟨d, hv⟩ := j
    rcases hi with h1 | h2
    · exact Or.inl ⟨TauCeti.CFSGIndex.lie ⟨d, hv⟩, h1, e⟩
    · exact Or.inr ⟨TauCeti.CFSGIndex.lie ⟨d, hv⟩, h2, e⟩

theorem i2017LieNoA7_of_omega (hO : I2017LieNoA7Omega) : I2017LieNoA7 := by
  intro S _ _ hcat T hT hT1 H hH hiso
  rcases catalogIs_onLie_or (P := fun d => d = TauCeti.LieTypeIndex.A 3 gfEightPP)
      (Q := fun d => d = TauCeti.LieTypeIndex.twistedD 4 gfTwoPP) hcat with h1 | h2
  · exact I2017LieNoA7L48_holds S h1 T hT hT1 H hH hiso
  · exact hO S h2 T hT hT1 H hH hiso

end CFSG.LocalAnalysis.GLTheoremA
