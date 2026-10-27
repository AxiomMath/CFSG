module

public import CFSG.GH74.QTGen4.CharTwoQuotient

public section

namespace CFSG.GH74.QTGen4

open Matrix

variable {R : Type*} [Semiring R]

noncomputable def splitFour {d k : ℕ} (h : d + k = 4) : Fin 4 ≃ Fin d ⊕ Fin k :=
  (finCongr h.symm).trans finSumFinEquiv.symm

noncomputable def blockMatrix {d k : ℕ} (e : Fin 4 ≃ Fin d ⊕ Fin k) (A : Matrix (Fin d) (Fin d) R) :
    Matrix (Fin 4) (Fin 4) R :=
  (fromBlocks A 0 0 (1 : Matrix (Fin k) (Fin k) R)).submatrix e e

theorem blockMatrix_mul {d k : ℕ} (e : Fin 4 ≃ Fin d ⊕ Fin k) (A B : Matrix (Fin d) (Fin d) R) :
    blockMatrix e (A * B) = blockMatrix e A * blockMatrix e B := by
  simp [blockMatrix, fromBlocks_multiply]

theorem blockMatrix_one {d k : ℕ} (e : Fin 4 ≃ Fin d ⊕ Fin k) :
    blockMatrix e (1 : Matrix (Fin d) (Fin d) R) = 1 := by
  simp [blockMatrix, fromBlocks_one]

noncomputable def blockMatrixHom {d k : ℕ} (e : Fin 4 ≃ Fin d ⊕ Fin k) :
    Matrix (Fin d) (Fin d) R →* Matrix (Fin 4) (Fin 4) R where
  toFun := blockMatrix e
  map_one' := blockMatrix_one e
  map_mul' := blockMatrix_mul e

theorem blockMatrixHom_injective {d k : ℕ} (e : Fin 4 ≃ Fin d ⊕ Fin k) :
    Function.Injective (blockMatrixHom (R := R) e) := by
  intro A B h
  ext i j
  have h' := congrFun (congrFun h (e.symm (Sum.inl i))) (e.symm (Sum.inl j))
  simpa [blockMatrixHom, blockMatrix] using h'

noncomputable def blockGL {d k : ℕ} (e : Fin 4 ≃ Fin d ⊕ Fin k) :
    GL (Fin d) R →* GL (Fin 4) R :=
  Units.map (blockMatrixHom e)

theorem blockGL_injective {d k : ℕ} (e : Fin 4 ≃ Fin d ⊕ Fin k) :
    Function.Injective (blockGL (R := R) e) :=
  Units.map_injective (blockMatrixHom_injective e)

theorem exists_injective_quotient_pCore_to_GL4 {X : Type*} [Group X] [Finite X]
    (hX : CFSG.IsCharacteristicP 2 X) (hgen : CFSG.GH74.Gen4 X) :
    ∃ ψ : X ⧸ CFSG.pCore 2 X →* GL (Fin 4) (ZMod 2), Function.Injective ψ := by
  obtain ⟨ψ₀, hψ₀⟩ := exists_injective_quotient_pCore_to_mulAut_frattini hX
  have hQp : IsPGroup 2 ↥(CFSG.pCore 2 X) := CFSG.pCore_isPGroup (p := 2) (G := X)
  have hrank : Group.rank ↥(CFSG.pCore 2 X) ≤ 4 := by
    have h := CFSG.GH74.E2.rank_le_four_of_subgroup hgen hQp ⊤
    rw [← Group.rank_congr (Subgroup.topEquiv (G := ↥(CFSG.pCore 2 X)))]
    exact h
  obtain ⟨d, hd, hcard, hcomm, hpow⟩ :=
    CFSG.RankThree.PartOne.SectionalRank.frattini_quotient_elementary_of_rank_le_four hQp hrank
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary hcomm hpow hcard
  let e4 : Fin 4 ≃ Fin d ⊕ Fin (4 - d) := splitFour (by omega : d + (4 - d) = 4)
  refine ⟨(blockGL (R := ZMod 2) e4).comp
    ((CFSG.SectionRank.Ccomm.elemAutEquivGL e).toMonoidHom.comp ψ₀), ?_⟩
  exact (blockGL_injective e4).comp ((CFSG.SectionRank.Ccomm.elemAutEquivGL e).injective.comp hψ₀)

end CFSG.GH74.QTGen4
