module

public import CFSG.LocalAnalysis.ComponentInitial.UnitarySixFieldTwoAutModel

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitarySixFieldTwoAut

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.Assembly.LowTwoRank

variable {F : Type} [Field F] (h : UnitaryFieldData 2 1 F)

@[expose] noncomputable def binCast : ZMod 2 →+* F :=
  have := h.charP
  ZMod.castHom (dvd_refl 2) F

theorem zmod_two_cases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

theorem binCast_mem_bot (a : ZMod 2) : binCast h a ∈ (⊥ : Subfield F) := by
  rcases zmod_two_cases a with rfl | rfl
  · rw [map_zero]
    exact zero_mem _
  · rw [map_one]
    exact one_mem _

theorem bar_binCast (a : ZMod 2) : h.bar (binCast h a) = binCast h a :=
  congrArg (fun φ : ZMod 2 →+* F => φ a) (RingHom.ext_zmod (h.bar.comp (binCast h)) (binCast h))

@[expose] noncomputable def binMat (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) :
    Matrix (Fin 6) (Fin 6) F :=
  reindex sixEquiv sixEquiv (A.map (binCast h))

theorem binMat_mul (A B : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) :
    binMat h (A * B) = binMat h A * binMat h B := by
  rw [binMat, binMat, binMat, reindex_mul_reindex, Matrix.map_mul]

theorem binMat_one : binMat h (1 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) = 1 := by
  rw [binMat, Matrix.map_one _ (map_zero _) (map_one _), reindex_apply, submatrix_one_equiv]

theorem binMat_transpose (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) :
    binMat h Aᵀ = (binMat h A)ᵀ := by
  rw [binMat, binMat, transpose_reindex, transpose_map]

theorem binMat_map_bar (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) :
    (binMat h A).map h.bar = binMat h A := by
  ext a b
  simp only [binMat, reindex_apply, submatrix_apply, map_apply, bar_binCast]

theorem binMat_J : binMat h (fromBlocks 0 1 (-1) 0) = (sixJ h : Matrix (Fin 6) (Fin 6) F) := by
  rw [sixJ_eq, binMat]
  congr 1
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [map_apply, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply, one_apply, map_zero,
      apply_ite (binCast h), map_one]
  split_ifs
  · change binCast h 1 = 1
    exact map_one _
  · change binCast h 0 = 0
    exact map_zero _

theorem det_binMat (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) :
    (binMat h A).det = binCast h A.det := by
  rw [binMat, det_reindex_self]
  exact (RingHom.map_det (binCast h) A).symm

theorem binMat_injective : Function.Injective (binMat h) := by
  intro A B hAB
  ext i j
  have := congrFun (congrFun hAB (sixEquiv i)) (sixEquiv j)
  simp only [binMat, reindex_apply, submatrix_apply, Equiv.symm_apply_apply, map_apply] at this
  exact (binCast h).injective this

@[expose] noncomputable def binMatHom :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) →* Matrix (Fin 6) (Fin 6) F where
  toFun := binMat h
  map_one' := binMat_one h
  map_mul' := binMat_mul h

theorem det_eq_one_of_GL (A : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) :
    (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)).det = 1 := by
  have h1 : (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp A.isUnit).ne_zero
  rcases zmod_two_cases (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)).det with h0 | h0
  · exact absurd h0 h1
  · exact h0

theorem binMat_mem_sixS {A : GL (Fin 3 ⊕ Fin 3) (ZMod 2)} (hA : A ∈ StatedSp 3 (ZMod 2)) :
    Units.map (binMatHom h) A ∈ sixS h := by
  refine ⟨?_, ?_⟩
  · change ((binMat h (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2))).map h.bar)ᵀ *
      (sixJ h : Matrix (Fin 6) (Fin 6) F) *
        binMat h (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) = sixJ h
    rw [binMat_map_bar, ← binMat_transpose]
    calc binMat h (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2))ᵀ *
          (sixJ h : Matrix (Fin 6) (Fin 6) F) *
            binMat h (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) =
          binMat h ((A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2))ᵀ *
            fromBlocks 0 1 (-1) 0 * (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2))) := by
          rw [binMat_mul, binMat_mul]
          congr 2
          exact (binMat_J h).symm
      _ = binMat h (fromBlocks 0 1 (-1) 0) :=
          congrArg (binMat h)
            (CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff.mp hA)
      _ = sixJ h := binMat_J h
  · change (binMat h (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2))).det = 1
    rw [det_binMat, det_eq_one_of_GL, map_one]

@[expose] noncomputable def binarySpEmbedding : StatedSp 3 (ZMod 2) →* sixS h :=
  ((Units.map (binMatHom h)).comp (StatedSp 3 (ZMod 2)).subtype).codRestrict (sixS h)
    fun A => binMat_mem_sixS h A.2

theorem coe_binarySpEmbedding (A : StatedSp 3 (ZMod 2)) :
    ((binarySpEmbedding h A : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
      binMat h ((A : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) _) :=
  rfl

theorem binarySpEmbedding_injective : Function.Injective (binarySpEmbedding h) := by
  intro A B hAB
  have := congrArg (fun x : sixS h => ((x : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) hAB
  simp only [coe_binarySpEmbedding] at this
  exact Subtype.ext (Units.ext (binMat_injective h this))

@[expose] noncomputable def binLift (x : F) : ZMod 2 :=
  haveI := Classical.decEq F
  if x = 0 then 0 else 1

theorem binCast_binLift {x : F} (hx : x ∈ (⊥ : Subfield F)) : binCast h (binLift x) = x := by
  rcases (mem_bot_iff h).mp hx with rfl | rfl
  · simp [binLift]
  · simp [binLift]

theorem range_binarySpEmbedding : (binarySpEmbedding h).range = binarySp h := by
  apply le_antisymm
  · rintro _ ⟨A, rfl⟩
    rw [mem_binarySp_iff]
    intro a b
    rw [coe_binarySpEmbedding, binMat, reindex_apply, submatrix_apply, map_apply]
    exact binCast_mem_bot h _
  · intro g hg
    set G := ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) with hG
    set A₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
      Matrix.of fun i j => binLift (G (sixEquiv i) (sixEquiv j)) with hA₀
    have hbin : binMat h A₀ = G := by
      ext a b
      rw [binMat, reindex_apply, submatrix_apply, map_apply, hA₀, Matrix.of_apply,
        Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact binCast_binLift h (hg a b)
    have hdet : A₀.det ≠ 0 := by
      intro h0
      have h1 := det_binMat h A₀
      rw [hbin, h0, map_zero, hG, g.2.2] at h1
      exact one_ne_zero h1
    set A : GL (Fin 3 ⊕ Fin 3) (ZMod 2) := GeneralLinearGroup.mkOfDetNeZero A₀ hdet with hA
    have hAmem : A ∈ StatedSp 3 (ZMod 2) := by
      have hgbar : G.map h.bar = G := (map_bar_eq_self_iff h G).mpr hg
      have hiso := mem_primeFormUnitary.mp g.2.1
      rw [← hG, hgbar] at hiso
      have key : binMat h (A₀ᵀ * fromBlocks 0 1 (-1) 0 * A₀) =
          binMat h (fromBlocks 0 1 (-1) 0) := by
        rw [binMat_mul, binMat_mul, binMat_transpose, hbin, binMat_J]
        exact hiso
      exact CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff.mpr
        (binMat_injective h key)
    refine ⟨⟨A, hAmem⟩, Subtype.ext (Units.ext ?_)⟩
    rw [coe_binarySpEmbedding]
    exact hbin

end CFSG.LocalAnalysis.ComponentInitial.UnitarySixFieldTwoAut
