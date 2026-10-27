module

public import CFSG.GH74.GLS.Stage1.Main.BrG2AutC
public import CFSG.GH74.GLS.Stage4.HexRev
public import CFSG.GH74.GLS.Stage4.RestSetupRank

public section

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.GH74.GLS.Stage4.Rest CFSG.GH74.BNPair CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Main CFSG.Semidihedral.MatrixCoverData

namespace CFSG.GH74.GLS.Stage4.Rest.Rem

theorem m3_D1 : ∀ y : SL2F3, (∀ x : SL2F3, y * y * x = x * (y * y)) → y ^ 4 = 1 := by decide +kernel

theorem m3_D2 : ∀ y : SL2F3, y * y = 1 → ∀ x : SL2F3, y * x = x * y := by decide +kernel

theorem m3_D3 : ∃ w : SL2F3, w ^ 4 = 1 ∧ w * w ≠ 1 := by decide +kernel

theorem m3_units : ∀ u : (ZMod 3)ˣ, (u : ZMod 3) = 1 ∨ (u : ZMod 3) = 2 := by decide

theorem m3_nonsq : ¬ IsSquare (2 : ZMod 3) := by decide

theorem exists_outer_diag_of_involution_three {F : Type} [Field F] [Finite F] (h3 : Nat.card F = 3)
    (α : MulAut (Matrix.SpecialLinearGroup (Fin 2) F)) (hα : α * α = 1)
    (hfix : ∀ x : Matrix.SpecialLinearGroup (Fin 2) F, α x = x → x ^ 4 = 1 → x * x = 1) :
    ∃ g : GL (Fin 2) F, ¬ IsSquare ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) ∧
      ∀ x : Matrix.SpecialLinearGroup (Fin 2) F,
        ((α x : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
          (g : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F) *
            ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
  have : Fintype F := Fintype.ofFinite F
  have hF : Fintype.card F = Fintype.card (ZMod 3) := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, h3]
  let τ : F ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq hF
  let Φ : Matrix.SpecialLinearGroup (Fin 2) F ≃* SL2F3 := sl2EquivOfRingEquiv τ
  let α' : MulAut SL2F3 := MulAut.congr Φ α
  have hα'x : ∀ x, α' (Φ x) = Φ (α x) := fun x => by
    simp [α', MulAut.congr_apply]
  have hα'2 : α' * α' = 1 := by
    have := congrArg (MulAut.congr Φ) hα
    rwa [map_mul, map_one] at this
  obtain ⟨G', hG'⟩ := exists_slConjugation_of_mulAut α'
  have hdet : ¬ IsSquare ((Matrix.GeneralLinearGroup.det G' : (ZMod 3)ˣ) : ZMod 3) := by
    rcases m3_units (Matrix.GeneralLinearGroup.det G') with h | h
    · exfalso
      let y : SL2F3 := ⟨(G' : Matrix (Fin 2) (Fin 2) (ZMod 3)), by
        rw [← Matrix.GeneralLinearGroup.val_det_apply, h]⟩
      have hy : Matrix.SpecialLinearGroup.toGL y = G' := Units.ext rfl
      have hconj : ∀ X : SL2F3, α' X = y * X * y⁻¹ := by
        intro X
        rw [hG']
        apply Matrix.SpecialLinearGroup.toGL_injective
        rw [slConjugation_toGL, map_mul, map_mul, map_inv, hy]
      have hy2 : ∀ X : SL2F3, y * y * X = X * (y * y) := by
        intro X
        have h1 := congrArg (fun β : MulAut SL2F3 => β X) hα'2
        simp only [MulAut.mul_apply, MulAut.one_apply, hconj] at h1
        calc y * y * X = (y * (y * X * y⁻¹) * y⁻¹) * (y * y) := by group
          _ = X * (y * y) := by rw [h1]
      have hy4 := m3_D1 y hy2
      have hyfix : α (Φ.symm y) = Φ.symm y := by
        apply Φ.injective
        rw [← hα'x, MulEquiv.apply_symm_apply, hconj]
        group
      have hy4' : (Φ.symm y) ^ 4 = 1 := by rw [← map_pow, hy4, map_one]
      have hyy : Φ.symm y * Φ.symm y = 1 := hfix _ hyfix hy4'
      have hyy' : y * y = 1 := by
        have := congrArg Φ hyy
        simpa using this
      have hcen := m3_D2 y hyy'
      have hα1 : ∀ x, α x = x := by
        intro x
        apply Φ.injective
        rw [← hα'x, hconj, hcen (Φ x)]
        group
      obtain ⟨w, hw4, hw2⟩ := m3_D3
      apply hw2
      have h1 : Φ.symm w * Φ.symm w = 1 := hfix _ (hα1 _) (by rw [← map_pow, hw4, map_one])
      have := congrArg Φ h1
      simpa using this
    · rw [h]; exact m3_nonsq
  have hmapval : ∀ M : GL (Fin 2) (ZMod 3),
      ((Matrix.GeneralLinearGroup.map τ.symm.toRingHom M : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        (M : Matrix (Fin 2) (Fin 2) (ZMod 3)).map τ.symm := fun M => rfl
  refine ⟨Matrix.GeneralLinearGroup.map τ.symm.toRingHom G', ?_, ?_⟩
  · intro hsq
    apply hdet
    have h1 : ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map τ.symm.toRingHom G') : Fˣ) : F) =
        τ.symm ((Matrix.GeneralLinearGroup.det G' : (ZMod 3)ˣ) : ZMod 3) := by
      rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, hmapval]
      exact (RingHom.map_det τ.symm.toRingHom _).symm
    rw [h1] at hsq
    have := hsq.map τ.toRingHom
    simpa using this
  · intro x
    have h1 : Φ (α x) = slConjugation (ZMod 3) G' (Φ x) := by rw [← hG', hα'x]
    have h2 := congrArg (fun X : SL2F3 => (X : Matrix (Fin 2) (Fin 2) (ZMod 3))) h1
    simp only [slConjugation_matrix] at h2
    have h3 := congrArg (RingHom.mapMatrix τ.symm.toRingHom) h2
    rw [map_mul, map_mul] at h3
    have hΦ : ∀ y : Matrix.SpecialLinearGroup (Fin 2) F,
        (RingHom.mapMatrix τ.symm.toRingHom) ((Φ y : SL2F3) : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
          (y : Matrix (Fin 2) (Fin 2) F) := by
      intro y
      ext i j
      simp [Φ, sl2EquivOfRingEquiv]
    rw [hΦ, hΦ] at h3
    rw [h3, hmapval, ← map_inv (Matrix.GeneralLinearGroup.map τ.symm.toRingHom) G', hmapval]
    rfl

end CFSG.GH74.GLS.Stage4.Rest.Rem
