module

public import CFSG.GH74.Generic.BProg.B3.S45EvenN4Fix
public import CFSG.GH74.Generic.BProg.B3.S45EvenDefs

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.Assembly.LowTwoRank CFSG.GH74.Generic.BProg.B3.S45TableA

theorem N4_sl4 {X : Type} [Group X] [Finite X] {F : Type} [Field F] [Finite F]
    (hF : Nat.card F % 4 = 3) (e : X ≃* ↥(StatedSL 4 F)) {y : MulAut X} (hy : orderOf y = 2)
    (hd : Datum X y)
    (hab : ∀ T : Subgroup X, IsPGroup 2 ↥T → (∀ t ∈ T, y t = t) → ∀ a ∈ T, ∀ b ∈ T, a * b = b * a)
    (hEA : EvenEA X y) : False := by
  classical
  have h2 : (2 : F) ≠ 0 := S45EvenN4Lin.two_ne_zero_of_card_mod hF
  let φ : X ≃* Matrix.SpecialLinearGroup (Fin 4) F := e.trans (specialLinearGroupEquivStatedSL 4 F).symm
  have hy2 : y * y = 1 := by
    have h := pow_orderOf_eq_one y
    rw [hy, pow_two] at h
    exact h
  rcases hEA with h1 | ⟨t, htt, htc, hyt⟩
  ·
    let u : MulAut (Matrix.SpecialLinearGroup (Fin 4) F) := MulAut.congr φ y
    have hu : u * u = 1 := by rw [← map_mul, hy2, map_one]
    obtain ⟨c, huc, hc4, hc2⟩ := S45EvenN4Fix.exists_fixed_order_four_sl4 hF u hu
    have hs : y (φ.symm c) = φ.symm c := by
      have : φ (y (φ.symm c)) = c := by simpa [u, MulAut.congr_apply] using huc
      apply φ.injective
      rw [this, MulEquiv.apply_symm_apply]
    have h4 : (φ.symm c) ^ (2 ^ 2) = 1 := by
      rw [← map_pow]
      have : c ^ (2 ^ 2) = 1 := by simpa using hc4
      rw [this, map_one]
    apply hc2
    have h5 := h1 _ hs 2 h4
    have := congrArg φ h5
    rwa [map_pow, MulEquiv.apply_symm_apply, map_one] at this
  ·
    have hTT : ((φ t : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
        ((φ t : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, ← map_mul, htt, map_one, Matrix.SpecialLinearGroup.coe_one]
    obtain ⟨a, b, hat, hbt, ha4, ha2, hb2, hba⟩ := S45EvenN4Eig.exists_D8_comm h2 hTT
    have hcomm : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
        (g : Matrix (Fin 4) (Fin 4) F) * (φ t : Matrix.SpecialLinearGroup (Fin 4) F) =
          (φ t : Matrix.SpecialLinearGroup (Fin 4) F) * g → y (φ.symm g) = φ.symm g := fun g hg => by
      have hg' : φ.symm g * t = t * φ.symm g := by
        apply φ.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
        exact Subtype.ext (by simpa using hg)
      rw [hyt, mul_inv_eq_iff_eq_mul]
      exact hg'.symm
    have hyfix : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
        (g : Matrix (Fin 4) (Fin 4) F) * (φ t : Matrix.SpecialLinearGroup (Fin 4) F) =
          (φ t : Matrix.SpecialLinearGroup (Fin 4) F) * g → y (φ.symm g) = φ.symm g := hcomm
    have h5 : Hyp5w X y := ⟨hy, hab, hd⟩
    refine h5.false_of_dihedral (a := φ.symm a) (b := φ.symm b) (hyfix a hat) (hyfix b hbt) ?_ ?_ ?_ ?_
    · rw [← map_pow, ha4, map_one]
    · intro h
      rw [← map_pow] at h
      exact ha2 (φ.symm.injective (by rw [h, map_one]))
    · rw [← map_mul, hb2, map_one]
    · rw [← map_inv, ← map_mul, ← map_mul, hba, map_inv]

end CFSG.GH74.Generic.BProg.B3
