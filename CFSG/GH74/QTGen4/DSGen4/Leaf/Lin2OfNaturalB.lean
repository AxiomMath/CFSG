module

public import CFSG.GH74.QTGen4.DSGen4.Leaf.Lin2OfNaturalA
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import Certificates.Data.A5GL42

public section

namespace CFSG.GH74.QTGen4.DSGen4.Lin2B

open CFSG.GH74.QTGen4.DSGen4.Lin2A
open Certificates.A5GL42 (aN bN aO bO HO Facts)
open scoped Matrix

abbrev Mat4 : Type := Matrix (Fin 4) (Fin 4) (ZMod 2)

theorem bO_ne_one : bO ≠ 1 := by
  decide

theorem bO_cube : bO * bO * bO = 1 := by
  decide

theorem exists_natural_conj (hF : Facts) (a b : GL (Fin 4) (ZMod 2))
    (ha : a * a = 1) (ha1 : a ≠ 1) (hb : b ^ 3 = 1) (hab : (a * b) ^ 5 = 1)
    (hff : ∀ v : Fin 4 → ZMod 2, (b : Mat4) *ᵥ v = v → v = 0) :
    ∃ g : GL (Fin 4) (ZMod 2), (g : Mat4) * (a : Mat4) = aN * (g : Mat4) ∧
      (g : Mat4) * (b : Mat4) = bN * (g : Mat4) := by
  have ha' : (a : Mat4) * (a : Mat4) = 1 := by rw [← Units.val_mul, ha, Units.val_one]
  have ha1' : (a : Mat4) ≠ 1 := fun h => ha1 (Units.ext h)
  have hb' : (b : Mat4) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hb, Units.val_one]
  have hab' : ((a : Mat4) * (b : Mat4)) ^ 5 = 1 := by
    rw [← Units.val_mul, ← Units.val_pow_eq_pow_val, hab, Units.val_one]
  obtain ⟨g, hdet, hcase⟩ := hF.classify _ _ ha' ha1' hb' hab'
  have hdetne : g.det ≠ 0 := by
    rw [hdet]
    exact one_ne_zero
  have hunit : IsUnit g.det := isUnit_iff_ne_zero.mpr hdetne
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero g hdetne, ?_⟩
  have hcoe : ((Matrix.GeneralLinearGroup.mkOfDetNeZero g hdetne : GL (Fin 4) (ZMod 2)) : Mat4) = g :=
    rfl
  rw [hcoe]
  rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨h1, h2⟩
  · exfalso
    obtain ⟨v0, hv0, hfix⟩ := hF.fixO bO hF.gens.2.2.2 bO_ne_one bO_cube
    have hb_eq : (b : Mat4) * g⁻¹ = g⁻¹ * bO := by
      calc (b : Mat4) * g⁻¹ = (g⁻¹ * g) * (b : Mat4) * g⁻¹ := by
            rw [Matrix.nonsing_inv_mul _ hunit, one_mul]
        _ = g⁻¹ * (g * (b : Mat4)) * g⁻¹ := by simp only [mul_assoc]
        _ = g⁻¹ * (bO * g) * g⁻¹ := by rw [h2]
        _ = g⁻¹ * bO := by
            simp only [mul_assoc]
            rw [Matrix.mul_nonsing_inv _ hunit, mul_one]
    have hw : (b : Mat4) *ᵥ (g⁻¹ *ᵥ v0) = g⁻¹ *ᵥ v0 := by
      rw [Matrix.mulVec_mulVec, hb_eq, ← Matrix.mulVec_mulVec, hfix]
    have hw0 := hff _ hw
    apply hv0
    have := congrArg (fun x => g *ᵥ x) hw0
    simpa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit] using this

section Natural

variable {F : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F] [Module.Finite (ZMod 2) F]

theorem natMat_fixFree (κ : (Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 2 → F))
    (g : Matrix.SpecialLinearGroup (Fin 2) F) (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1)
    (x : Fin 4 → ZMod 2) (hx : natMat F κ g *ᵥ x = x) : x = 0 := by
  rw [natMat_mulVec] at hx
  have h1 : natLin F g (κ x) = κ x := by
    have := congrArg κ hx
    simpa using this
  have h2 : (g : Matrix (Fin 2) (Fin 2) F) *ᵥ κ x = κ x := by
    rw [← natLin_apply]
    exact h1
  have h3 : (g : Matrix (Fin 2) (Fin 2) F) ^ 3 = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, hg3]
    rfl
  have h1' : (g : Matrix (Fin 2) (Fin 2) F) ≠ 1 := fun h => hg1 (Subtype.ext h)
  have hk : κ x = 0 := fixed_eq_zero (g : Matrix (Fin 2) (Fin 2) F) g.2 h3 h1' (κ x) h2
  simpa using hk

theorem eq_one_of_natMat_eq_one (κ : (Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 2 → F))
    {g : Matrix.SpecialLinearGroup (Fin 2) F} (h : natMat F κ g = 1) : g = 1 := by
  apply eq_one_of_natLin_eq_one F
  apply LinearMap.ext
  intro v
  have hx := natMat_mulVec F κ g (κ.symm v)
  rw [h, Matrix.one_mulVec] at hx
  have := congrArg κ hx
  simp only [LinearEquiv.apply_symm_apply] at this
  simpa using this.symm

end Natural

end CFSG.GH74.QTGen4.DSGen4.Lin2B
