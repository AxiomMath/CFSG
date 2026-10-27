module

public import CFSG.ClassicalInvolution.Solomon73
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixLagrangianSylow
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixCoverModel
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
import Certificates.Data.Kernel.F4M3B
import CFSG.Certificates.Kernel.F4M3BSound
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisGL3
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.Open.ClassicalInvolutionTheoremMilestoneDefs

public section

namespace CFSG.ClassicalInvolution.Solomon73

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

section GL32

local notation "Mat3" => Matrix (Fin 3) (Fin 3) (ZMod 2)

private abbrev t0 : Mat3 := !![1, 1, 0; 0, 1, 0; 0, 0, 1]

private theorem orders9 : ∀ a b c d e f g h i : ZMod 2,
    (!![a, b, c; d, e, f; g, h, i] : Mat3).det = 1 →
    (!![a, b, c; d, e, f; g, h, i] : Mat3) ^ 4 = 1 ∨ (!![a, b, c; d, e, f; g, h, i] : Mat3) ^ 3 = 1 ∨
      (!![a, b, c; d, e, f; g, h, i] : Mat3) ^ 7 = 1 := by decide

private theorem mat_orders (M : Mat3) (h : M.det = 1) : M ^ 4 = 1 ∨ M ^ 3 = 1 ∨ M ^ 7 = 1 := by
  have := orders9 (M 0 0) (M 0 1) (M 0 2) (M 1 0) (M 1 1) (M 1 2) (M 2 0) (M 2 1) (M 2 2)
  rw [← Matrix.eta_fin_three M] at this
  exact this h

private theorem mat_conj_invol : ∀ B : Mat3, B.det = 1 → B * B = 1 → B ≠ 1 →
    ∃ K : Mat3, K.det = 1 ∧ K * t0 = B * K := by
  decide +kernel

private theorem mat_cycle : ∀ B : Mat3, B.det = 1 → B * t0 = t0 * B → B * B = 1 → B ≠ 1 →
    B ≠ t0 → ∃ K : Mat3, K.det = 1 ∧ K ^ 3 = 1 ∧ K * t0 = B * K ∧ K * B = (t0 * B) * K := by
  decide +kernel

private theorem det_GL32 (g : GL (Fin 3) (ZMod 2)) : (g : Mat3).det = 1 := by
  have h1 : Matrix.GeneralLinearGroup.det g = 1 := Subsingleton.elim _ _
  have h2 := congrArg (fun u : (ZMod 2)ˣ => (u : ZMod 2)) h1
  simpa using h2

private noncomputable def matUnit (M : Mat3) (h : M.det = 1) : GL (Fin 3) (ZMod 2) :=
  ((Matrix.isUnit_iff_isUnit_det M).mpr (by rw [h]; exact isUnit_one)).unit

private theorem matUnit_val (M : Mat3) (h : M.det = 1) :
    ((matUnit M h : GL (Fin 3) (ZMod 2)) : Mat3) = M := rfl

theorem orders_GL32 (g : GL (Fin 3) (ZMod 2)) : g ^ 4 = 1 ∨ g ^ 3 = 1 ∨ g ^ 7 = 1 := by
  rcases mat_orders (g : Mat3) (det_GL32 g) with h | h | h
  · exact Or.inl (Units.ext (by rw [Units.val_pow_eq_pow_val, h]; rfl))
  · exact Or.inr (Or.inl (Units.ext (by rw [Units.val_pow_eq_pow_val, h]; rfl)))
  · exact Or.inr (Or.inr (Units.ext (by rw [Units.val_pow_eq_pow_val, h]; rfl)))

theorem exists_cycle_GL32 {a b : GL (Fin 3) (ZMod 2)} (ha : a * a = 1) (hb : b * b = 1)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) (hc : a * b = b * a) :
    ∃ k : GL (Fin 3) (ZMod 2), k ^ 3 = 1 ∧ k * a * k⁻¹ = b ∧ k * b * k⁻¹ = a * b := by
  have hsq : (a : Mat3) * a = 1 := by simpa using congrArg (fun x : GL (Fin 3) (ZMod 2) => (x : Mat3)) ha
  have hne : (a : Mat3) ≠ 1 := fun h => ha1 (Units.ext (by simpa using h))
  obtain ⟨K, hK, hKa⟩ := mat_conj_invol (a : Mat3) (det_GL32 a) hsq hne
  set c : GL (Fin 3) (ZMod 2) := matUnit K hK
  have hc' : c * matUnit t0 (by decide) = a * c := Units.ext (by
    rw [Units.val_mul, Units.val_mul, matUnit_val, matUnit_val]; exact hKa)
  set t : GL (Fin 3) (ZMod 2) := matUnit t0 (by decide)
  have hat : a = c * t * c⁻¹ := by rw [hc']; group
  set b' := c⁻¹ * b * c with hb'
  have hb'sq : b' * b' = 1 := by
    calc b' * b' = c⁻¹ * (b * b) * c := by rw [hb']; group
      _ = 1 := by rw [hb]; group
  have hb'c : b' * t = t * b' := by
    have h1 : t = c⁻¹ * a * c := by rw [hat]; group
    rw [h1, hb']
    calc c⁻¹ * b * c * (c⁻¹ * a * c) = c⁻¹ * (b * a) * c := by group
      _ = c⁻¹ * (a * b) * c := by rw [hc]
      _ = c⁻¹ * a * c * (c⁻¹ * b * c) := by group
  have hb'1 : b' ≠ 1 := by
    intro h
    apply hb1
    have : b = c * b' * c⁻¹ := by rw [hb']; group
    rw [this, h]; group
  have hb't : b' ≠ t := by
    intro h
    apply hab
    have h1 : b = c * b' * c⁻¹ := by rw [hb']; group
    rw [hat, h1, h]
  have mb'sq : (b' : Mat3) * b' = 1 := by
    simpa using congrArg (fun x : GL (Fin 3) (ZMod 2) => (x : Mat3)) hb'sq
  have mb'c : (b' : Mat3) * t0 = t0 * b' := by
    simpa [t, matUnit_val] using congrArg (fun x : GL (Fin 3) (ZMod 2) => (x : Mat3)) hb'c
  have mb'1 : (b' : Mat3) ≠ 1 := fun h => hb'1 (Units.ext (by simpa using h))
  have mb't : (b' : Mat3) ≠ t0 := fun h => hb't (Units.ext (by simpa [t, matUnit_val] using h))
  obtain ⟨K', hK', hK'3, hK't, hK'b⟩ := mat_cycle (b' : Mat3) (det_GL32 b') mb'c mb'sq mb'1 mb't
  set k' : GL (Fin 3) (ZMod 2) := matUnit K' hK'
  have hk'3 : k' ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, matUnit_val, hK'3]; rfl)
  have hk't : k' * t = b' * k' := Units.ext (by
    rw [Units.val_mul, Units.val_mul, matUnit_val, matUnit_val]; exact hK't)
  have hk'b : k' * b' = (t * b') * k' := Units.ext (by
    rw [Units.val_mul, Units.val_mul, Units.val_mul, matUnit_val, matUnit_val]; exact hK'b)
  refine ⟨c * k' * c⁻¹, ?_, ?_, ?_⟩
  · rw [conj_pow, hk'3, mul_one, mul_inv_cancel]
  · calc c * k' * c⁻¹ * a * (c * k' * c⁻¹)⁻¹ = c * (k' * t) * k'⁻¹ * c⁻¹ := by rw [hat]; group
      _ = c * (b' * k') * k'⁻¹ * c⁻¹ := by rw [hk't]
      _ = b := by rw [hb']; group
  · calc c * k' * c⁻¹ * b * (c * k' * c⁻¹)⁻¹ = c * (k' * b') * k'⁻¹ * c⁻¹ := by rw [hb']; group
      _ = c * (t * b' * k') * k'⁻¹ * c⁻¹ := by rw [hk'b]
      _ = a * b := by rw [hat, hb']; group

theorem orders_of_mulEquiv {R : Type*} [Group R] (ψ : R ≃* GL (Fin 3) (ZMod 2)) (g : R) :
    g ^ 4 = 1 ∨ g ^ 3 = 1 ∨ g ^ 7 = 1 := by
  rcases orders_GL32 (ψ g) with h | h | h
  · exact Or.inl (ψ.injective (by rw [map_pow, h, map_one]))
  · exact Or.inr (Or.inl (ψ.injective (by rw [map_pow, h, map_one])))
  · exact Or.inr (Or.inr (ψ.injective (by rw [map_pow, h, map_one])))

theorem exists_cycle_of_mulEquiv {R : Type*} [Group R] (ψ : R ≃* GL (Fin 3) (ZMod 2)) {a b : R}
    (ha : a * a = 1) (hb : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b)
    (hc : a * b = b * a) : ∃ k : R, k ^ 3 = 1 ∧ k * a * k⁻¹ = b ∧ k * b * k⁻¹ = a * b := by
  obtain ⟨k, hk3, hka, hkb⟩ := exists_cycle_GL32 (a := ψ a) (b := ψ b)
    (by rw [← map_mul, ha, map_one]) (by rw [← map_mul, hb, map_one])
    (fun h => ha1 (ψ.injective (by rw [h, map_one]))) (fun h => hb1 (ψ.injective (by rw [h, map_one])))
    (fun h => hab (ψ.injective h)) (by rw [← map_mul, ← map_mul, hc])
  refine ⟨ψ.symm k, ψ.injective ?_, ψ.injective ?_, ψ.injective ?_⟩
  · rw [map_pow, MulEquiv.apply_symm_apply, hk3, map_one]
  · rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hka]
  · rw [map_mul, map_mul, map_inv, map_mul, MulEquiv.apply_symm_apply, hkb]

end GL32

end CFSG.ClassicalInvolution.Solomon73
