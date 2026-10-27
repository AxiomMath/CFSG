module

public import CFSG.GH74.Generic.BProg.B2.GenLocL3ThreeMat
public import CFSG.GH74.Generic.BProg.B2.GenLocL3NineBase

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 Subgroup CFSG.LocalAnalysis.ComponentInitial GenLocL3Pair GenLocL3Good Matrix
open scoped MatrixGroups

namespace GenLocL3Three

abbrev P3 : Type := LinearFlag.projectiveSL 3 K3

@[expose] noncomputable def cU (u : Fin 3 → K3ˣ) : MulAut P3 := LinearFlag.conjAut 3 K3 (diag3 u)

@[expose] noncomputable def cT (k : Fin 3) : MulAut P3 := cU (tauU k)

@[expose] noncomputable def dl : MulAut P3 := LinearFlag.dualAut 3 K3

theorem D_cases (D : Subgroup (MulAut P3)) (hfs : D ≤ frameStab 3 K3) (y : D) :
    (∃ u : Fin 3 → K3ˣ, (y : MulAut P3) = cU u) ∨ (∃ u : Fin 3 → K3ˣ, (y : MulAut P3) = cU u * dl) := by
  obtain ⟨u, σ, ε, hε, h⟩ := GenLocL3Nine.exists_data (hfs y.2)
  rw [sigma_eq_one σ, map_one, mul_one] at h
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with rfl | rfl
  · left; exact ⟨u, by rw [h, pow_zero, mul_one]; rfl⟩
  · right; exact ⟨u, by rw [h, pow_one]; rfl⟩

theorem diag3_const_one : diag3 (fun _ : Fin 3 => (1 : K3ˣ)) = (1 : GL (Fin 3) K3) := by
  apply Units.ext
  rw [coe_diag3]
  simp

theorem cU_cases (u : Fin 3 → K3ˣ) : cU u = 1 ∨ ∃ k, cU u = cT k := by
  have key : ∀ u : Fin 3 → K3ˣ, (∃ l : K3ˣ, u = fun i => l * 1) ∨
      ∃ (l : K3ˣ) (k : Fin 3), u = fun i => l * tauU k i := by decide
  rcases key u with ⟨l, rfl⟩ | ⟨l, k, rfl⟩
  · left
    have h := GenLocL3Nine.conjAut_diag3_smul l (fun _ : Fin 3 => (1 : K3ˣ))
    unfold cU
    rw [h, diag3_const_one, map_one]
  · right
    exact ⟨k, GenLocL3Nine.conjAut_diag3_smul l (tauU k)⟩

theorem outer_mul_outer (u v : Fin 3 → K3ˣ) :
    (cU u * dl) * (cU v * dl) = cU (fun i => u i * (v i)⁻¹) := by
  have hδδ : LinearFlag.dualAut 3 K3 * LinearFlag.dualAut 3 K3 = 1 :=
    (LinearFlag.standard_automorphism_transport (K := K3) (n := 3)).2.2.2.1
  have s2 := LinearFlag.dualAut_mul_conjAut (n := 3) (K := K3) (diag3 v)
  have hit : GeneralLinearGroup.inverseTranspose (diag3 v) = diag3 (fun i => (v i)⁻¹) := by
    apply Units.ext
    rw [GeneralLinearGroup.coe_inverseTranspose, coe_diag3_inv, Matrix.diagonal_transpose, coe_diag3]
  have hmul : diag3 u * diag3 (fun i => (v i)⁻¹) = diag3 (fun i => u i * (v i)⁻¹) := by
    apply Units.ext
    rw [Units.val_mul, coe_diag3, coe_diag3, coe_diag3, Matrix.diagonal_mul_diagonal]
    rfl
  unfold cU dl
  calc (LinearFlag.conjAut 3 K3 (diag3 u) * LinearFlag.dualAut 3 K3) *
        (LinearFlag.conjAut 3 K3 (diag3 v) * LinearFlag.dualAut 3 K3)
      = LinearFlag.conjAut 3 K3 (diag3 u) * (LinearFlag.dualAut 3 K3 *
          LinearFlag.conjAut 3 K3 (diag3 v)) * LinearFlag.dualAut 3 K3 := by simp only [mul_assoc]
    _ = LinearFlag.conjAut 3 K3 (diag3 u) * (LinearFlag.conjAut 3 K3 (diag3 (fun i => (v i)⁻¹)) *
          LinearFlag.dualAut 3 K3) * LinearFlag.dualAut 3 K3 := by rw [s2, hit]
    _ = LinearFlag.conjAut 3 K3 (diag3 u) * LinearFlag.conjAut 3 K3 (diag3 (fun i => (v i)⁻¹)) *
          (LinearFlag.dualAut 3 K3 * LinearFlag.dualAut 3 K3) := by simp only [mul_assoc]
    _ = _ := by rw [hδδ, mul_one, ← map_mul, hmul]

theorem pair_shape (D : Subgroup (MulAut P3)) (hfs : D ≤ frameStab 3 K3)
    (hD : CFSG.IsElementaryAbelian 2 ↥D) (s t : D) (hs : s ≠ 1) (ht : t ≠ 1) (hst : s ≠ t) :
    ∃ a b : D, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧
      (∀ x : P3, (s : MulAut P3) x = x → (t : MulAut P3) x = x →
        (a : MulAut P3) x = x ∧ (b : MulAut P3) x = x) ∧
      ((∃ k m : Fin 3, k ≠ m ∧ (a : MulAut P3) = cT k ∧ (b : MulAut P3) = cT m) ∨
        ∃ (k : Fin 3) (u : Fin 3 → K3ˣ), (a : MulAut P3) = cT k ∧ (b : MulAut P3) = cU u * dl) := by
  have hne : ∀ y : D, y ≠ 1 → (y : MulAut P3) ≠ 1 := fun y hy h => hy (Subtype.ext h)
  rcases D_cases D hfs s with ⟨u, hu⟩ | ⟨u, hu⟩ <;> rcases D_cases D hfs t with ⟨u', hu'⟩ | ⟨u', hu'⟩
  ·
    rcases cU_cases u with h1 | ⟨k, hk⟩
    · exact absurd (hu.trans h1) (hne s hs)
    rcases cU_cases u' with h2 | ⟨m, hm⟩
    · exact absurd (hu'.trans h2) (hne t ht)
    refine ⟨s, t, hs, ht, hst, fun x h1 h2 => ⟨h1, h2⟩, Or.inl ⟨k, m, ?_, hu.trans hk, hu'.trans hm⟩⟩
    rintro rfl
    exact hst (Subtype.ext (hu.trans (hk.trans (hu'.trans hm).symm)))
  ·
    rcases cU_cases u with h1 | ⟨k, hk⟩
    · exact absurd (hu.trans h1) (hne s hs)
    exact ⟨s, t, hs, ht, hst, fun x h1 h2 => ⟨h1, h2⟩, Or.inr ⟨k, u', hu.trans hk, hu'⟩⟩
  ·
    rcases cU_cases u' with h1 | ⟨k, hk⟩
    · exact absurd (hu'.trans h1) (hne t ht)
    exact ⟨t, s, ht, hs, hst.symm, fun x h1 h2 => ⟨h2, h1⟩, Or.inr ⟨k, u, hu'.trans hk, hu⟩⟩
  ·
    have htt : t * t = 1 := WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hD t
    have hst1 : s * t ≠ 1 := by
      intro h
      apply hst
      calc s = s * (t * t) := by rw [htt, mul_one]
        _ = (s * t) * t := by rw [mul_assoc]
        _ = t := by rw [h, one_mul]
    have hprod : ((s * t : D) : MulAut P3) = cU (fun i => u i * (u' i)⁻¹) := by
      rw [Subgroup.coe_mul, hu, hu', outer_mul_outer]
    rcases cU_cases (fun i => u i * (u' i)⁻¹) with h1 | ⟨k, hk⟩
    · exact absurd (hprod.trans h1) (hne _ hst1)
    refine ⟨s * t, s, hst1, hs, ?_, ?_, Or.inr ⟨k, u, hprod.trans hk, hu⟩⟩
    · intro h
      apply ht
      calc t = s⁻¹ * (s * t) := by rw [inv_mul_cancel_left]
        _ = s⁻¹ * s := by rw [h]
        _ = 1 := inv_mul_cancel s
    · intro x h1 h2
      refine ⟨?_, h1⟩
      rw [Subgroup.coe_mul, MulAut.mul_apply, h2, h1]

end GenLocL3Three

end CFSG.GH74.Generic.BProg.B2
