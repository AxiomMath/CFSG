module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGOmA2Frame
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421SpSL

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open QuadraticMap (polar polarBilin)
open LinearMap (BilinForm)
open CFSG.ClassicalGroups.Orthogonal (polar_map_of_mem)
open CFSG.ClassicalInvolution.Models.OrthogonalPairs (Frame)
open CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame (coe_transvection_one_zero
  coe_transvection_zero_one)
open scoped MatrixGroups

private theorem oma2_coords_eq_zero {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    {Q : QuadraticForm F V} (Fr : Frame Q) {x : V} (h : ∀ Y, polar Q x (Fr.incl Y) = 0) :
    Fr.coords x = 0 := by
  have h' := fun Y => (Fr.polar_incl_right x Y).symm.trans (h Y)
  ext i j
  fin_cases i <;> fin_cases j
  · simpa using h' !![0, 0; 0, 1]
  · simpa using h' !![0, 0; 1, 0]
  · simpa using h' !![0, 1; 0, 0]
  · simpa using h' !![1, 0; 0, 0]

theorem SG.exists_sl2_commuting (F V : Type) [Field F] [Finite F] [CharP F 2] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (hF : 4 ≤ Nat.card F) (Q : QuadraticForm F V)
    (U : Submodule F V) (hU : 4 ≤ Module.finrank F U)
    (hUnd : (BilinForm.restrict (polarBilin Q) U).Nondegenerate)
    (t : V ≃ₗ[F] V) (ht : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (ht3 : t ^ 3 = 1)
    (htU : ∀ u ∈ U, t u ∈ U) (htfix : ∀ u ∈ U, t u = u → u = 0) :
    ∃ A : Subgroup (V ≃ₗ[F] V), A ≤ CFSG.RankThree.Classical2.orthDerived Q ∧
      IsSimpleGroup A ∧ (∃ a b : A, a * b ≠ b * a) ∧ 3 ∣ Nat.card A ∧
      ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, ∀ k : ℕ, (∀ u ∈ U, g u = (t ^ k) u) →
        ∀ a ∈ A, a * g = g * a := by
  obtain ⟨Fr, hFrU, hFrt⟩ := SG.exists_frame_incl_mul hU hUnd ht ht3 htU htfix
  obtain ⟨M, hFrt⟩ : ∃ M : Matrix (Fin 2) (Fin 2) F, ∀ X, t (Fr.incl X) = Fr.incl (X * M) :=
    ⟨_, hFrt⟩
  have hpow : ∀ j : ℕ, ∀ X, (t ^ j) (Fr.incl X) = Fr.incl (X * M ^ j) := by
    intro j
    induction j with
    | zero => intro X; simp
    | succ j ih =>
      intro X
      rw [pow_succ', LinearEquiv.mul_apply, ih, hFrt, pow_succ, Matrix.mul_assoc]
  have hcomm : ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, ∀ k : ℕ,
      (∀ u ∈ U, g u = (t ^ k) u) → ∀ a ∈ Fr.La.range, a * g = g * a := by
    rintro g hg k hgk _ ⟨B, rfl⟩
    have hg1 : ∀ X, g (Fr.incl X) = Fr.incl (X * M ^ k) := fun X => by
      rw [hgk _ (hFrU X), hpow]
    have hg2 : ∀ Y, g (Fr.incl (Y * M ^ (2 * k))) = Fr.incl Y := fun Y => by
      rw [hg1, Matrix.mul_assoc, ← pow_add, ← hpow, show 2 * k + k = 3 * k by ring, pow_mul, ht3]
      simp
    have hperp : ∀ r, Fr.coords r = 0 → Fr.coords (g r) = 0 := fun r hr =>
      oma2_coords_eq_zero Fr fun Y => by
        rw [← hg2 Y, polar_map_of_mem hg, Fr.polar_incl_right, hr]
        simp
    refine LinearEquiv.ext fun x => ?_
    obtain ⟨X, r, hr, rfl⟩ : ∃ X r, Fr.coords r = 0 ∧ x = Fr.incl X + r :=
      ⟨Fr.coords x, x - Fr.incl (Fr.coords x), by rw [map_sub, Fr.coords_incl, sub_self],
        (add_sub_cancel _ x).symm⟩
    simp only [LinearEquiv.mul_apply, map_add, hg1, Fr.La_apply_incl,
      Fr.La_apply_of_coords_eq_zero B hr, Fr.La_apply_of_coords_eq_zero B (hperp r hr),
      Matrix.mul_assoc]
  have := CFSG.LocalAnalysis.RankThreeUC.S15.K421SpSLProof.isSimpleGroup_sl2_charTwo hF
  obtain ⟨e⟩ : Nonempty (SL(2, F) ≃* Fr.La.range) := ⟨MonoidHom.ofInjective Fr.La_injective⟩
  have hsA : IsSimpleGroup Fr.La.range := e.symm.isSimpleGroup
  have hnc : ∃ a b : Fr.La.range, a * b ≠ b * a := by
    refine ⟨e (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) 1),
      e (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) 1), fun h => ?_⟩
    rw [← map_mul, ← map_mul] at h
    have h' := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) (e.injective h)
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_transvection_zero_one,
      coe_transvection_one_zero, Matrix.mul_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
      mul_one, mul_zero, add_zero] at h'
    rw [CharTwo.add_self_eq_zero] at h'
    exact zero_ne_one h'
  have hcard : Nat.card Fr.La.range = Nat.card F * (Nat.card F ^ 2 - 1) := by
    rw [← Nat.card_congr e.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
  have h3 : 3 ∣ Nat.card F * (Nat.card F ^ 2 - 1) := by
    obtain ⟨m, hm | hm | hm⟩ : ∃ m, Nat.card F = 3 * m ∨ Nat.card F = 3 * m + 1 ∨
        Nat.card F = 3 * m + 2 := ⟨Nat.card F / 3, by omega⟩
    · rw [hm]
      exact Dvd.dvd.mul_right (dvd_mul_right 3 m) _
    · rw [hm]
      exact Dvd.dvd.mul_left ⟨3 * m ^ 2 + 2 * m, Nat.sub_eq_of_eq_add (by ring)⟩ _
    · rw [hm]
      exact Dvd.dvd.mul_left ⟨3 * m ^ 2 + 4 * m + 1, Nat.sub_eq_of_eq_add (by ring)⟩ _
  have hAO : Fr.La.range ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rintro _ ⟨B, rfl⟩
    exact Fr.La_mem_orthogonalGroup B
  have : Group.IsPerfect Fr.La.range :=
    TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative fun h => by
      obtain ⟨a, b, hab⟩ := hnc
      exact hab (h.is_comm.comm a b)
  have hΩ : Fr.La.range ≤ CFSG.RankThree.Classical2.orthDerived Q :=
    Subgroup.commutator_eq_self.symm.le.trans (Subgroup.commutator_mono hAO hAO)
  exact ⟨Fr.La.range, hΩ, hsA, hnc, by rw [hcard]; exact h3, hcomm⟩

end CFSG.LocalAnalysis.GLTheoremA.S265

end
