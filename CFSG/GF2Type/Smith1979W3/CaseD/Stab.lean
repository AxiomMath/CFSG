module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

namespace CFSG.GF2Type.Smith1979W3.CaseD

open Module QuadraticMap

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem orthogonal_eq_of_totallySingular (q : QuadraticForm (ZMod 2) V)
    (hq : (polarBilin q).Nondegenerate) {W : Submodule (ZMod 2) V}
    (hW : ∀ w ∈ W, q w = 0) (hV : finrank (ZMod 2) V = 2 * finrank (ZMod 2) W) :
    LinearMap.BilinForm.orthogonal (polarBilin q) W = W := by
  have hle : W ≤ LinearMap.BilinForm.orthogonal (polarBilin q) W := by
    intro w hw
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro w' hw'
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
      hW (w' + w) (W.add_mem hw' hw), hW w' hw', hW w hw]
    simp
  have hfin : finrank (ZMod 2) W
      = finrank (ZMod 2) (LinearMap.BilinForm.orthogonal (polarBilin q) W) := by
    rw [LinearMap.BilinForm.finrank_orthogonal hq W, hV]
    omega
  exact (Submodule.eq_of_le_of_finrank_eq hle hfin).symm

theorem mul_self_eq_one_of_fix (q : QuadraticForm (ZMod 2) V)
    (hq : (polarBilin q).Nondegenerate) {W : Submodule (ZMod 2) V}
    (hW : ∀ w ∈ W, q w = 0) (hV : finrank (ZMod 2) V = 2 * finrank (ZMod 2) W)
    (p : V ≃ₗ[ZMod 2] V) (hpq : ∀ v, q (p v) = q v) (hpW : ∀ w ∈ W, p w = w) : p * p = 1 := by
  have hpolar : ∀ x y, polarBilin q (p x) (p y) = polarBilin q x y := by
    intro x y
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply,
      QuadraticMap.polar, QuadraticMap.polar]
    rw [← map_add p x y, hpq (x + y), hpq x, hpq y]
  apply LinearEquiv.ext
  intro v
  show p (p v) = v
  have horth := orthogonal_eq_of_totallySingular q hq hW hV
  have hmem : p v - v ∈ LinearMap.BilinForm.orthogonal (polarBilin q) W := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    have h1 : polarBilin q w (p v) = polarBilin q (p w) (p v) := by rw [hpW w hw]
    rw [map_sub, h1, hpolar w v, sub_self]
  have hmemW : p v - v ∈ W := by
    rwa [horth] at hmem
  have hfix := hpW (p v - v) hmemW
  have hsub : p (p v) - p v = p v - v := by
    rwa [map_sub] at hfix
  have hpv2 : p v + p v = 0 := by
    have h : (2 : ZMod 2) • p v = 0 := by
      rw [show (2 : ZMod 2) = 0 by decide, zero_smul]
    simpa [two_smul] using h
  have hvneg : -v = v := by
    rw [← neg_one_smul (ZMod 2) v, show (-1 : ZMod 2) = 1 by decide, one_smul]
  calc
    p (p v) = (p v - v) + p v := sub_eq_iff_eq_add.mp hsub
    _ = (p v + p v) - v := by abel
    _ = 0 - v := by rw [hpv2]
    _ = -v := by rw [zero_sub]
    _ = v := hvneg

theorem card_linearEquiv_of_finrank_three {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (hW : finrank (ZMod 2) W = 3) : Nat.card (W ≃ₗ[ZMod 2] W) = 168 := by
  haveI : Module.Finite (ZMod 2) W := Module.finite_of_finrank_pos (by rw [hW]; norm_num)
  let b : Module.Basis (Fin 3) (ZMod 2) W := Module.finBasisOfFinrankEq (ZMod 2) W hW
  calc
    Nat.card (W ≃ₗ[ZMod 2] W)
        = Nat.card (LinearMap.GeneralLinearGroup (ZMod 2) W) :=
          (Nat.card_congr (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W).toEquiv).symm
    _ = Nat.card (GL (Fin 3) (ZMod 2)) :=
          (Nat.card_congr (Matrix.GeneralLinearGroup.toLin' b).toEquiv).symm
    _ = 168 := by
          rw [Matrix.card_GL_field, Fin.prod_univ_three, ZMod.card]
          norm_num

theorem card_ne_nine_of_stab (q : QuadraticForm (ZMod 2) V)
    (hq : (polarBilin q).Nondegenerate) (hV : finrank (ZMod 2) V = 6)
    (W : Submodule (ZMod 2) V) (hW : ∀ w ∈ W, q w = 0) (hW3 : finrank (ZMod 2) W = 3)
    (P : Subgroup (V ≃ₗ[ZMod 2] V)) (hPq : ∀ p ∈ P, ∀ v, q (p v) = q v)
    (hPW : ∀ p ∈ P, W.map (p : V →ₗ[ZMod 2] V) = W) : Nat.card P ≠ 9 := by
  intro hP9
  have hV' : finrank (ZMod 2) V = 2 * finrank (ZMod 2) W := by
    rw [hV, hW3]
  let φ : P →* (W ≃ₗ[ZMod 2] W) :=
    { toFun := fun p => (p : V ≃ₗ[ZMod 2] V).ofSubmodules W W (hPW (p : V ≃ₗ[ZMod 2] V) p.2)
      map_one' := by
        ext x
        simp
      map_mul' := by
        intro p r
        ext x
        simp [LinearEquiv.ofSubmodules_apply, Subgroup.coe_mul] }
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rw [Subgroup.eq_bot_iff_forall]
    intro p hp
    have hφp : φ p = 1 := MonoidHom.mem_ker.mp hp
    have hfix : ∀ w ∈ W, (p : V ≃ₗ[ZMod 2] V) w = w := by
      intro w hw
      have h1 : ((p : V ≃ₗ[ZMod 2] V).ofSubmodules W W
            (hPW (p : V ≃ₗ[ZMod 2] V) p.2)) ⟨w, hw⟩
          = (1 : W ≃ₗ[ZMod 2] W) ⟨w, hw⟩ := by
        change (φ p) ⟨w, hw⟩ = (1 : W ≃ₗ[ZMod 2] W) ⟨w, hw⟩
        rw [hφp]
      have h2 : ↑(((p : V ≃ₗ[ZMod 2] V).ofSubmodules W W
            (hPW (p : V ≃ₗ[ZMod 2] V) p.2)) ⟨w, hw⟩) = w := by
        rw [h1]; rfl
      rw [LinearEquiv.ofSubmodules_apply] at h2
      simpa using h2
    have hppV : (p : V ≃ₗ[ZMod 2] V) * (p : V ≃ₗ[ZMod 2] V) = 1 :=
      mul_self_eq_one_of_fix q hq hW hV' (p : V ≃ₗ[ZMod 2] V)
        (hPq (p : V ≃ₗ[ZMod 2] V) p.2) hfix
    have hpp : p * p = 1 := by
      apply Subtype.ext
      simpa using hppV
    have h2 : orderOf p ∣ 2 := orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hpp)
    have h9 : orderOf p ∣ 9 := by
      have := orderOf_dvd_natCard p
      rwa [hP9] at this
    have h1 : orderOf p = 1 := by
      have hg : orderOf p ∣ Nat.gcd 2 9 := Nat.dvd_gcd h2 h9
      rw [show Nat.gcd 2 9 = 1 by norm_num] at hg
      exact Nat.dvd_one.mp hg
    exact orderOf_eq_one_iff.mp h1
  have hdvd : Nat.card P ∣ Nat.card (W ≃ₗ[ZMod 2] W) :=
    Subgroup.card_dvd_of_injective φ hinj
  rw [card_linearEquiv_of_finrank_three hW3, hP9] at hdvd
  norm_num at hdvd

end CFSG.GF2Type.Smith1979W3.CaseD
