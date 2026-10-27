module

public import CFSG.ClassicalInvolution.Generic.SL2Anticommute

public section

namespace CFSG.ClassicalInvolution.Generic

open scoped MatrixGroups
open Matrix CFSG.ComponentClassification.CatalogueBHigherLinearAction

variable {F : Type*} [Field F]

@[expose] noncomputable def fixSub (A : GL (Fin 2) F) : Subgroup SL(2, F) :=
  MonoidHom.eqLocus (slConjugation 2 F A).toMonoidHom (MonoidHom.id _)

theorem mem_fixSub_iff {A : GL (Fin 2) F} {s : SL(2, F)} :
    s ∈ fixSub A ↔ slConjugation 2 F A s = s := Iff.rfl

theorem mem_fixSub_iff_comm {A : GL (Fin 2) F} {s : SL(2, F)} :
    s ∈ fixSub A ↔ A.val * (s : Matrix (Fin 2) (Fin 2) F) = (s : Matrix (Fin 2) (Fin 2) F) * A.val :=
  slConj_eq_iff A s s

section Quad

variable {a b e c : F}

theorem gmat_sq (hc : a ^ 2 + b * e = c) :
    (!![a, b; e, -a] : Matrix (Fin 2) (Fin 2) F) * !![a, b; e, -a] =
      c • (1 : Matrix (Fin 2) (Fin 2) F) + (0 : F) • (!![a, b; e, -a] : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> grind

@[expose] noncomputable def theta (hc : a ^ 2 + b * e = c) :
    QuadraticAlgebra F c 0 →ₐ[F] Matrix (Fin 2) (Fin 2) F :=
  QuadraticAlgebra.lift ⟨!![a, b; e, -a], gmat_sq hc⟩

theorem theta_apply (hc : a ^ 2 + b * e = c) (z : QuadraticAlgebra F c 0) :
    theta hc z = z.re • (1 : Matrix (Fin 2) (Fin 2) F) + z.im • (!![a, b; e, -a] : Matrix (Fin 2) (Fin 2) F) := by
  simp [theta]

theorem det_theta (hc : a ^ 2 + b * e = c) (z : QuadraticAlgebra F c 0) :
    (theta hc z).det = QuadraticAlgebra.norm z := by
  rw [theta_apply, Matrix.det_fin_two]
  simp only [QuadraticAlgebra.norm_def]
  simp
  grind

theorem theta_injective (h2 : (2 : F) ≠ 0) (hnsc : ¬ (b = 0 ∧ e = 0 ∧ a = 0))
    (hc : a ^ 2 + b * e = c) : Function.Injective (theta hc) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  rw [theta_apply] at hz
  have e00 := congrFun (congrFun hz 0) 0
  have e01 := congrFun (congrFun hz 0) 1
  have e11 := congrFun (congrFun hz 1) 1
  have e10 := congrFun (congrFun hz 1) 0
  simp at e00 e01 e10 e11
  by_cases him : z.im = 0
  · have hre : z.re = 0 := by simpa [him] using e00
    exact QuadraticAlgebra.ext hre him
  · exfalso
    have hb : b = 0 := e01.resolve_left him
    have he : e = 0 := e10.resolve_left him
    have ha : a = 0 := by
      have : (2 * z.im) * a = 0 := by linear_combination e00 - e11
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (mul_ne_zero h2 him)
      · exact h
    exact hnsc ⟨hb, he, ha⟩

@[expose] def quadNormOne (c : F) : Subgroup (QuadraticAlgebra F c 0)ˣ :=
  (Units.map (QuadraticAlgebra.norm : QuadraticAlgebra F c 0 →* F)).ker

theorem mem_quadNormOne_iff {c : F} (u : (QuadraticAlgebra F c 0)ˣ) :
    u ∈ quadNormOne c ↔ QuadraticAlgebra.norm (u : QuadraticAlgebra F c 0) = 1 := by
  rw [quadNormOne, MonoidHom.mem_ker, Units.ext_iff]
  simp

@[expose] noncomputable def toSL (hc : a ^ 2 + b * e = c) : quadNormOne c →* SL(2, F) where
  toFun u := ⟨theta hc ((u : (QuadraticAlgebra F c 0)ˣ) : QuadraticAlgebra F c 0), by
    rw [det_theta]
    exact (mem_quadNormOne_iff _).mp u.2⟩
  map_one' := by
    apply sl_ext
    simp
  map_mul' u v := by
    apply sl_ext
    simp only [Subgroup.coe_mul, Units.val_mul, map_mul]
    rfl

theorem coe_toSL (hc : a ^ 2 + b * e = c) (u : quadNormOne c) :
    ((toSL hc u : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      theta hc ((u : (QuadraticAlgebra F c 0)ˣ) : QuadraticAlgebra F c 0) := rfl

theorem toSL_injective (h2 : (2 : F) ≠ 0) (hnsc : ¬ (b = 0 ∧ e = 0 ∧ a = 0))
    (hc : a ^ 2 + b * e = c) : Function.Injective (toSL hc) := by
  intro u v huv
  have h1 := congrArg (fun s : SL(2, F) => (s : Matrix (Fin 2) (Fin 2) F)) huv
  simp only [coe_toSL] at h1
  exact Subtype.ext (Units.ext (theta_injective h2 hnsc hc h1))

end Quad

namespace IsInvolDiag

variable {A : GL (Fin 2) F} {a b e c : F}

theorem not_all_zero (hA : IsInvolDiag A) (hAmat : A.val = !![a, b; e, -a]) :
    ¬ (b = 0 ∧ e = 0 ∧ a = 0) := by
  rintro ⟨hb, he, ha⟩
  apply hA.not_scalar 0
  rw [hAmat, hb, he, ha]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem range_toSL (hA : IsInvolDiag A) (h2 : (2 : F) ≠ 0) (hAmat : A.val = !![a, b; e, -a])
    (hc : a ^ 2 + b * e = c) : (toSL hc).range = fixSub A := by
  ext s
  constructor
  · rintro ⟨u, rfl⟩
    rw [mem_fixSub_iff_comm, coe_toSL, theta_apply, hAmat]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  · intro hs
    rw [mem_fixSub_iff_comm] at hs
    obtain ⟨x, y, hxy⟩ := hA.exists_comm_eq h2 _ hs
    rw [hAmat] at hxy
    have hdet : QuadraticAlgebra.norm (⟨x, y⟩ : QuadraticAlgebra F c 0) = 1 := by
      rw [← det_theta hc, theta_apply]
      simp only
      rw [← hxy]
      exact s.2
    have hunit : IsUnit (⟨x, y⟩ : QuadraticAlgebra F c 0) :=
      QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr (by rw [hdet]; exact isUnit_one)
    obtain ⟨u, hu⟩ := hunit
    refine ⟨⟨u, (mem_quadNormOne_iff u).mpr (by rw [hu]; exact hdet)⟩, ?_⟩
    apply sl_ext
    rw [coe_toSL, hxy, theta_apply]
    simp [hu]

@[expose] noncomputable def fixSubEquiv (hA : IsInvolDiag A) (h2 : (2 : F) ≠ 0)
    (hAmat : A.val = !![a, b; e, -a]) (hc : a ^ 2 + b * e = c) : quadNormOne c ≃* fixSub A :=
  (MonoidHom.ofInjective (toSL_injective h2 (hA.not_all_zero hAmat) hc)).trans
    (MulEquiv.subgroupCongr (hA.range_toSL h2 hAmat hc))

end IsInvolDiag

section Split

variable {c μ : F}

theorem norm_split (hcμ : c = μ * μ) (z : QuadraticAlgebra F c 0) :
    QuadraticAlgebra.norm z = (z.re + μ * z.im) * (z.re - μ * z.im) := by
  rw [QuadraticAlgebra.norm_def]
  linear_combination (-(z.im * z.im)) * hcμ

@[expose] noncomputable def splitMap (hcμ : c = μ * μ) : quadNormOne c →* Fˣ where
  toFun u := Units.mkOfMulEqOne (((u : (QuadraticAlgebra F c 0)ˣ) : QuadraticAlgebra F c 0).re +
      μ * ((u : (QuadraticAlgebra F c 0)ˣ) : QuadraticAlgebra F c 0).im)
    (((u : (QuadraticAlgebra F c 0)ˣ) : QuadraticAlgebra F c 0).re -
      μ * ((u : (QuadraticAlgebra F c 0)ˣ) : QuadraticAlgebra F c 0).im)
    (by rw [← norm_split hcμ]; exact (mem_quadNormOne_iff _).mp u.2)
  map_one' := by
    ext
    simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_mul' u v := by
    ext
    simp only [Subgroup.coe_mul, Units.val_mul, Units.val_mkOfMulEqOne]
    rw [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
    linear_combination
      (((u : (QuadraticAlgebra F c 0)ˣ) : QuadraticAlgebra F c 0).im *
        ((v : (QuadraticAlgebra F c 0)ˣ) : QuadraticAlgebra F c 0).im) * hcμ

theorem val_splitMap (hcμ : c = μ * μ) (u : quadNormOne c) :
    ((splitMap hcμ u : Fˣ) : F) = ((u : (QuadraticAlgebra F c 0)ˣ) : QuadraticAlgebra F c 0).re +
      μ * ((u : (QuadraticAlgebra F c 0)ˣ) : QuadraticAlgebra F c 0).im := rfl

theorem splitMap_injective (h2 : (2 : F) ≠ 0) (hμ : μ ≠ 0) (hcμ : c = μ * μ) :
    Function.Injective (splitMap hcμ) := by
  rw [injective_iff_map_eq_one]
  intro u hu
  have h1 : ((u : (QuadraticAlgebra F c 0)ˣ) : QuadraticAlgebra F c 0).re +
      μ * ((u : (QuadraticAlgebra F c 0)ˣ) : QuadraticAlgebra F c 0).im = 1 := by
    rw [← val_splitMap hcμ, hu]
    rfl
  have h3 := (mem_quadNormOne_iff _).mp u.2
  rw [norm_split hcμ, h1, one_mul] at h3
  have hre : ((u : (QuadraticAlgebra F c 0)ˣ) : QuadraticAlgebra F c 0).re = 1 := by
    have h4 : (2 : F) * ((u : (QuadraticAlgebra F c 0)ˣ) : QuadraticAlgebra F c 0).re = 2 * 1 := by
      linear_combination h1 + h3
    exact mul_left_cancel₀ h2 h4
  have him : ((u : (QuadraticAlgebra F c 0)ˣ) : QuadraticAlgebra F c 0).im = 0 := by
    have h5 : (2 * μ) * ((u : (QuadraticAlgebra F c 0)ˣ) : QuadraticAlgebra F c 0).im = 0 := by
      linear_combination h1 - h3
    exact (mul_eq_zero.mp h5).resolve_left (mul_ne_zero h2 hμ)
  apply Subtype.ext
  apply Units.ext
  exact QuadraticAlgebra.ext hre him

theorem splitMap_surjective (h2 : (2 : F) ≠ 0) (hμ : μ ≠ 0) (hcμ : c = μ * μ) :
    Function.Surjective (splitMap hcμ) := by
  intro t
  have ht : (t : F) ≠ 0 := t.ne_zero
  set z : QuadraticAlgebra F c 0 :=
    ⟨((t : F) + (t : F)⁻¹) / 2, ((t : F) - (t : F)⁻¹) / (2 * μ)⟩ with hz
  have hz1 : z.re + μ * z.im = t := by
    rw [hz]
    simp only
    field_simp
    ring
  have hz2 : z.re - μ * z.im = (t : F)⁻¹ := by
    rw [hz]
    simp only
    field_simp
    ring
  have hnorm : QuadraticAlgebra.norm z = 1 := by
    rw [norm_split hcμ, hz1, hz2]
    exact mul_inv_cancel₀ ht
  have hunit : IsUnit z :=
    QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr (by rw [hnorm]; exact isUnit_one)
  obtain ⟨u, hu⟩ := hunit
  refine ⟨⟨u, (mem_quadNormOne_iff u).mpr (by rw [hu]; exact hnorm)⟩, ?_⟩
  apply Units.ext
  rw [val_splitMap]
  simp only [← hu] at hz1
  exact hz1

@[expose] noncomputable def splitEquiv (h2 : (2 : F) ≠ 0) (hμ : μ ≠ 0) (hcμ : c = μ * μ) :
    quadNormOne c ≃* Fˣ :=
  MulEquiv.ofBijective (splitMap hcμ) ⟨splitMap_injective h2 hμ hcμ, splitMap_surjective h2 hμ hcμ⟩

theorem isCyclic_quadNormOne_of_split [Finite F] (h2 : (2 : F) ≠ 0) (hμ : μ ≠ 0) (hcμ : c = μ * μ) :
    IsCyclic (quadNormOne c) :=
  (splitEquiv h2 hμ hcμ).isCyclic.mpr inferInstance

theorem card_quadNormOne_of_split [Finite F] (h2 : (2 : F) ≠ 0) (hμ : μ ≠ 0) (hcμ : c = μ * μ) :
    Nat.card (quadNormOne c) = Nat.card F - 1 := by
  rw [Nat.card_congr (splitEquiv h2 hμ hcμ).toEquiv, Nat.card_units]

end Split

section NonSplit

variable {c : F} [Finite F]

omit [Finite F] in
theorem card_quadraticAlgebra (c : F) :
    Nat.card (QuadraticAlgebra F c 0) = Nat.card F * Nat.card F := by
  rw [Nat.card_congr (QuadraticAlgebra.equivProd c 0), Nat.card_prod]

instance (c : F) : Finite (QuadraticAlgebra F c 0) :=
  Finite.of_equiv (F × F) (QuadraticAlgebra.equivProd c 0).symm

theorem exists_norm_eq (hodd : Odd (Nat.card F)) (hc : c ≠ 0) (t : F) :
    ∃ z : QuadraticAlgebra F c 0, QuadraticAlgebra.norm z = t := by
  have := Fintype.ofFinite F
  open Polynomial in
  obtain ⟨x, y, hxy⟩ := FiniteField.exists_root_sum_quadratic
    (f := (X ^ 2 - C t : F[X])) (g := -(C c * X ^ 2 : F[X]))
    (by exact degree_X_pow_sub_C (by norm_num) t)
    (by rw [degree_neg]; exact degree_C_mul_X_pow 2 hc)
    (by rw [← Nat.card_eq_fintype_card]; exact Nat.odd_iff.mp hodd)
  refine ⟨⟨x, y⟩, ?_⟩
  rw [QuadraticAlgebra.norm_def]
  simp at hxy
  simp only
  linear_combination hxy

theorem card_quadNormOne_of_nonsplit (hodd : Odd (Nat.card F)) (hc : c ≠ 0) (hns : ¬ IsSquare c) :
    Nat.card (quadNormOne c) = Nat.card F + 1 := by
  have : Fact (¬ IsSquare c) := ⟨hns⟩
  let ν : (QuadraticAlgebra F c 0)ˣ →* Fˣ := Units.map (QuadraticAlgebra.norm : _ →* F)
  have hν : Function.Surjective ν := by
    intro t
    obtain ⟨z, hz⟩ := exists_norm_eq hodd hc (t : F)
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [QuadraticAlgebra.norm_zero] at hz
      exact t.ne_zero hz.symm
    refine ⟨Units.mk0 z hz0, Units.ext ?_⟩
    simpa [ν] using hz
  have h1 := Subgroup.card_ker_mul_card_of_surjective hν
  rw [Nat.card_units, Nat.card_units, card_quadraticAlgebra] at h1
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have h2 : Nat.card ν.ker * (Nat.card F - 1) = (Nat.card F + 1) * (Nat.card F - 1) := by
    rw [h1]
    obtain ⟨m, hm⟩ : ∃ m, Nat.card F = m + 1 := ⟨Nat.card F - 1, by omega⟩
    rw [hm, Nat.add_sub_cancel]
    apply Nat.sub_eq_of_eq_add
    ring
  exact Nat.eq_of_mul_eq_mul_right (by omega) h2

theorem isCyclic_quadNormOne_of_nonsplit (hns : ¬ IsSquare c) : IsCyclic (quadNormOne c) := by
  have : Fact (¬ IsSquare c) := ⟨hns⟩
  refine isCyclic_of_injective_ringHom
    ((Units.coeHom (QuadraticAlgebra F c 0)).comp (quadNormOne c).subtype) ?_
  intro u v huv
  exact Subtype.ext (Units.ext huv)

end NonSplit

namespace IsInvolDiag

variable {A : GL (Fin 2) F}

theorem isCyclic_and_card_fixSub [Finite F] (hA : IsInvolDiag A) (hodd : Odd (Nat.card F)) :
    IsCyclic (fixSub A) ∧
      ∃ η : ℤ, (η = 1 ∨ η = -1) ∧ (Nat.card (fixSub A) : ℤ) = Nat.card F - η := by
  have h2 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd
  obtain ⟨a, b, e, c, hc0, hAmat, hac, -⟩ := hA.entries
  have hq : 1 < Nat.card F := Finite.one_lt_card
  by_cases hsq : IsSquare c
  · obtain ⟨μ, hμ⟩ := hsq
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      exact hc0 (by simpa using hμ)
    refine ⟨?_, 1, Or.inl rfl, ?_⟩
    · exact (hA.fixSubEquiv h2 hAmat hac).isCyclic.mp (isCyclic_quadNormOne_of_split h2 hμ0 hμ)
    · rw [← Nat.card_congr (hA.fixSubEquiv h2 hAmat hac).toEquiv, card_quadNormOne_of_split h2 hμ0 hμ]
      push_cast [Nat.cast_sub hq.le]
      ring
  · refine ⟨?_, -1, Or.inr rfl, ?_⟩
    · exact (hA.fixSubEquiv h2 hAmat hac).isCyclic.mp (isCyclic_quadNormOne_of_nonsplit hsq)
    · rw [← Nat.card_congr (hA.fixSubEquiv h2 hAmat hac).toEquiv,
        card_quadNormOne_of_nonsplit hodd hc0 hsq]
      push_cast
      ring

theorem isCyclic_fixSub [Finite F] (hA : IsInvolDiag A) (hodd : Odd (Nat.card F)) :
    IsCyclic (fixSub A) :=
  (hA.isCyclic_and_card_fixSub hodd).1

end IsInvolDiag

end CFSG.ClassicalInvolution.Generic
