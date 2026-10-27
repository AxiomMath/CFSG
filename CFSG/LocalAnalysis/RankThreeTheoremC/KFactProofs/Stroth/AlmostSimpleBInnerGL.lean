module

public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeSpecial

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open Subgroup

section Leaves

variable {E : Type*} [Field E] {W : Type*} [AddCommGroup W] [Module E W] [FiniteDimensional E W]

theorem finite_generalLinearGroup' [Finite E] :
    Finite (LinearMap.GeneralLinearGroup E W) := by
  have : Finite W := Module.finite_of_finite E
  have : Finite (Module.End E W) :=
    Finite.of_injective _ (DFunLike.coe_injective (F := W →ₗ[E] W))
  exact Finite.of_injective _ Units.val_injective

private theorem eq_one_of_apply_smul [CharP E 2] (g : LinearMap.GeneralLinearGroup E W)
    (hg : g ^ 2 = 1) (c : E) (hcw : ∀ w, (g : Module.End E W) w = c • w) : g = 1 := by
  rcases subsingleton_or_nontrivial W with hW | hW
  · exact Units.ext (LinearMap.ext fun w => Subsingleton.elim _ _)
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  have h1 : ((g ^ 2 : LinearMap.GeneralLinearGroup E W) : Module.End E W) w = w := by
    rw [hg]
    rfl
  rw [pow_two, Units.val_mul, Module.End.mul_apply, hcw, hcw, smul_smul] at h1
  have h2 : c * c = 1 := smul_left_injective E hw (by simpa using h1)
  have h3 : c = 1 := by
    have h2' : (2 : E) = 0 := by exact_mod_cast CharP.cast_eq_zero E 2
    have h4 : (c - 1) ^ 2 = 0 := by linear_combination h2 + (1 - c) * h2'
    exact sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h4)
  refine Units.ext (LinearMap.ext fun v => ?_)
  rw [hcw, h3, one_smul]
  rfl

theorem eq_one_of_commute_special_of_sq_eq_one [CharP E 2] (hm : 2 ≤ Module.finrank E W)
    (g : LinearMap.GeneralLinearGroup E W) (hg : g ^ 2 = 1)
    (hc : ∀ δ : LinearMap.GeneralLinearGroup E W, LinearMap.det (δ : Module.End E W) = 1 →
      δ * g = g * δ) : g = 1 := by
  obtain ⟨c, hcw⟩ := CFSG.RankThree.PartOne.KCUnitary.exists_smul_of_commute_special_linear hm
    (g : Module.End E W) fun δ hδ => by
      have h := congrArg Units.val (hc δ hδ)
      rw [Units.val_mul, Units.val_mul] at h
      exact h.symm
  exact eq_one_of_apply_smul g hg c hcw

theorem eq_one_of_sq_eq_one_of_finrank_le_one [CharP E 2] (hm : Module.finrank E W ≤ 1)
    (g : LinearMap.GeneralLinearGroup E W) (hg : g ^ 2 = 1) : g = 1 := by
  obtain ⟨v, hv⟩ := finrank_le_one_iff.mp hm
  obtain ⟨c, hc⟩ := hv ((g : Module.End E W) v)
  refine eq_one_of_apply_smul g hg c fun w => ?_
  obtain ⟨t, rfl⟩ := hv w
  rw [map_smul, ← hc, smul_comm]

private theorem sub_one_sq_dvd_prod (q m : ℕ) (hm : 2 ≤ m) :
    (q - 1) ^ 2 ∣ ∏ i : Fin m, (q ^ m - q ^ (i : ℕ)) := by
  let a : Fin m := ⟨0, by omega⟩
  let b : Fin m := ⟨1, by omega⟩
  have hab : a ≠ b := fun h => by simpa [a, b, Fin.ext_iff] using h
  have h0 : q - 1 ∣ q ^ m - q ^ (a : ℕ) := by
    simpa [a] using Nat.sub_one_dvd_pow_sub_one q m
  have h1 : q - 1 ∣ q ^ m - q ^ (b : ℕ) := by
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    have e : q ^ (j + 1) - q ^ (b : ℕ) = q * (q ^ j - 1) := by
      simp [b, pow_succ, mul_comm, Nat.mul_sub_one]
    rw [e]
    exact (Nat.sub_one_dvd_pow_sub_one q j).mul_left q
  calc (q - 1) ^ 2 = (q - 1) * (q - 1) := sq _
    _ ∣ (q ^ m - q ^ (a : ℕ)) * (q ^ m - q ^ (b : ℕ)) := mul_dvd_mul h0 h1
    _ = ∏ i ∈ ({a, b} : Finset (Fin m)), (q ^ m - q ^ (i : ℕ)) :=
      (Finset.prod_pair (f := fun i : Fin m => q ^ m - q ^ (i : ℕ)) hab).symm
    _ ∣ ∏ i : Fin m, (q ^ m - q ^ (i : ℕ)) :=
      Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ _)

theorem natCard_sub_one_dvd_card_ker_det [Finite E] (hm : 2 ≤ Module.finrank E W) :
    Nat.card E - 1 ∣ Nat.card (Units.map (LinearMap.det : Module.End E W →* E)).ker := by
  classical
  obtain ⟨e⟩ := CFSG.RankThree.PartOne.KCUnitary.nonempty_specialLinearGroup_mulEquiv_ker_det
    (E := E) (W := W)
  rw [← Nat.card_congr e.toEquiv]
  have : Nonempty (Fin (Module.finrank E W)) := ⟨⟨0, by omega⟩⟩
  have hq : 1 < Nat.card E := Finite.one_lt_card
  have h := Matrix.card_SL_mul_card_units (n := Fin (Module.finrank E W)) (R := E)
  have := Fintype.ofFinite E
  rw [Nat.card_units, Matrix.card_GL_field, ← Nat.card_eq_fintype_card] at h
  obtain ⟨k, hk⟩ := sub_one_sq_dvd_prod (Nat.card E) _ hm
  rw [hk] at h
  refine ⟨k, Nat.eq_of_mul_eq_mul_right (Nat.sub_pos_of_lt hq) ?_⟩
  rw [h]
  ring

theorem natCard_generalLinearGroup_two_two [Finite E] (hE : Nat.card E = 2)
    (hm : Module.finrank E W = 2) : Nat.card (LinearMap.GeneralLinearGroup E W) = 6 := by
  let b : Module.Basis (Fin 2) E W := Module.finBasisOfFinrankEq E W hm
  let e : LinearMap.GeneralLinearGroup E W ≃* Matrix.GeneralLinearGroup (Fin 2) E :=
    (LinearMap.GeneralLinearGroup.congrLinearEquiv b.equivFun).trans
      Matrix.GeneralLinearGroup.toLin.symm
  have := Fintype.ofFinite E
  have hE' : Fintype.card E = 2 := by rw [← Nat.card_eq_fintype_card, hE]
  rw [Nat.card_congr e.toEquiv, Matrix.card_GL_field, hE', Fin.prod_univ_two]
  norm_num

end Leaves

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
