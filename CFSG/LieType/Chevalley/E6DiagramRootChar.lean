module

public import CFSG.LocalAnalysis.ComponentInitial.RootDiagonalConjugation

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem weyl_smul_eq_add_zsmul_of_dvd_cartan {τ : Tag} {m : ℕ} {v : Fin τ.rank → ℤ}
    (hv : ∀ i, (m : ℤ) ∣ ∑ j, τ.cartan i j * v j) (w : WeylGroup τ) :
    ∃ x : Fin τ.rank → ℤ, w • v = v + (m : ℤ) • x := by
  induction w using (coxeterSystem τ).simple_induction_left with
  | one => exact ⟨0, by simp⟩
  | mul_simple_left w i ih =>
    obtain ⟨x, hx⟩ := ih
    obtain ⟨k, hk⟩ := hv i
    have hsmul : simple τ i • ((m : ℤ) • x) = (m : ℤ) • (simple τ i • x) := by
      change CFSG.LieType.RootSystem.weylAction (isFiniteType_cartan τ) (simple τ i)
          ((m : ℤ) • x) =
        (m : ℤ) • CFSG.LieType.RootSystem.weylAction (isFiniteType_cartan τ) (simple τ i) x
      exact map_smul _ (m : ℤ) x
    refine ⟨-(k • Pi.single i 1) + simple τ i • x, ?_⟩
    rw [mul_smul, hx, smul_add, hsmul, simple_smul, reflect, hk, mul_smul, smul_add, smul_neg]
    abel

private theorem rootChar_zsmul_nat {τ : Tag} {K : Type} [Field K] {m : ℕ}
    {a : Fin τ.rank → Kˣ} (ha : ∀ i, a i ^ m = 1) (x : Fin τ.rank → ℤ) :
    rootChar a ((m : ℤ) • x) = 1 := by
  rw [rootChar]
  refine Finset.prod_eq_one fun i _ => ?_
  simp only [Pi.smul_apply, zsmul_eq_mul]
  rw [zpow_mul]
  have hm : a i ^ (m : ℤ) = 1 := by simpa using ha i
  change (a i ^ (m : ℤ)) ^ x i = 1
  rw [hm, one_zpow]

theorem rootChar_smul_eq_of_dvd_cartan
    {τ : Tag} {K : Type} [Field K] {m : ℕ}
    {a : Fin τ.rank → Kˣ} (ha : ∀ i, a i ^ m = 1) {v : Fin τ.rank → ℤ}
    (hv : ∀ i, (m : ℤ) ∣ ∑ j, τ.cartan i j * v j) (w : WeylGroup τ) :
    rootChar a (w • v) = rootChar a v := by
  obtain ⟨x, hx⟩ := weyl_smul_eq_add_zsmul_of_dvd_cartan hv w
  rw [hx, rootChar_add, rootChar_zsmul_nat ha x, mul_one]

private theorem rootChar_perm_E6_prod {K : Type} [Field K]
    {a : Fin TwistTag.E6.tag.rank → Kˣ}
    (h : rootChar a (![1, 0, 2, 0, 1, 2] : Fin TwistTag.E6.tag.rank → ℤ) =
      rootChar (fun i => a (TwistTag.E6.perm.symm i))
        (![1, 0, 2, 0, 1, 2] : Fin TwistTag.E6.tag.rank → ℤ)) :
    (a (0 : Fin 6) * a (2 : Fin 6) ^ 2 * a (4 : Fin 6) * a (5 : Fin 6) ^ 2 : Kˣ) =
      a (5 : Fin 6) * a (4 : Fin 6) ^ 2 * a (2 : Fin 6) * a (0 : Fin 6) ^ 2 := by
  have h6 : (∏ i : Fin 6, a i ^ (![1, 0, 2, 0, 1, 2] : Fin 6 → ℤ) i) =
      ∏ i : Fin 6, a (TwistTag.E6.perm.symm i) ^ (![1, 0, 2, 0, 1, 2] : Fin 6 → ℤ) i := by
    change rootChar a (![1, 0, 2, 0, 1, 2] : Fin TwistTag.E6.tag.rank → ℤ) =
      rootChar (fun i => a (TwistTag.E6.perm.symm i))
        (![1, 0, 2, 0, 1, 2] : Fin TwistTag.E6.tag.rank → ℤ)
    exact h
  have hp0 : TwistTag.E6.perm.symm (0 : Fin 6) = (5 : Fin 6) := rfl
  have hp1 : TwistTag.E6.perm.symm (1 : Fin 6) = (1 : Fin 6) := rfl
  have hp2 : TwistTag.E6.perm.symm (2 : Fin 6) = (4 : Fin 6) := rfl
  have hp3 : TwistTag.E6.perm.symm (3 : Fin 6) = (3 : Fin 6) := rfl
  have hp4 : TwistTag.E6.perm.symm (4 : Fin 6) = (2 : Fin 6) := rfl
  have hp5 : TwistTag.E6.perm.symm (5 : Fin 6) = (0 : Fin 6) := rfl
  rw [Fin.prod_univ_six, Fin.prod_univ_six] at h6
  simpa [hp0, hp1, hp2, hp3, hp4, hp5] using h6

theorem not_exists_weyl_rootChar_eq_perm_E6
    {K : Type} [Field K]
    {a : Fin TwistTag.E6.tag.rank → Kˣ} (ha : ∀ i, a i ^ 3 = 1)
    (hc : a ⟨0, by decide⟩ * a ⟨4, by decide⟩ ≠ a ⟨2, by decide⟩ * a ⟨5, by decide⟩) :
    ¬ ∃ w : WeylGroup TwistTag.E6.tag, ∀ v : Fin TwistTag.E6.tag.rank → ℤ,
      rootChar a (w • v) = rootChar (fun i => a (TwistTag.E6.perm.symm i)) v := by
  rintro ⟨w, hw⟩
  let v₀ : Fin TwistTag.E6.tag.rank → ℤ := ![1, 0, 2, 0, 1, 2]
  have hv : ∀ i : Fin 6, (3 : ℤ) ∣ ∑ j : Fin 6, TwistTag.E6.tag.cartan i j * v₀ j := by
    intro i
    fin_cases i <;> decide
  have h3 : rootChar a (w • v₀) = rootChar a v₀ :=
    rootChar_smul_eq_of_dvd_cartan (τ := TwistTag.E6.tag) (m := 3) ha hv w
  have heq : rootChar a v₀ =
      rootChar (fun i => a (TwistTag.E6.perm.symm i)) v₀ := by
    rw [← h3]
    exact hw v₀
  have hprod := rootChar_perm_E6_prod heq
  have hne : ((a (0 : Fin 6) : K) * a (2 : Fin 6) * a (4 : Fin 6) *
      a (5 : Fin 6)) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _))
      (Units.ne_zero _)) (Units.ne_zero _)
  have hQ : (a (2 : Fin 6) : K) * a (5 : Fin 6) =
      a (0 : Fin 6) * a (4 : Fin 6) := by
    have h := congrArg (fun u : Kˣ => (u : K)) hprod
    simp only [Units.val_mul, Units.val_pow_eq_pow_val] at h
    have hfac : ((a (0 : Fin 6) : K) * a (2 : Fin 6) * a (4 : Fin 6) *
        a (5 : Fin 6)) * (a (2 : Fin 6) * a (5 : Fin 6)) =
        ((a (0 : Fin 6) : K) * a (2 : Fin 6) * a (4 : Fin 6) * a (5 : Fin 6)) *
          (a (0 : Fin 6) * a (4 : Fin 6)) := by
      calc ((a (0 : Fin 6) : K) * a (2 : Fin 6) * a (4 : Fin 6) * a (5 : Fin 6)) *
            (a (2 : Fin 6) * a (5 : Fin 6))
          = a (0 : Fin 6) * a (2 : Fin 6) ^ 2 * a (4 : Fin 6) * a (5 : Fin 6) ^ 2 := by
            ring
        _ = a (5 : Fin 6) * a (4 : Fin 6) ^ 2 * a (2 : Fin 6) *
              a (0 : Fin 6) ^ 2 := h
        _ = ((a (0 : Fin 6) : K) * a (2 : Fin 6) * a (4 : Fin 6) * a (5 : Fin 6)) *
              (a (0 : Fin 6) * a (4 : Fin 6)) := by ring
    exact mul_left_cancel₀ hne hfac
  have hunits : a (2 : Fin 6) * a (5 : Fin 6) = a (0 : Fin 6) * a (4 : Fin 6) := by
    apply Units.ext
    simpa only [Units.val_mul] using hQ
  exact hc hunits.symm

end CFSG.LieType.Chevalley
