module

public import CFSG.ClassicalInvolution.Phan.Center

public section

namespace CFSG.ClassicalInvolution.PhanDn.QTwo

open Matrix CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem center_Su_four_eq_bot (hK : Nat.card K = 4) :
    Subgroup.center (Su K 2 1 4) = ⊥ := by
  have hF : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  have hσ : CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution (unitaryInvolution K 2 1) :=
    CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution (p := 2) (f := 1) hF
  refine (Subgroup.eq_bot_iff_forall _).2 fun z hz => ?_
  obtain ⟨u, hu⟩ :=
    exists_scalar_of_mem_center hσ (by norm_num : 3 ≤ 4) hz
  obtain ⟨hdet, hiso⟩ := mem_SUid.mp z.2
  have hzm : (((z : Su K 2 1 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      Matrix.scalar (Fin 4) (u : K) := hu
  rw [hzm, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] at hdet
  have h3 : (u : K) ^ 2 * (u : K) = 1 := by
    have h1 := congrFun (congrFun hiso 0) 0
    rw [hzm] at h1
    simp only [conjTr, Matrix.scalar_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, Matrix.diagonal_apply] at h1
    simpa [Fin.sum_univ_four, unitaryInvolution_apply, frobenius_def] using h1
  have hu1 : (u : K) = 1 := by
    calc (u : K) = (u : K) ^ 4 * ((u : K) ^ 2 * (u : K))⁻¹ := by
          field_simp [u.ne_zero]
      _ = 1 := by rw [hdet, h3, inv_one, one_mul]
  apply Subtype.ext
  apply Units.ext
  rw [hzm, hu1, Matrix.scalar_apply, Matrix.diagonal_one]
  rfl

theorem isQuasisimple_Su_four (hK : Nat.card K = 4) :
    CFSG.IsQuasisimple (Su K 2 1 4) := by
  have hF : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  exact CFSG.IsQuasisimple.of_mulEquiv
    (MulEquiv.subgroupCongr (SUid_eq_statedSU (F := K) (p := 2) (f := 1) hF 4))
    (isQuasisimple_statedSU_of_card (F := K) (p := 2) (f := 1) hF
      (n := 4) (by norm_num) (by decide)).1

theorem injective_of_exists_ne_one {G : Type*} [Group G] (hK : Nat.card K = 4)
    (θ : Su K 2 1 4 →* G) (h : ∃ x, θ x ≠ 1) : Function.Injective θ := by
  have hker := CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple
    (isQuasisimple_Su_four (K := K) hK) h
  rw [center_Su_four_eq_bot (K := K) hK, le_bot_iff] at hker
  exact (MonoidHom.ker_eq_bot_iff θ).mp hker

private theorem card_Su_two (hK : Nat.card K = 4) : Nat.card (Su K 2 1 2) = 6 := by
  have hF : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  obtain ⟨P, hP⟩ := exists_wittMatrix (F := K) (p := 2) (f := 1) hF 2
  rw [← Nat.card_congr (conjEquiv P hP).toEquiv,
    CFSG.LieType.Steinberg.card_SU_two hF]
  norm_num

theorem eq_one_of_hom_Su_two {A : Type*} [Group A] (hK : Nat.card K = 4)
    (χ : Su K 2 1 2 →* A) (h3 : ∀ a : A, a ^ 3 = 1) : χ = 1 := by
  have hF : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  obtain ⟨ω, hω, hω1⟩ := exists_norm_eq_one_ne_one (F := K) (p := 2) (f := 1) hF
  have hω2 : ω ^ 2 = unitaryInvolution K 2 1 ω := by
    rw [unitaryInvolution_apply]
    norm_num
  have hω3 : ω ^ 3 = 1 := by
    rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, hω2]
    exact hω
  have hωmul : ω * ω ^ 2 = 1 := by rw [← pow_succ', hω3]
  have hωmul' : ω ^ 2 * ω = 1 := by rw [← pow_succ, hω3]
  have hω6 : ω ^ 6 = 1 := by
    rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul, hω3, one_pow]
  have hω6' : (ω ^ 2) ^ 2 * ω ^ 2 = 1 := by
    rw [show (ω ^ 2) ^ 2 * ω ^ 2 = ω ^ 6 by ring]
    exact hω6
  have hω3m : ω * ω * ω = 1 := by
    rw [show ω * ω * ω = ω ^ 3 by ring]
    exact hω3
  have hω6m : ω ^ 2 * ω ^ 2 * ω ^ 2 = 1 := by
    rw [show ω ^ 2 * ω ^ 2 * ω ^ 2 = ω ^ 6 by ring]
    exact hω6
  have hSdet : (!![(0 : K), 1; 1, 0] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    rw [Matrix.det_fin_two_of]
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    linear_combination -h2
  have hTdet : (!![(0 : K), ω; ω ^ 2, 0] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    rw [Matrix.det_fin_two_of]
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    linear_combination -h2 - hω3
  let S0 : GL (Fin 2) K :=
    GeneralLinearGroup.mkOfDetNeZero !![(0 : K), 1; 1, 0] (by
      rw [hSdet]
      exact one_ne_zero)
  let T0 : GL (Fin 2) K :=
    GeneralLinearGroup.mkOfDetNeZero !![(0 : K), ω; ω ^ 2, 0] (by
      rw [hTdet]
      exact one_ne_zero)
  have hSmat : ((S0 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![(0 : K), 1; 1, 0] := by
    simp [S0]
  have hTmat : ((T0 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![(0 : K), ω; ω ^ 2, 0] := by
    simp [T0]
  have hSmem : S0 ∈ SUid (unitaryInvolution K 2 1) 2 := by
    refine mem_SUid.mpr ⟨hSdet, ?_⟩
    rw [hSmat]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [conjTr, Matrix.mul_apply, Fin.sum_univ_two, frobenius_def]
  have hTmem : T0 ∈ SUid (unitaryInvolution K 2 1) 2 := by
    refine mem_SUid.mpr ⟨hTdet, ?_⟩
    rw [hTmat]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [conjTr, Matrix.mul_apply, Fin.sum_univ_two, frobenius_def, hωmul', hω6']
  let S : Su K 2 1 2 := ⟨S0, hSmem⟩
  let T : Su K 2 1 2 := ⟨T0, hTmem⟩
  have hS : (((S : Su K 2 1 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![(0 : K), 1; 1, 0] := by
    simp [S, hSmat]
  have hT : (((T : Su K 2 1 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![(0 : K), ω; ω ^ 2, 0] := by
    simp [T, hTmat]
  have hS2 : S * S = 1 := by
    apply Subtype.ext
    apply Units.ext
    change (((S : Su K 2 1 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
      (((S : Su K 2 1 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1
    rw [hS]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hT2 : T * T = 1 := by
    apply Subtype.ext
    apply Units.ext
    change (((T : Su K 2 1 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
      (((T : Su K 2 1 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1
    rw [hT]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hωmul, hωmul']
  have hSTmat : (((S * T : Su K 2 1 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![ω ^ 2, 0; 0, ω] := by
    change (((S : Su K 2 1 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
      (((T : Su K 2 1 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = _
    rw [hS, hT]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hS_ne_one : S ≠ 1 := by
    intro h
    have h1 := congrArg (fun g : Su K 2 1 2 =>
      (((g : GL (Fin 2) K)) : Matrix (Fin 2) (Fin 2) K) 0 1) h
    simp [hS] at h1
  have hT_ne_one : T ≠ 1 := by
    intro h
    have h1 := congrArg (fun g : Su K 2 1 2 =>
      (((g : GL (Fin 2) K)) : Matrix (Fin 2) (Fin 2) K) 0 0) h
    simp [hT] at h1
  have hSTne : S * T ≠ 1 := by
    intro h
    have h1 := congrArg (fun g : Su K 2 1 2 =>
      (((g : GL (Fin 2) K)) : Matrix (Fin 2) (Fin 2) K) 1 1) h
    rw [hSTmat] at h1
    simp at h1
    exact hω1 h1
  have hST3 : (S * T) ^ 3 = 1 := by
    have h3' : (S * T) * (S * T) * (S * T) = 1 := by
      apply Subtype.ext
      apply Units.ext
      change (((S * T : Su K 2 1 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
        (((S * T : Su K 2 1 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
        (((S * T : Su K 2 1 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1
      rw [hSTmat]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, hω3m, hω6m]
    simpa [pow_succ, pow_two, mul_assoc] using h3'
  have hS2' : S ^ 2 = 1 := by rw [pow_two]; exact hS2
  have hT2' : T ^ 2 = 1 := by rw [pow_two]; exact hT2
  have hordS : orderOf S = 2 := orderOf_eq_prime hS2' hS_ne_one
  have hordST : orderOf (S * T) = 3 := orderOf_eq_prime hST3 hSTne
  let D : Subgroup (Su K 2 1 2) := Subgroup.closure ({S, T} : Set (Su K 2 1 2))
  have hS_mem : S ∈ D := Subgroup.subset_closure (by simp)
  have hT_mem : T ∈ D := Subgroup.subset_closure (by simp)
  have hST_mem : S * T ∈ D := D.mul_mem hS_mem hT_mem
  have h2dvd : 2 ∣ Nat.card D := by
    have h := Subgroup.orderOf_dvd_natCard D hS_mem
    rwa [hordS] at h
  have h3dvd : 3 ∣ Nat.card D := by
    have h := Subgroup.orderOf_dvd_natCard D hST_mem
    rwa [hordST] at h
  have h6dvd : 6 ∣ Nat.card D :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 2 3) h2dvd h3dvd
  have hcard : Nat.card (Su K 2 1 2) = 6 := card_Su_two hK
  have hdvd : Nat.card D ∣ 6 := hcard ▸ Subgroup.card_subgroup_dvd_card D
  have hDcard : Nat.card D = 6 := Nat.dvd_antisymm hdvd h6dvd
  have hDtop : D = ⊤ := Subgroup.eq_top_of_card_eq D (by rw [hDcard, hcard])
  have hχS : χ S = 1 := by
    have h2 : (χ S) ^ 2 = 1 := by rw [← map_pow, hS2', map_one]
    have h3' : (χ S) ^ 3 = 1 := h3 (χ S)
    calc χ S = (χ S) ^ 3 * ((χ S) ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3', h2, inv_one, mul_one]
  have hχT : χ T = 1 := by
    have h2 : (χ T) ^ 2 = 1 := by rw [← map_pow, hT2', map_one]
    have h3' : (χ T) ^ 3 = 1 := h3 (χ T)
    calc χ T = (χ T) ^ 3 * ((χ T) ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3', h2, inv_one, mul_one]
  ext x
  have hx : x ∈ D := by rw [hDtop]; trivial
  refine Subgroup.closure_induction (p := fun y _ => χ y = 1) ?_ ?_ ?_ ?_ hx
  · intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact hχS
    · exact hχT
  · exact map_one χ
  · intro a b _ _ ha hb
    rw [map_mul, ha, hb, one_mul]
  · intro a _ ha
    rw [map_inv, ha, inv_one]

end CFSG.ClassicalInvolution.PhanDn.QTwo

end
