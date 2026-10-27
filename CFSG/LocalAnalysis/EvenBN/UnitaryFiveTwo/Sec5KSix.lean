module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Model
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaInputsSU
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import all CFSG.Fischer.F4

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Matrix Subgroup CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaInputs

@[expose] def extMat (y : Matrix (Fin 4) (Fin 4) F4) : Matrix (Fin 5) (Fin 5) F4 :=
  !![y 0 0, y 0 1, 0, y 0 2, y 0 3; y 1 0, y 1 1, 0, y 1 2, y 1 3; 0, 0, 1, 0, 0;
    y 2 0, y 2 1, 0, y 2 2, y 2 3; y 3 0, y 3 1, 0, y 3 2, y 3 3]

@[expose] def subMat (M : Matrix (Fin 5) (Fin 5) F4) : Matrix (Fin 4) (Fin 4) F4 :=
  !![M 0 0, M 0 1, M 0 3, M 0 4; M 1 0, M 1 1, M 1 3, M 1 4; M 3 0, M 3 1, M 3 3, M 3 4;
    M 4 0, M 4 1, M 4 3, M 4 4]

theorem subMat_extMat (y : Matrix (Fin 4) (Fin 4) F4) : subMat (extMat y) = y := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem extMat_injective {y z : Matrix (Fin 4) (Fin 4) F4} (h : extMat y = extMat z) : y = z := by
  rw [← subMat_extMat y, h, subMat_extMat]

theorem extMat_mul (y z : Matrix (Fin 4) (Fin 4) F4) :
    extMat (y * z) = extMat y * extMat z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [extMat, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_five]

theorem extMat_map_bar (y : Matrix (Fin 4) (Fin 4) F4) :
    (extMat y).map bar = extMat (y.map bar) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [extMat]

theorem extMat_transpose (y : Matrix (Fin 4) (Fin 4) F4) : (extMat y)ᵀ = extMat yᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [extMat]

theorem extMat_one : extMat 1 = 1 := by decide

theorem J5_eq_extMat : J5 = extMat (revGL 4 F4 : Matrix (Fin 4) (Fin 4) F4) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J5, extMat, revGL_apply]

theorem det_extMat (y : Matrix (Fin 4) (Fin 4) F4) : (extMat y).det = y.det := by
  rw [Matrix.det_succ_row _ 2, Fin.sum_univ_five]
  have e : (extMat y).submatrix (Fin.succAbove 2) (Fin.succAbove 2) = y := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have h0 : extMat y 2 0 = 0 := rfl
  have h1 : extMat y 2 1 = 0 := rfl
  have h2 : extMat y 2 2 = 1 := rfl
  have h3 : extMat y 2 3 = 0 := rfl
  have h4 : extMat y 2 4 = 0 := rfl
  rw [h0, h1, h2, h3, h4, e]
  norm_num

@[expose] def StabSub : Subgroup SU52 where
  carrier := {g | mat g = extMat (subMat (mat g))}
  mul_mem' {g h} hg hh := by
    change mat g = _ at hg
    change mat h = _ at hh
    change mat g * mat h = extMat (subMat (mat g * mat h))
    rw [hg, hh, ← extMat_mul, subMat_extMat]
  one_mem' := by
    change mat 1 = extMat (subMat (mat 1))
    rw [mat_one, show subMat 1 = 1 by decide, extMat_one]
  inv_mem' {g} hg := by
    change mat g = _ at hg
    change mat g⁻¹ = extMat (subMat (mat g⁻¹))
    have h : mat g⁻¹ = extMat ((revGL 4 F4 : Matrix (Fin 4) (Fin 4) F4) *
        ((subMat (mat g)).map bar)ᵀ * (revGL 4 F4 : Matrix (Fin 4) (Fin 4) F4)) := by
      rw [mat_inv, hg, extMat_map_bar, extMat_transpose, J5_eq_extMat, extMat_mul, extMat_mul,
        subMat_extMat]
    rw [h, subMat_extMat]

theorem mem_StabSub {g : SU52} : g ∈ StabSub ↔ mat g = extMat (subMat (mat g)) := Iff.rfl

theorem K₃sub_le_StabSub : K₃sub ≤ StabSub := by
  have hx₁ : ∀ b : F4, x₁Mat 0 b = extMat (subMat (x₁Mat 0 b)) := by decide
  have hx₂ : ∀ a : F4, x₂Mat a = extMat (subMat (x₂Mat a)) := by decide
  have hx₃ : ∀ a : F4, x₃Mat a = extMat (subMat (x₃Mat a)) := by decide
  have hx₄ : ∀ b : F4, x₄Mat 0 b = extMat (subMat (x₄Mat 0 b)) := by decide
  have hu : uSU ∈ StabSub := by
    rw [mem_StabSub, mat_uSU]
    decide
  have hv : vSU ∈ StabSub := by
    rw [mem_StabSub, mat_vSU]
    decide
  refine sup_le (sup_le (sup_le (sup_le (sup_le ?_ ?_) ?_) ?_) (zpowers_le.2 hu))
    (zpowers_le.2 hv)
  · intro g hg
    obtain ⟨a, b, ha, hab⟩ := (mem_x₁Sub (P := (· = 0)) (hP0 := rfl) (hPadd := zero_add_zero)).1
      hg
    rw [mem_StabSub, hab, ha]
    exact hx₁ b
  · intro g hg
    obtain ⟨a, -, ha⟩ := (mem_x₂Sub (P := fun _ => True) (hP0 := trivial)
      (hPadd := true_add)).1 hg
    rw [mem_StabSub, ha]
    exact hx₂ a
  · intro g hg
    obtain ⟨a, -, ha⟩ := (mem_x₃Sub (P := fun _ => True) (hP0 := trivial)
      (hPadd := true_add)).1 hg
    rw [mem_StabSub, ha]
    exact hx₃ a
  · intro g hg
    obtain ⟨a, b, ha, hab⟩ := (mem_x₄Sub (P := (· = 0)) (hP0 := rfl) (hPadd := zero_add_zero)).1
      hg
    rw [mem_StabSub, hab, ha]
    exact hx₄ b

theorem transpose_J5_mul_diag (M : Matrix (Fin 5) (Fin 5) F4) (j : Fin 5) :
    (Mᵀ * J5 * M) j j = M 2 j * M 2 j := by
  simp only [Matrix.mul_apply, Fin.sum_univ_five, transpose_apply, J5, of_apply]
  norm_num
  ring_nf
  simp [CharTwo.two_eq_zero]

theorem J5_mul_transpose_diag (M : Matrix (Fin 5) (Fin 5) F4) (j : Fin 5) :
    (M * J5 * Mᵀ) j j = M j 2 * M j 2 := by
  have h := transpose_J5_mul_diag Mᵀ j
  rwa [transpose_transpose] at h

theorem eq_of_mul_self_eq : ∀ x c : F4, (c = 0 ∨ c = 1) → x * x = c → x = c := by decide

theorem CfldSub_le_StabSub : CfldSub ≤ StabSub := by
  intro g hg
  have hb : (mat g).map bar = mat g := by rw [← mat_fld, mem_CfldSub.1 hg]
  obtain ⟨h1, -⟩ := mem_SU52.1 g.2
  obtain ⟨h2, -⟩ := mem_SU52_iff.1 g.2
  change (mat g).map bar = mat g at hb
  rw [hb] at h1 h2
  have hr : ∀ j : Fin 5, mat g 2 j = J5 j j := fun j => by
    refine eq_of_mul_self_eq _ _ ?_ ?_
    · simp only [J5, of_apply]
      split_ifs <;> simp
    · rw [← transpose_J5_mul_diag, h1]
  have hc : ∀ j : Fin 5, mat g j 2 = J5 j j := fun j => by
    refine eq_of_mul_self_eq _ _ ?_ ?_
    · simp only [J5, of_apply]
      split_ifs <;> simp
    · rw [← J5_mul_transpose_diag, h2]
  rw [mem_StabSub]
  have r0 := hr 0
  have r1 := hr 1
  have r2 := hr 2
  have r3 := hr 3
  have r4 := hr 4
  have c0 := hc 0
  have c1 := hc 1
  have c3 := hc 3
  have c4 := hc 4
  simp only [J5, of_apply] at r0 r1 r2 r3 r4 c0 c1 c3 c4
  norm_num at r0 r1 r2 r3 r4 c0 c1 c3 c4
  ext i j
  fin_cases i <;> fin_cases j <;> simp [extMat, subMat, r0, r1, r2, r3, r4, c0, c1, c3, c4]

theorem subMat_mem {g : SU52} (hg : g ∈ StabSub) :
    ((subMat (mat g)).map bar)ᵀ * (revGL 4 F4 : Matrix (Fin 4) (Fin 4) F4) * subMat (mat g) =
        (revGL 4 F4 : Matrix (Fin 4) (Fin 4) F4) ∧ (subMat (mat g)).det = 1 := by
  obtain ⟨h1, h2⟩ := mem_SU52.1 g.2
  rw [mem_StabSub] at hg
  refine ⟨extMat_injective ?_, ?_⟩
  · rw [extMat_mul, extMat_mul, ← extMat_transpose, ← extMat_map_bar, ← hg, ← J5_eq_extMat]
    exact h1
  · rw [← det_extMat, ← hg]
    exact h2

theorem card_StabSub_le : Nat.card StabSub ≤ 25920 := by
  have hF : Nat.card F4 = 4 := by rw [Nat.card_eq_fintype_card, F4.card]
  have key := card_slUnitary_four hF (σ := bar) bar_apply
  rw [← key]
  refine Nat.card_le_card_of_injective (fun g => ⟨⟨subMat (mat g), (subMat_mem g.2).2⟩,
    (subMat_mem g.2).1⟩) fun g g' h => ?_
  have h1 : subMat (mat g) = subMat (mat g') :=
    congrArg (fun z : slUnitary (bar : F4 →+* F4) (revGL 4 F4 : Matrix (Fin 4) (Fin 4) F4) =>
      ((z : SpecialLinearGroup (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4)) h
  apply Subtype.ext
  apply ext_mat
  rw [mem_StabSub.1 g.2, mem_StabSub.1 g'.2, h1]

@[expose] def p₉ : SU52 := x₁SU 0 1 (by decide) * uSU

@[expose] def q₉ : SU52 := x₄SU 0 1 (by decide) * vSU * uSU * vSU

@[expose] def p₉Mat : Matrix (Fin 5) (Fin 5) F4 :=
  !![1, 0, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 1, 0, 0; 0, 1, 0, 1, 0; 0, 0, 0, 0, 1]

@[expose] def q₉Mat : Matrix (Fin 5) (Fin 5) F4 :=
  !![0, 0, 0, 0, 1; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 1, 0, 0, 0, 1]

theorem mat_p₉ : mat p₉ = p₉Mat := by
  rw [p₉, mat_mul, mat_x₁SU, mat_uSU]
  decide

theorem mat_q₉ : mat q₉ = q₉Mat := by
  rw [q₉, mat_mul, mat_mul, mat_mul, mat_x₄SU, mat_vSU, mat_uSU]
  decide

theorem mem_K₃sub_of_ZX₁ {g : SU52} (hg : g ∈ ZX₁sub) : g ∈ K₃sub := by
  unfold K₃sub
  exact mem_sup_left (mem_sup_left (mem_sup_left (mem_sup_left (mem_sup_left hg))))

theorem mem_K₃sub_of_ZX₄ {g : SU52} (hg : g ∈ ZX₄sub) : g ∈ K₃sub := by
  unfold K₃sub
  exact mem_sup_left (mem_sup_left (mem_sup_right hg))

theorem uSU_mem_K₃sub : uSU ∈ K₃sub := by
  unfold K₃sub
  exact mem_sup_left (mem_sup_right (mem_zpowers uSU))

theorem vSU_mem_K₃sub : vSU ∈ K₃sub := by
  unfold K₃sub
  exact mem_sup_right (mem_zpowers vSU)

theorem p₉_mem : p₉ ∈ K₃sub ⊓ CfldSub := by
  have hz : x₁SU 0 1 (by decide) ∈ K₃sub := mem_K₃sub_of_ZX₁
    ((mem_x₁Sub (P := (· = 0)) (hP0 := rfl) (hPadd := zero_add_zero)).2 ⟨0, 1, rfl, rfl⟩)
  refine mem_inf.2 ⟨mul_mem hz uSU_mem_K₃sub, mem_CfldSub.2 ?_⟩
  rw [p₉, map_mul, fld_uSU, fld_x₁SU]
  rfl

theorem q₉_mem : q₉ ∈ K₃sub ⊓ CfldSub := by
  have hz : x₄SU 0 1 (by decide) ∈ K₃sub := mem_K₃sub_of_ZX₄
    ((mem_x₄Sub (P := (· = 0)) (hP0 := rfl) (hPadd := zero_add_zero)).2 ⟨0, 1, rfl, rfl⟩)
  refine mem_inf.2 ⟨mul_mem (mul_mem (mul_mem hz vSU_mem_K₃sub) uSU_mem_K₃sub) vSU_mem_K₃sub,
    mem_CfldSub.2 ?_⟩
  rw [q₉, map_mul, map_mul, map_mul, fld_uSU, fld_vSU, fld_x₄SU]
  rfl

theorem p₉_facts : p₉ ^ 3 = 1 ∧ q₉ ^ 3 = 1 ∧ p₉ * q₉ = q₉ * p₉ ∧ p₉ ≠ 1 ∧ q₉ ≠ 1 ∧
    p₉ ≠ q₉ ∧ p₉ ≠ q₉ * q₉ := by
  refine ⟨ext_mat ?_, ext_mat ?_, ext_mat ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [mat_pow_three, mat_p₉, mat_one]
    decide
  · rw [mat_pow_three, mat_q₉, mat_one]
    decide
  · rw [mat_mul, mat_mul, mat_p₉, mat_q₉]
    decide
  · have := congrArg mat h
    rw [mat_p₉, mat_one] at this
    exact absurd this (by decide)
  · have := congrArg mat h
    rw [mat_q₉, mat_one] at this
    exact absurd this (by decide)
  · have := congrArg mat h
    rw [mat_p₉, mat_q₉] at this
    exact absurd this (by decide)
  · have := congrArg mat h
    rw [mat_mul, mat_p₉, mat_q₉] at this
    exact absurd this (by decide)

theorem exists_E₉ : ∃ E : Subgroup SU52, E ≤ K₃sub ⊓ CfldSub ∧ Nat.card E = 9 := by
  obtain ⟨hp3, hq3, hpq, hp1, hq1, hpq', hpq''⟩ := p₉_facts
  have hop : orderOf p₉ = 3 := orderOf_eq_prime hp3 hp1
  have hoq : orderOf q₉ = 3 := orderOf_eq_prime hq3 hq1
  refine ⟨zpowers p₉ ⊔ zpowers q₉, sup_le (zpowers_le.2 p₉_mem) (zpowers_le.2 q₉_mem), ?_⟩
  obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (zpowers p₉)
    (zpowers q₉) fun a ha b hb => by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 ha
      obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hb
      exact ((Commute.zpow_zpow (hpq : Commute p₉ q₉) k m)).eq
  have hinf : zpowers p₉ ⊓ zpowers q₉ = ⊥ := by
    have hdvd : Nat.card (zpowers p₉ ⊓ zpowers q₉ : Subgroup SU52) ∣ 3 := by
      rw [← hop, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
    · exact Subgroup.card_eq_one.1 h1
    · exfalso
      have heq : zpowers p₉ ⊓ zpowers q₉ = zpowers p₉ :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [Nat.card_zpowers, hop, h3])
      have hp' : p₉ ∈ zpowers p₉ ⊓ zpowers q₉ := by
        rw [heq]
        exact mem_zpowers p₉
      have hp : p₉ ∈ zpowers q₉ := hp'.2
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hp
      rw [← zpow_mod_orderOf, hoq] at hk
      have hk3 : k % (3 : ℕ) < 3 := Int.emod_lt_of_pos k (by norm_num)
      have hk0 : 0 ≤ k % (3 : ℕ) := Int.emod_nonneg k (by norm_num)
      interval_cases h : k % (3 : ℕ)
      · rw [zpow_zero] at hk
        exact hp1 hk.symm
      · rw [zpow_one] at hk
        exact hpq' hk.symm
      · rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, sq] at hk
        exact hpq'' hk.symm
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, hop, hoq] at hcard
  exact hcard

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
