module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.KU6CentGaps
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HU7Eigen

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KU6Cent

open Matrix CFSG.Fischer CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
  CFSG.LocalAnalysis.GLTheoremA.HU7

theorem F4_pow_four (x : CFSG.Fischer.F4) : x ^ 4 = x := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, CFSG.Fischer.F4.sq_sq x]

theorem F4_omega_ne_zero : CFSG.Fischer.F4.ω ≠ 0 := fun h => absurd (congrArg CFSG.Fischer.F4.code h) (by decide)

theorem F4_omega_ne_one : CFSG.Fischer.F4.ω ≠ 1 := fun h => absurd (congrArg CFSG.Fischer.F4.code h) (by decide)

theorem F4_omega_pow_three : CFSG.Fischer.F4.ω ^ 3 = 1 := by
  have h4 : CFSG.Fischer.F4.ω ^ 4 = CFSG.Fischer.F4.ω := by
    rw [show CFSG.Fischer.F4.ω ^ 4 = (CFSG.Fischer.F4.ω ^ 2) ^ 2 by ring]
    exact CFSG.Fischer.F4.sq_sq _
  have h : CFSG.Fischer.F4.ω * (CFSG.Fischer.F4.ω ^ 3 - 1) = 0 := by linear_combination h4
  rcases mul_eq_zero.1 h with h1 | h1
  · exact absurd h1 F4_omega_ne_zero
  · linear_combination h1

theorem bar_F4 (c : CFSG.Fischer.F4) : hF4.bar c = c ^ 2 := by
  rw [UnitaryFieldData.bar_apply, pow_one]

theorem gu_mat_unitary (g : Gu) :
    (((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4).map (fun x : F4 => x ^ 2))ᵀ *
      ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = 1 := by
  have hb : (⇑hF4.bar : F4 → F4) = fun x => x ^ 2 := funext bar_F4
  have h := mem_primeFormUnitary.1 g.2
  simp only [idGram, Units.val_one, Matrix.mul_one, hb] at h
  exact h

theorem coe_scalar_eq (u : F4ˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 6) u : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
      (u : F4) • 1 := by
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

theorem scalar_comm (u : F4ˣ) (x : GL (Fin 6) F4) :
    x * Matrix.GeneralLinearGroup.scalar (Fin 6) u = Matrix.GeneralLinearGroup.scalar (Fin 6) u * x := by
  have hmem : Matrix.GeneralLinearGroup.scalar (Fin 6) u ∈ Subgroup.center (GL (Fin 6) F4) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨u, rfl⟩
  exact (Subgroup.mem_center_iff.1 hmem) x

theorem conj_pow_three {Γ : Type} [Group Γ] {s B G : Γ} (hsc : ∀ x : Γ, x * s = s * x)
    (hrel : B * G = G * B * s) (hs3 : s ^ 3 = 1) : B * G ^ 3 = G ^ 3 * B := by
  have h1 : B * G * B⁻¹ = G * s := by
    calc B * G * B⁻¹ = (G * B * s) * B⁻¹ := by rw [hrel]
      _ = G * (B * s) * B⁻¹ := by simp only [mul_assoc]
      _ = G * (s * B) * B⁻¹ := by rw [hsc B]
      _ = G * s := by group
  have hGs : Commute G s := hsc G
  have h2 : (B * G * B⁻¹) ^ 3 = G ^ 3 := by
    rw [h1, hGs.mul_pow 3, hs3, mul_one]
  rw [conj_pow] at h2
  calc B * G ^ 3 = B * G ^ 3 * B⁻¹ * B := by group
    _ = G ^ 3 * B := by rw [h2]

theorem kU6CentGapOne_holds : KU6CentGapOne := by
  intro B hB3 hBne h7
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨g, hg7⟩ := exists_prime_orderOf_dvd_card' 7 h7
  have hgc : (g : PGU6) * (QuotientGroup.mk B : PGU6) = (QuotientGroup.mk B : PGU6) * (g : PGU6) :=
    Subgroup.mem_centralizer_singleton_iff.1 g.2
  have hgo : orderOf (g : PGU6) = 7 := (Subgroup.orderOf_coe g).trans hg7
  obtain ⟨g', hg'⟩ := QuotientGroup.mk_surjective (g : PGU6)
  have hcomm : (QuotientGroup.mk (g' * B) : PGU6) = QuotientGroup.mk (B * g') := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, hg']
    exact hgc
  obtain ⟨c, hc⟩ := mem_ZG.1 (QuotientGroup.eq.1 hcomm)
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hc
  have hrel : (B : GL (Fin 6) F4) * (g' : GL (Fin 6) F4) =
      (g' : GL (Fin 6) F4) * (B : GL (Fin 6) F4) * Matrix.GeneralLinearGroup.scalar (Fin 6) c := by
    rw [hc]
    group
  have hsc3 : (Matrix.GeneralLinearGroup.scalar (Fin 6) c) ^ 3 = 1 := by
    rw [← map_pow, units_cube c, map_one]
  have hH : (B : GL (Fin 6) F4) * (g' : GL (Fin 6) F4) ^ 3 =
      (g' : GL (Fin 6) F4) ^ 3 * (B : GL (Fin 6) F4) :=
    conj_pow_three (fun x => scalar_comm c x) hrel hsc3
  have hmk3 : (QuotientGroup.mk (g' ^ 3 : Gu) : PGU6) = (g : PGU6) ^ 3 := by
    rw [QuotientGroup.mk_pow, hg']
  have hcop : (orderOf (g : PGU6)).Coprime 3 := by
    rw [hgo]
    norm_num
  have hord3 : orderOf ((g : PGU6) ^ 3) = 7 := (Nat.Coprime.orderOf_pow hcop).trans hgo
  have hmk7 : (QuotientGroup.mk ((g' ^ 3) ^ 7 : Gu) : PGU6) = 1 := by
    rw [QuotientGroup.mk_pow, hmk3]
    have h := pow_orderOf_eq_one ((g : PGU6) ^ 3)
    rwa [hord3] at h
  obtain ⟨d, hd⟩ := mem_ZG.1 ((QuotientGroup.eq_one_iff _).1 hmk7)
  have hd' : ((g' : GL (Fin 6) F4) ^ 3) ^ 7 = Matrix.GeneralLinearGroup.scalar (Fin 6) d := by
    rw [hd]
    simp only [Subgroup.coe_pow]
  have hdcube : (d⁻¹ : F4ˣ) ^ 3 = 1 := by
    rw [inv_pow, units_cube, inv_one]
  have hYcomm : Commute (Matrix.GeneralLinearGroup.scalar (Fin 6) d⁻¹) ((g' : GL (Fin 6) F4) ^ 3) :=
    (scalar_comm d⁻¹ _).symm
  have hdinv7 : (d⁻¹ : F4ˣ) ^ 7 * d = 1 := by
    calc (d⁻¹ : F4ˣ) ^ 7 * d = ((d⁻¹ : F4ˣ) ^ 3) ^ 2 * (d⁻¹ * d) := by group
      _ = 1 := by rw [hdcube, one_pow, one_mul, inv_mul_cancel]
  have hY7 : (Matrix.GeneralLinearGroup.scalar (Fin 6) d⁻¹ * (g' : GL (Fin 6) F4) ^ 3) ^ 7 = 1 := by
    rw [hYcomm.mul_pow, hd', ← map_pow, ← map_mul, hdinv7, map_one]
  have hYne : Matrix.GeneralLinearGroup.scalar (Fin 6) d⁻¹ * (g' : GL (Fin 6) F4) ^ 3 ≠ 1 := by
    intro hY1
    have hH3 : (g' : GL (Fin 6) F4) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) d := by
      calc (g' : GL (Fin 6) F4) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) d *
            (Matrix.GeneralLinearGroup.scalar (Fin 6) d⁻¹ * (g' : GL (Fin 6) F4) ^ 3) := by
            rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
        _ = Matrix.GeneralLinearGroup.scalar (Fin 6) d := by rw [hY1, mul_one]
    have hmem : (g' ^ 3 : Gu) ∈ ZG := mem_ZG.2 ⟨d, by rw [Subgroup.coe_pow]; exact hH3.symm⟩
    have h1 : (QuotientGroup.mk (g' ^ 3 : Gu) : PGU6) = 1 := (QuotientGroup.eq_one_iff _).2 hmem
    rw [hmk3] at h1
    rw [h1, orderOf_one] at hord3
    norm_num at hord3
  set Y : GL (Fin 6) F4 := Matrix.GeneralLinearGroup.scalar (Fin 6) d⁻¹ * (g' : GL (Fin 6) F4) ^ 3 with hYdef
  have hYB : Commute Y (B : GL (Fin 6) F4) := by
    have h1 : Commute (B : GL (Fin 6) F4) (Matrix.GeneralLinearGroup.scalar (Fin 6) d⁻¹) :=
      scalar_comm d⁻¹ (B : GL (Fin 6) F4)
    have h2 : Commute (B : GL (Fin 6) F4) ((g' : GL (Fin 6) F4) ^ 3) := hH
    exact (h1.mul_right h2).symm
  have hHU : (((g' : GL (Fin 6) F4) ^ 3 : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
      (((g' ^ 3 : Gu) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) := by
    rw [Subgroup.coe_pow]
  have hHiso : ∀ a b : Fin 6 → F4,
      herm2 ((((g' : GL (Fin 6) F4) ^ 3 : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ a)
        ((((g' : GL (Fin 6) F4) ^ 3 : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ b) = herm2 a b := by
    intro a b
    apply herm2_unitary
    have h := gu_mat_unitary (g' ^ 3)
    rw [Subgroup.coe_pow] at h
    exact h
  have hc3 : ((d⁻¹ : F4ˣ) : F4) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hdcube, Units.val_one]
  have hYv : ∀ a : Fin 6 → F4,
      ((Y : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ a =
        ((d⁻¹ : F4ˣ) : F4) • ((((g' : GL (Fin 6) F4) ^ 3 : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ a) := by
    intro a
    rw [hYdef, Units.val_mul, coe_scalar_eq, smul_mul_assoc, one_mul, Matrix.smul_mulVec]
  have hYiso : ∀ a b : Fin 6 → F4,
      herm2 (((Y : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ a)
        (((Y : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ b) = herm2 a b := by
    intro a b
    rw [hYv a, hYv b, herm2_smul_left, herm2_smul_right, hHiso a b]
    linear_combination (herm2 a b) * hc3
  have hYB' : Commute ((Y : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)
      ((B : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) := by
    have h := congrArg Units.val hYB.eq
    rw [Units.val_mul, Units.val_mul] at h
    exact h
  have hY7' : ((Y : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) ^ 7 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hY7, Units.val_one]
  have hB3m : ((B : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hB3, Units.val_one]
  have hBns : ∀ c : F4, ((B : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) ≠ c • 1 := by
    intro c hcB
    have hc3' : c ^ 3 = 1 := by
      have h := hB3m
      rw [hcB, smul_pow, one_pow] at h
      have h00 := congrFun (congrFun h 0) 0
      simpa using h00
    have hc0 : c ≠ 0 := by
      intro h0
      rw [h0] at hc3'
      norm_num at hc3'
    apply hBne
    rw [QuotientGroup.eq_one_iff, mem_ZG]
    refine ⟨Units.mk0 c hc0, ?_⟩
    apply Units.ext
    rw [coe_scalar_eq, Units.val_mk0, hcB]
  have hMat := eq_one_of_isometry_commute F4_omega_pow_three F4_omega_ne_one F4_pow_four
    (gu_mat_unitary B) hB3m hBns hYiso hY7' hYB'
  apply hYne
  exact Units.ext (by rw [hMat, Units.val_one])

end CFSG.LocalAnalysis.GLTheoremA.KU6Cent

end
