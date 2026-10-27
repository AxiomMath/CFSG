module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA4UKern

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KC3

open CFSG.Open CFSG.Open.StatedAPI

noncomputable section

theorem not_three_dvd_of_sq_one {G : Type} [Group G] [Finite G] (h : ∀ x : G, x ^ 2 = 1) :
    ¬ 3 ∣ Nat.card G := by
  intro hdvd
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := G) 3 hdvd
  have h2 := h x
  have h3 : x ^ 3 = 1 := by
    rw [← hx]
    exact pow_orderOf_eq_one x
  have h1 : x = 1 := by
    calc x = x ^ 3 * (x ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, h2, inv_one, mul_one]
  rw [h1, orderOf_one] at hx
  exact absurd hx (by norm_num)

theorem three_not_dvd_card_of_char {K : Type} [Field K] [Finite K] (h3 : (3 : K) ≠ 0) :
    ¬ 3 ∣ Nat.card K := by
  intro hdvd
  haveI := Fintype.ofFinite K
  haveI : Fact (Nat.Prime (ringChar K)) := ⟨CharP.char_is_prime K (ringChar K)⟩
  obtain ⟨n, hp, hcard⟩ := FiniteField.card K (ringChar K)
  rw [Nat.card_eq_fintype_card, hcard] at hdvd
  have h3p : 3 ∣ ringChar K := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
  have heq : 3 = ringChar K := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h3p
  apply h3
  have hc : ((3 : ℕ) : K) = 0 := by
    rw [heq]
    exact ringChar.spec K (ringChar K) |> fun _ => CharP.cast_eq_zero K (ringChar K)
  simpa using hc

theorem three_dvd_card_SL2_quot (K : Type) [Field K] [Finite K] (h3 : (3 : K) ≠ 0) :
    3 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) K ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) := by
  have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) =
      Nat.card K * (Nat.card K ^ 2 - 1) := by
    rw [← card_statedSL 2 K, card_statedSL_two]
  have hq : ¬ 3 ∣ Nat.card K := three_not_dvd_card_of_char h3
  have hq2 : Nat.card K ^ 2 % 3 = 1 := by
    have h1 : Nat.card K % 3 = 1 ∨ Nat.card K % 3 = 2 := by omega
    rw [Nat.pow_mod]
    rcases h1 with h1 | h1 <;> rw [h1]
  have h3sq : 3 ∣ Nat.card K ^ 2 - 1 := by
    have : 1 ≤ Nat.card K ^ 2 := Nat.one_le_pow _ _ (Nat.card_pos)
    omega
  have hdvd : 3 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) := by
    rw [hSL]
    exact Dvd.dvd.mul_left h3sq _
  have hZ : ¬ 3 ∣ Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) := by
    apply not_three_dvd_of_sq_one
    intro x
    apply Subtype.ext
    rw [Subgroup.coe_pow, OneMemClass.coe_one]
    exact sq_eq_one_of_mem_center_SL2 K x.2
  have hsplit := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))
  rw [hsplit] at hdvd
  rcases (Nat.Prime.dvd_mul Nat.prime_three).1 hdvd with h | h
  · exact h
  · exact absurd h hZ

theorem ker_mk_scalar {K : Type} [Field K] (x : StatedSp 3 K)
    (hx : (QuotientGroup.mk x : StatedProj (StatedSp 3 K)) = 1) :
    ∃ c : Kˣ, (x : GL (Fin 3 ⊕ Fin 3) K) = Matrix.GeneralLinearGroup.scalar (Fin 3 ⊕ Fin 3) c := by
  have hx' : x ∈ (StatedScalars (Fin 3 ⊕ Fin 3) K).subgroupOf (StatedSp 3 K) := by
    rw [← QuotientGroup.ker_mk' ((StatedScalars (Fin 3 ⊕ Fin 3) K).subgroupOf (StatedSp 3 K))]
    exact hx
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hx'
  obtain ⟨c, hc⟩ := hx'
  exact ⟨c, hc.symm⟩

theorem scalar_eq_one_iff {K : Type} [Field K] (c : Kˣ)
    (h : Matrix.GeneralLinearGroup.scalar (Fin 3 ⊕ Fin 3) c = 1) : c = 1 := by
  have := congrArg (fun g : GL (Fin 3 ⊕ Fin 3) K => (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K)
    (Sum.inl 0) (Sum.inl 0)) h
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
    Units.val_one, Matrix.one_apply_eq] at this
  exact Units.ext this

theorem commute_of_mk_commute {K : Type} [Field K] {x y : StatedSp 3 K} (hy : y ^ 3 = 1)
    (hxy : (QuotientGroup.mk x : StatedProj (StatedSp 3 K)) * QuotientGroup.mk y =
      QuotientGroup.mk y * QuotientGroup.mk x) : x * y = y * x := by
  have hwk : (QuotientGroup.mk (x * y * x⁻¹ * y⁻¹) : StatedProj (StatedSp 3 K)) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv, hxy]
    group
  obtain ⟨c, hc⟩ := ker_mk_scalar (x * y * x⁻¹ * y⁻¹) hwk
  have hc2 : c ^ 2 = 1 := by
    have hcS : Matrix.GeneralLinearGroup.scalar (Fin 3 ⊕ Fin 3) c ∈ StatedSp 3 K := by
      rw [← hc]
      exact (x * y * x⁻¹ * y⁻¹).2
    exact (scalar_mem_statedSp_iff (K := K) (by norm_num) c).1 hcS
  set xg : GL (Fin 3 ⊕ Fin 3) K := (x : GL (Fin 3 ⊕ Fin 3) K) with hxg
  set yg : GL (Fin 3 ⊕ Fin 3) K := (y : GL (Fin 3 ⊕ Fin 3) K) with hyg
  set S : GL (Fin 3 ⊕ Fin 3) K := Matrix.GeneralLinearGroup.scalar (Fin 3 ⊕ Fin 3) c with hS
  have hcen : S ∈ Subgroup.center (GL (Fin 3 ⊕ Fin 3) K) := by
    rw [← statedScalars_eq_center]
    exact ⟨c, rfl⟩
  have hcomm : Commute S yg := (Subgroup.mem_center_iff.1 hcen yg).symm
  have hc' : xg * yg * xg⁻¹ * yg⁻¹ = S := by
    have h := hc
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
    exact h
  have h2 : xg * yg * xg⁻¹ = S * yg := by
    rw [← hc', inv_mul_cancel_right]
  have hyg3 : yg ^ 3 = 1 := by
    rw [hyg, ← Subgroup.coe_pow, hy, OneMemClass.coe_one]
  have hcube : (x * y * x⁻¹) ^ 3 = (1 : StatedSp 3 K) := by
    rw [conj_pow, hy, mul_one, mul_inv_cancel]
  have hcube' : (xg * yg * xg⁻¹) ^ 3 = 1 := by
    have h := congrArg (fun g : StatedSp 3 K => (g : GL (Fin 3 ⊕ Fin 3) K)) hcube
    simpa [hxg, hyg, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow] using h
  rw [h2, hcomm.mul_pow, hyg3, mul_one] at hcube'
  have hc3 : c ^ 3 = 1 := scalar_eq_one_iff (c ^ 3) (by rw [map_pow, ← hS]; exact hcube')
  have hc1 : c = 1 := by
    calc c = c ^ 3 * (c ^ 2)⁻¹ := by group
      _ = 1 := by rw [hc3, hc2, inv_one, mul_one]
  have hS1 : S = 1 := by
    rw [hS, hc1, map_one]
  rw [hS1, one_mul] at h2
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  calc xg * yg = xg * yg * xg⁻¹ * xg := by rw [inv_mul_cancel_right]
    _ = yg * xg := by rw [h2]

end

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KC3

end
