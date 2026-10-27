module

public import CFSG.HardMathSupport.Dickson.Sec6.HeisAux.Switch

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.Heis

open Matrix CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54Ns CFSG.RankThree.PartTwo.KFacts
  CFSG.Quasithin.A318P CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.HardMathSupport.Solomon.LocalBalance.AutL3
  CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3

theorem charP_two_of_card {K : Type} [Field K] [Finite K] (hK : Nat.card K = 64) : CharP K 2 := by
  haveI : Fintype K := Fintype.ofFinite K
  have hp : CharP K (ringChar K) := ringChar.charP K
  obtain ⟨n, hpr, hcard⟩ := FiniteField.card K (ringChar K)
  have hK' : Fintype.card K = 64 := by rw [← Nat.card_eq_fintype_card]; exact hK
  rw [hK'] at hcard
  have hdvd : ringChar K ∣ 2 ^ 6 := by
    rw [show (2 : ℕ) ^ 6 = 64 by norm_num, hcard]
    exact dvd_pow_self _ n.ne_zero
  have h2 : ringChar K = 2 :=
    (Nat.prime_dvd_prime_iff_eq hpr Nat.prime_two).1 (hpr.dvd_of_dvd_pow hdvd)
  rw [h2] at hp
  exact hp

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K}

theorem exists_scalar_cube (u : GL (Fin 3) K)
    (h : LinearFlag.conjAut 3 K u ^ 3 = 1) :
    ∃ t : K, (u : Matrix (Fin 3) (Fin 3) K) ^ 3 = t • (1 : Matrix (Fin 3) (Fin 3) K) := by
  obtain ⟨c, hc⟩ := (conjAut_eq_one_iff_scalar (u ^ 3)).1 (by rw [map_pow, h])
  refine ⟨(c : K), ?_⟩
  have := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) hc
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Units.val_pow_eq_pow_val]
    at this
  rw [← this]
  ext i j
  simp [Matrix.diagonal_apply, Matrix.one_apply]

theorem exists_rational_lift (hσ : orderOf σ = 3) {A : Subgroup (MulAut (projectiveSL 3 K))}
    (hAel : IsElemAbelian 3 A) (hf : LinearFlag.fieldAut 3 K σ ∈ A) (g : GL (Fin 3) K)
    (hg : LinearFlag.conjAut 3 K g ∈ A) :
    ∃ (u : GL (Fin 3) K) (μ : K), μ ≠ 0 ∧ RatGL σ u ∧ LinearFlag.conjAut 3 K u ∈ A ∧
      (u : Matrix (Fin 3) (Fin 3) K) = μ • (g : Matrix (Fin 3) (Fin 3) K) := by
  have hcomm : LinearFlag.conjAut 3 K g * LinearFlag.fieldAut 3 K σ =
      LinearFlag.fieldAut 3 K σ * LinearFlag.conjAut 3 K g := by
    have := hAel.1.is_comm.comm ⟨LinearFlag.conjAut 3 K g, hg⟩ ⟨LinearFlag.fieldAut 3 K σ, hf⟩
    simpa using congrArg Subtype.val this
  obtain ⟨μ, hμ0, hμ⟩ := exists_scalar_fixed hσ g hcomm
  refine ⟨g * GeneralLinearGroup.scalar (Fin 3) (Units.mk0 μ hμ0), μ, hμ0, ?_, ?_, ?_⟩
  · intro i j
    rw [bgll_coe_mul_scalar]
    simpa using hμ i j
  · rw [map_mul, conjAut_scalar, mul_one]
    exact hg
  · rw [bgll_coe_mul_scalar]
    rfl

theorem fixed_cube [CharP K 2] {ω : K} (hK : Nat.card K = 64) (hσ : orderOf σ = 3)
    (hω : ω ^ 2 + ω + 1 = 0) (hσω : σ ω = ω) {x : K} (hx0 : x ≠ 0) (hxσ : σ x = x) :
    x ^ 3 = 1 := by
  obtain ⟨b, hb⟩ := exists_ev_of_fixed hK hσ hω hσω hxσ
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hx0 (by rw [← hb]; rfl)
  rw [← hb]
  exact ev_cube hω b hb0

theorem scalar_cube_data [CharP K 2] {ω : K} (hK : Nat.card K = 64) (hσ : orderOf σ = 3)
    (hω : ω ^ 2 + ω + 1 = 0) (hσω : σ ω = ω) {A : Subgroup (MulAut (projectiveSL 3 K))}
    (hAel : IsElemAbelian 3 A) {u : GL (Fin 3) K} (hr : RatGL σ u)
    (hc : LinearFlag.conjAut 3 K u ∈ A) :
    ∃ t : K, (u : Matrix (Fin 3) (Fin 3) K) ^ 3 = t • (1 : Matrix (Fin 3) (Fin 3) K) ∧
      t ^ 3 = 1 ∧ σ t = t := by
  obtain ⟨t, ht⟩ := exists_scalar_cube u (hAel.2 _ hc)
  have ht0 : t ≠ 0 := by
    intro h0
    have hu : IsUnit ((u : Matrix (Fin 3) (Fin 3) K) ^ 3) := u.isUnit.pow 3
    rw [ht, h0, zero_smul] at hu
    exact not_isUnit_zero hu
  have htσ : σ t = t := by
    have := (hr.pow 3) 0 0
    rw [Units.val_pow_eq_pow_val, ht] at this
    simpa using this
  exact ⟨t, ht, fixed_cube hK hσ hω hσω ht0 htσ, htσ⟩

theorem heis_gen_of_field [CharP K 2] (hK : Nat.card K = 64) (hσ : orderOf σ = 3)
    {A : Subgroup (MulAut (projectiveSL 3 K))} (hAel : IsElemAbelian 3 A) (hA27 : Nat.card A = 27)
    (hf : LinearFlag.fieldAut 3 K σ ∈ A) (hL : ¬ LiftsCommute A) : GenP A := by
  have h2 : (2 : K) = 0 := two_eq_zero_K
  have h3 : 3 ∣ Nat.card K - 1 := by rw [hK]; norm_num
  obtain ⟨ω, hω3, hω1⟩ := exists_cube_root_of_unity h3
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hσω : σ ω = ω := ringEquiv_fix_cube_root hσ3 hω3 hω1
  have hω : ω ^ 2 + ω + 1 = 0 := by
    have : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination hω3
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hω1)
  simp only [LiftsCommute, not_forall] at hL
  obtain ⟨g, g', hg, hg', hne⟩ := hL
  obtain ⟨u1, μ1, hμ1, hr1, hc1, hu1⟩ := exists_rational_lift hσ hAel hf g hg
  obtain ⟨u2, μ2, hμ2, hr2, hc2, hu2⟩ := exists_rational_lift hσ hAel hf g' hg'
  have hcc : LinearFlag.conjAut 3 K u1 * LinearFlag.conjAut 3 K u2 =
      LinearFlag.conjAut 3 K u2 * LinearFlag.conjAut 3 K u1 := by
    have := hAel.1.is_comm.comm ⟨_, hc1⟩ ⟨_, hc2⟩
    simpa using congrArg Subtype.val this
  obtain ⟨c, hc⟩ := (conjAut_eq_one_iff_scalar (u1 * u2 * (u2 * u1)⁻¹)).1
    (by rw [map_mul, map_mul, map_inv, map_mul, hcc]; group)
  have hu12gl : u1 * u2 = GeneralLinearGroup.scalar (Fin 3) c * (u2 * u1) := by
    rw [hc]; group
  have hu12 : (u1 : Matrix (Fin 3) (Fin 3) K) * u2 = (c : K) • ((u2 : Matrix (Fin 3) (Fin 3) K) * u1) := by
    have := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) hu12gl
    simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at this
    rw [this, Matrix.smul_eq_diagonal_mul]
  have hcrat : RatGL σ (GeneralLinearGroup.scalar (Fin 3) c) := by
    rw [hc]
    exact (hr1.mul hr2).mul (hr2.mul hr1).inv
  have hcσ : σ (c : K) = c := by
    have := hcrat 0 0
    simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using this
  have hc1' : (c : K) ≠ 1 := by
    intro h1
    apply hne
    apply Units.ext
    have e : (u1 : Matrix (Fin 3) (Fin 3) K) * u2 = (u2 : Matrix (Fin 3) (Fin 3) K) * u1 := by
      rw [hu12, h1, one_smul]
    have e1 : (u1 : Matrix (Fin 3) (Fin 3) K) * u2 =
        (μ1 * μ2) • ((g : Matrix (Fin 3) (Fin 3) K) * g') := by
      rw [hu1, hu2, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have e2 : (u2 : Matrix (Fin 3) (Fin 3) K) * u1 =
        (μ1 * μ2) • ((g' : Matrix (Fin 3) (Fin 3) K) * g) := by
      rw [hu1, hu2, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm μ2 μ1]
    rw [Units.val_mul, Units.val_mul]
    have hμ : μ1 * μ2 ≠ 0 := mul_ne_zero hμ1 hμ2
    have e' : (μ1 * μ2) • ((g : Matrix (Fin 3) (Fin 3) K) * g') =
        (μ1 * μ2) • ((g' : Matrix (Fin 3) (Fin 3) K) * g) := by rw [← e1, ← e2, e]
    exact smul_right_injective _ hμ e'
  have hz3 : (c : K) ^ 3 = 1 := fixed_cube hK hσ hω hσω c.ne_zero hcσ
  have hz : (c : K) ^ 2 + (c : K) + 1 = 0 := cube_root_nontrivial hz3 hc1'
  obtain ⟨t1, ht1, ht1c, ht1σ⟩ := scalar_cube_data hK hσ hω hσω hAel hr1 hc1
  obtain ⟨t2, ht2, ht2c, ht2σ⟩ := scalar_cube_data hK hσ hω hσω hAel hr2 hc2
  exact pair_gen hK hσ hω hσω hAel hA27 hf
    (fun u0 u1 z hr0 hr1 hc0 hc1 hz hzσ hcomm h30 h31 =>
      switch_gen hK hσ hω hσω hAel hA27 hf u0 u1 z hr0 hr1 hc0 hc1 hz hzσ hcomm h30 h31)
    u1 u2 hr1 hr2 hc1 hc2 (c : K) hz hcσ hu12 t1 t2 ht1 ht2 ht1c ht2c ht1σ ht2σ

end CFSG.HardMathSupport.Dickson.Sec6.Heis
