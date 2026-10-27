module

public import CFSG.HardMathSupport.Dickson.Sec6.HeisAux.Pair

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.Heis

open Matrix CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54Ns CFSG.RankThree.PartTwo.KFacts
  CFSG.Quasithin.A318P CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.HardMathSupport.Solomon.LocalBalance.AutL3
  CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3

variable {K : Type} [Field K] [CharP K 2] [Finite K] {ω : K} {σ : K ≃+* K}

theorem ratGL_iff (g : GL (Fin 3) K) :
    RatGL σ g ↔ GeneralLinearGroup.map (σ : K →+* K) g = g := by
  constructor
  · intro h
    apply Units.ext
    ext i j
    exact h i j
  · intro h i j
    exact congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K) i j) h

theorem iterMat_three_of_rat (hσ : orderOf σ = 3) {B : Matrix (Fin 3) (Fin 3) K}
    (hB : B.map σ = B) (h3 : B ^ 3 = 1) :
    CFSG.Quasithin.SteinbergCB.GDescent.iterMat σ B 3 = 1 := by
  have key : ∀ n, CFSG.Quasithin.SteinbergCB.GDescent.iterMat σ B n = B ^ n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [CFSG.Quasithin.SteinbergCB.GDescent.iterMat_succ, ih, pow_succ']
      congr 1
      have : (B ^ n).map σ = (B.map σ) ^ n := by
        have := map_pow (RingHom.mapMatrix (σ : K →+* K)) B n
        simpa [RingHom.mapMatrix_apply] using this
      rw [this, hB]
  rw [key, h3]

theorem switch_gen (hK : Nat.card K = 64) (hσ : orderOf σ = 3) (hω : ω ^ 2 + ω + 1 = 0)
    (hσω : σ ω = ω) {A : Subgroup (MulAut (projectiveSL 3 K))} (hAel : IsElemAbelian 3 A)
    (hA27 : Nat.card A = 27) (hf : LinearFlag.fieldAut 3 K σ ∈ A) (u0 u1 : GL (Fin 3) K) (z : K)
    (hr0 : RatGL σ u0) (hr1 : RatGL σ u1) (hc0 : LinearFlag.conjAut 3 K u0 ∈ A)
    (hc1 : LinearFlag.conjAut 3 K u1 ∈ A) (hz : z ^ 2 + z + 1 = 0) (hzσ : σ z = z)
    (hcomm : (u0 : Matrix (Fin 3) (Fin 3) K) * u1 = z • ((u1 : Matrix (Fin 3) (Fin 3) K) * u0))
    (h30 : (u0 : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1)
    (h31 : (u1 : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1) : GenP A := by
  have h2 : (2 : K) = 0 := two_eq_zero_K
  have hz3 : z ^ 3 = 1 := by linear_combination (z - 1) * hz
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  have hz1 : z ≠ 1 := fun h => by
    rw [h] at hz
    have : (1 : K) = 0 := by linear_combination hz - h2
    exact one_ne_zero this
  have hu0map : GeneralLinearGroup.map (σ : K →+* K) u0 = u0 := (ratGL_iff u0).1 hr0
  have hu0mat : (u0 : Matrix (Fin 3) (Fin 3) K).map σ = u0 :=
    congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) hu0map
  obtain ⟨κ, hκu, hκ⟩ := bgll_exists_fixed_basis σ hσ (by norm_num)
    (B := (u0 : Matrix (Fin 3) (Fin 3) K)) u0.isUnit (iterMat_three_of_rat hσ hu0mat h30)
  let κg : GL (Fin 3) K := hκu.unit
  have hκg : (κg : Matrix (Fin 3) (Fin 3) K) = κ := rfl
  have hκeq : u0 * GeneralLinearGroup.map (σ : K →+* K) κg = κg := by
    apply Units.ext
    rw [Units.val_mul, hκg]
    exact hκ
  have hMκ : GeneralLinearGroup.map (σ : K →+* K) κg = u0⁻¹ * κg := by
    rw [eq_inv_mul_iff_mul_eq]
    exact hκeq
  obtain ⟨lam, hlam0, hlam⟩ := hilbert90_three hσ hz0 (by rw [hzσ, hzσ]; linear_combination hz3)
  have hu1map : GeneralLinearGroup.map (σ : K →+* K) u1 = u1 := (ratGL_iff u1).1 hr1
  set g0 : GL (Fin 3) K := κg⁻¹ * u0 * κg with hg0def
  set G : GL (Fin 3) K := κg⁻¹ * u1 * κg with hGdef
  set g1 : GL (Fin 3) K := G * GeneralLinearGroup.scalar (Fin 3) (Units.mk0 lam hlam0) with hg1def
  have hg0rat : RatGL σ g0 := by
    rw [ratGL_iff]
    simp only [hg0def, map_mul, map_inv, hMκ, hu0map]
    group
  have hconjmat : ((u0 * u1 * u0⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      z • (u1 : Matrix (Fin 3) (Fin 3) K) := by
    rw [Units.val_mul, Units.val_mul, hcomm, Matrix.smul_mul, mul_assoc, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, mul_one]
  have hMG : ((GeneralLinearGroup.map (σ : K →+* K) G : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      z • (G : Matrix (Fin 3) (Fin 3) K) := by
    have : GeneralLinearGroup.map (σ : K →+* K) G = κg⁻¹ * (u0 * u1 * u0⁻¹) * κg := by
      simp only [hGdef, map_mul, map_inv, hMκ, hu1map]
      group
    rw [this, Units.val_mul, Units.val_mul, hconjmat]
    simp only [hGdef, Units.val_mul, Matrix.mul_smul, Matrix.smul_mul]
  have hg1mat : (g1 : Matrix (Fin 3) (Fin 3) K) = lam • (G : Matrix (Fin 3) (Fin 3) K) := by
    rw [hg1def, bgll_coe_mul_scalar]
    rfl
  have hg1rat : RatGL σ g1 := by
    intro i j
    have e : σ ((G : Matrix (Fin 3) (Fin 3) K) i j) = z * (G : Matrix (Fin 3) (Fin 3) K) i j :=
      congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M i j) hMG
    rw [hg1mat]
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul]
    rw [e]
    linear_combination ((G : Matrix (Fin 3) (Fin 3) K) i j) * hlam
  have hu0gl3 : u0 ^ 3 = 1 := Units.ext (by simpa [Units.val_pow_eq_pow_val] using h30)
  have hu1gl3 : u1 ^ 3 = 1 := Units.ext (by simpa [Units.val_pow_eq_pow_val] using h31)
  have hg0gl3 : g0 ^ 3 = 1 := by
    have := conj_pow (a := κg⁻¹) (b := u0) (i := 3)
    rw [inv_inv] at this
    rw [hg0def, this, hu0gl3]
    group
  have hGgl3 : G ^ 3 = 1 := by
    have := conj_pow (a := κg⁻¹) (b := u1) (i := 3)
    rw [inv_inv] at this
    rw [hGdef, this, hu1gl3]
    group
  have hg0cube : (g0 : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
    have := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) hg0gl3
    simpa [Units.val_pow_eq_pow_val] using this
  have hGcube : (G : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
    have := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) hGgl3
    simpa [Units.val_pow_eq_pow_val] using this
  have hg1cube : (g1 : Matrix (Fin 3) (Fin 3) K) ^ 3 = (lam ^ 3) • (1 : Matrix (Fin 3) (Fin 3) K) := by
    rw [hg1mat, smul_pow, hGcube]
  have hg0G : (g0 : Matrix (Fin 3) (Fin 3) K) * (G : Matrix (Fin 3) (Fin 3) K) =
      z • ((G : Matrix (Fin 3) (Fin 3) K) * (g0 : Matrix (Fin 3) (Fin 3) K)) := by
    have e1 : g0 * G = κg⁻¹ * (u0 * u1) * κg := by simp only [hg0def, hGdef]; group
    have e2 : G * g0 = κg⁻¹ * (u1 * u0) * κg := by simp only [hg0def, hGdef]; group
    rw [← Units.val_mul, ← Units.val_mul, e1, e2]
    simp only [Units.val_mul]
    rw [hcomm]
    simp only [Matrix.smul_mul, Matrix.mul_smul]
  have hcomm' : (g0 : Matrix (Fin 3) (Fin 3) K) * (g1 : Matrix (Fin 3) (Fin 3) K) =
      z • ((g1 : Matrix (Fin 3) (Fin 3) K) * (g0 : Matrix (Fin 3) (Fin 3) K)) := by
    rw [hg1mat, Matrix.mul_smul, hg0G, Matrix.smul_mul, smul_comm]
  set τ : MulAut (projectiveSL 3 K) := (LinearFlag.conjAut 3 K κg)⁻¹ with hτ
  set A' : Subgroup (MulAut (projectiveSL 3 K)) := A.map (MulAut.conj τ).toMonoidHom with hA'
  have hf' : LinearFlag.fieldAut 3 K σ ∈ A' := by
    refine ⟨LinearFlag.conjAut 3 K u0 * LinearFlag.fieldAut 3 K σ, A.mul_mem hc0 hf, ?_⟩
    show τ * (LinearFlag.conjAut 3 K u0 * LinearFlag.fieldAut 3 K σ) * τ⁻¹ =
      LinearFlag.fieldAut 3 K σ
    have hfc : LinearFlag.fieldAut 3 K σ * LinearFlag.conjAut 3 K κg =
        LinearFlag.conjAut 3 K (u0⁻¹ * κg) * LinearFlag.fieldAut 3 K σ := by
      have := conjAut_mul_fieldAut_mul (n := 3) (K := K) 1 κg σ 1
      rw [map_one, one_mul, map_one, mul_one, one_mul, mul_one, hMκ] at this
      exact this
    calc τ * (LinearFlag.conjAut 3 K u0 * LinearFlag.fieldAut 3 K σ) * τ⁻¹
        = (LinearFlag.conjAut 3 K κg)⁻¹ * LinearFlag.conjAut 3 K u0 *
          (LinearFlag.fieldAut 3 K σ * LinearFlag.conjAut 3 K κg) := by rw [hτ, inv_inv]; group
      _ = LinearFlag.fieldAut 3 K σ := by
        rw [hfc, map_mul, map_inv]
        group
  have hcj : ∀ g : GL (Fin 3) K, LinearFlag.conjAut 3 K g ∈ A →
      LinearFlag.conjAut 3 K (κg⁻¹ * g * κg) ∈ A' := by
    intro g hg
    refine ⟨LinearFlag.conjAut 3 K g, hg, ?_⟩
    show τ * LinearFlag.conjAut 3 K g * τ⁻¹ = _
    rw [hτ, inv_inv, map_mul, map_mul, map_inv]
  have hd : LinearFlag.conjAut 3 K g0 ∈ A' := hcj u0 hc0
  have hC : LinearFlag.conjAut 3 K g1 ∈ A' := by
    have : LinearFlag.conjAut 3 K g1 = LinearFlag.conjAut 3 K G := by
      rw [hg1def, map_mul, conjAut_scalar, mul_one]
    rw [this]
    exact hcj u1 hc1
  have hσlam : σ lam = z ^ 2 * lam := by
    linear_combination (-(σ lam)) * hz3 + z ^ 2 * hlam
  have hlam3σ : σ (lam ^ 3) = lam ^ 3 := by
    rw [map_pow, hσlam, mul_pow, ← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, hz3, one_pow,
      one_mul]
  have hlam30 : lam ^ 3 ≠ 0 := pow_ne_zero 3 hlam0
  have hμ3 : (lam ^ 3) ^ 3 = 1 := by
    obtain ⟨b, hb⟩ := exists_ev_of_fixed hK hσ hω hσω hlam3σ
    have hb0 : b ≠ 0 := by
      rintro rfl
      exact hlam30 (by rw [← hb]; rfl)
    rw [← hb]
    exact ev_cube hω b hb0
  have hμ1 : lam ^ 3 ≠ 1 := by
    intro hl3
    have hfix : σ lam = lam := by
      by_cases hl1 : lam = 1
      · rw [hl1, map_one]
      · obtain ⟨c, -, hcl⟩ := exists_good_code hω (cube_root_nontrivial hl3 hl1)
        rw [← hcl]
        exact ev_fixed hσω c
    apply hz1
    rw [hfix] at hlam
    exact mul_right_cancel₀ hlam0 (by rw [one_mul]; exact hlam)
  have hcard : Nat.card A' = 27 := by
    rw [hA', Subgroup.card_map_of_injective (MulAut.conj τ).injective, hA27]
  exact GenP_of_conj τ A (good_gen hK hσ hω hσω (isElemAbelian_map _ hAel) hcard hf' z (lam ^ 3)
    hz hzσ (cube_root_nontrivial hμ3 hμ1) hlam3σ g0 g1 hg0rat hg1rat hg0cube hg1cube hcomm' hd hC)

end CFSG.HardMathSupport.Dickson.Sec6.Heis
