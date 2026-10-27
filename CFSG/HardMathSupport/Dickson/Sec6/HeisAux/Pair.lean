module

public import CFSG.HardMathSupport.Dickson.Sec6.HeisAux.Good

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.Heis

open Matrix CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54Ns CFSG.RankThree.PartTwo.KFacts
  CFSG.Quasithin.A318P CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.HardMathSupport.Solomon.LocalBalance.AutL3
  CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3

section Rat

variable {K : Type} [Field K] {σ : K ≃+* K}

@[expose] def RatGL (σ : K ≃+* K) (g : GL (Fin 3) K) : Prop :=
  ∀ i j, σ ((g : Matrix (Fin 3) (Fin 3) K) i j) = (g : Matrix (Fin 3) (Fin 3) K) i j

theorem RatGL.mul {g h : GL (Fin 3) K} (hg : RatGL σ g) (hh : RatGL σ h) : RatGL σ (g * h) := by
  intro i j
  simp only [Units.val_mul, Matrix.mul_apply, map_sum, map_mul]
  exact Finset.sum_congr rfl fun k _ => by rw [hg i k, hh k j]

theorem RatGL.inv {g : GL (Fin 3) K} (hg : RatGL σ g) : RatGL σ g⁻¹ := by
  have hmap : GeneralLinearGroup.map (σ : K →+* K) g = g := by
    apply Units.ext
    ext i j
    exact hg i j
  intro i j
  have := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K) i j)
    (show GeneralLinearGroup.map (σ : K →+* K) g⁻¹ = g⁻¹ by rw [map_inv, hmap])
  exact this

theorem RatGL.pow {g : GL (Fin 3) K} (hg : RatGL σ g) (n : ℕ) : RatGL σ (g ^ n) := by
  induction n with
  | zero =>
    intro i j
    simp only [pow_zero, Units.val_one]
    by_cases h : i = j
    · subst h; simp
    · simp [Matrix.one_apply_ne h]
  | succ n ih => rw [pow_succ]; exact ih.mul hg

end Rat

variable {K : Type} [Field K] [CharP K 2] [Finite K] {ω : K} {σ : K ≃+* K}

theorem cube_mul_comm {R : Type*} [Ring R] [Algebra K R] {X Y : R} {ζ : K} (hζ : ζ ^ 3 = 1)
    (h : X * Y = ζ • (Y * X)) : (X * Y) ^ 3 = X ^ 3 * Y ^ 3 := by
  have hba : Y * X = ζ ^ 2 • (X * Y) := by
    calc Y * X = (ζ ^ 3) • (Y * X) := by rw [hζ, one_smul]
      _ = ζ ^ 2 • (ζ • (Y * X)) := by rw [smul_smul, ← pow_succ]
      _ = ζ ^ 2 • (X * Y) := by rw [← h]
  have e1 : (X * Y) ^ 3 = X * (Y * X) * (Y * X) * Y := by noncomm_ring
  have e2 : X * (X * Y) * (X * Y) * Y = X * X * (Y * X) * Y * Y := by noncomm_ring
  have e3 : X * X * (X * Y) * Y * Y = X ^ 3 * Y ^ 3 := by noncomm_ring
  rw [e1, hba]
  simp only [mul_smul_comm, smul_mul_assoc, smul_smul]
  rw [e2, hba]
  simp only [mul_smul_comm, smul_mul_assoc, smul_smul]
  have h6 : ζ ^ 2 * ζ ^ 2 * ζ ^ 2 = 1 := by
    calc ζ ^ 2 * ζ ^ 2 * ζ ^ 2 = (ζ ^ 3) ^ 2 := by ring
      _ = 1 := by rw [hζ, one_pow]
  rw [e3, h6, one_smul]

theorem cube_root_nontrivial {t : K} (h3 : t ^ 3 = 1) (h1 : t ≠ 1) : t ^ 2 + t + 1 = 0 := by
  have : (t - 1) * (t ^ 2 + t + 1) = 0 := by linear_combination h3
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 h1)

theorem swap_comm {X Y : Matrix (Fin 3) (Fin 3) K} {z : K} (hz3 : z ^ 3 = 1)
    (h : X * Y = z • (Y * X)) : Y * X = z ^ 2 • (X * Y) := by
  calc Y * X = (z ^ 3) • (Y * X) := by rw [hz3, one_smul]
    _ = z ^ 2 • (z • (Y * X)) := by rw [smul_smul, ← pow_succ]
    _ = z ^ 2 • (X * Y) := by rw [← h]

theorem pair_gen_distinct (hK : Nat.card K = 64) (hσ : orderOf σ = 3) (hω : ω ^ 2 + ω + 1 = 0)
    (hσω : σ ω = ω) {A : Subgroup (MulAut (projectiveSL 3 K))} (hAel : IsElemAbelian 3 A)
    (hA27 : Nat.card A = 27) (hf : LinearFlag.fieldAut 3 K σ ∈ A)
    (u1 u2 : GL (Fin 3) K) (hr1 : RatGL σ u1) (hr2 : RatGL σ u2)
    (hc1 : LinearFlag.conjAut 3 K u1 ∈ A) (hc2 : LinearFlag.conjAut 3 K u2 ∈ A) (z : K)
    (hz : z ^ 2 + z + 1 = 0) (hzσ : σ z = z)
    (hcomm : (u1 : Matrix (Fin 3) (Fin 3) K) * u2 = z • ((u2 : Matrix (Fin 3) (Fin 3) K) * u1))
    (t1 t2 : K) (ht1 : (u1 : Matrix (Fin 3) (Fin 3) K) ^ 3 = t1 • (1 : Matrix (Fin 3) (Fin 3) K))
    (ht2 : (u2 : Matrix (Fin 3) (Fin 3) K) ^ 3 = t2 • (1 : Matrix (Fin 3) (Fin 3) K))
    (ht1c : t1 ^ 3 = 1) (ht2c : t2 ^ 3 = 1) (ht1σ : σ t1 = t1) (ht2σ : σ t2 = t2)
    (h1 : t1 ≠ 1) (h2 : t2 ≠ 1) (h12 : t1 ≠ t2) : GenP A := by
  have hz3 : z ^ 3 = 1 := by linear_combination (z - 1) * hz
  have ht1r := cube_root_nontrivial ht1c h1
  have ht2r := cube_root_nontrivial ht2c h2
  have ht12 : t1 * t2 = 1 := by
    have : (t1 - t2) * (t1 + t2 + 1) = 0 := by linear_combination ht1r - ht2r
    have h' := (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 h12)
    linear_combination t1 * h' - ht1r
  have hcomm' : (u2 : Matrix (Fin 3) (Fin 3) K) * u1 = z ^ 2 • ((u1 : Matrix (Fin 3) (Fin 3) K) * u2) :=
    swap_comm hz3 hcomm
  refine good_gen hK hσ hω hσω hAel hA27 hf (z ^ 2) t1 (by linear_combination (z ^ 2 - z + 1) * hz)
    (by rw [map_pow, hzσ]) ht1r ht1σ (u1 * u2) u1 (hr1.mul hr2) hr1 ?_ ht1 ?_ ?_ ?_
  ·
    rw [Units.val_mul, cube_mul_comm hz3 hcomm, ht1, ht2, smul_mul_smul_comm, one_mul, ht12, one_smul]
  ·
    rw [Units.val_mul, mul_assoc, hcomm', mul_smul_comm, ← mul_assoc]
  · rw [map_mul]
    exact A.mul_mem hc1 hc2
  · exact hc1

theorem pair_gen (hK : Nat.card K = 64) (hσ : orderOf σ = 3) (hω : ω ^ 2 + ω + 1 = 0)
    (hσω : σ ω = ω) {A : Subgroup (MulAut (projectiveSL 3 K))} (hAel : IsElemAbelian 3 A)
    (hA27 : Nat.card A = 27) (hf : LinearFlag.fieldAut 3 K σ ∈ A)
    (hsw : ∀ (u0 u1 : GL (Fin 3) K) (z : K), RatGL σ u0 → RatGL σ u1 →
      LinearFlag.conjAut 3 K u0 ∈ A → LinearFlag.conjAut 3 K u1 ∈ A → z ^ 2 + z + 1 = 0 → σ z = z →
      (u0 : Matrix (Fin 3) (Fin 3) K) * u1 = z • ((u1 : Matrix (Fin 3) (Fin 3) K) * u0) →
      (u0 : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 → (u1 : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 → GenP A)
    (u1 u2 : GL (Fin 3) K) (hr1 : RatGL σ u1) (hr2 : RatGL σ u2)
    (hc1 : LinearFlag.conjAut 3 K u1 ∈ A) (hc2 : LinearFlag.conjAut 3 K u2 ∈ A) (z : K)
    (hz : z ^ 2 + z + 1 = 0) (hzσ : σ z = z)
    (hcomm : (u1 : Matrix (Fin 3) (Fin 3) K) * u2 = z • ((u2 : Matrix (Fin 3) (Fin 3) K) * u1))
    (t1 t2 : K) (ht1 : (u1 : Matrix (Fin 3) (Fin 3) K) ^ 3 = t1 • (1 : Matrix (Fin 3) (Fin 3) K))
    (ht2 : (u2 : Matrix (Fin 3) (Fin 3) K) ^ 3 = t2 • (1 : Matrix (Fin 3) (Fin 3) K))
    (ht1c : t1 ^ 3 = 1) (ht2c : t2 ^ 3 = 1) (ht1σ : σ t1 = t1) (ht2σ : σ t2 = t2) : GenP A := by
  have hz3 : z ^ 3 = 1 := by linear_combination (z - 1) * hz
  by_cases h1 : t1 = 1
  · by_cases h2 : t2 = 1
    · subst h1 h2
      exact hsw u1 u2 z hr1 hr2 hc1 hc2 hz hzσ hcomm (by simpa using ht1) (by simpa using ht2)
    · subst h1
      exact good_gen hK hσ hω hσω hAel hA27 hf z t2 hz hzσ (cube_root_nontrivial ht2c h2) ht2σ
        u1 u2 hr1 hr2 (by simpa using ht1) ht2 hcomm hc1 hc2
  · by_cases h2 : t2 = 1
    · subst h2
      exact good_gen hK hσ hω hσω hAel hA27 hf (z ^ 2) t1 (by linear_combination (z ^ 2 - z + 1) * hz)
        (by rw [map_pow, hzσ]) (cube_root_nontrivial ht1c h1) ht1σ u2 u1 hr2 hr1 (by simpa using ht2)
        ht1 (swap_comm hz3 hcomm) hc2 hc1
    · by_cases h12 : t1 = t2
      · subst h12
        have hv : ((u2 * u2 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 =
            (t1 ^ 2) • (1 : Matrix (Fin 3) (Fin 3) K) := by
          have : ((u2 * u2 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 =
              (u2 : Matrix (Fin 3) (Fin 3) K) ^ 3 * (u2 : Matrix (Fin 3) (Fin 3) K) ^ 3 := by
            rw [Units.val_mul]; noncomm_ring
          rw [this, ht2, smul_mul_smul_comm, one_mul, pow_two]
        have ht0 : t1 ≠ 0 := by rintro rfl; simp at ht1c
        refine pair_gen_distinct hK hσ hω hσω hAel hA27 hf u1 (u2 * u2) hr1 (hr2.mul hr2) hc1
          (by rw [map_mul]; exact A.mul_mem hc2 hc2) (z ^ 2)
          (by linear_combination (z ^ 2 - z + 1) * hz) (by rw [map_pow, hzσ]) ?_ t1 (t1 ^ 2) ht1 hv
          ht1c (by rw [← pow_mul, mul_comm, pow_mul, ht1c, one_pow]) ht1σ (by rw [map_pow, ht1σ])
          h1 ?_ ?_
        · rw [Units.val_mul, ← mul_assoc, hcomm, smul_mul_assoc, mul_assoc, hcomm, mul_smul_comm,
            smul_smul, ← mul_assoc, ← pow_two]
        · intro h
          exact h2 (by linear_combination ht1c - t1 * h)
        · intro h
          apply h2
          have : t1 * (t1 - 1) = 0 := by linear_combination -h
          rcases mul_eq_zero.1 this with h' | h'
          · exact absurd h' ht0
          · linear_combination h'
      · exact pair_gen_distinct hK hσ hω hσω hAel hA27 hf u1 u2 hr1 hr2 hc1 hc2 z hz hzσ hcomm t1 t2
          ht1 ht2 ht1c ht2c ht1σ ht2σ h1 h2 h12

end CFSG.HardMathSupport.Dickson.Sec6.Heis
