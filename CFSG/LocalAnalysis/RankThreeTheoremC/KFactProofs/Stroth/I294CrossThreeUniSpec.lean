module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294ODUnitaryTorus

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

namespace CrossUni

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
open CFSG.LocalAnalysis.RankFourTheoremC.TorusU

section Spectral

variable {K : Type} [Field K] {σ : K ≃+* K} {n p : ℕ}

@[expose] def spec (ζ : K) (S : (Fin n → K) →ₗ[K] (Fin n → K)) (p i : ℕ) (w : Fin n → K) :
    Fin n → K :=
  (p : K)⁻¹ • ∑ j ∈ Finset.range p, ζ⁻¹ ^ (i * j) • (S ^ j) w

variable {ζ : K} {S : (Fin n → K) →ₗ[K] (Fin n → K)}

theorem S_spec (hζ : IsPrimitiveRoot ζ p) (hp : 0 < p) (hSp : S ^ p = 1) (i : ℕ)
    (w : Fin n → K) : S (spec ζ S p i w) = ζ ^ i • spec ζ S p i w := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne'
  set T : ℕ → Fin n → K := fun m => ζ⁻¹ ^ (i * m) • (S ^ m) w with hT
  have h1 : ∀ j, ζ⁻¹ ^ (i * j) • S ((S ^ j) w) = ζ ^ i • T (j + 1) := by
    intro j
    have e1 : S ((S ^ j) w) = (S ^ (j + 1)) w := by rw [pow_succ', Module.End.mul_apply]
    have e2 : ζ ^ i * ζ⁻¹ ^ (i * (j + 1)) = ζ⁻¹ ^ (i * j) := by
      have h0 : ζ ^ i * ζ⁻¹ ^ i = 1 := by rw [← mul_pow, mul_inv_cancel₀ hζ0, one_pow]
      calc ζ ^ i * ζ⁻¹ ^ (i * (j + 1)) = (ζ ^ i * ζ⁻¹ ^ i) * ζ⁻¹ ^ (i * j) := by
            rw [mul_add, mul_one, pow_add]; ring
        _ = ζ⁻¹ ^ (i * j) := by rw [h0, one_mul]
    simp only [hT, e1, smul_smul, e2]
  have hTp : T p = T 0 := by
    have h2 : ζ⁻¹ ^ (i * p) = 1 := by
      rw [pow_mul', inv_pow, hζ.pow_eq_one, inv_one, one_pow]
    show ζ⁻¹ ^ (i * p) • (S ^ p) w = ζ⁻¹ ^ (i * 0) • (S ^ 0) w
    rw [h2, hSp]
    simp
  have hsum : ∑ j ∈ Finset.range p, T (j + 1) = ∑ j ∈ Finset.range p, T j := by
    have h2 := Finset.sum_range_succ' T p
    rw [Finset.sum_range_succ, hTp] at h2
    exact (add_right_cancel h2).symm
  have h3 : ∑ j ∈ Finset.range p, S (ζ⁻¹ ^ (i * j) • (S ^ j) w) =
      ζ ^ i • ∑ j ∈ Finset.range p, T j := by
    rw [← hsum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, h1]
  unfold spec
  rw [map_smul, map_sum, h3, smul_comm]

theorem sum_spec (hζ : IsPrimitiveRoot ζ p) (hp : 0 < p) (hp0 : (p : K) ≠ 0)
    (w : Fin n → K) : ∑ i ∈ Finset.range p, spec ζ S p i w = w := by
  have hgeom : ∀ j ∈ Finset.range p,
      ∑ i ∈ Finset.range p, ζ⁻¹ ^ (i * j) = if j = 0 then (p : K) else 0 := by
    intro j hj
    rw [Finset.mem_range] at hj
    simp_rw [pow_mul']
    split_ifs with h0
    · subst h0
      simp
    · have hx : ζ⁻¹ ^ j ≠ 1 := by
        intro h1
        rw [inv_pow, inv_eq_one] at h1
        have := Nat.le_of_dvd (Nat.pos_of_ne_zero h0) (hζ.dvd_of_pow_eq_one j h1)
        omega
      have hxp : (ζ⁻¹ ^ j) ^ p = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, inv_pow, hζ.pow_eq_one, inv_one, one_pow]
      have h2 := geom_sum_mul (ζ⁻¹ ^ j) p
      rw [hxp, sub_self] at h2
      exact (mul_eq_zero.mp h2).resolve_right (sub_ne_zero.mpr hx)
  calc ∑ i ∈ Finset.range p, spec ζ S p i w
      = (p : K)⁻¹ • ∑ j ∈ Finset.range p, (∑ i ∈ Finset.range p, ζ⁻¹ ^ (i * j)) • (S ^ j) w := by
        unfold spec
        rw [← Finset.smul_sum, Finset.sum_comm]
        simp_rw [Finset.sum_smul]
    _ = w := by
        rw [Finset.sum_congr rfl fun j hj => by rw [hgeom j hj], Finset.sum_eq_single 0]
        · simp [smul_smul, inv_mul_cancel₀ hp0]
        · intro j _ hj0
          simp [hj0]
        · intro h
          exact absurd (Finset.mem_range.mpr hp) h

theorem spec_mem {W : Submodule K (Fin n → K)} (hW : ∀ x ∈ W, S x ∈ W) {w : Fin n → K}
    (hw : w ∈ W) (i : ℕ) : spec ζ S p i w ∈ W := by
  have hpow : ∀ j, (S ^ j) w ∈ W := by
    intro j
    induction j with
    | zero => simpa using hw
    | succ j ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact hW _ ih
  exact W.smul_mem _ (W.sum_mem fun j _ => W.smul_mem _ (hpow j))

theorem herm_eq_zero_of_eigen' (hS : ∀ x y, herm σ (S x) (S y) = herm σ x y)
    {x y : Fin n → K} {a b : K} (hx : S x = a • x) (hy : S y = b • y) (hab : σ a * b ≠ 1) :
    herm σ x y = 0 := by
  have h1 := hS x y
  rw [hx, hy, herm_smul_left, herm_smul_right, ← mul_assoc] at h1
  have h2 : (σ a * b - 1) * herm σ x y = 0 := by linear_combination h1
  exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hab)

theorem herm_eq_zero_of_eigen (hζ : IsPrimitiveRoot ζ p) (hp : 0 < p) (hσζ : σ ζ = ζ⁻¹)
    (hS : ∀ x y, herm σ (S x) (S y) = herm σ x y) {x y : Fin n → K} {i i' : ℕ} (hi : i < p)
    (hi' : i' < p) (hne : i ≠ i') (hx : S x = ζ ^ i • x) (hy : S y = ζ ^ i' • y) :
    herm σ x y = 0 := by
  have h1 := hS x y
  rw [hx, hy, herm_smul_left, herm_smul_right, map_pow, hσζ] at h1
  by_contra h0
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne'
  have h2 : ζ ^ i' * herm σ x y = ζ ^ i * herm σ x y := by
    have h3 : ζ ^ i * (ζ⁻¹ ^ i * (ζ ^ i' * herm σ x y)) = ζ ^ i * herm σ x y := by rw [h1]
    rwa [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hζ0, one_pow, one_mul] at h3
  exact hne (hζ.pow_inj hi' hi (mul_right_cancel₀ h0 h2)).symm

theorem exists_eigenvector_aniso (hζ : IsPrimitiveRoot ζ p) (hp : 0 < p) (hp0 : (p : K) ≠ 0)
    (hσζ : σ ζ = ζ⁻¹) (hSp : S ^ p = 1) (hS : ∀ x y, herm σ (S x) (S y) = herm σ x y)
    (W : Submodule K (Fin n → K)) (hW : ∀ x ∈ W, S x ∈ W) {w : Fin n → K} (hw : w ∈ W)
    (hww : herm σ w w ≠ 0) : ∃ w' ∈ W, ∃ a : K, S w' = a • w' ∧ herm σ w' w' ≠ 0 := by
  have hsum := sum_spec (S := S) hζ hp hp0 w
  have hdiag : ∑ i ∈ Finset.range p, herm σ (spec ζ S p i w) (spec ζ S p i w) = herm σ w w := by
    conv_rhs => rw [← hsum]
    rw [herm_sum_left]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [herm_sum_right, Finset.sum_eq_single i]
    · intro i' hi' hne
      exact herm_eq_zero_of_eigen hζ hp hσζ hS (Finset.mem_range.mp hi) (Finset.mem_range.mp hi')
        (Ne.symm hne) (S_spec hζ hp hSp i w) (S_spec hζ hp hSp i' w)
    · intro h
      exact absurd hi h
  obtain ⟨i, -, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [hdiag]; exact hww)
  exact ⟨spec ζ S p i w, spec_mem hW hw i, ζ ^ i, S_spec hζ hp hSp i w, hne⟩

theorem exists_orthonormal_eigenbasis (hσ : IsUnitaryInvolution σ)
    (hζ : IsPrimitiveRoot ζ p) (hp : 0 < p) (hp0 : (p : K) ≠ 0) (hσζ : σ ζ = ζ⁻¹)
    (hSp : S ^ p = 1) (hS : ∀ x y, herm σ (S x) (S y) = herm σ x y) :
    ∃ (b : Fin n → Fin n → K) (u : Fin n → K),
      (∀ i j, herm σ (b i) (b j) = if i = j then 1 else 0) ∧ ∀ i, S (b i) = u i • b i := by
  have key : ∀ k ≤ n, ∃ (b : Fin k → Fin n → K) (u : Fin k → K),
      (∀ i j, herm σ (b i) (b j) = if i = j then 1 else 0) ∧ ∀ i, S (b i) = u i • b i := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
    | succ k ih =>
      intro hk
      obtain ⟨b, u, hb, hu⟩ := ih (by omega)
      have hu0 : ∀ i, σ (u i) ≠ 0 := by
        intro i h0
        have h1 := hS (b i) (b i)
        rw [hu i, herm_smul_left, herm_smul_right, hb i i, if_pos rfl, h0, zero_mul] at h1
        exact zero_ne_one h1
      have hWst : ∀ x ∈ perp σ b, S x ∈ perp σ b := by
        intro x hx j
        have h1 := hS (b j) x
        rw [hu j, herm_smul_left, mem_perp.mp hx j] at h1
        exact (mul_eq_zero.mp h1).resolve_left (hu0 j)
      let Q : (Fin n → K) →ₗ[K] (Fin n → K) :=
        LinearMap.id - ∑ i, (hermL σ (b i)).smulRight (b i)
      have hQy : ∀ y, Q y = y - ∑ i, herm σ (b i) y • b i := fun y => by simp [Q]
      have hQ1 : ∀ y j, herm σ (b j) (Q y) = 0 := by
        intro y j
        rw [hQy, herm_sub_right, herm_sum_right]
        simp [herm_smul_right, hb]
      obtain ⟨y, hy⟩ := exists_aniso_of_lt hσ (by omega : k < n) b Q
        (fun y => by
          rw [hQy, sub_sub_cancel]
          exact Submodule.sum_mem _ fun i _ =>
            Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
        hQ1
      obtain ⟨w, hwW, a, hSw, hww⟩ := exists_eigenvector_aniso hζ hp hp0 hσζ hSp hS (perp σ b)
        hWst (w := Q y) (mem_perp.mpr (hQ1 y)) hy
      obtain ⟨c, hc⟩ := exists_smul_norm_one hσ hww
      have hbv : ∀ i, herm σ (b i) (c • w) = 0 := fun i =>
        mem_perp.mp ((perp σ b).smul_mem c hwW) i
      have hvb : ∀ i, herm σ (c • w) (b i) = 0 := fun i =>
        herm_eq_zero_comm σ hσ.invol (hbv i)
      have hSv : S (c • w) = a • c • w := by rw [map_smul, hSw, smul_comm]
      refine ⟨Fin.cons (c • w) b, Fin.cons a u, fun i j => ?_, fun i => ?_⟩
      · cases i using Fin.cases <;> cases j using Fin.cases <;>
          simp [hc, hbv, hvb, hb, (Fin.succ_ne_zero _).symm]
      · cases i using Fin.cases <;> simp [hSv, hu]
  exact key n le_rfl

end Spectral

section Field

theorem pow_prime_eq_one_zmod {p : ℕ} [NeZero p] (a : Multiplicative (ZMod p)) : a ^ p = 1 := by
  rw [← toAdd_eq_zero, toAdd_pow]
  simp

theorem exists_prime_pow_of_card_sq {K : Type} [Field K] [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) : ∃ r f : ℕ, r.Prime ∧ CharP K r ∧ q = r ^ f := by
  obtain ⟨r, m, hr, hchar, -, hKr⟩ := CFSG.LocalAnalysis.RankFourTheoremC.exists_char_pow_card K
  obtain ⟨f, -, hqf⟩ : ∃ f ≤ m, q = r ^ f := by
    refine (Nat.dvd_prime_pow hr).1 ?_
    rw [← hKr, hK]
    exact dvd_pow_self q two_ne_zero
  exact ⟨r, f, hr, hchar, hqf⟩

theorem exists_isPrimitiveRoot_three {K : Type} [Field K] [Finite K] (h : 3 ∣ Nat.card Kˣ) :
    ∃ ζ : K, IsPrimitiveRoot ζ 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ζu, hζu⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 h
  exact ⟨(ζu : K), IsPrimitiveRoot.coe_units_iff.mpr (hζu ▸ IsPrimitiveRoot.orderOf ζu)⟩

end Field

end CrossUni

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
