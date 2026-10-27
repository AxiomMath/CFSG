module

public import CFSG.HardMathSupport.Curtis.Coordinator.TorCenterSL3Center
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.HardMathSupport.Curtis.Coordinator.TorCenterSL3Diag

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open Matrix CFSG.AGLEmbedding.LinearThreeKit CFSG.LocalAnalysis.ComponentInitial LinearFlag

variable {K : Type} [Field K]

theorem eq_one_or_omega {ω : K} (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1) {x : K} (hx : x ^ 3 = 1) :
    x = 1 ∨ x = ω ∨ x = ω ^ 2 := by
  have h1 := one_add_omega_add_sq hω1 hω3
  have h : (x - 1) * ((x - ω) * (x - ω ^ 2)) = 0 := by
    linear_combination hx + (x - x ^ 2) * h1 + (x - 1) * hω3
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inr (Or.inl (sub_eq_zero.mp h))
    · exact Or.inr (Or.inr (sub_eq_zero.mp h))

theorem apply_eq_self_of_sq {G : Type*} [Group G] {β : MulAut G} {k : ℕ} (hβ : β ^ 3 ^ k = 1)
    {g : G} (hg : β (β g) = g) : β g = g := by
  have hβ2 : (β ^ 2) g = g := by rw [pow_two, MulAut.mul_apply, hg]
  have hpow : ∀ n : ℕ, (β ^ (2 * n)) g = g := fun n => by
    induction n with
    | zero => simp
    | succ n ih => rw [show 2 * (n + 1) = 2 + 2 * n by ring, pow_add, MulAut.mul_apply, ih, hβ2]
  have hN : (β ^ (3 ^ k + 1)) g = β g := by
    rw [pow_succ, hβ, one_mul]
  have hev : Even (3 ^ k + 1) := by
    have : Odd (3 ^ k) := Odd.pow (by decide)
    exact this.add_one
  obtain ⟨n, hn⟩ := hev
  rw [show 3 ^ k + 1 = n + n by omega, ← two_mul, hpow n] at hN
  exact hN.symm

theorem eq_one_of_apply_eq_inv {G : Type*} [Group G] {β : MulAut G} {k : ℕ} (hβ : β ^ 3 ^ k = 1)
    {h : G} (h3 : h ^ 3 = 1) (hh : β h = h⁻¹) : h = 1 := by
  have hβ2 : β (β h) = h := by rw [hh, map_inv, hh, inv_inv]
  have hfix := apply_eq_self_of_sq hβ hβ2
  rw [hh] at hfix
  have h2 : h ^ 2 = 1 := by
    rw [pow_two]; exact mul_eq_one_iff_eq_inv.mpr hfix.symm
  calc h = h ^ 3 * (h ^ 2)⁻¹ := by group
    _ = 1 := by rw [h3, h2]; simp

theorem pow_three_of_mem_scalars {z : SpecialLinearGroup (Fin 3) K} (hz : z ∈ scalars 3 K) :
    z ^ 3 = 1 := by
  obtain ⟨c, hc, hzc⟩ := mem_scalars.mp hz
  have hc3 : ((c : K)) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]
  have key : (z : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
    rw [hzc, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, smul_pow, one_pow, hc3,
      one_smul]
  refine Subtype.ext ?_
  show (z : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1
  exact key

theorem mem_scalars_cases [Finite K] {z w : SpecialLinearGroup (Fin 3) K} (hz : z ∈ scalars 3 K)
    (hw : w ∈ scalars 3 K) (hz1 : z ≠ 1) : w = 1 ∨ w = z ∨ w = z⁻¹ := by
  have hz3 := pow_three_of_mem_scalars hz
  have hord : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have hle : Subgroup.zpowers z ≤ scalars 3 K := by
    rw [Subgroup.zpowers_le]; exact hz
  have hcard : Nat.card (scalars 3 K) ≤ Nat.card (Subgroup.zpowers z) := by
    rw [Nat.card_zpowers, hord]; exact card_scalars_le_three
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard
  rw [← heq] at hw
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  have : z ^ i = z ^ (i % 3) := by
    rw [← zpow_mod_orderOf, hord]; rfl
  rw [this]
  have hi : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
  rcases hi with h | h | h
  · left; rw [h]; simp
  · right; left; rw [h]; simp
  · right; right
    rw [h]
    have : z ^ (2 : ℤ) * z = 1 := by
      rw [← _root_.zpow_add_one, show (2 : ℤ) + 1 = 3 by norm_num]
      exact_mod_cast hz3
    exact eq_inv_of_mul_eq_one_left this

theorem aut_fixes_scalars [Finite K] {β : MulAut (SpecialLinearGroup (Fin 3) K)} {k : ℕ}
    (hβ : β ^ 3 ^ k = 1) {z : SpecialLinearGroup (Fin 3) K} (hz : z ∈ scalars 3 K) :
    β z = z := by
  by_cases hz1 : z = 1
  · rw [hz1, map_one]
  have hβz : β z ∈ scalars 3 K := by
    have := map_scalars_eq 3 K β
    rw [← this]; exact ⟨z, hz, rfl⟩
  rcases mem_scalars_cases hz hβz hz1 with h | h | h
  · exact absurd (β.injective (by rw [h, map_one])) hz1
  · exact h
  · exact absurd (eq_one_of_apply_eq_inv hβ (pow_three_of_mem_scalars hz) h) hz1

theorem aut_apply_eq_scalar_smul [Finite K] {ω : K} (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1)
    {s : SpecialLinearGroup (Fin 3) K} {b : Fin 3 → Fin 3 → K} (hb : LinearIndependent K b)
    (hb0 : (s : Matrix (Fin 3) (Fin 3) K) *ᵥ b 0 = b 0)
    (hb1 : (s : Matrix (Fin 3) (Fin 3) K) *ᵥ b 1 = ω • b 1)
    (hb2 : (s : Matrix (Fin 3) (Fin 3) K) *ᵥ b 2 = ω ^ 2 • b 2) (hs : s ∉ scalars 3 K)
    {β : MulAut (SpecialLinearGroup (Fin 3) K)} {k : ℕ} (hβ : β ^ 3 ^ k = 1)
    {y : Fin 3 → K} (hy3 : ∀ i, y i ^ 3 = 1)
    (hy : ∀ i, ((β s : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ b i =
      y i • b i) :
    ∃ c : K, c ^ 3 = 1 ∧ ((β s : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      c • (s : Matrix (Fin 3) (Fin 3) K) := by
  have hy0 : ∀ i, y i ≠ 0 := fun i h0 => by
    have := hy3 i; rw [h0] at this; simp at this
  have hω0 : ω ≠ 0 := fun h => by rw [h] at hω3; simp at hω3
  have hdet : y 0 * y 1 * y 2 = 1 := by
    have h := det_eq_of_mulVec_eq_sum (A := ((β s : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K)) (M := Matrix.diagonal y) hb (fun j => by
        rw [hy j]; simp [Matrix.diagonal_apply])
    rw [(β s).2, Matrix.det_diagonal, Fin.prod_univ_three] at h
    exact h.symm
  have hρ1 : (y 1 / y 0) ^ 3 = 1 := by rw [div_pow, hy3 1, hy3 0, div_one]
  have hρ2 : (y 2 / y 0) ^ 3 = 1 := by rw [div_pow, hy3 2, hy3 0, div_one]
  have hy12 : y 1 * y 2 = y 0 ^ 2 := by
    refine mul_left_cancel₀ (hy0 0) ?_
    linear_combination hdet - hy3 0
  have hprod : (y 1 / y 0) * (y 2 / y 0) = 1 := by
    rw [div_mul_div_comm, hy12, ← pow_two, div_self (pow_ne_zero 2 (hy0 0))]
  have hss : s ^ 3 = 1 := by
    refine Subtype.ext ?_
    show (s : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1
    refine eq_of_mulVec_eq hb (forall_fin_three ?_ ?_ ?_)
    · show ((s : Matrix (Fin 3) (Fin 3) K) ^ 3) *ᵥ b 0 = (1 : Matrix (Fin 3) (Fin 3) K) *ᵥ b 0
      have hb0' : (s : Matrix (Fin 3) (Fin 3) K) *ᵥ b 0 = (1 : K) • b 0 := by
        rw [one_smul]; exact hb0
      rw [pow_mulVec_of_mulVec_eq_smul hb0', one_pow, one_smul, Matrix.one_mulVec]
    · show ((s : Matrix (Fin 3) (Fin 3) K) ^ 3) *ᵥ b 1 = (1 : Matrix (Fin 3) (Fin 3) K) *ᵥ b 1
      rw [pow_mulVec_of_mulVec_eq_smul hb1, hω3, one_smul, Matrix.one_mulVec]
    · show ((s : Matrix (Fin 3) (Fin 3) K) ^ 3) *ᵥ b 2 = (1 : Matrix (Fin 3) (Fin 3) K) *ᵥ b 2
      rw [pow_mulVec_of_mulVec_eq_smul hb2, ← pow_mul, mul_comm, pow_mul, hω3, one_pow, one_smul,
        Matrix.one_mulVec]
  let u0 : Kˣ := Units.mk0 (y 0) (hy0 0)
  have hu03 : u0 ^ 3 = 1 := Units.ext (by simpa [u0] using hy3 0)
  obtain ⟨z, hzs, hzmat⟩ : ∃ z : SpecialLinearGroup (Fin 3) K, z ∈ scalars 3 K ∧
      (z : Matrix (Fin 3) (Fin 3) K) = (y 0) • (1 : Matrix (Fin 3) (Fin 3) K) := by
    refine ⟨scalarElement u0 hu03, scalarElement_mem_scalars u0 hu03, ?_⟩
    show Matrix.scalar (Fin 3) (u0 : K) = _
    rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]; rfl
  rcases eq_one_or_omega hω1 hω3 hρ1 with h1 | h1 | h1
  ·
    exfalso
    have hy1 : y 1 = y 0 := (div_eq_one_iff_eq (hy0 0)).mp h1
    have hρ2' : y 2 / y 0 = 1 := by rw [h1, one_mul] at hprod; exact hprod
    have hy2 : y 2 = y 0 := (div_eq_one_iff_eq (hy0 0)).mp hρ2'
    have hβs : β s ∈ scalars 3 K := by
      refine ⟨u0, hu03, ?_⟩
      refine eq_of_mulVec_eq hb fun i => ?_
      rw [hy i, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mulVec,
        Matrix.one_mulVec]
      fin_cases i
      · rfl
      · exact (congrArg (· • b 1) hy1)
      · exact (congrArg (· • b 2) hy2)
    apply hs
    have := map_scalars_eq 3 K β⁻¹
    rw [← this]
    exact ⟨β s, hβs, by simp⟩
  ·
    have hρ2' : y 2 / y 0 = ω ^ 2 := by
      rw [h1] at hprod
      refine mul_left_cancel₀ hω0 ?_
      rw [hprod]; linear_combination -hω3
    have hy1 : y 1 = ω * y 0 := by
      have := (div_eq_iff (hy0 0)).mp h1; rw [this]
    have hy2 : y 2 = ω ^ 2 * y 0 := (div_eq_iff (hy0 0)).mp hρ2'
    refine ⟨y 0, hy3 0, ?_⟩
    refine eq_of_mulVec_eq hb (forall_fin_three ?_ ?_ ?_)
    · show _ *ᵥ b 0 = _ *ᵥ b 0
      rw [hy 0, Matrix.smul_mulVec, hb0]
    · show _ *ᵥ b 1 = _ *ᵥ b 1
      rw [hy 1, Matrix.smul_mulVec, hb1, hy1, smul_smul, mul_comm]
    · show _ *ᵥ b 2 = _ *ᵥ b 2
      rw [hy 2, Matrix.smul_mulVec, hb2, hy2, smul_smul, mul_comm]
  ·
    exfalso
    have hρ2' : y 2 / y 0 = ω := by
      rw [h1] at hprod
      refine mul_left_cancel₀ (pow_ne_zero 2 hω0) ?_
      rw [hprod]; linear_combination -hω3
    have hy1 : y 1 = ω ^ 2 * y 0 := (div_eq_iff (hy0 0)).mp h1
    have hy2 : y 2 = ω * y 0 := (div_eq_iff (hy0 0)).mp hρ2'
    have hsinv : ∀ (i : Fin 3) (d : K), d ≠ 0 → (s : Matrix (Fin 3) (Fin 3) K) *ᵥ b i = d • b i →
        ((s⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ b i = d⁻¹ • b i := by
      intro i d hd h
      have h' := inv_mulVec_mulVec s (b i)
      rw [h, Matrix.mulVec_smul] at h'
      have h'' := congrArg (fun v => d⁻¹ • v) h'
      simp only [smul_smul, inv_mul_cancel₀ hd, one_smul] at h''
      exact h''
    have hω2 : ω * ω ^ 2 = 1 := by rw [← pow_succ']; exact hω3
    have hωinv : ω⁻¹ = ω ^ 2 := inv_eq_of_mul_eq_one_right hω2
    have hω2inv : (ω ^ 2)⁻¹ = ω := inv_eq_of_mul_eq_one_right (by rw [mul_comm]; exact hω2)
    have hmatvec : ∀ i, ((β s : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ b i =
        ((z * s⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ b i := by
      refine forall_fin_three ?_ ?_ ?_
      · rw [hy 0, Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec,
          hsinv 0 1 one_ne_zero (by rw [one_smul]; exact hb0), hzmat, inv_one, one_smul,
          Matrix.smul_mulVec, Matrix.one_mulVec]
      · rw [hy 1, Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec,
          hsinv 1 ω hω0 hb1, hzmat, hωinv, Matrix.mulVec_smul, Matrix.smul_mulVec,
          Matrix.one_mulVec, hy1, smul_smul, mul_comm]
      · rw [hy 2, Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec,
          hsinv 2 (ω ^ 2) (pow_ne_zero 2 hω0) hb2, hzmat, hω2inv, Matrix.mulVec_smul,
          Matrix.smul_mulVec, Matrix.one_mulVec, hy2, smul_smul, mul_comm]
    have hβsz : β s = z * s⁻¹ := Subtype.ext (eq_of_mulVec_eq hb hmatvec)
    have hzc : ∀ g : SpecialLinearGroup (Fin 3) K, g * z = z * g := fun g => by
      have := (scalars_eq_center 3 K) ▸ hzs
      exact Subgroup.mem_center_iff.mp this g
    have hβz : β z = z := aut_fixes_scalars hβ hzs
    have hβ2 : β (β s) = s := by
      rw [hβsz, map_mul, hβz, map_inv, hβsz, _root_.mul_inv_rev, inv_inv]
      calc z * (s * z⁻¹) = (z * s) * z⁻¹ := by rw [mul_assoc]
        _ = (s * z) * z⁻¹ := by rw [← hzc s]
        _ = s := by rw [mul_assoc, mul_inv_cancel, mul_one]
    have hβs1 : β s = s := apply_eq_self_of_sq hβ hβ2
    rw [hβs1] at hβsz
    have hz2 : z = s * s := by
      calc z = z * s⁻¹ * s := by rw [mul_assoc, inv_mul_cancel, mul_one]
        _ = s * s := by rw [← hβsz]
    apply hs
    have hsz : s = z⁻¹ := by
      calc s = s ^ 3 * (s * s)⁻¹ := by group
        _ = z⁻¹ := by rw [hss, ← hz2, one_mul]
    rw [hsz]
    exact (scalars 3 K).inv_mem hzs

end CFSG.HardMathSupport.Curtis.Coordinator
