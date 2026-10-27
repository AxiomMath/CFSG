module

public import CFSG.LieType.SeitzGeneration.OuterRank2
public import CFSG.LieType.SeitzGeneration.OutdiagHeis

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open

section Independent

variable {P : Type*} [Group P] {p : ℕ}

theorem independent_of_not_mem_zpowers (hp : p.Prime) {s t : P} (hs1 : s ≠ 1) (hsp : s ^ p = 1)
    (htp : t ^ p = 1) (ht : t ∉ Subgroup.zpowers s) :
    ∀ i j : ℤ, s ^ i * t ^ j = 1 → (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j := by
  intro i j hij
  have : Fact p.Prime := ⟨hp⟩
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have htj : t ^ j ∈ Subgroup.zpowers s := by
    rw [eq_inv_of_mul_eq_one_right hij]
    exact Subgroup.inv_mem _ (Subgroup.zpow_mem_zpowers s i)
  have hpj : (p : ℤ) ∣ j := by
    by_contra hl
    obtain ⟨a, b, hab⟩ : IsCoprime (p : ℤ) j :=
      (Irreducible.coprime_iff_not_dvd hpp.irreducible).mpr hl
    have htp' : t ^ (p : ℤ) = 1 := by rw [zpow_natCast, htp]
    apply ht
    have h1 : t = (t ^ j) ^ b := by
      calc t = t ^ (a * (p : ℤ) + b * j) := by rw [hab, zpow_one]
        _ = (t ^ (p : ℤ)) ^ a * (t ^ j) ^ b := by
            rw [zpow_add, mul_comm a, mul_comm b, zpow_mul, zpow_mul]
        _ = (t ^ j) ^ b := by rw [htp', one_zpow, one_mul]
    rw [h1]
    exact zpow_mem htj b
  have htj1 : t ^ j = 1 := by
    obtain ⟨m, rfl⟩ := hpj
    rw [zpow_mul, zpow_natCast, htp, one_zpow]
  rw [htj1, mul_one] at hij
  refine ⟨?_, hpj⟩
  rw [← orderOf_eq_prime hsp hs1]
  exact orderOf_dvd_iff_zpow_eq_one.mpr hij

theorem NarrowScope.false_of_fixed_e9 [Finite P] (hp : p.Prime)
    (hinj : Function.Injective (MulAut.conj : P →* MulAut P)) {E : Subgroup (MulAut P)}
    (hs : NarrowScope p E) {f : MulAut P} (hfE : f ∈ E) (hf : f ^ p = 1)
    (hfout : ∀ x, f ≠ MulAut.conj x) {s t : P} (hcomm : Commute s t) (hs1 : s ≠ 1)
    (hsp : s ^ p = 1) (htp : t ^ p = 1) (ht : t ∉ Subgroup.zpowers s) (hfs : f s = s)
    (hft : f t = t) : False :=
  NarrowScope.false_of_fixed_pair hp hinj hs hfE hf hfout hcomm hsp htp
    (independent_of_not_mem_zpowers hp hs1 hsp htp ht) hfs hft

end Independent

section Group

variable {G Q : Type*} [Group G] [Group Q]

theorem heis_pair_of_central (φ : G →* Q) (hφ : φ.ker ≤ Subgroup.center G) {d s z : G}
    (hz : φ z = 1) (hz1 : z ≠ 1) (h : d * s = z * (s * d)) :
    Commute (φ d) (φ s) ∧ φ d ≠ 1 ∧ φ s ∉ Subgroup.zpowers (φ d) := by
  have key : Commute d s → False := fun hc => hz1 (by
    have h1 : s * d = z * (s * d) := hc.eq.symm.trans h
    exact mul_right_cancel (b := s * d) (by rw [← h1, one_mul]))
  refine ⟨?_, fun hd => key ?_, fun hmem => key ?_⟩
  · have h1 : φ d * φ s = φ s * φ d := by
      rw [← map_mul, h, map_mul, hz, one_mul, map_mul]
    exact h1
  · exact (Subgroup.mem_center_iff.mp (hφ (MonoidHom.mem_ker.mpr hd)) s).symm
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hc : s * (d ^ k)⁻¹ ∈ Subgroup.center G := hφ (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_zpow, hk, mul_inv_cancel])
    have hcd : Commute d (s * (d ^ k)⁻¹) := Subgroup.mem_center_iff.mp hc d
    have h2 := hcd.mul_right ((Commute.refl d).zpow_right k)
    simpa using h2

end Group

section CubeRoots

variable {K : Type*} [Field K]

theorem eq_of_pow_three_eq_one {ω x : K} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) (hx : x ^ 3 = 1) :
    x = 1 ∨ x = ω ∨ x = ω ^ 2 := by
  have h : 1 + ω + ω ^ 2 = 0 := by
    have h1 : (ω - 1) * (1 + ω + ω ^ 2) = 0 := by linear_combination hω3
    exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hω1)
  have hprod : (x - 1) * (x - ω) * (x - ω ^ 2) = 0 := by
    linear_combination hx + (x - x ^ 2) * h + (x - 1) * hω3
  rcases mul_eq_zero.mp hprod with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · exact Or.inl (sub_eq_zero.mp h2)
    · exact Or.inr (Or.inl (sub_eq_zero.mp h2))
  · exact Or.inr (Or.inr (sub_eq_zero.mp h1))

theorem ringAut_apply_eq_of_pow_three {σ : K ≃+* K} (hσ : σ ^ 3 = 1) {ω : K} (hω3 : ω ^ 3 = 1)
    (hω1 : ω ≠ 1) : σ ω = ω := by
  have hσω3 : (σ ω) ^ 3 = 1 := by rw [← map_pow, hω3, map_one]
  have hω0 : ω ≠ 0 := by rintro rfl; norm_num at hω3
  rcases eq_of_pow_three_eq_one hω3 hω1 hσω3 with h | h | h
  · exact absurd (σ.injective (h.trans (map_one σ).symm)) hω1
  · exact h
  · exfalso
    have h2 : σ (σ ω) = ω := by
      rw [h, map_pow, h, ← pow_mul]
      calc ω ^ (2 * 2) = ω ^ 3 * ω := by ring
        _ = ω := by rw [hω3, one_mul]
    have h3 : σ (σ (σ ω)) = ω := by
      have h4 := congrArg (fun τ : K ≃+* K => τ ω) hσ
      simpa [pow_succ] using h4
    rw [h2, h] at h3
    exact hω1 (mul_left_cancel₀ hω0 (by linear_combination h3))

end CubeRoots

section Matrices

open Matrix

variable {K : Type*} [Field K] {ω : K}

theorem det_heisD (ω : K) : (heisD ω).det = ω ^ 3 := by
  rw [heisD, det_diagonal, Fin.prod_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  ring

theorem det_heisC_one : (heisC (1 : K)).det = 1 := by
  rw [heisC, Matrix.det_fin_three]
  simp

theorem heisD_pow_three (hω3 : ω ^ 3 = 1) : heisD ω ^ 3 = 1 := by
  rw [heisD, diagonal_pow, ← diagonal_one]
  congr 1
  ext i
  fin_cases i <;> simp
  · exact hω3
  · rw [← pow_mul, mul_comm, pow_mul, hω3, one_pow]

theorem heisC_one_pow_three : heisC (1 : K) ^ 3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [heisC, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]

theorem heisD_mul_heisC (hω3 : ω ^ 3 = 1) :
    heisD ω * heisC 1 = scalar (Fin 3) ω * (heisC 1 * heisD ω) := by
  ext i j
  rw [heisD, scalar_apply, diagonal_mul, ← Matrix.mul_assoc, mul_diagonal, diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp [heisC]
  · rw [← pow_succ', hω3]
  · ring

theorem map_heisD (σ : K →+* K) (hσω : σ ω = ω) : (heisD ω).map σ = heisD ω := by
  rw [heisD, diagonal_map (map_zero σ)]
  congr 1
  funext i
  fin_cases i <;> simp [hσω]

theorem map_heisC_one (σ : K →+* K) : (heisC (1 : K)).map σ = heisC 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [heisC]

end Matrices

section Linear

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type*} [Field K]

theorem exists_heis_pair_linear {ω : K} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) {σ : K ≃+* K}
    (hσω : σ ω = ω) :
    ∃ s t : projectiveSL 3 K, Commute s t ∧ s ≠ 1 ∧ s ^ 3 = 1 ∧ t ^ 3 = 1 ∧
      t ∉ Subgroup.zpowers s ∧ fieldAut 3 K σ s = s ∧ fieldAut 3 K σ t = t := by
  have hω0 : ω ≠ 0 := by rintro rfl; norm_num at hω3
  set u : Kˣ := Units.mk0 ω hω0 with hu
  have hu3 : u ^ 3 = 1 := Units.ext (by simpa [hu] using hω3)
  let D : Matrix.SpecialLinearGroup (Fin 3) K := ⟨heisD ω, by rw [det_heisD, hω3]⟩
  let S : Matrix.SpecialLinearGroup (Fin 3) K := ⟨heisC 1, det_heisC_one⟩
  have hDS : D * S = scalarElement u hu3 * (S * D) := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, coe_scalarElement, hu, Units.val_mk0]
    exact heisD_mul_heisC hω3)
  have hker : (proj 3 K).ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K) := by
    rw [ker_proj]
    exact scalars_le_center 3 K
  have hz1 : scalarElement u hu3 ≠ 1 := by
    intro h
    have h1 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 3) K =>
      (A : Matrix (Fin 3) (Fin 3) K) 0 0) h
    simp [hu, scalar_apply] at h1
    exact hω1 h1
  obtain ⟨hcomm, hd1, hnot⟩ := heis_pair_of_central (proj 3 K) hker
    (proj_eq_one_iff.mpr (scalarElement_mem_scalars u hu3)) hz1 hDS
  have hfix : ∀ g : Matrix.SpecialLinearGroup (Fin 3) K,
      Matrix.SpecialLinearGroup.map σ.toRingHom g = g →
        fieldAut 3 K σ (proj 3 K g) = proj 3 K g := fun g hg => by rw [fieldAut_proj, hg]
  refine ⟨proj 3 K D, proj 3 K S, hcomm, hd1, ?_, ?_, hnot, hfix D (Subtype.ext ?_),
    hfix S (Subtype.ext ?_)⟩
  · rw [← map_pow, show D ^ 3 = 1 from Subtype.ext (by
      rw [Matrix.SpecialLinearGroup.coe_pow]; exact heisD_pow_three hω3), map_one]
  · rw [← map_pow, show S ^ 3 = 1 from Subtype.ext (by
      rw [Matrix.SpecialLinearGroup.coe_pow]; exact heisC_one_pow_three), map_one]
  · rw [Matrix.SpecialLinearGroup.map_apply_coe]
    exact map_heisD σ.toRingHom hσω
  · rw [Matrix.SpecialLinearGroup.map_apply_coe]
    exact map_heisC_one σ.toRingHom

end Linear

end CFSG.LieType.SeitzGeneration
