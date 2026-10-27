module

public import CFSG.GroupTheory.GL52.SylowTools
public import CFSG.GroupTheory.GL52.Simple
public import Mathlib.Tactic.NormNum.Prime

public noncomputable section

namespace CFSG.GroupTheory.GL52

open Matrix

@[expose] def eps5M : M5 :=
  !![0, 0, 0, 1, 0; 1, 0, 0, 1, 0; 0, 1, 0, 1, 0; 0, 0, 1, 1, 0; 0, 0, 0, 0, 1]

@[expose] def gamma5M : M5 :=
  !![0, 1, 1, 1, 0; 1, 1, 0, 0, 0; 0, 0, 0, 1, 0; 1, 1, 1, 1, 0; 0, 0, 0, 0, 1]

@[expose] def phi5M : M5 :=
  !![1, 0, 1, 0, 0; 0, 0, 1, 1, 0; 0, 1, 1, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 1]

set_option maxRecDepth 100000 in
theorem syl5_facts : eps5M ^ 5 = 1 ∧ eps5M * eps5M ^ 4 = 1 ∧ eps5M ≠ 1 ∧
    gamma5M ^ 15 = 1 ∧ gamma5M * gamma5M ^ 14 = 1 ∧
    (∀ m : Fin 15, 0 < (m : ℕ) → gamma5M ^ (m : ℕ) ≠ 1) ∧ gamma5M * eps5M = eps5M * gamma5M ∧
    phi5M * phi5M ^ 3 = 1 ∧ phi5M * eps5M = eps5M ^ 2 * phi5M ∧
    phi5M ^ 2 * eps5M = eps5M ^ 4 * phi5M ^ 2 ∧ phi5M ^ 3 * eps5M = eps5M ^ 3 * phi5M ^ 3 ∧
    (∀ j : Fin 4, (j : ℕ) ≠ 0 → phi5M ^ (j : ℕ) * eps5M ≠ eps5M * phi5M ^ (j : ℕ)) := by
  decide +kernel

theorem syl5_mulVec_single :
    eps5M *ᵥ Pi.single 0 1 = Pi.single 1 1 ∧ eps5M *ᵥ Pi.single 1 1 = Pi.single 2 1 ∧
      eps5M *ᵥ Pi.single 2 1 = Pi.single 3 1 := by
  decide +kernel

theorem syl5_kernels :
    (∀ v : V5, (eps5M + 1) *ᵥ v = 0 → v = 0 ∨ v = Pi.single 4 1) ∧
    (∀ v : V5, (eps5M ^ 4 + eps5M ^ 3 + eps5M ^ 2 + eps5M + 1) *ᵥ v = 0 → v 4 = 0) ∧
    (eps5M + 1) *ᵥ Pi.single 4 1 = 0 ∧
    (eps5M ^ 4 + eps5M ^ 3 + eps5M ^ 2 + eps5M + 1) *ᵥ Pi.single 0 1 = 0 := by
  decide +kernel

@[expose] def eps5 : G52 :=
  mk5 eps5M (eps5M ^ 4) syl5_facts.2.1

@[expose] def gamma5 : G52 :=
  mk5 gamma5M (gamma5M ^ 14) syl5_facts.2.2.2.2.1

@[expose] def phi5 : G52 :=
  mk5 phi5M (phi5M ^ 3) syl5_facts.2.2.2.2.2.2.2.1

theorem orderOf_eps5 : orderOf eps5 = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine orderOf_eq_prime (Units.ext ?_) fun h => syl5_facts.2.2.1 ?_
  · rw [Units.val_pow_eq_pow_val, eps5, coe_mk5, Units.val_one]
    exact syl5_facts.1
  · have := congrArg (fun g : G52 => (g : M5)) h
    simpa [eps5] using this

theorem orderOf_gamma5 : orderOf gamma5 = 15 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨Units.ext ?_, fun m hm hm0 h => syl5_facts.2.2.2.2.2.1 ⟨m, hm⟩ hm0 ?_⟩
  · rw [Units.val_pow_eq_pow_val, gamma5, coe_mk5, Units.val_one]
    exact syl5_facts.2.2.2.1
  · have := congrArg (fun g : G52 => (g : M5)) h
    simpa [gamma5, Units.val_pow_eq_pow_val] using this

theorem syl5_eq_of_commute {A B : M5} (hA : A * eps5M = eps5M * A) (hB : B * eps5M = eps5M * B)
    (h0 : A *ᵥ Pi.single 0 1 = B *ᵥ Pi.single 0 1)
    (h4 : A *ᵥ Pi.single 4 1 = B *ᵥ Pi.single 4 1) : A = B := by
  obtain ⟨h1, h2, h3⟩ := syl5_mulVec_single
  have h3' : eps5M *ᵥ Pi.single 3 1 = Pi.single 0 1 + Pi.single 1 1 + Pi.single 2 1 +
      Pi.single 3 1 := by decide
  have e1 : A *ᵥ Pi.single 1 1 = B *ᵥ Pi.single 1 1 := by
    rw [← h1, mulVec_comm hA, mulVec_comm hB, h0]
  have e2 : A *ᵥ Pi.single 2 1 = B *ᵥ Pi.single 2 1 := by
    rw [← h2, mulVec_comm hA, mulVec_comm hB, e1]
  have e3 : A *ᵥ Pi.single 3 1 = B *ᵥ Pi.single 3 1 := by
    rw [← h3, mulVec_comm hA, mulVec_comm hB, e2]
  refine ext_cols fun j => ?_
  fin_cases j
  exacts [h0, e1, e2, e3, h4]

theorem syl5_matrix_commute {g : G52} (hg : g ∈ Subgroup.centralizer {eps5}) :
    (g : M5) * eps5M = eps5M * (g : M5) := by
  have := congrArg (fun x : G52 => (x : M5)) (Subgroup.mem_centralizer_singleton_iff.1 hg)
  simpa [eps5] using this

theorem syl5_mulVec_of_commute {g : G52} (hg : g ∈ Subgroup.centralizer {eps5}) :
    (g : M5) *ᵥ Pi.single 4 1 = Pi.single 4 1 ∧ ((g : M5) *ᵥ Pi.single 0 1) 4 = 0 := by
  have hc := syl5_matrix_commute hg
  obtain ⟨hk1, hk4, h41, h04⟩ := syl5_kernels
  have hc1 : (g : M5) * (eps5M + 1) = (eps5M + 1) * (g : M5) := by
    rw [mul_add, add_mul, hc, mul_one, one_mul]
  have hc4 : (g : M5) * (eps5M ^ 4 + eps5M ^ 3 + eps5M ^ 2 + eps5M + 1) =
      (eps5M ^ 4 + eps5M ^ 3 + eps5M ^ 2 + eps5M + 1) * (g : M5) := by
    have hp : ∀ n : ℕ, (g : M5) * eps5M ^ n = eps5M ^ n * (g : M5) := fun n =>
      ((Commute.pow_right hc n)).eq
    simp only [mul_add, add_mul, hp, mul_one, one_mul, hc]
  refine ⟨?_, ?_⟩
  · have e := mulVec_comm hc1 (Pi.single 4 1)
    rw [h41, mulVec_zero] at e
    rcases hk1 _ e.symm with h | h
    · exact absurd (eq_zero_of_mulVec_eq_zero g h) (by decide)
    · exact h
  · have e := mulVec_comm hc4 (Pi.single 0 1)
    rw [h04, mulVec_zero] at e
    exact hk4 _ e.symm

theorem syl5_card_nonzero : Nat.card {v : V5 // v ≠ 0 ∧ v 4 = 0} = 15 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem syl5_card_centralizer_le : Nat.card (Subgroup.centralizer {eps5}) ≤ 15 := by
  have he : (Pi.single 0 1 : V5) ≠ 0 := by decide
  let f : Subgroup.centralizer {eps5} → {v : V5 // v ≠ 0 ∧ v 4 = 0} := fun g =>
    ⟨((g : G52) : M5) *ᵥ Pi.single 0 1, fun h => he (eq_zero_of_mulVec_eq_zero _ h),
      (syl5_mulVec_of_commute g.2).2⟩
  have hf : Function.Injective f := by
    intro g h hgh
    have e : ((g : G52) : M5) *ᵥ Pi.single 0 1 = ((h : G52) : M5) *ᵥ Pi.single 0 1 :=
      congrArg Subtype.val hgh
    refine Subtype.ext (Units.ext (syl5_eq_of_commute (syl5_matrix_commute g.2)
      (syl5_matrix_commute h.2) e ?_))
    rw [(syl5_mulVec_of_commute g.2).1, (syl5_mulVec_of_commute h.2).1]
  calc Nat.card (Subgroup.centralizer {eps5}) ≤ Nat.card {v : V5 // v ≠ 0 ∧ v 4 = 0} :=
        Nat.card_le_card_of_injective f hf
    _ = 15 := syl5_card_nonzero

theorem syl5_centralizer_eq : Subgroup.centralizer {eps5} = Subgroup.zpowers gamma5 := by
  have hle : Subgroup.zpowers gamma5 ≤ Subgroup.centralizer {eps5} := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    refine Units.ext ?_
    simp only [Units.val_mul, gamma5, eps5, coe_mk5]
    exact syl5_facts.2.2.2.2.2.2.1
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [Nat.card_zpowers, orderOf_gamma5]
  exact syl5_card_centralizer_le

theorem syl5_card_zpowers : Nat.card (Subgroup.zpowers eps5) = 5 := by
  rw [Nat.card_zpowers, orderOf_eps5]

theorem syl5_centralizer_zpowers :
    Subgroup.centralizer (Subgroup.zpowers eps5 : Set G52) = Subgroup.zpowers gamma5 := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure, syl5_centralizer_eq]

theorem syl5_phi_pow_mul :
    phi5 ^ 1 * eps5 = eps5 ^ 2 * phi5 ^ 1 ∧ phi5 ^ 2 * eps5 = eps5 ^ 4 * phi5 ^ 2 ∧
      phi5 ^ 3 * eps5 = eps5 ^ 3 * phi5 ^ 3 := by
  refine ⟨Units.ext ?_, Units.ext ?_, Units.ext ?_⟩ <;>
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, phi5, eps5, coe_mk5, pow_one]
  · exact syl5_facts.2.2.2.2.2.2.2.2.1
  · exact syl5_facts.2.2.2.2.2.2.2.2.2.1
  · exact syl5_facts.2.2.2.2.2.2.2.2.2.2.1

theorem syl5_phi_mem_normalizer :
    phi5 ∈ Subgroup.normalizer (Subgroup.zpowers eps5 : Set G52) := by
  have h := syl5_phi_pow_mul.1
  simp only [pow_one] at h
  have e : phi5 * eps5 * phi5⁻¹ = eps5 ^ 2 := by rw [h, mul_inv_cancel_right]
  exact mem_normalizer_zpowers_of_conj_mem (e ▸ Subgroup.pow_mem _ (Subgroup.mem_zpowers eps5) 2)

theorem syl5_cover {g : G52} (hg : g ∈ Subgroup.normalizer (Subgroup.zpowers eps5 : Set G52)) :
    ∃ j < 4, (phi5 ^ j)⁻¹ * g ∈ Subgroup.zpowers gamma5 := by
  classical
  have hmem : g * eps5 * g⁻¹ ∈ Subgroup.zpowers eps5 :=
    (Subgroup.mem_normalizer_iff.1 hg eps5).1 (Subgroup.mem_zpowers eps5)
  rw [mem_zpowers_iff_mem_range_orderOf, orderOf_eps5] at hmem
  obtain ⟨k, hk, hgk⟩ := Finset.mem_image.1 hmem
  rw [Finset.mem_range] at hk
  have hconj : ∀ j : ℕ, phi5 ^ j * eps5 = eps5 ^ k * phi5 ^ j →
      (phi5 ^ j)⁻¹ * g ∈ Subgroup.zpowers gamma5 := by
    intro j hj
    rw [← syl5_centralizer_eq, Subgroup.mem_centralizer_singleton_iff]
    have hgs : g * eps5 = eps5 ^ k * g := by rw [hgk, inv_mul_cancel_right]
    calc (phi5 ^ j)⁻¹ * g * eps5 = (phi5 ^ j)⁻¹ * (eps5 ^ k * g) := by rw [mul_assoc, hgs]
      _ = (phi5 ^ j)⁻¹ * (phi5 ^ j * eps5 * (phi5 ^ j)⁻¹ * g) := by
          rw [hj, mul_inv_cancel_right]
      _ = eps5 * ((phi5 ^ j)⁻¹ * g) := by group
  obtain ⟨h1, h2, h3⟩ := syl5_phi_pow_mul
  interval_cases k
  · exfalso
    rw [pow_zero] at hgk
    have : eps5 = 1 := by
      have := congrArg (fun x => g⁻¹ * x * g) hgk
      simpa [mul_assoc] using this.symm
    have h := orderOf_eps5
    rw [this, orderOf_one] at h
    norm_num at h
  · exact ⟨0, by norm_num, hconj 0 (by simp)⟩
  · exact ⟨1, by norm_num, hconj 1 h1⟩
  · exact ⟨3, by norm_num, hconj 3 h3⟩
  · exact ⟨2, by norm_num, hconj 2 h2⟩

theorem syl5_disj (j : ℕ) (hj : j < 4) (h : phi5 ^ j ∈ Subgroup.zpowers gamma5) : j = 0 := by
  by_contra hj0
  rw [← syl5_centralizer_eq, Subgroup.mem_centralizer_singleton_iff] at h
  apply syl5_facts.2.2.2.2.2.2.2.2.2.2.2 ⟨j, hj⟩ hj0
  have := congrArg (fun x : G52 => (x : M5)) h
  simpa [phi5, eps5, Units.val_pow_eq_pow_val] using this

theorem syl5_card_normalizer :
    Nat.card (Subgroup.normalizer (Subgroup.zpowers eps5 : Set G52)) = 60 := by
  have hCN : Subgroup.zpowers gamma5 ≤ Subgroup.normalizer (Subgroup.zpowers eps5 : Set G52) := by
    rw [Subgroup.zpowers_le]
    refine mem_normalizer_zpowers_of_conj_mem ?_
    have hc : gamma5 ∈ Subgroup.centralizer {eps5} := by
      rw [syl5_centralizer_eq]
      exact Subgroup.mem_zpowers gamma5
    rw [Subgroup.mem_centralizer_singleton_iff.1 hc, mul_inv_cancel_right]
    exact Subgroup.mem_zpowers eps5
  rw [card_eq_mul_of_cosets hCN syl5_phi_mem_normalizer (fun g hg => syl5_cover hg) syl5_disj,
    Nat.card_zpowers, orderOf_gamma5]

theorem syl5_card_sylow (P : Sylow 5 G52) : Nat.card P = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact card_sylow_of_card_eq_prime_mul (m := 1999872) (by rw [card_G52]; norm_num) (by norm_num) P

theorem syl5_structure (F : Sylow 5 G52) :
    IsCyclic (Subgroup.centralizer (F : Set G52)) ∧
    Nat.card (Subgroup.centralizer (F : Set G52)) = 15 ∧
    Nat.card (Subgroup.normalizer (F : Set G52)) = 60 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨Q, hQ⟩ := exists_sylow_eq_of_card syl5_card_zpowers syl5_card_sylow
  obtain ⟨c, hc⟩ := exists_eq_map_conj_sylow Q F
  rw [hQ] at hc
  have hF : ((F : Set G52)) = ((F : Subgroup G52) : Set G52) := rfl
  rw [hF, hc, normalizer_map_conj, centralizer_map_conj, syl5_centralizer_zpowers]
  have hinj : Function.Injective (MulAut.conj c).toMonoidHom := (MulAut.conj c).injective
  refine ⟨?_, ?_, ?_⟩
  · exact isCyclic_of_surjective (Subgroup.equivMapOfInjective _ _ hinj).toMonoidHom
      (Subgroup.equivMapOfInjective _ _ hinj).surjective
  · rw [Subgroup.card_map_of_injective hinj, Nat.card_zpowers, orderOf_gamma5]
  · rw [Subgroup.card_map_of_injective hinj, syl5_card_normalizer]

end CFSG.GroupTheory.GL52
