module

public import CFSG.ClassicalInvolution.Phan.Geometry.NondegComplex
public import CFSG.ClassicalInvolution.Phan.Geometry.Collinear
import CFSG.Monster.B.Recog.GenericWalkHomotopy

public section

namespace CFSG.ClassicalInvolution.Phan

open CFSG.ClassicalGroups.Unitary Module CFSG.Monster.B.Recog

variable {K : Type*} [Field K] {σ : K ≃+* K} {d : ℕ} [Finite K]

private theorem ndq_norm_one (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4)
    {a : K} (ha : a ≠ 0) : σ a * a = 1 := by
  classical
  let : Fintype K := Fintype.ofFinite K
  have hcard_units : Nat.card Kˣ = 3 := by
    have hcard : Fintype.card K = 4 := by rwa [Nat.card_eq_fintype_card] at hK
    have h := Fintype.card_eq_card_units_add_one (α := K)
    have h' : Fintype.card Kˣ = 3 := by
      have h1 : 4 = Fintype.card Kˣ + 1 := by rw [← hcard]; exact h
      have h2 : Nat.succ 3 = Nat.succ (Fintype.card Kˣ) := by simpa using h1
      exact (Nat.succ.inj h2).symm
    rwa [Nat.card_eq_fintype_card]
  let H : Subgroup Kˣ := {
    carrier := {x | σ (x : K) = x}
    one_mem' := by simp
    mul_mem' := by
      intro x y hx hy
      simp only [Set.mem_setOf_eq] at hx hy ⊢
      rw [Units.val_mul, map_mul, hx, hy]
    inv_mem' := by
      intro x hx
      simp only [Set.mem_setOf_eq] at hx ⊢
      rw [Units.val_inv_eq_inv_val, map_inv₀, hx]
  }
  have hH_ne_top : H ≠ ⊤ := by
    obtain ⟨c, hc⟩ := hσ.exists_ne
    have hc0 : c ≠ 0 := by
      intro h; rw [h, map_zero] at hc; exact hc rfl
    let u : Kˣ := Units.mk0 c hc0
    intro htop
    have : u ∈ H := by rw [htop]; exact Subgroup.mem_top u
    exact hc this
  have hdvd : Nat.card H ∣ Nat.card Kˣ := Subgroup.card_subgroup_dvd_card H
  have hH_card : Nat.card H = 1 := by
    have hdvd' : Nat.card H ∣ 3 := by rwa [hcard_units] at hdvd
    have hH_ne_three : Nat.card H ≠ 3 := by
      intro h3
      have htop : H = ⊤ := by
        apply Subgroup.eq_top_of_card_eq H
        rw [h3, hcard_units]
      exact hH_ne_top htop
    have hdiv := Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three (Nat.card H) hdvd'
    rcases hdiv with h1 | h3
    · exact h1
    · exact absurd h3 hH_ne_three
  have hH_eq_bot : H = ⊥ := Subgroup.eq_bot_of_card_eq H hH_card
  have hnorm_fixed : σ ((σ a) * a) = (σ a) * a := by
    rw [map_mul, hσ.invol]
    exact mul_comm _ _
  have hσa0 : σ a ≠ 0 := (map_ne_zero σ).mpr ha
  have hnorm_mem : (Units.mk0 ((σ a) * a) (mul_ne_zero hσa0 ha)) ∈ H := hnorm_fixed
  have hone : (Units.mk0 ((σ a) * a) (mul_ne_zero hσa0 ha)) = 1 := by
    rw [hH_eq_bot] at hnorm_mem
    simpa using hnorm_mem
  simpa using congrArg (fun x : Kˣ => (x : K)) hone

private theorem ndq_char_two (hK : Nat.card K = 4) : (2 : K) = 0 := by
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 4 := by rwa [Nat.card_eq_fintype_card] at hK
  have h2 : Fintype.card K = 2 ^ 2 := by rw [hcard]; norm_num
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2) h2
  exact CharP.cast_eq_zero K 2

omit [Finite K] in
private theorem ndq_sum_zero_or_one (h2 : (2 : K) = 0) {n : ℕ} (f : Fin n → K)
    (hf : ∀ i, f i = 0 ∨ f i = 1) : ∑ i, f i = 0 ∨ ∑ i, f i = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    have h := ih (fun i => f i.succ) (fun i => hf i.succ)
    have hone : (1 : K) + 1 = 0 := by
      rw [one_add_one_eq_two]
      exact h2
    rcases h with h0 | h1
    · rcases hf 0 with hf0 | hf1
      · left; rw [hf0, h0, add_zero]
      · right; rw [hf1, h0, add_zero]
    · rcases hf 0 with hf0 | hf1
      · right; rw [hf0, h1, zero_add]
      · left; rw [hf1, h1]
        exact hone

private theorem ndq_herm_self_eq_one (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4)
    {u : Fin d → K} (hu : u ≠ 0) (hnd : Nondeg σ (K ∙ u)) : herm σ u u = 1 := by
  have h2 : (2 : K) = 0 := ndq_char_two hK
  have hterm : ∀ i, σ (u i) * u i = 0 ∨ σ (u i) * u i = 1 := by
    intro i
    by_cases hi : u i = 0
    · left; rw [hi, mul_zero]
    · right; exact ndq_norm_one hσ hK hi
  have hsum := ndq_sum_zero_or_one h2 (fun i => σ (u i) * u i) hterm
  rcases hsum with h0 | h1
  · exfalso
    have h0' : herm σ u u = 0 := by simpa [herm] using h0
    exact herm_self_ne_zero_of_nondeg_span hu hnd h0'
  · simpa [herm] using h1

theorem isCollinear_iff_orth (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4)
    {x y : Submodule K (Fin d → K)} (hx : x ∈ nsPts σ ⊤) (hy : y ∈ nsPts σ ⊤) :
    IsCollinear σ x y ↔ Orth σ x y := by
  obtain ⟨u, hu_ne, -, hx_eq⟩ := mem_nsPts_iff.mp hx
  obtain ⟨v, hv_ne, -, hy_eq⟩ := mem_nsPts_iff.mp hy
  rw [hx_eq, hy_eq]
  have hu0 : u ≠ 0 := by
    intro h
    have : herm σ u u = 0 := by rw [h]; simp
    exact hu_ne this
  have hv0 : v ≠ 0 := by
    intro h
    have : herm σ v v = 0 := by rw [h]; simp
    exact hv_ne this
  have hu1 : herm σ u u = 1 := ndq_herm_self_eq_one hσ hK hu0 (nondeg_span_singleton hu_ne)
  have hv1 : herm σ v v = 1 := ndq_herm_self_eq_one hσ hK hv0 (nondeg_span_singleton hv_ne)
  have hdet : herm σ u u * herm σ v v - herm σ u v * herm σ v u =
      1 - herm σ u v * σ (herm σ u v) := by
    rw [hu1, hv1, one_mul, herm_conj σ hσ.invol u v]
  rw [isCollinear_span_iff hσ hu_ne hv_ne, orth_span_singleton_iff, hdet]
  constructor
  · intro hnd
    by_contra hne
    have hnorm : herm σ u v * σ (herm σ u v) = 1 := by
      rw [mul_comm, ndq_norm_one hσ hK hne]
    rw [hnorm, sub_self] at hnd
    exact hnd rfl
  · intro hzero
    rw [hzero, zero_mul, sub_zero]
    exact one_ne_zero

omit [Finite K] in
theorem NdVert.exists_nsPts_le {W : Submodule K (Fin d → K)} (hσ : IsUnitaryInvolution σ)
    (S : NdVert σ W) : ∃ p ∈ nsPts σ W, p ≤ S.1 := by
  have hSnd : Nondeg σ S.1 := S.2.2.2.2
  have hSne : S.1 ≠ ⊥ := S.2.2.1
  obtain ⟨p, hp⟩ := nsPts_nonempty_of_nondeg hσ hSnd hSne
  exact ⟨p, ⟨hp.1.trans S.2.1, hp.2.1, hp.2.2⟩, hp.1⟩

omit [Finite K] in
theorem exists_ndVert_lt_of_orth {W : Submodule K (Fin d → K)} (hσ : IsUnitaryInvolution σ)
    (hd : 3 ≤ finrank K W) {p q : Submodule K (Fin d → K)} (hp : p ∈ nsPts σ W)
    (hq : q ∈ nsPts σ W) (hpq : p ≠ q) (horth : Orth σ p q) :
    ∃ S : NdVert σ W, p < S.1 ∧ q < S.1 := by
  have hPnd : Nondeg σ (p ⊔ q) := Nondeg.sup_of_orth hσ hp.2.2 hq.2.2 horth
  have hPW : p ⊔ q ≤ W := sup_le hp.1 hq.1
  have hPdim : finrank K ↥(p ⊔ q) = 2 := finrank_sup_of_ne_pts hp.2.1 hq.2.1 hpq
  have hPneW : p ⊔ q ≠ W := by
    intro h
    rw [h] at hPdim
    omega
  have hPneBot : p ⊔ q ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hPdim
    omega
  refine ⟨⟨p ⊔ q, hPW, hPneBot, hPneW, hPnd⟩, ?_, ?_⟩
  · rw [lt_iff_le_and_ne]
    refine ⟨le_sup_left, fun h => ?_⟩
    have h_eq : p ⊔ q = p := by
      rw [h]
      simp
    rw [h_eq, hp.2.1] at hPdim
    omega
  · rw [lt_iff_le_and_ne]
    refine ⟨le_sup_right, fun h => ?_⟩
    have h_eq : p ⊔ q = q := by
      rw [h]
      simp
    rw [h_eq, hq.2.1] at hPdim
    omega

end CFSG.ClassicalInvolution.Phan
