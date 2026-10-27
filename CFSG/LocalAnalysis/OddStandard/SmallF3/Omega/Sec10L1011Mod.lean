module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Comb5
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L1011Moda
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L107bAux

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

@[expose] def sec1011_wfour (i : Fin 5) : Fin 5 → ZMod 2 := fun j => if j = i then 0 else 1

theorem sec1011_wfour_weight (i : Fin 5) : vecWeight (sec1011_wfour i) = 4 := by
  revert i
  unfold vecWeight sec1011_wfour
  decide +kernel

theorem sec1011_wfour_even (i : Fin 5) : IsEvenVec (sec1011_wfour i) := by
  revert i
  unfold IsEvenVec sec1011_wfour
  decide +kernel

theorem sec1011_wfour_injective : Function.Injective sec1011_wfour := by
  unfold Function.Injective sec1011_wfour
  decide +kernel

theorem sec1011_exists_wfour (v : Fin 5 → ZMod 2) (hv : vecWeight v = 4) :
    ∃ i, v = sec1011_wfour i := by
  revert v
  unfold vecWeight sec1011_wfour
  decide +kernel

theorem sec1011_wfour_add_weight {i j : Fin 5} (h : i ≠ j) :
    vecWeight (sec1011_wfour i + sec1011_wfour j) = 2 := by
  revert i j
  unfold vecWeight sec1011_wfour
  decide +kernel

theorem sec1011_exists_wfour_add (v : Fin 5 → ZMod 2) (hv : vecWeight v = 2) :
    ∃ i j : Fin 5, i ≠ j ∧ v = sec1011_wfour i + sec1011_wfour j := by
  revert v
  unfold vecWeight sec1011_wfour
  decide +kernel

theorem sec1011_permVec_add {n : ℕ} (σ : Equiv.Perm (Fin n)) (v w : Fin n → ZMod 2) :
    permVec σ (v + w) = permVec σ v + permVec σ w := by
  funext i
  simp only [permVec, Function.comp_apply, Pi.add_apply]

theorem sec1011_permVec_single {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    permVec σ (Pi.single i (1 : ZMod 2)) = Pi.single (σ i) (1 : ZMod 2) := by
  funext j
  unfold permVec
  simp only [Function.comp_apply, Pi.single_apply]
  by_cases h : j = σ i
  · have h' : σ.symm j = i := (Equiv.symm_apply_eq σ).mpr h
    simp [h, h']
  · have h' : σ.symm j ≠ i := fun hh => h ((Equiv.symm_apply_eq σ).mp hh)
    simp [h, h']

theorem sec1011_isEvenVec_add {n : ℕ} {v w : Fin n → ZMod 2} (hv : IsEvenVec v)
    (hw : IsEvenVec w) : IsEvenVec (v + w) := by
  unfold IsEvenVec at *
  simp only [Pi.add_apply]
  rw [Finset.sum_add_distrib, hv, hw, add_zero]

theorem sec1011_vec_add_self {n : ℕ} (v : Fin n → ZMod 2) : v + v = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (v i)

theorem sec1011_alt_weight_two (v u : Fin 5 → ZMod 2) (hv : vecWeight v = 2)
    (hu : vecWeight u = 2) : ∃ σ ∈ alternatingGroup (Fin 5), permVec σ v = u := by
  revert v u
  unfold vecWeight permVec
  simp only [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

theorem sec1011_weight_four_sum_two (w : Fin 5 → ZMod 2) (hw : vecWeight w = 4) :
    ∃ x y : Fin 5 → ZMod 2, vecWeight x = 2 ∧ vecWeight y = 2 ∧ w = x + y := by
  revert w
  unfold vecWeight
  decide +kernel

theorem sec1011_alt5_irreducible (U : Set (Fin 5 → ZMod 2)) (hev : ∀ u ∈ U, IsEvenVec u)
    (hadd : ∀ u ∈ U, ∀ w ∈ U, u + w ∈ U)
    (hperm : ∀ σ ∈ alternatingGroup (Fin 5), ∀ u ∈ U, permVec σ u ∈ U)
    (hne : ∃ u ∈ U, u ≠ 0) : ∀ w : Fin 5 → ZMod 2, IsEvenVec w → w ∈ U := by
  obtain ⟨u, huU, hu0⟩ := hne
  have hu_even : IsEvenVec u := hev u huU
  have hzero : (0 : Fin 5 → ZMod 2) ∈ U := by
    have hz := hadd u huU u huU
    rwa [sec1011_vec_add_self] at hz
  have h2mem : ∀ v, vecWeight v = 2 → v ∈ U := by
    intro v hv
    rcases even_weight_cases_five u hu_even with hu0' | hu2 | hu4
    · exact absurd hu0' hu0
    · obtain ⟨σ, hσ, hσu⟩ := sec1011_alt_weight_two u v hu2 hv
      rw [← hσu]
      exact hperm σ hσ u huU
    · obtain ⟨x, y, hx, hy, hxy⟩ := weight_two_sum_five v hv
      rw [hxy]
      exact hadd x (by
          obtain ⟨σ, hσ, hσx⟩ := exists_alt_permVec_weight_four u x hu4 hx
          rw [← hσx]
          exact hperm σ hσ u huU)
        y (by
          obtain ⟨σ, hσ, hσy⟩ := exists_alt_permVec_weight_four u y hu4 hy
          rw [← hσy]
          exact hperm σ hσ u huU)
  have h4mem : ∀ v, vecWeight v = 4 → v ∈ U := by
    intro v hv
    rcases even_weight_cases_five u hu_even with hu0' | hu2 | hu4
    · exact absurd hu0' hu0
    · obtain ⟨x, y, hx, hy, hxy⟩ := sec1011_weight_four_sum_two v hv
      rw [hxy]
      exact hadd x (h2mem x hx) y (h2mem y hy)
    · obtain ⟨σ, hσ, hσu⟩ := exists_alt_permVec_weight_four u v hu4 hv
      rw [← hσu]
      exact hperm σ hσ u huU
  intro w hw
  rcases even_weight_cases_five w hw with h0 | h2 | h4
  · rw [h0]
    exact hzero
  · exact h2mem w h2
  · exact h4mem w h4

theorem sec1011_alt3_fixing (v : Fin 5 → ZMod 2) (hv : vecWeight v = 4) :
    ∃ σ ∈ alternatingGroup (Fin 5), σ ≠ 1 ∧ σ ^ 3 = 1 ∧ permVec σ v = v := by
  revert v
  unfold vecWeight permVec
  simp only [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

theorem sec1011_five_comm_cube (σ1 σ2 : Equiv.Perm (Fin 5)) (h1 : σ1 ^ 3 = 1) (h2 : σ2 ^ 3 = 1)
    (hc : σ1 * σ2 = σ2 * σ1) (w1 w2 : Fin 5 → ZMod 2) (hw1 : IsEvenVec w1)
    (hw2 : IsEvenVec w2) :
    vecWeight ((w1 + permVec σ1 w1) + (w2 + permVec σ2 w2)) ≤ 2 := by
  rcases sec1011_comm_cube_cases σ1 σ2 h1 h2 hc with h | h | h | h
  · rw [h]
    have hz : w1 + permVec (1 : Equiv.Perm (Fin 5)) w1 = 0 := by
      rw [permVec_one]
      exact sec1011_vec_add_self w1
    rw [hz, zero_add]
    exact sec1011_cube_bound σ2 h2 w2 hw2
  · rw [h]
    have hz : w2 + permVec (1 : Equiv.Perm (Fin 5)) w2 = 0 := by
      rw [permVec_one]
      exact sec1011_vec_add_self w2
    rw [hz, add_zero]
    exact sec1011_cube_bound σ1 h1 w1 hw1
  · rw [h]
    have heq : (w1 + permVec σ1 w1) + (w2 + permVec σ1 w2)
        = (w1 + w2) + permVec σ1 (w1 + w2) := by
      rw [sec1011_permVec_add]
      abel
    rw [heq]
    exact sec1011_cube_bound σ1 h1 (w1 + w2) (sec1011_isEvenVec_add hw1 hw2)
  · rw [h]
    exact sec1011_cube_inv_bound σ1 h1 w1 w2 hw1 hw2

theorem sec1011_alt5_normal_two (P : Subgroup ↥(alternatingGroup (Fin 5))) (hP : P.Normal)
    (h2 : IsPGroup 2 P) : P = ⊥ := by
  rcases Subgroup.Normal.eq_bot_or_eq_top P with h | h
  · exact h
  · exfalso
    have hcardA : Nat.card (alternatingGroup (Fin 5)) = 60 := by
      rw [nat_card_alternatingGroup]
      norm_num
    have hPcard : Nat.card P = 60 := by
      rw [h]
      simpa using hcardA
    obtain ⟨k, hk⟩ := h2.exists_card_eq
    have h3 : (3 : ℕ) ∣ 2 ^ k := by
      rw [← hk, hPcard]
      norm_num
    have h32 : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by norm_num) h3
    norm_num at h32

theorem sec1011_perm5_normal_two (P : Subgroup (Equiv.Perm (Fin 5))) (hP : P.Normal)
    (h2 : IsPGroup 2 P) : P = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  simp only [Subgroup.mem_bot]
  by_contra hx1
  obtain ⟨k, hk⟩ := h2.exists_card_eq
  have hmul : Nat.card P * P.index = 120 := by
    have := Subgroup.card_mul_index (H := P)
    rwa [sec1011_card_perm_five] at this
  have hdvd120 : 2 ^ k ∣ 120 := by
    rw [← hk]
    exact ⟨P.index, hmul.symm⟩
  have hk_le : k ≤ 3 := by
    by_contra hk4
    push_neg at hk4
    have hk4' : 4 ≤ k := by omega
    have h16dvd : 16 ∣ 2 ^ k := by
      simpa using (pow_dvd_pow 2 hk4' : 2 ^ 4 ∣ 2 ^ k)
    exact (by norm_num : ¬ (16 : ℕ) ∣ 120) (dvd_trans h16dvd hdvd120)
  have hx4 : x ^ 4 = 1 := by
    have hdvd : orderOf x ∣ 2 ^ k := by
      rw [← hk]
      exact Subgroup.orderOf_dvd_natCard P hx
    exact sec1011_perm5_two_pow_bounded x ⟨k, hk_le, (orderOf_dvd_iff_pow_eq_one).mp hdvd⟩
  obtain ⟨g, hg⟩ := sec1011_perm5_conj_four x hx1 hx4
  have hconj : g * x * g⁻¹ ∈ P := hP.conj_mem x hx g
  have hprod : x * (g * x * g⁻¹) ∈ P := P.mul_mem hx hconj
  have hprod4 : (x * (g * x * g⁻¹)) ^ 4 = 1 := by
    have hdvd : orderOf (x * (g * x * g⁻¹)) ∣ 2 ^ k := by
      rw [← hk]
      exact Subgroup.orderOf_dvd_natCard P hprod
    exact sec1011_perm5_two_pow_bounded _
      ⟨k, hk_le, (orderOf_dvd_iff_pow_eq_one).mp hdvd⟩
  exact hg hprod4

theorem sec1011_eq_alt_six (X : Subgroup (Equiv.Perm (Fin 6))) (h : Nat.card X = 360) :
    X = alternatingGroup (Fin 6) := by
  apply Equiv.Perm.eq_alternatingGroup_of_index_eq_two
  have hmul : Nat.card X * X.index = Nat.card (Equiv.Perm (Fin 6)) :=
    Subgroup.card_mul_index (H := X)
  rw [h, sec1011_card_perm_six] at hmul
  omega

theorem sec1011_eq_top_six (X : Subgroup (Equiv.Perm (Fin 6))) (h : Nat.card X = 720) :
    X = ⊤ := by
  apply Subgroup.eq_top_of_card_eq
  rw [h, sec1011_card_perm_six]

@[expose] def sec1011_one6 : Fin 6 → ZMod 2 := fun _ => 1

@[expose] def sec1011_vtriple : Fin 6 → ZMod 2 := Pi.single 0 1 + Pi.single 1 1 + Pi.single 2 1

@[expose] def sec1011_rho1 : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 1 2

@[expose] def sec1011_rho2 : Equiv.Perm (Fin 6) := Equiv.swap 3 4 * Equiv.swap 4 5

theorem sec1011_rho_mem_alt :
    sec1011_rho1 ∈ alternatingGroup (Fin 6) ∧ sec1011_rho2 ∈ alternatingGroup (Fin 6) := by
  unfold sec1011_rho1 sec1011_rho2
  simp only [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

theorem sec1011_rho_comm : sec1011_rho1 * sec1011_rho2 = sec1011_rho2 * sec1011_rho1 := by
  unfold sec1011_rho1 sec1011_rho2
  decide +kernel

theorem sec1011_rho_cube : sec1011_rho1 ^ 3 = 1 ∧ sec1011_rho2 ^ 3 = 1 := by
  unfold sec1011_rho1 sec1011_rho2
  decide +kernel

theorem sec1011_rho_fix :
    permVec sec1011_rho1 sec1011_vtriple = sec1011_vtriple ∧
      permVec sec1011_rho2 sec1011_vtriple = sec1011_vtriple := by
  unfold sec1011_rho1 sec1011_rho2 sec1011_vtriple permVec
  decide +kernel

theorem sec1011_rho_span (u : Fin 6 → ZMod 2) (hu : IsEvenVec u) :
    ∃ w1 w2 : Fin 6 → ZMod 2, IsEvenVec w1 ∧ IsEvenVec w2 ∧
      (u = (w1 + permVec sec1011_rho1 w1) + (w2 + permVec sec1011_rho2 w2) ∨
        u + sec1011_one6 = (w1 + permVec sec1011_rho1 w1) + (w2 + permVec sec1011_rho2 w2)) := by
  revert hu
  revert u
  unfold IsEvenVec sec1011_one6 sec1011_rho1 sec1011_rho2 permVec
  decide +kernel

end CFSG.OddStandard.SmallF3.Omega
