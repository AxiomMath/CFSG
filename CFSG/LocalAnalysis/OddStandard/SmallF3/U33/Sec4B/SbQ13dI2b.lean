module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13dI2b0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13dI1b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13dI2a

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem q13d_I_card_P1_cent_f_le (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hI : closure ({t, om} : Set G) ⊓
      centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) = closure ({tau, om} : Set G))
    (hlo : lam * om * lam⁻¹ = om) :
    Nat.card ↥((q13A t tau x₁ x₂ rho ⊔ closure ({tau, om} : Set G)) ⊓ centralizer ({t * lam} :
      Set G)) ≤ 8 := by
  let A := q13A t tau x₁ x₂ rho
  let P1 := A ⊔ closure ({tau, om} : Set G)
  let C := centralizer ({t * lam} : Set G)
  have htau_mem : tau ∈ closure ({t, om} : Set G) := q13dI2b_tau_mem h
  have hsub : P1 ⊓ C ≤ (A ⊓ C) ⊔ zpowers tau := by
    intro p hp
    obtain ⟨hp1, hpC⟩ := Subgroup.mem_inf.mp hp
    obtain ⟨a, haA, hcases⟩ := (q13d_I_mem_P1 h hI).mp hp1
    have hpconj : (t * lam) * p * (t * lam)⁻¹ = p := by
      have hcomm : p * (t * lam) = (t * lam) * p :=
        Subgroup.mem_centralizer_singleton_iff.mp hpC
      calc (t * lam) * p * (t * lam)⁻¹ = (p * (t * lam)) * (t * lam)⁻¹ := by rw [hcomm]
        _ = p := by group
    obtain ⟨hc1, hcτ, hcom, hcτω⟩ := q13dI2b_conj_cases h hlo haA
    have hbA : lam * a * lam⁻¹ ∈ A := (q13a_A_inv h a haA).2.1
    rcases hcases with rfl | rfl | rfl | rfl
    · simpa using Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨haA, hpC⟩)
        (Subgroup.one_mem (zpowers tau))
    · have hEq : (lam * a * lam⁻¹)⁻¹ * tau = a * tau := by
        rw [← hcτ]; exact hpconj
      have hb1 : (lam * a * lam⁻¹)⁻¹ = a := by
        have hh := congrArg (fun z => z * tau) hEq
        simpa [mul_assoc, q13a_tau_mul_self h] using hh
      have hconj : (t * lam) * a * (t * lam)⁻¹ = a := by rw [hc1, hb1]
      have haC : a ∈ C := q13dI2b_mem_cent_of_conj h hconj
      exact Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨haA, haC⟩) (Subgroup.mem_zpowers tau)
    · exfalso
      have hEq : (lam * a * lam⁻¹)⁻¹ * (om * tau) = a * om := by
        rw [← hcom]; exact hpconj
      have h2 : (lam * a * lam⁻¹)⁻¹ * tau = a := by
        have h3 : ((lam * a * lam⁻¹)⁻¹ * (om * tau)) * om = (a * om) * om := by rw [hEq]
        have h4 : ((lam * a * lam⁻¹)⁻¹ * (om * tau)) * om =
            (lam * a * lam⁻¹)⁻¹ * tau := by
          rw [mul_assoc, q13dI2b_om_tau_om h]
        have h5 : (a * om) * om = a := by rw [mul_assoc, h.om_sq, mul_one]
        rw [h4, h5] at h3
        exact h3
      have hb : lam * a * lam⁻¹ = tau * a⁻¹ := by
        have h6 : (lam * a * lam⁻¹)⁻¹ = a * tau := by
          have hh := congrArg (fun z => z * tau) h2
          simpa [mul_assoc, q13a_tau_mul_self h] using hh
        calc lam * a * lam⁻¹ = ((lam * a * lam⁻¹)⁻¹)⁻¹ := by group
          _ = (a * tau)⁻¹ := by rw [h6]
          _ = tau⁻¹ * a⁻¹ := by group
          _ = tau * a⁻¹ := by rw [inv_eq_of_mul_eq_one_right (q13a_tau_mul_self h)]
      have htau : tau = (lam * a * lam⁻¹) * a := by rw [hb]; group
      have htauA : tau ∈ A := by rw [htau]; exact Subgroup.mul_mem A hbA haA
      exact q13d_tau_not_mem_A h htauA
    · exfalso
      have hEq : (lam * a * lam⁻¹)⁻¹ * om = a * (tau * om) := by
        rw [← hcτω]; exact hpconj
      have h2 : (lam * a * lam⁻¹)⁻¹ = a * tau := by
        have h3 : ((lam * a * lam⁻¹)⁻¹ * om) * om = (a * (tau * om)) * om := by rw [hEq]
        have h4 : ((lam * a * lam⁻¹)⁻¹ * om) * om = (lam * a * lam⁻¹)⁻¹ := by
          rw [mul_assoc, h.om_sq, mul_one]
        have h5 : (a * (tau * om)) * om = a * tau := by
          rw [mul_assoc, mul_assoc, h.om_sq, mul_one]
        rw [h4, h5] at h3
        exact h3
      have hb : lam * a * lam⁻¹ = tau * a⁻¹ := by
        calc lam * a * lam⁻¹ = ((lam * a * lam⁻¹)⁻¹)⁻¹ := by group
          _ = (a * tau)⁻¹ := by rw [h2]
          _ = tau⁻¹ * a⁻¹ := by group
          _ = tau * a⁻¹ := by rw [inv_eq_of_mul_eq_one_right (q13a_tau_mul_self h)]
      have htau : tau = (lam * a * lam⁻¹) * a := by rw [hb]; group
      have htauA : tau ∈ A := by rw [htau]; exact Subgroup.mul_mem A hbA haA
      exact q13d_tau_not_mem_A h htauA
  have hnorm : ∀ k ∈ zpowers tau, ∀ y ∈ A ⊓ C, k * y * k⁻¹ ∈ A ⊓ C := by
    intro k hk y hy
    obtain ⟨hyA, hyC⟩ := Subgroup.mem_inf.mp hy
    have hky : k * y * k⁻¹ = y := by
      have htau_cent : tau ∈ centralizer ({y} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.mpr (q13d_A_cent_tau h y hyA).symm
      have hkz : k ∈ centralizer ({y} : Set G) := Subgroup.zpowers_le.mpr htau_cent hk
      have hcomm : k * y = y * k := Subgroup.mem_centralizer_singleton_iff.mp hkz
      calc k * y * k⁻¹ = (y * k) * k⁻¹ := by rw [hcomm]
        _ = y := by group
    rw [hky]; exact Subgroup.mem_inf.mpr ⟨hyA, hyC⟩
  have hbot : (A ⊓ C) ⊓ zpowers tau = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxA, hxzp⟩ := Subgroup.mem_inf.mp hx
    have hxco : x ∈ closure ({t, om} : Set G) := Subgroup.zpowers_le.mpr htau_mem hxzp
    exact q13d_A_inf_CO h x (Subgroup.mem_inf.mp hxA).1 hxco
  have hcardT : Nat.card ↥((A ⊓ C) ⊔ zpowers tau) =
      Nat.card ↥(A ⊓ C) * Nat.card ↥(zpowers tau) := card_sup_eq_mul hnorm hbot
  have hA4 : Nat.card ↥(A ⊓ C) = 4 := q13a_card_CA_tlam h
  have hz2 : Nat.card ↥(zpowers tau) = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by simpa [pow_two] using q13a_tau_mul_self h) (q13b_tau_ne_one h)
  calc Nat.card ↥(P1 ⊓ C) ≤ Nat.card ↥((A ⊓ C) ⊔ zpowers tau) :=
        Subgroup.card_le_of_le hsub
    _ = Nat.card ↥(A ⊓ C) * Nat.card ↥(zpowers tau) := hcardT
    _ = 4 * 2 := by rw [hA4, hz2]
    _ = 8 := by norm_num

theorem q13d_I_card_E0_cent_f_le (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hI : closure ({t, om} : Set G) ⊓
      centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) = closure ({tau, om} : Set G))
    (hlo : lam * om * lam⁻¹ = om) :
    Nat.card ↥(q13E0 t tau x₁ x₂ rho om ⊓ centralizer ({t * lam} : Set G)) ≤ 16 := by
  let A := q13A t tau x₁ x₂ rho
  let P1 := A ⊔ closure ({tau, om} : Set G)
  let E0 := q13E0 t tau x₁ x₂ rho om
  let C := centralizer ({t * lam} : Set G)
  have hle1 : Nat.card ↥(P1 ⊓ C) ≤ 8 := q13d_I_card_P1_cent_f_le h hI hlo
  have hBA : E0 ⊓ C ≤ E0 := inf_le_left
  have hQA : P1.relIndex E0 = 2 := q13d_I_relIndex h hI
  have h1 := card_le_two_mul_card_inf (A := E0) (B := E0 ⊓ C) (Q := P1) hBA hQA
  have h2 : (E0 ⊓ C) ⊓ P1 ≤ P1 ⊓ C :=
    le_inf inf_le_right (inf_le_left.trans inf_le_right)
  have h3 : Nat.card ↥((E0 ⊓ C) ⊓ P1) ≤ Nat.card ↥(P1 ⊓ C) := Subgroup.card_le_of_le h2
  calc Nat.card ↥(E0 ⊓ C) ≤ 2 * Nat.card ↥((E0 ⊓ C) ⊓ P1) := h1
    _ ≤ 2 * Nat.card ↥(P1 ⊓ C) := Nat.mul_le_mul_left 2 h3
    _ ≤ 2 * 8 := Nat.mul_le_mul_left 2 hle1
    _ = 16 := by norm_num

theorem q13d_I_card_invol_fP1_le (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hI : closure ({t, om} : Set G) ⊓
      centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) = closure ({tau, om} : Set G))
    (hlo : lam * om * lam⁻¹ = om) :
    ({x : G | x ∈ (t * lam) • ((q13A t tau x₁ x₂ rho ⊔ closure ({tau, om} : Set G) :
      Subgroup G) : Set G) ∧ x * x = 1}).ncard ≤ 8 := by
  let A := q13A t tau x₁ x₂ rho
  let P1 := A ⊔ closure ({tau, om} : Set G)
  let D := A ⊓ centralizer ({lam} : Set G)
  let T := D ⊔ zpowers tau
  have htau_mem : tau ∈ closure ({t, om} : Set G) := q13dI2b_tau_mem h
  have hf2 : (t * lam) * (t * lam) = 1 := by
    calc (t * lam) * (t * lam) = t * (lam * t) * lam := by group
      _ = t * (t * lam) * lam := by rw [(q13a_t_comm h).1]
      _ = (t * t) * (lam * lam) := by group
      _ = 1 := by rw [q13a_t_mul_self h, q13a_lam_mul_self h, one_mul]
  have hfinv : (t * lam)⁻¹ = t * lam := inv_eq_of_mul_eq_one_right hf2
  have hsub : {x : G | x ∈ (t * lam) • (P1 : Set G) ∧ x * x = 1} ⊆
      (t * lam) • (T : Set G) := by
    intro x hx
    obtain ⟨hxmem, hxinv⟩ := hx
    obtain ⟨p, hp1, hpx⟩ := Set.mem_smul_set.mp hxmem
    obtain ⟨a, haA, hcases⟩ := (q13d_I_mem_P1 h hI).mp hp1
    have hxconj : (t * lam) * p * (t * lam)⁻¹ = p⁻¹ := by
      have h1 : (t * lam) * p * (t * lam) = p⁻¹ := by
        have h2 : (t * lam) * p * (t * lam) * p = 1 := by
          have hh := hxinv
          rw [← hpx] at hh
          simpa [mul_assoc] using hh
        calc (t * lam) * p * (t * lam) = ((t * lam) * p * (t * lam) * p) * p⁻¹ := by group
          _ = 1 * p⁻¹ := by rw [h2]
          _ = p⁻¹ := one_mul _
      simpa [hfinv] using h1
    obtain ⟨hc1, hcτ, hcom, hcτω⟩ := q13dI2b_conj_cases h hlo haA
    have hbA : lam * a * lam⁻¹ ∈ A := (q13a_A_inv h a haA).2.1
    have hbominv : om * (lam * a * lam⁻¹)⁻¹ = (lam * a * lam⁻¹)⁻¹ * om :=
      q13dI2b_om_inv_comm h hI hbA
    have hcomm_tau : (lam * a * lam⁻¹) * tau = tau * (lam * a * lam⁻¹) :=
      q13d_A_cent_tau h _ hbA
    rcases hcases with hp | hp | hp | hp
    · subst p
      have hb : lam * a * lam⁻¹ = a := by
        have hh : (lam * a * lam⁻¹)⁻¹ = a⁻¹ := by rw [← hc1]; exact hxconj
        calc lam * a * lam⁻¹ = ((lam * a * lam⁻¹)⁻¹)⁻¹ := by group
          _ = (a⁻¹)⁻¹ := by rw [hh]
          _ = a := by group
      have haD : a ∈ D := by
        refine Subgroup.mem_inf.mpr ⟨haA, ?_⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h' := congrArg (fun z => z * lam) hb
        have h'' : lam * a = a * lam := by simpa [mul_assoc] using h'
        exact h''.symm
      exact Set.mem_smul_set.mpr ⟨a, Subgroup.mem_sup_left haD, hpx⟩
    · subst p
      have hEq : (lam * a * lam⁻¹)⁻¹ * tau = tau * a⁻¹ := by
        rw [← hcτ]
        calc (t * lam) * (a * tau) * (t * lam)⁻¹ = (a * tau)⁻¹ := hxconj
          _ = tau * a⁻¹ := by
            rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (q13a_tau_mul_self h)]
      have hb1 : (lam * a * lam⁻¹)⁻¹ = a⁻¹ := by
        have hci := q13dI2b_inv_comm hcomm_tau
        rw [hci] at hEq
        exact mul_left_cancel hEq
      have hb : lam * a * lam⁻¹ = a := by
        calc lam * a * lam⁻¹ = ((lam * a * lam⁻¹)⁻¹)⁻¹ := by group
          _ = (a⁻¹)⁻¹ := by rw [hb1]
          _ = a := by group
      have haD : a ∈ D := by
        refine Subgroup.mem_inf.mpr ⟨haA, ?_⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h' := congrArg (fun z => z * lam) hb
        have h'' : lam * a = a * lam := by simpa [mul_assoc] using h'
        exact h''.symm
      exact Set.mem_smul_set.mpr ⟨a * tau, Subgroup.mul_mem_sup haD (Subgroup.mem_zpowers tau),
        hpx⟩
    · exfalso
      subst p
      have hEq : (lam * a * lam⁻¹)⁻¹ * (om * tau) = om * a⁻¹ := by
        rw [← hcom]
        calc (t * lam) * (a * om) * (t * lam)⁻¹ = (a * om)⁻¹ := hxconj
          _ = om * a⁻¹ := by rw [mul_inv_rev, inv_eq_of_mul_eq_one_right h.om_sq]
      have h2 : (lam * a * lam⁻¹)⁻¹ * tau = a⁻¹ := by
        have h4 : (lam * a * lam⁻¹)⁻¹ * (om * tau) =
            om * ((lam * a * lam⁻¹)⁻¹ * tau) := by
          calc (lam * a * lam⁻¹)⁻¹ * (om * tau) = ((lam * a * lam⁻¹)⁻¹ * om) * tau := by
                group
            _ = (om * (lam * a * lam⁻¹)⁻¹) * tau := by rw [← hbominv]
            _ = om * ((lam * a * lam⁻¹)⁻¹ * tau) := by group
        rw [h4] at hEq
        exact mul_left_cancel hEq
      have hb : lam * a * lam⁻¹ = tau * a := by
        have h6 : (lam * a * lam⁻¹)⁻¹ = a⁻¹ * tau := by
          have hh := congrArg (fun z => z * tau) h2
          simpa [mul_assoc, q13a_tau_mul_self h] using hh
        calc lam * a * lam⁻¹ = ((lam * a * lam⁻¹)⁻¹)⁻¹ := by group
          _ = (a⁻¹ * tau)⁻¹ := by rw [h6]
          _ = tau⁻¹ * a := by group
          _ = tau * a := by rw [inv_eq_of_mul_eq_one_right (q13a_tau_mul_self h)]
      have htau : tau = (lam * a * lam⁻¹) * a⁻¹ := by rw [hb]; group
      have htauA : tau ∈ A := by
        rw [htau]; exact Subgroup.mul_mem A hbA (Subgroup.inv_mem A haA)
      exact q13d_tau_not_mem_A h htauA
    · exfalso
      subst p
      have hEq : (lam * a * lam⁻¹)⁻¹ * om = om * (tau * a⁻¹) := by
        rw [← hcτω]
        calc (t * lam) * (a * (tau * om)) * (t * lam)⁻¹ = (a * (tau * om))⁻¹ := hxconj
          _ = om * (tau * a⁻¹) := by
            have hom_inv : om⁻¹ = om := inv_eq_of_mul_eq_one_right h.om_sq
            have htau_inv : tau⁻¹ = tau := inv_eq_of_mul_eq_one_right (q13a_tau_mul_self h)
            rw [mul_inv_rev, mul_inv_rev, hom_inv, htau_inv]
            group
      have h2 : (lam * a * lam⁻¹)⁻¹ = tau * a⁻¹ := by
        rw [← hbominv] at hEq
        exact mul_left_cancel hEq
      have hb : lam * a * lam⁻¹ = a * tau := by
        calc lam * a * lam⁻¹ = ((lam * a * lam⁻¹)⁻¹)⁻¹ := by group
          _ = (tau * a⁻¹)⁻¹ := by rw [h2]
          _ = a * tau := by
            rw [mul_inv_rev, inv_inv, inv_eq_of_mul_eq_one_right (q13a_tau_mul_self h)]
      have htau : tau = a⁻¹ * (lam * a * lam⁻¹) := by rw [hb]; group
      have htauA : tau ∈ A := by
        rw [htau]; exact Subgroup.mul_mem A (Subgroup.inv_mem A haA) hbA
      exact q13d_tau_not_mem_A h htauA
  have hnorm : ∀ k ∈ zpowers tau, ∀ y ∈ D, k * y * k⁻¹ ∈ D := by
    intro k hk y hy
    obtain ⟨hyA, hyC⟩ := Subgroup.mem_inf.mp hy
    have hky : k * y * k⁻¹ = y := by
      have htau_cent : tau ∈ centralizer ({y} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.mpr (q13d_A_cent_tau h y hyA).symm
      have hkz : k ∈ centralizer ({y} : Set G) := Subgroup.zpowers_le.mpr htau_cent hk
      have hcomm : k * y = y * k := Subgroup.mem_centralizer_singleton_iff.mp hkz
      calc k * y * k⁻¹ = (y * k) * k⁻¹ := by rw [hcomm]
        _ = y := by group
    rw [hky]; exact Subgroup.mem_inf.mpr ⟨hyA, hyC⟩
  have hbot : D ⊓ zpowers tau = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxD, hxzp⟩ := Subgroup.mem_inf.mp hx
    have hxco : x ∈ closure ({t, om} : Set G) := Subgroup.zpowers_le.mpr htau_mem hxzp
    exact q13d_A_inf_CO h x (Subgroup.mem_inf.mp hxD).1 hxco
  have hcardT : Nat.card ↥T = Nat.card ↥D * Nat.card ↥(zpowers tau) :=
    card_sup_eq_mul hnorm hbot
  have hDle : Nat.card ↥D ≤ 4 := q13d_card_CA_lam_le h
  have hz2 : Nat.card ↥(zpowers tau) = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by simpa [pow_two] using q13a_tau_mul_self h) (q13b_tau_ne_one h)
  calc ({x : G | x ∈ (t * lam) • (P1 : Set G) ∧ x * x = 1}).ncard
      ≤ ((t * lam) • (T : Set G)).ncard := Set.ncard_le_ncard hsub
    _ = (T : Set G).ncard := Set.ncard_smul_set _ _
    _ = Nat.card ↥T := (Nat.card_coe_set_eq (T : Set G)).symm
    _ = Nat.card ↥D * Nat.card ↥(zpowers tau) := hcardT
    _ = Nat.card ↥D * 2 := by rw [hz2]
    _ ≤ 4 * 2 := Nat.mul_le_mul_right 2 hDle
    _ = 8 := by norm_num

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
