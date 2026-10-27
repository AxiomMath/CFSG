module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13b1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13d0

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem q13d_I_om_cent_A (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hI : closure ({t, om} : Set G) ⊓
      centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) = closure ({tau, om} : Set G)) :
    ∀ a ∈ q13A t tau x₁ x₂ rho, om * a = a * om := by
  intro a ha
  have hom : om ∈ closure ({tau, om} : Set G) := Subgroup.subset_closure (by simp)
  have hom' : om ∈ centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) := by
    have hmem : om ∈ closure ({t, om} : Set G) ⊓
        centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) := by
      rw [hI]; exact hom
    exact (Subgroup.mem_inf.mp hmem).2
  exact (Subgroup.mem_centralizer_iff.mp hom' a ha).symm

private lemma q13d_I_K_le_cent_A (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hI : closure ({t, om} : Set G) ⊓
      centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) = closure ({tau, om} : Set G)) :
    closure ({tau, om} : Set G) ≤
      Subgroup.centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) := by
  rw [Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with hx | hx
  · rw [hx]
    exact Subgroup.mem_centralizer_iff.mpr (fun a ha => q13d_A_cent_tau h a ha)
  · rw [hx]
    exact Subgroup.mem_centralizer_iff.mpr (fun a ha => (q13d_I_om_cent_A h hI a ha).symm)

private lemma q13d_I_K_norm_A (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hI : closure ({t, om} : Set G) ⊓
      centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) = closure ({tau, om} : Set G)) :
    ∀ k ∈ closure ({tau, om} : Set G), ∀ a ∈ q13A t tau x₁ x₂ rho,
      k * a * k⁻¹ ∈ q13A t tau x₁ x₂ rho := by
  intro k hk a ha
  have hcomm : a * k = k * a :=
    Subgroup.mem_centralizer_iff.mp (q13d_I_K_le_cent_A h hI hk) a ha
  have hka : k * a * k⁻¹ = a := by
    rw [← hcomm]; group
  rwa [hka]

private lemma q13d_I_K_le_CO (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    closure ({tau, om} : Set G) ≤ closure ({t, om} : Set G) := by
  rw [Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with hx | hx
  · rw [hx]
    have ht : t ∈ closure ({t, om} : Set G) := Subgroup.subset_closure (by simp)
    have hom : om ∈ closure ({t, om} : Set G) := Subgroup.subset_closure (by simp)
    have hconj : om * t * om⁻¹ ∈ closure ({t, om} : Set G) :=
      mul_mem (mul_mem hom ht) (inv_mem hom)
    have htau : tau = t * (om * t * om⁻¹) := by
      rw [h.t_om, ← mul_assoc, q13a_t_mul_self h, one_mul]
    rw [htau]
    exact mul_mem ht hconj
  · rw [hx]
    exact Subgroup.subset_closure (by simp)

private lemma q13d_I_card_closure_tau_om (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    Nat.card ↥(closure ({tau, om} : Set G)) = 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hom2 : om ^ 2 = 1 := by rw [pow_two]; exact h.om_sq
  have htau2 : tau ^ 2 = 1 := by rw [pow_two]; exact q13a_tau_mul_self h
  have hom1 : om ≠ 1 := by
    intro h1
    exact h.om_not_mem (by rw [h1]; exact Subgroup.one_mem _)
  have htau1 : tau ≠ 1 := q13b_tau_ne_one h
  have homtauc : Commute om tau := (q13a_om_comm h).1
  have hcardom : Nat.card ↥(zpowers om) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hom2 hom1
  have hcardtau : Nat.card ↥(zpowers tau) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime htau2 htau1
  have htau_not_zp : tau ∉ zpowers om := by
    intro hz
    have hle : zpowers tau ≤ zpowers om := Subgroup.zpowers_le.mpr hz
    have heq : zpowers tau = zpowers om :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcardom, hcardtau])
    have hom_zp : om ∈ zpowers tau := by
      rw [heq]; exact Subgroup.mem_zpowers om
    have hle2 : zpowers tau ≤ closure ({t, tau} : Set G) :=
      Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
    exact h.om_not_mem (hle2 hom_zp)
  have hcl : closure ({tau, om} : Set G) = zpowers tau ⊔ zpowers om := by
    rw [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
      ← Subgroup.zpowers_eq_closure]
  have hinf : zpowers tau ⊓ zpowers om = ⊥ := by
    by_contra hne
    have hdvd : Nat.card ↥(zpowers tau ⊓ zpowers om) ∣ 2 := by
      rw [← hcardtau]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases Nat.prime_two.eq_one_or_self_of_dvd _ hdvd with h1 | h2
    · exact hne ((Subgroup.card_eq_one).mp h1)
    · have heq : (zpowers tau ⊓ zpowers om) = zpowers tau :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h2, hcardtau])
      have hle : zpowers tau ≤ zpowers om := heq ▸ inf_le_right
      exact htau_not_zp (hle (Subgroup.mem_zpowers tau))
  have hnorm : ∀ k ∈ zpowers om, ∀ d ∈ zpowers tau, k * d * k⁻¹ ∈ zpowers tau := by
    intro k hk d hd
    have hkd : k * d = d * k := by
      rw [Subgroup.mem_zpowers_iff] at hk hd
      obtain ⟨m, rfl⟩ := hk
      obtain ⟨n, rfl⟩ := hd
      exact homtauc.zpow_zpow m n
    rw [hkd, mul_assoc, mul_inv_cancel, mul_one]
    exact hd
  have hcard := card_sup_eq_mul (H := zpowers tau) (K := zpowers om) hnorm hinf
  rw [hcl, hcard, hcardtau, hcardom]

theorem q13d_I_P1_comm (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hI : closure ({t, om} : Set G) ⊓
      centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) = closure ({tau, om} : Set G)) :
    ∀ p ∈ (q13A t tau x₁ x₂ rho ⊔ closure ({tau, om} : Set G)), ∀ q ∈ (q13A t tau x₁ x₂ rho
      ⊔ closure ({tau, om} : Set G)), p * q = q * p := by
  have hAc : (q13A t tau x₁ x₂ rho : Subgroup G) ≤
      Subgroup.centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) := by
    intro a ha
    exact Subgroup.mem_centralizer_iff.mpr (fun b hb => q13a_A_comm h b hb a ha)
  have hKcA := q13d_I_K_le_cent_A h hI
  have hKcK : closure ({tau, om} : Set G) ≤
      Subgroup.centralizer ((closure ({tau, om} : Set G) : Subgroup G) : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · rw [hx]
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro d hd
      rcases q13b_mem_closure_pair (a := tau) (b := om) (q13a_tau_mul_self h) h.om_sq
          (q13a_om_comm h).1.symm hd with hd | hd | hd | hd
      · rw [hd, one_mul, mul_one]
      · rw [hd]
      · rw [hd]; exact (q13a_om_comm h).1
      · rw [hd]; rw [mul_assoc, (q13a_om_comm h).1, ← mul_assoc]
    · rw [hx]
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro d hd
      rcases q13b_mem_closure_pair (a := tau) (b := om) (q13a_tau_mul_self h) h.om_sq
          (q13a_om_comm h).1.symm hd with hd | hd | hd | hd
      · rw [hd, one_mul, mul_one]
      · rw [hd]; exact (q13a_om_comm h).1.symm
      · rw [hd]
      · rw [hd]
        rw [mul_assoc, h.om_sq, mul_one, ← mul_assoc, (q13a_om_comm h).1, mul_assoc, h.om_sq,
          mul_one]
  have hle : (q13A t tau x₁ x₂ rho ⊔ closure ({tau, om} : Set G)) ≤
      Subgroup.centralizer (((q13A t tau x₁ x₂ rho ⊔ closure ({tau, om} : Set G)) :
        Subgroup G) : Set G) := by
    refine sup_le ?_ ?_
    · rw [Subgroup.le_centralizer_iff]
      exact sup_le hAc hKcA
    · rw [Subgroup.le_centralizer_iff]
      exact sup_le ((Subgroup.le_centralizer_iff).mp hKcA) hKcK
  intro p hp q hq
  exact (Subgroup.mem_centralizer_iff.mp (hle hp) q hq).symm

theorem q13d_I_mem_P1 (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hI : closure ({t, om} : Set G) ⊓
      centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) = closure ({tau, om} :
        Set G)) {p : G} :
    p ∈ (q13A t tau x₁ x₂ rho ⊔ closure ({tau, om} : Set G)) ↔ ∃ a ∈ q13A t tau x₁ x₂ rho,
      p = a ∨ p = a * tau ∨ p = a * om ∨ p = a * (tau * om) := by
  have hK := q13d_I_K_norm_A h hI
  rw [mem_sup_iff_of_normalizes hK]
  constructor
  · rintro ⟨a, ha, k, hk, rfl⟩
    rcases q13b_mem_closure_pair (a := tau) (b := om) (q13a_tau_mul_self h) h.om_sq
        (q13a_om_comm h).1.symm hk with hk | hk | hk | hk
    · exact ⟨a, ha, Or.inl (by rw [hk, mul_one])⟩
    · exact ⟨a, ha, Or.inr (Or.inl (by rw [hk]))⟩
    · exact ⟨a, ha, Or.inr (Or.inr (Or.inl (by rw [hk])))⟩
    · exact ⟨a, ha, Or.inr (Or.inr (Or.inr (by rw [hk])))⟩
  · rintro ⟨a, ha, hdisj⟩
    rcases hdisj with hdisj | hdisj | hdisj | hdisj
    · exact ⟨a, ha, 1, Subgroup.one_mem _, by rw [hdisj, mul_one]⟩
    · exact ⟨a, ha, tau, Subgroup.subset_closure (by simp), by rw [hdisj]⟩
    · exact ⟨a, ha, om, Subgroup.subset_closure (by simp), by rw [hdisj]⟩
    · exact ⟨a, ha, tau * om,
        mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)),
        by rw [hdisj]⟩

theorem q13d_I_card_P1 (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hI : closure ({t, om} : Set G) ⊓
      centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) = closure ({tau, om} : Set G)) :
    Nat.card ↥(q13A t tau x₁ x₂ rho ⊔ closure ({tau, om} : Set G)) = 2 ^ 6 := by
  have hK := q13d_I_K_norm_A h hI
  have hHK : q13A t tau x₁ x₂ rho ⊓ closure ({tau, om} : Set G) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro g hg
    rw [Subgroup.mem_inf] at hg
    exact q13d_A_inf_CO h g hg.1 (q13d_I_K_le_CO h hg.2)
  rw [card_sup_eq_mul hK hHK, q13a_card_A h, q13d_I_card_closure_tau_om h]
  norm_num

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
