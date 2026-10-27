module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S0a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ARem

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup
open scoped Pointwise
open CFSG.OddStandard.SmallF3.HarrisU33.L34

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


private lemma mem_zpowers_eq_one_or_eq {z x : G} (hz : z * z = 1) (hx : x ∈ zpowers z) :
    x = 1 ∨ x = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h2 : z ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, pow_two, hz]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [← Int.emod_add_mul_ediv k 2, h, zero_add, zpow_mul, h2, one_zpow]
  · right
    rw [← Int.emod_add_mul_ediv k 2, h, zpow_add, zpow_mul, h2, one_zpow, mul_one, zpow_one]

private theorem mem_ctxN_cases_of {w : G} (hw2 : w * w = 1)
    (hcomm : ∀ v ∈ fourGrp x₁ x₂, w * v = v * w) {u : G} (hu : u ∈ ctxN w x₁ x₂) :
    u ∈ fourGrp x₁ x₂ ∨ ∃ v ∈ fourGrp x₁ x₂, u = w * v := by
  have hcomm' : ∀ a ∈ fourGrp x₁ x₂, ∀ b ∈ zpowers w, a * b = b * a := by
    intro a ha b hb
    rcases mem_zpowers_eq_one_or_eq hw2 hb with h1 | h1
    · rw [h1, mul_one, one_mul]
    · rw [h1]; exact (hcomm a ha).symm
  have hle : ctxN w x₁ x₂ ≤ fourGrp x₁ x₂ ⊔ zpowers w := by
    rw [ctxN, fourGrp, closure_le]
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
  obtain ⟨a, ha, b, hb, hua⟩ := (mem_sup_iff_of_commute hcomm').mp (hle hu)
  rcases mem_zpowers_eq_one_or_eq hw2 hb with h1 | h1
  · left
    rw [hua, h1, mul_one]
    exact ha
  · right
    exact ⟨a, ha, by rw [hua, h1]; exact (hcomm a ha).symm⟩

variable (hc : Ctx4Q t L S x₁ x₂ lam rho tau)
include hc

theorem lam_mem_L : lam ∈ L := by
  have h : lam ∈ S ⊓ L := by rw [hc.inf_eq]; exact subset_closure (by simp)
  exact h.2

theorem fourGrp_le_L : fourGrp x₁ x₂ ≤ L := by
  have hV : fourGrp x₁ x₂ ≤ wreathGrp x₁ x₂ lam := by
    rw [fourGrp, wreathGrp, closure_le]
    rintro _ (rfl | rfl)
    · exact pow_mem (subset_closure (by simp)) 2
    · exact pow_mem (mul_mem (subset_closure (by simp)) (subset_closure (by simp))) 2
  intro a ha
  have h' : a ∈ S ⊓ L := by rw [hc.inf_eq]; exact hV ha
  exact h'.2

theorem t_comm_L {g : G} (hg : g ∈ L) : t * g = g * t :=
  (mem_centralizer_iff.mp hc.hyp.mem_centralizer g hg).symm

private theorem V_comm_closure {a : G} (ha : a ∈ closure ({t, tau} : Set G)) :
    ∀ v ∈ fourGrp x₁ x₂, a * v = v * a := by
  have hle : fourGrp x₁ x₂ ≤ closure ({x₁ ^ 2, (x₁ * x₂) ^ 2, rho, lam} : Set G) := by
    rw [fourGrp]
    exact Subgroup.closure_mono (by
      intro b hb
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb ⊢
      tauto)
  intro v hv
  exact (Ctx4.centralizer_t_tau hc.toCtx4).2.2.2.2 a ha v (hle hv)

private theorem ttau_mul_self : (t * tau) * (t * tau) = 1 := by
  calc (t * tau) * (t * tau) = t * (tau * t) * tau := by group
    _ = t * (t * tau) * tau := by rw [← hc.t_comm_tau]
    _ = (t * t) * (tau * tau) := by group
    _ = 1 := by rw [hc.t_mul_self, hc.tau_mul_self, one_mul]

theorem N_le_X : ctxN tau x₁ x₂ ≤ ctxX t tau x₁ x₂ := by
  rw [ctxN, ctxX, closure_le]
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl | rfl <;> exact subset_closure (by simp)

theorem tN_le_X : ctxN (t * tau) x₁ x₂ ≤ ctxX t tau x₁ x₂ := by
  rw [ctxN, ctxX, closure_le]
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl | rfl
  · exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
  · exact subset_closure (by simp)
  · exact subset_closure (by simp)

theorem mem_N_cases {u : G} (hu : u ∈ ctxN tau x₁ x₂) :
    u ∈ fourGrp x₁ x₂ ∨ ∃ v ∈ fourGrp x₁ x₂, u = tau * v :=
  mem_ctxN_cases_of (w := tau) hc.tau_mul_self
    (V_comm_closure hc (subset_closure (by simp))) hu

theorem mem_tN_cases {u : G} (hu : u ∈ ctxN (t * tau) x₁ x₂) :
    u ∈ fourGrp x₁ x₂ ∨ ∃ v ∈ fourGrp x₁ x₂, u = (t * tau) * v :=
  mem_ctxN_cases_of (w := t * tau) (ttau_mul_self hc)
    (V_comm_closure hc
      (mul_mem (subset_closure (by simp)) (subset_closure (by simp)))) hu

theorem tG_N_field : ∀ g : G, ∀ u ∈ ctxN tau x₁ x₂, g * t * g⁻¹ ≠ u := by
  intro g u hu heq
  have huX : u ∈ ctxX t tau x₁ x₂ := N_le_X hc hu
  have huV : u ∈ t • (fourGrp x₁ x₂ : Set G) := by
    rw [← heq]
    exact hc.tG_X g (heq.symm ▸ huX)
  obtain ⟨v, hv, hvu⟩ := Set.mem_smul_set.mp huV
  rw [smul_eq_mul] at hvu
  rcases mem_N_cases hc hu with huF | ⟨v', hv', huv'⟩
  · exact hc.toCtx4.tG_inf_four g u huF heq
  · exfalso
    apply hc.ttau_not_mem_Q
    have h1 : tau * t = v' * v⁻¹ := by
      have h2 : tau * t * v = v' := by
        calc tau * t * v = tau * (t * v) := by group
          _ = tau * (tau * v') := by rw [hvu, huv']
          _ = (tau * tau) * v' := by group
          _ = v' := by rw [hc.tau_mul_self, one_mul]
      exact eq_mul_inv_of_mul_eq h2
    have h2 : t * tau = v' * v⁻¹ := by rw [hc.t_comm_tau, h1]
    rw [h2]
    exact mul_mem (hc.V_le_Q hv') (inv_mem (hc.V_le_Q hv))

theorem tG_tN_field : ∀ g : G, ∀ u ∈ ctxN (t * tau) x₁ x₂, g * t * g⁻¹ ≠ u := by
  intro g u hu heq
  have huX : u ∈ ctxX t tau x₁ x₂ := tN_le_X hc hu
  have huV : u ∈ t • (fourGrp x₁ x₂ : Set G) := by
    rw [← heq]
    exact hc.tG_X g (heq.symm ▸ huX)
  obtain ⟨v, hv, hvu⟩ := Set.mem_smul_set.mp huV
  rw [smul_eq_mul] at hvu
  rcases mem_tN_cases hc hu with huF | ⟨v', hv', huv'⟩
  · exact hc.toCtx4.tG_inf_four g u huF heq
  · exfalso
    apply hc.tau_not_mem_Q
    have h1 : v = tau * v' := by
      have h2 : t * v = t * (tau * v') := by rw [hvu, huv']; group
      exact mul_left_cancel h2
    have h2 : tau = v * v'⁻¹ := eq_mul_inv_of_mul_eq h1.symm
    have hm : v * v'⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
      mul_mem (hc.V_le_Q hv) (inv_mem (hc.V_le_Q hv'))
    exact h2.symm ▸ hm

theorem t_conj_tz : ∃ n : G, n * t * n⁻¹ = t * (x₁ * x₂) ^ 2 := by
  have hmem : t * (x₁ * x₂) ^ 2 ∈ conjIn (Subgroup.normalizer (S : Set G)) t := by
    rw [Ctx4.fusion_tz hc.toCtx4]
    exact ⟨(x₁ * x₂) ^ 2, Subgroup.mem_zpowers _, by simp [smul_eq_mul]⟩
  obtain ⟨n, -, hn⟩ := hmem
  exact ⟨n, hn⟩

theorem inv_tl_field : ∀ u ∈ fourGrp x₁ x₂, (t * lam * u) * (t * lam * u) = 1 →
    ∃ g : G, g * t * g⁻¹ = t * lam * u := by
  intro u hu he
  have heL : lam * u ∈ L := mul_mem (lam_mem_L hc) (fourGrp_le_L hc hu)
  have hne : lam * u ≠ 1 := by
    intro h
    apply lam_not_mem_O hc
    have h2 : lam = u⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [h2]
    exact inv_mem (V_le_O hc hu)
  have he2 : (lam * u) * (lam * u) = 1 := by
    have he' : (t * (lam * u)) * (t * (lam * u)) = 1 := by
      simpa only [mul_assoc] using he
    have htcomm : t * (lam * u) = (lam * u) * t := t_comm_L hc heL
    have h : (t * (lam * u)) * (t * (lam * u)) =
        (t * t) * ((lam * u) * (lam * u)) := by
      calc (t * (lam * u)) * (t * (lam * u))
          = t * ((lam * u) * t) * (lam * u) := by group
        _ = t * (t * (lam * u)) * (lam * u) := by rw [htcomm]
        _ = (t * t) * ((lam * u) * (lam * u)) := by group
    rw [h, hc.t_mul_self, one_mul] at he'
    exact he'
  obtain ⟨c, hcL, hcz⟩ := hc.invol_L (lam * u) heL he2 hne
  obtain ⟨n, hn⟩ := t_conj_tz hc
  refine ⟨c * n, ?_⟩
  have hct : c * t * c⁻¹ = t := by
    have hcomm : c * t = t * c := (t_comm_L hc hcL).symm
    rw [hcomm]; group
  calc (c * n) * t * (c * n)⁻¹ = c * (n * t * n⁻¹) * c⁻¹ := by group
    _ = c * (t * (x₁ * x₂) ^ 2) * c⁻¹ := by rw [hn]
    _ = (c * t * c⁻¹) * (c * (x₁ * x₂) ^ 2 * c⁻¹) := by group
    _ = t * (lam * u) := by rw [hct, hcz]
    _ = t * lam * u := by group

theorem inv_l_field : ∀ u ∈ fourGrp x₁ x₂, (lam * u) * (lam * u) = 1 →
    ∃ g : G, g * (x₁ * x₂) ^ 2 * g⁻¹ = lam * u := by
  intro u hu he
  have hne : lam * u ≠ 1 := by
    intro h
    apply lam_not_mem_O hc
    have h2 : lam = u⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [h2]
    exact inv_mem (V_le_O hc hu)
  obtain ⟨c, -, hcz⟩ :=
    hc.invol_L (lam * u) (mul_mem (lam_mem_L hc) (fourGrp_le_L hc hu)) he hne
  exact ⟨c, hcz⟩

theorem inv_tltau_field : ∀ u ∈ fourGrp x₁ x₂, (t * lam * tau * u) * (t * lam * tau * u) = 1 →
    ∃ g : G, g * (t * tau) * g⁻¹ = t * lam * tau * u := by
  intro u hu he
  have heL : lam * u ∈ L := mul_mem (lam_mem_L hc) (fourGrp_le_L hc hu)
  have heq : (t * tau) * (lam * u) = t * lam * tau * u := by
    have hmid : t * tau * lam = t * lam * tau := by
      calc t * tau * lam = t * (tau * lam) := by rw [mul_assoc]
        _ = t * (lam * tau) := by rw [hc.tau_lam]
        _ = t * lam * tau := by rw [mul_assoc]
    calc (t * tau) * (lam * u) = (t * tau * lam) * u := by group
      _ = (t * lam * tau) * u := by rw [hmid]
      _ = t * lam * tau * u := by group
  have he2 : ((t * tau) * (lam * u)) * ((t * tau) * (lam * u)) = 1 := by
    rw [heq]; exact he
  obtain ⟨c, -, hcq⟩ := (Ctx4.involutions_tau_coset hc.toCtx4).2 (lam * u) heL he2
  exact ⟨c, by rw [heq] at hcq; exact hcq⟩

theorem inv_ltau_field : ∀ u ∈ fourGrp x₁ x₂, (lam * tau * u) * (lam * tau * u) = 1 →
    ∃ g : G, g * tau * g⁻¹ = lam * tau * u := by
  intro u hu he
  have heL : lam * u ∈ L := mul_mem (lam_mem_L hc) (fourGrp_le_L hc hu)
  have heq : tau * (lam * u) = lam * tau * u := by
    calc tau * (lam * u) = (tau * lam) * u := by rw [mul_assoc]
      _ = (lam * tau) * u := by rw [hc.tau_lam]
      _ = lam * tau * u := rfl
  have he2 : (tau * (lam * u)) * (tau * (lam * u)) = 1 := by
    rw [heq]; exact he
  obtain ⟨c, -, hcq⟩ := (Ctx4.involutions_tau_coset hc.toCtx4).1 (lam * u) heL he2
  exact ⟨c, by rw [heq] at hcq; exact hcq⟩

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
