module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13c0

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem q13c_lam_norm_CO (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ∀ c ∈ closure {t, om}, lam * c * lam⁻¹ ∈ closure {t, om} := by
  have hconj_t : lam * t * lam⁻¹ = t := by
    have hcomm : lam * t = t * lam := (q13a_t_comm h).1.symm
    calc lam * t * lam⁻¹ = (t * lam) * lam⁻¹ := by rw [hcomm]
      _ = t := by group
  have htau_cl : tau ∈ closure {t, om} := by
    have h1 : t * (om * t * om⁻¹) ∈ closure {t, om} :=
      (closure {t, om}).mul_mem (Subgroup.subset_closure (by simp))
        ((closure {t, om}).mul_mem
          ((closure {t, om}).mul_mem (Subgroup.subset_closure (by simp))
            (Subgroup.subset_closure (by simp)))
          ((closure {t, om}).inv_mem (Subgroup.subset_closure (by simp))))
    have heq : t * (om * t * om⁻¹) = tau := by
      rw [h.t_om, ← mul_assoc, q13a_t_mul_self h, one_mul]
    rwa [heq] at h1
  have hconj_om : lam * om * lam⁻¹ ∈ closure {t, om} := by
    rcases q13a_lam_om h with h1 | h1
    · rw [h1]; exact Subgroup.subset_closure (by simp)
    · rw [h1]
      exact (closure {t, om}).mul_mem (Subgroup.subset_closure (by simp)) htau_cl
  intro c hc
  induction hc using Subgroup.closure_induction with
  | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · rw [hconj_t]; exact Subgroup.subset_closure (by simp)
      · exact hconj_om
  | one =>
      have h1 : lam * 1 * lam⁻¹ = 1 := by group
      rw [h1]; exact Subgroup.one_mem _
  | mul x y hx hy ihx ihy =>
      have heq : lam * (x * y) * lam⁻¹ = (lam * x * lam⁻¹) * (lam * y * lam⁻¹) := by
        group
      rw [heq]
      exact (closure {t, om}).mul_mem ihx ihy
  | inv x hx ihx =>
      have heq : lam * x⁻¹ * lam⁻¹ = (lam * x * lam⁻¹)⁻¹ := by group
      rw [heq]
      exact (closure {t, om}).inv_mem ihx

private lemma q13c_zpowers_lam_norm_CO (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ∀ k ∈ zpowers lam, ∀ c ∈ closure {t, om}, k * c * k⁻¹ ∈ closure {t, om} := by
  intro k hk c hc
  rcases q13c_zpowers_lam h k hk with rfl | rfl
  · simpa using hc
  · exact q13c_lam_norm_CO h c hc

theorem q13c_card_E (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    Nat.card ↥(closure {t, om} ⊔ zpowers lam) = 16 := by
  have hnorm := q13c_zpowers_lam_norm_CO h
  have hdis : closure {t, om} ⊓ zpowers lam = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxH, hxK⟩ := Subgroup.mem_inf.mp hx
    rcases q13c_zpowers_lam h x hxK with hx1 | hxlam
    · rw [hx1]
    · rw [hxlam] at hxH ⊢
      exfalso
      have hmem : lam ∈ ctxCO t tau x₁ x₂ rho := h.CO_eq.symm ▸ hxH
      exact q13c_lam_not_mem_O h (Subgroup.mem_inf.mp hmem).1
  have hE8 : Nat.card ↥(closure {t, om}) = 8 := by
    rw [← h.CO_eq]
    obtain ⟨e⟩ := h.c11.CO_dihedral
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hK2 : Nat.card ↥(zpowers lam) = 2 := by
    rw [Nat.card_zpowers, h.c11.wreath.ord_lam]
  rw [card_sup_eq_mul hnorm hdis, hE8, hK2]

theorem q13c_E_inf_Q (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ∀ q ∈ ctxQ t tau x₁ x₂ rho, q ∈ closure {t, om} ⊔ zpowers lam → q = 1 := by
  have hnorm := q13c_zpowers_lam_norm_CO h
  have hH_O : closure {t, om} ≤ ctxO t tau x₁ x₂ := by
    rw [← h.CO_eq]; exact inf_le_left
  have hQ_O : ctxQ t tau x₁ x₂ rho ≤ ctxO t tau x₁ x₂ := by
    rw [q13b_O_eq h]; exact le_sup_left
  intro q hq hqE
  obtain ⟨c, hcH, k, hkK, hq_eq⟩ :=
    (mem_sup_iff_of_normalizes (H := closure {t, om}) (K := zpowers lam) hnorm).mp hqE
  rcases q13c_zpowers_lam h k hkK with hk1 | hklam
  · subst k
    rw [mul_one] at hq_eq
    have hcCO : c ∈ ctxCO t tau x₁ x₂ rho := h.CO_eq.symm ▸ hcH
    have hcQ : c ∈ ctxQ t tau x₁ x₂ rho := hq_eq ▸ hq
    exact hq_eq.trans (q13b_Q_inf_CO h c hcQ hcCO)
  · subst k
    have hlam : c⁻¹ * q = lam := by rw [hq_eq]; group
    have hmemO : c⁻¹ * q ∈ ctxO t tau x₁ x₂ :=
      (ctxO t tau x₁ x₂).mul_mem ((ctxO t tau x₁ x₂).inv_mem (hH_O hcH)) (hQ_O hq)
    exact absurd (hlam ▸ hmemO) (q13c_lam_not_mem_O h)

theorem q13c_E_le_U (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    closure {t, om} ⊔ zpowers lam ≤ ctxU t tau x₁ x₂ lam := by
  refine sup_le ?_ ?_
  · rw [← h.CO_eq]
    exact inf_le_left.trans (q13b_O_le_U h)
  · rw [ctxU]
    exact le_sup_right

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
