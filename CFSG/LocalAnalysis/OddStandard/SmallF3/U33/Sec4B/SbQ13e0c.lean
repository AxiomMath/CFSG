module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13e0b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13d8e
public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem q13e_E0_le_M (h : Q13Om t L S x₁ x₂ lam rho tau om) (hD : Q13D t x₁ x₂ lam rho tau om) :
    q13E0 t tau x₁ x₂ rho om ≤ ctxM t tau x₁ x₂ := by
  rw [← hD.E0_eq]
  exact inf_le_left.trans (q13b_U_le_M h)

theorem q13e_B_inf_M (h : Q13Om t L S x₁ x₂ lam rho tau om) (hB : Q13Bs t x₁ x₂ lam tau)
    (hD : Q13D t x₁ x₂ lam rho tau om) :
    q13B t tau x₁ x₂ rho om ⊓ ctxM t tau x₁ x₂ = q13E0 t tau x₁ x₂ rho om := by
  have hE0le : q13E0 t tau x₁ x₂ rho om ≤ q13B t tau x₁ x₂ rho om ⊓ ctxM t tau x₁ x₂ :=
    le_inf hD.E0_le_B (q13e_E0_le_M h hD)
  have hle : q13B t tau x₁ x₂ rho om ⊓ ctxM t tau x₁ x₂ ≤
      ctxM t tau x₁ x₂ ⊓ centralizer ((ctxN tau x₁ x₂ : Subgroup G) : Set G) :=
    le_inf inf_le_right (inf_le_left.trans inf_le_right)
  have hcard : Nat.card ↥(q13B t tau x₁ x₂ rho om ⊓ ctxM t tau x₁ x₂) ≤
      Nat.card ↥(q13E0 t tau x₁ x₂ rho om) :=
    (Subgroup.card_le_of_le hle).trans
      ((q13d_card_CM_N_le h hB hD.A_cent).trans (le_of_eq (q13d_card_E0 h).symm))
  exact (Subgroup.eq_of_le_of_card_ge hE0le hcard).symm

theorem q13e_card_L (h : Q13Om t L S x₁ x₂ lam rho tau om) (hB : Q13Bs t x₁ x₂ lam tau)
    (hD : Q13D t x₁ x₂ lam rho tau om) :
    Nat.card (q13L t tau x₁ x₂ rho om) = 24 * Nat.card (q13B t tau x₁ x₂ rho om) := by
  have hMB : ctxM t tau x₁ x₂ ≤
      Subgroup.normalizer ((q13B t tau x₁ x₂ rho om : Subgroup G) : Set G) := by
    intro m hm
    rw [Subgroup.mem_set_normalizer_iff]
    intro b
    constructor
    · intro hb
      exact hD.B_normal.2 m (hD.M_le_L hm) b hb
    · intro hb
      have hmem := hD.B_normal.2 m⁻¹ (hD.M_le_L (inv_mem hm)) (m * b * m⁻¹) hb
      rwa [show m⁻¹ * (m * b * m⁻¹) * (m⁻¹)⁻¹ = b by group] at hmem
  have hprod := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
    (H := ctxM t tau x₁ x₂) (K := q13B t tau x₁ x₂ rho om) hMB
  have hinf : Nat.card ↥(ctxM t tau x₁ x₂ ⊓ q13B t tau x₁ x₂ rho om) = 2 ^ 7 := by
    rw [inf_comm, q13e_B_inf_M h hB hD, q13d_card_E0 h]
  rw [hinf, h.c11.card_M] at hprod
  have hLs : Nat.card (q13L t tau x₁ x₂ rho om) =
      Nat.card ↥(ctxM t tau x₁ x₂ ⊔ q13B t tau x₁ x₂ rho om) := by
    rw [q13d_L_eq_BM h hB hD.A_cent, sup_comm]
  rw [hLs]
  refine Nat.eq_of_mul_eq_mul_right (show 0 < 2 ^ 7 by norm_num) ?_
  rw [hprod]
  ring

theorem q13e_card_B (h : Q13Om t L S x₁ x₂ lam rho tau om) (hB : Q13Bs t x₁ x₂ lam tau)
    (hD : Q13D t x₁ x₂ lam rho tau om) :
    Nat.card (q13B t tau x₁ x₂ rho om) = 2 ^ 8 ∨ Nat.card (q13B t tau x₁ x₂ rho om) = 2 ^ 9 ∨
      Nat.card (q13B t tau x₁ x₂ rho om) = 2 ^ 10 := by
  have hL := q13e_card_L h hB hD
  rcases hD.L_card with hc | hc | hc
  · left
    rw [hc] at hL
    have hh : 24 * 2 ^ 8 = 24 * Nat.card (q13B t tau x₁ x₂ rho om) := by
      rw [← hL]; norm_num
    exact (Nat.eq_of_mul_eq_mul_left (by norm_num) hh).symm
  · right; left
    rw [hc] at hL
    have hh : 24 * 2 ^ 9 = 24 * Nat.card (q13B t tau x₁ x₂ rho om) := by
      rw [← hL]; norm_num
    exact (Nat.eq_of_mul_eq_mul_left (by norm_num) hh).symm
  · right; right
    rw [hc] at hL
    have hh : 24 * 2 ^ 10 = 24 * Nat.card (q13B t tau x₁ x₂ rho om) := by
      rw [← hL]; norm_num
    exact (Nat.eq_of_mul_eq_mul_left (by norm_num) hh).symm

theorem q13e_CB_t (h : Q13Om t L S x₁ x₂ lam rho tau om) (hB : Q13Bs t x₁ x₂ lam tau)
    (hD : Q13D t x₁ x₂ lam rho tau om) :
    ∀ b ∈ q13B t tau x₁ x₂ rho om, b * t = t * b → b ∈ q13E0 t tau x₁ x₂ rho om := by
  intro b hb hbt
  have hbL : b ∈ q13L t tau x₁ x₂ rho om := (inf_le_left : q13B t tau x₁ x₂ rho om ≤
    q13L t tau x₁ x₂ rho om) hb
  have hbcent : b ∈ centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hbt
  have hbM : b ∈ ctxM t tau x₁ x₂ := by
    have hmem : b ∈ q13L t tau x₁ x₂ rho om ⊓ centralizer ({t} : Set G) := ⟨hbL, hbcent⟩
    rw [hD.CL_t] at hmem
    exact (Subgroup.mem_inf.mp hmem).1
  have hbBM : b ∈ q13B t tau x₁ x₂ rho om ⊓ ctxM t tau x₁ x₂ := ⟨hb, hbM⟩
  rwa [q13e_B_inf_M h hB hD] at hbBM

theorem q13e_CP_t (h : Q13Om t L S x₁ x₂ lam rho tau om) (hD : Q13D t x₁ x₂ lam rho tau om) :
    ∀ p ∈ q13P t tau x₁ x₂ rho om, p * t = t * p → p ∈ ctxN tau x₁ x₂ := by
  intro p hp hpt
  have h1 : t * p * t⁻¹ = p⁻¹ := hD.t_inv_P p hp
  have h2 : t * p * t⁻¹ = p := by rw [← hpt]; group
  have h3 : p = p⁻¹ := h2.symm.trans h1
  have hp2 : p ^ 2 = 1 := by
    rw [pow_two]
    exact mul_eq_one_iff_eq_inv.mpr h3
  exact q13d_P_sq_eq_one_mem_N h hD.A_cent p hp hp2

theorem q13e_CLP_inf_E0 (h : Q13Om t L S x₁ x₂ lam rho tau om) (hD : Q13D t x₁ x₂ lam rho tau om) :
    ∀ k ∈ q13CLP t tau x₁ x₂ rho om,
      k ∈ q13E0 t tau x₁ x₂ rho om → k ∈ q13P t tau x₁ x₂ rho om := by
  intro k hk hkE0
  rw [q13d_mem_E0 h hD.A_cent] at hkE0
  rcases hkE0 with hkP | ⟨p, hp, rfl⟩
  · exact hkP
  · exfalso
    have hcent : (t * p) ∈ centralizer ((q13P t tau x₁ x₂ rho om : Subgroup G) : Set G) :=
      (Subgroup.mem_inf.mp hk).2
    have hgam : t * om ∈ q13P t tau x₁ x₂ rho om := q13d_gam_mem_P h
    have hcomm : (t * p) * (t * om) = (t * om) * (t * p) :=
      (Subgroup.mem_centralizer_iff.mp hcent (t * om) hgam).symm
    have hpc : p ∈ centralizer ({t * om} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        (q13d_P_comm h hD.A_cent p hp (t * om) hgam)
    have hkc : (t * p) ∈ centralizer ({t * om} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hcomm
    have htcent : t ∈ centralizer ({t * om} : Set G) := by
      have hmem := mul_mem hkc (inv_mem hpc)
      rwa [show (t * p) * p⁻¹ = t by group] at hmem
    have htg : t * (t * om) = (t * om) * t :=
      Subgroup.mem_centralizer_singleton_iff.mp htcent
    have hconj : t * (t * om) * t⁻¹ = t * om := by rw [htg]; group
    have h1 : t * (t * om) * t⁻¹ = (t * om)⁻¹ := hD.t_inv_P (t * om) hgam
    have hginv : t * om = (t * om)⁻¹ := hconj.symm.trans h1
    have hgsq : (t * om) ^ 2 = 1 := by
      rw [pow_two]
      exact mul_eq_one_iff_eq_inv.mpr hginv
    exact q13b_tau_ne_one h (by rw [← hD.gam_sq]; exact hgsq)

theorem q13e_CK_t (h : Q13Om t L S x₁ x₂ lam rho tau om) (hB : Q13Bs t x₁ x₂ lam tau)
    (hD : Q13D t x₁ x₂ lam rho tau om) :
    ∀ k ∈ q13CLP t tau x₁ x₂ rho om, k * t = t * k → k ∈ ctxN tau x₁ x₂ := by
  intro k hk hkt
  have hkB : k ∈ q13B t tau x₁ x₂ rho om := by
    have hkL : k ∈ q13L t tau x₁ x₂ rho om := (Subgroup.mem_inf.mp hk).1
    have hkcent : k ∈ centralizer ((ctxN tau x₁ x₂ : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro n hn
      exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hk).2 n (q13d_N_le_P h hn)
    exact ⟨hkL, hkcent⟩
  have hkE0 : k ∈ q13E0 t tau x₁ x₂ rho om := q13e_CB_t h hB hD k hkB hkt
  have hkP : k ∈ q13P t tau x₁ x₂ rho om := q13e_CLP_inf_E0 h hD k hk hkE0
  exact q13e_CP_t h hD k hkP hkt

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
