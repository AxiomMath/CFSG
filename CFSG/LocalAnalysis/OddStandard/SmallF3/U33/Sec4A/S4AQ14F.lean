module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AQ14E

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open scoped Pointwise commutatorElement

section Q14F

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem q14_F_eq (h : L41GPh10 t L S x₁ x₂ lam rho) :
    l41F t x₁ x₂ rho = ctxW t x₁ x₂ ⊔ l41Y t x₁ x₂ rho := by
  apply le_antisymm
  · change l41R t x₁ x₂ rho ⊔ zpowers t ≤ ctxW t x₁ x₂ ⊔ l41Y t x₁ x₂ rho
    obtain ⟨F', hF'R, _hF'elem, _hF'card, _hF'inf, hBF, _hF'norm, hYF⟩ := m11_exists_F h
    have hR : l41R t x₁ x₂ rho ≤ ctxW t x₁ x₂ ⊔ l41Y t x₁ x₂ rho := by
      rw [← hBF]
      refine sup_le ?_ ?_
      · exact (le_sup_right : baseGrp x₁ x₂ ≤ twoCore t ⊔ baseGrp x₁ x₂).trans le_sup_left
      · have hF'Y : F' ≤ l41Y t x₁ x₂ rho := by
          rw [hYF]
          exact le_sup_right
        exact hF'Y.trans le_sup_right
    refine sup_le hR ?_
    rw [← h.p2]
    exact (le_sup_left : twoCore t ≤ ctxW t x₁ x₂).trans le_sup_left
  · exact sup_le (m13_W_le_F h.toL41GPh8)
      ((m13_Y_le_R t x₁ x₂ rho).trans le_sup_left)

private theorem q14_comm_swap_t_mem_fourGrp (h : L41GPh10 t L S x₁ x₂ lam rho) {r : G}
    (hr : r ∈ l41R t x₁ x₂ rho) : ⁅t, r⁆ ∈ fourGrp x₁ x₂ := by
  obtain ⟨f, hf, hfr⟩ := m13_conj_t_R h.toL41GPh8 hr
  have h1 : ⁅t, r⁆ = f := by
    rw [commutatorElement_def, hfr, mul_assoc, mul_inv_cancel, mul_one]
  rw [h1]
  exact hf

private theorem q14_comm_mem_fourGrp (h : L41GPh10 t L S x₁ x₂ lam rho) {r : G}
    (hr : r ∈ l41R t x₁ x₂ rho) : ⁅r, t⁆ ∈ fourGrp x₁ x₂ := by
  have h1 : ⁅r, t⁆ = ⁅t, r⁆⁻¹ := (commutatorElement_inv t r).symm
  rw [h1]
  exact Subgroup.inv_mem _ (q14_comm_swap_t_mem_fourGrp h hr)

theorem q14_comm_mem_Y (h : L41GPh10 t L S x₁ x₂ lam rho) {f : G}
    (hf : f ∈ l41F t x₁ x₂ rho) : ⁅f, t⁆ ∈ l41Y t x₁ x₂ rho := by
  rcases m13_mem_F h.toL41GPh8 hf with hfR | ⟨k, hk, rfl⟩
  · exact m11_fourGrp_le_Y h (q14_comm_mem_fourGrp h hfR)
  · have hnorm : t * ⁅k, t⁆ * t⁻¹ ∈ l41Y t x₁ x₂ rho :=
      (m13_normal_Y h).2 t (q14_F_le_M t x₁ x₂ rho (q14_t_mem_F t x₁ x₂ rho)) _
        (m11_fourGrp_le_Y h (q14_comm_mem_fourGrp h hk))
    have h1 : ⁅t * k, t⁆ = t * ⁅k, t⁆ * t⁻¹ * ⁅t, t⁆ :=
      commutatorElement_mul_left_eq_conj_mul t k t
    rw [h1]
    simpa using hnorm

theorem q14_sq_mem_Y (h : L41GPh10 t L S x₁ x₂ lam rho) {f : G}
    (hf : f ∈ l41F t x₁ x₂ rho) : f * f ∈ l41Y t x₁ x₂ rho := by
  rcases m13_mem_F h.toL41GPh8 hf with hfR | ⟨k, hk, rfl⟩
  · exact m11_fourGrp_le_Y h (h.rfacts.sq_mem f hfR)
  · obtain ⟨fo, hfo, hconj⟩ := m13_conj_t_R h.toL41GPh8 hk
    rw [m13_t_inv h.hyp] at hconj
    have hsq : (t * k) * (t * k) = fo * (k * k) := by
      calc (t * k) * (t * k) = (t * k * t) * k := by group
        _ = (fo * k) * k := by rw [hconj]
        _ = fo * (k * k) := by group
    rw [hsq]
    exact m11_fourGrp_le_Y h (Subgroup.mul_mem _ hfo (h.rfacts.sq_mem k hk))

theorem q14_cent_Qbar_t_F (h : L41GPh10 t L S x₁ x₂ lam rho) :
    {q | q ∈ l41Q t x₁ x₂ rho ∧ ⁅q, t⁆ ∈ l41Y t x₁ x₂ rho} =
      ((l41F t x₁ x₂ rho : Subgroup G) : Set G) := by
  ext q
  constructor
  · rintro ⟨hqQ, hcY⟩
    have hu : q * t * q⁻¹ = ⁅q, t⁆ * t := by
      rw [commutatorElement_def]
      group
    have hc2 : ⁅q, t⁆ * ⁅q, t⁆ = 1 := ((m11_mem_Y_iff h).mp hcY).2
    have hcinv : ⁅q, t⁆⁻¹ = ⁅q, t⁆ := inv_eq_of_mul_eq_one_right hc2
    have huu : (q * t * q⁻¹) * (q * t * q⁻¹) = 1 := by
      calc (q * t * q⁻¹) * (q * t * q⁻¹) = q * (t * t) * q⁻¹ := by group
        _ = 1 := by rw [t_mul_self h.hyp]; group
    have hctt : (⁅q, t⁆ * t) * (⁅q, t⁆ * t) = 1 := by
      rw [← hu]
      exact huu
    have hcomm : ⁅q, t⁆ * t = t * ⁅q, t⁆ := by
      rw [← commutatorElement_eq_one_iff_mul_comm, commutatorElement_def,
        hcinv, m13_t_inv h.hyp]
      simpa only [mul_assoc] using hctt
    have hc4 : ⁅q, t⁆ ∈ fourGrp x₁ x₂ := by
      rw [← m11_Y_inf_cent_t h]
      exact Subgroup.mem_inf.mpr ⟨hcY, mem_invCent_iff.mpr hcomm⟩
    have hu4 : q * t * q⁻¹ ∈ conjIn (l41R t x₁ x₂ rho) t := by
      rw [h.rfacts.orbit_t, hu]
      exact n4_mem_smul_iff.mpr ⟨⁅q, t⁆, hc4, hcomm⟩
    obtain ⟨r, hr, hru⟩ := hu4
    have hqQ' : r⁻¹ * q ∈ l41Q t x₁ x₂ rho :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (q14_R_le_Q h.toL41GPh8 hr)) hqQ
    have hconj' : (r⁻¹ * q) * t * (r⁻¹ * q)⁻¹ = t := by
      calc (r⁻¹ * q) * t * (r⁻¹ * q)⁻¹ = r⁻¹ * (q * t * q⁻¹) * r := by group
        _ = r⁻¹ * (r * t * r⁻¹) * r := by rw [← hru]
        _ = t := by group
    have hinv : r⁻¹ * q ∈ invCent t := by
      rw [mem_invCent_iff]
      have h' := congrArg (· * (r⁻¹ * q)) hconj'
      simpa [mul_assoc] using h'
    have hW : r⁻¹ * q ∈ ctxW t x₁ x₂ := by
      rw [← q14_cent_Q_t h]
      exact Subgroup.mem_inf.mpr ⟨hqQ', hinv⟩
    have hqRW : q ∈ l41R t x₁ x₂ rho ⊔ ctxW t x₁ x₂ := by
      have hrq : r * (r⁻¹ * q) = q := by group
      rw [← hrq]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hr) (Subgroup.mem_sup_right hW)
    exact (sup_le le_sup_left (m13_W_le_F h.toL41GPh8)) hqRW
  · rintro hqF
    exact ⟨q14_F_le_Q h.toL41GPh8 hqF, q14_comm_mem_Y h hqF⟩

theorem q14_cent_Qbar_t (h : L41GPh10 t L S x₁ x₂ lam rho) :
    {q | q ∈ l41Q t x₁ x₂ rho ∧ ⁅q, t⁆ ∈ l41Y t x₁ x₂ rho} =
      ((ctxW t x₁ x₂ ⊔ l41Y t x₁ x₂ rho : Subgroup G) : Set G) := by
  rw [q14_cent_Qbar_t_F h, q14_F_eq h]

end Q14F

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
