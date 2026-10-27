module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC16A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC16B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC16F
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AQ15C

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem c16_K_le_Q (h : L41GPh15 t L S x₁ x₂ lam rho) :
    fourGrp x₁ x₂ ≤ l41Q t x₁ x₂ rho :=
  (m11_fourGrp_le_Y h.toL41GPh10).trans (q14_Y_le_Q h.toL41GPh10)

private theorem c16_rho_move (h : L41GPh15 t L S x₁ x₂ lam rho) {k : G}
    (hk : k ∈ fourGrp x₁ x₂) (hk1 : k ≠ 1) : rho * k * rho⁻¹ ≠ k := by
  intro hconj
  refine hk1 (eq_one_of_commute_rho_of_mem_fourGrp h.toCtx0 hk ?_)
  calc rho * k = (rho * k * rho⁻¹) * rho := by group
    _ = k * rho := by rw [hconj]

theorem c16_Q_cent_K (h : L41GPh15 t L S x₁ x₂ lam rho) {q k : G}
    (hq : q ∈ l41Q t x₁ x₂ rho) (hk : k ∈ fourGrp x₁ x₂) : q * k = k * q :=
  c16_comm_of_rho (Q := l41Q t x₁ x₂ rho) (K := fourGrp x₁ x₂) (rho := rho)
    (q14_Q_isPGroup t x₁ x₂ rho) (c16_K_le_Q h) h.wreath.fourGrp_eq_omega.2.2
    (fun q hq k hk => c16_K_normal h (q14_Q_le_M t x₁ x₂ rho hq) hk)
    (fun q hq => q14_conj_Q (q14_rho_mem_M h.toL41GPh8) hq)
    (fun k hk => rho_conj_mem_fourGrp h.toCtx0 hk)
    (q15_rho_cube h.toL41GPh1)
    (fun k hk hk1 => c16_rho_move h hk hk1) q hq k hk

theorem c16_N_conj (h : L41GPh15 t L S x₁ x₂ lam rho) {q f : G} (hq : q ∈ l41Q t x₁ x₂ rho)
    (hf : f ∈ l41R t x₁ x₂ rho) : ⁅q * f * q⁻¹, t⁆ = ⁅f, t⁆ := by
  have hqM : q⁻¹ ∈ l41M t x₁ x₂ rho :=
    Subgroup.inv_mem _ (q14_Q_le_M t x₁ x₂ rho hq)
  obtain ⟨r, hr, hrt⟩ := c16_conj_t h hqM
  have hrt' : q⁻¹ * t * q = t * r := by simpa using hrt
  have hkey : ⁅q * f * q⁻¹, t⁆ = q * ⁅f, q⁻¹ * t * q⁆ * q⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [hkey, hrt']
  have hfr : ⁅f, t * r⁆ = ⁅f, t⁆ := by
    rw [commutatorElement_mul_right_eq_mul_conj,
      commutatorElement_eq_one_iff_mul_comm.mpr (m13_comm_R h.toL41GPh10 hf hr)]
    group
  rw [hfr]
  have hcK : ⁅f, t⁆ ∈ fourGrp x₁ x₂ := c16_comm_mem_K h hf
  have hcq : q * ⁅f, t⁆ = ⁅f, t⁆ * q := c16_Q_cent_K h hq hcK
  rw [hcq]
  group

theorem c16_Q_comm_Y (h : L41GPh15 t L S x₁ x₂ lam rho) {q f : G}
    (hq : q ∈ l41Q t x₁ x₂ rho) (hf : f ∈ l41Y t x₁ x₂ rho) : ⁅q, f⁆ ∈ fourGrp x₁ x₂ := by
  have hqM : q ∈ l41M t x₁ x₂ rho := q14_Q_le_M t x₁ x₂ rho hq
  have hfR : f ∈ l41R t x₁ x₂ rho := m13_Y_le_R t x₁ x₂ rho hf
  have hconjY : q * f * q⁻¹ ∈ l41Y t x₁ x₂ rho :=
    (m13_normal_Y h.toL41GPh10).2 q hqM f hf
  have hfinvY : f⁻¹ ∈ l41Y t x₁ x₂ rho := Subgroup.inv_mem _ hf
  have hprodY : (q * f * q⁻¹) * f⁻¹ ∈ l41Y t x₁ x₂ rho :=
    Subgroup.mul_mem _ hconjY hfinvY
  have hYcomm : ∀ a ∈ l41Y t x₁ x₂ rho, ∀ b ∈ l41Y t x₁ x₂ rho, a * b = b * a :=
    fun a ha b hb => m11_comm_Y h.toL41GPh10 ha hb
  have hAt : ∀ a ∈ l41Y t x₁ x₂ rho, ⁅a, t⁆ ∈ l41Y t x₁ x₂ rho :=
    fun a ha => m11_fourGrp_le_Y h.toL41GPh10 (c16_comm_mem_K h (m13_Y_le_R t x₁ x₂ rho ha))
  have hNinv : ⁅f⁻¹, t⁆ = (⁅f, t⁆)⁻¹ := by
    have h1 : ⁅f⁻¹, t⁆ * ⁅f, t⁆ = 1 := by
      rw [← c16_comm_mul_of_abelian hYcomm hAt hfinvY hf,
        inv_mul_cancel, commutatorElement_one_left]
    exact eq_inv_of_mul_eq_one_left h1
  have hN : ⁅(q * f * q⁻¹) * f⁻¹, t⁆ = 1 := by
    rw [c16_comm_mul_of_abelian hYcomm hAt hconjY hfinvY,
      c16_N_conj h hq hfR, hNinv, mul_inv_cancel]
  have hgK : (q * f * q⁻¹) * f⁻¹ ∈ fourGrp x₁ x₂ := by
    rw [← h.yfacts.cent_Y_t]
    refine Subgroup.mem_inf.mpr ⟨hprodY, ?_⟩
    rw [mem_invCent_iff]
    exact commutatorElement_eq_one_iff_mul_comm.mp hN
  have hg_eq : ⁅q, f⁆ = (q * f * q⁻¹) * f⁻¹ := by
    simp only [commutatorElement_def]
  rw [hg_eq]
  exact hgK

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
