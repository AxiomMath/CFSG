module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AM13C
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AY11A

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem c16_conj_t (h : L41GPh15 t L S x₁ x₂ lam rho) {m : G} (hm : m ∈ l41M t x₁ x₂ rho) :
    ∃ r ∈ l41R t x₁ x₂ rho, m * t * m⁻¹ = t * r :=
  n4_mem_smul_iff.mp (m13_conj_mem_X h.toL41GPh10 hm).1

theorem c16_comm_mem_K (h : L41GPh15 t L S x₁ x₂ lam rho) {r : G}
    (hr : r ∈ l41R t x₁ x₂ rho) : ⁅r, t⁆ ∈ fourGrp x₁ x₂ := by
  obtain ⟨f, hf, hfr⟩ := m13_conj_t_R h.toL41GPh8 hr
  have h1 : ⁅t, r⁆ = f := by
    rw [commutatorElement_def, hfr, mul_assoc, mul_inv_cancel, mul_one]
  have h2 : ⁅r, t⁆ = ⁅t, r⁆⁻¹ := (commutatorElement_inv t r).symm
  rw [h2, h1]
  exact Subgroup.inv_mem _ hf

theorem c16_K_comm_t (h : L41GPh15 t L S x₁ x₂ lam rho) {k : G} (hk : k ∈ fourGrp x₁ x₂) :
    k * t = t * k := by
  have hk' : k ∈ l41Y t x₁ x₂ rho ⊓ invCent t := by
    rw [h.yfacts.cent_Y_t]
    exact hk
  exact mem_invCent_iff.mp (Subgroup.mem_inf.mp hk').2

theorem c16_K_normal (h : L41GPh15 t L S x₁ x₂ lam rho) {m : G} (hm : m ∈ l41M t x₁ x₂ rho)
    {k : G} (hk : k ∈ fourGrp x₁ x₂) : m * k * m⁻¹ ∈ fourGrp x₁ x₂ := by
  have hkY : k ∈ l41Y t x₁ x₂ rho := m11_fourGrp_le_Y h.toL41GPh10 hk
  have hX : m * k * m⁻¹ ∈ l41Y t x₁ x₂ rho := (m13_normal_Y h.toL41GPh10).2 m hm k hkY
  rw [← h.yfacts.cent_Y_t]
  refine Subgroup.mem_inf.mpr ⟨hX, mem_invCent_iff.mpr ?_⟩
  obtain ⟨r, hr, hmt⟩ := c16_conj_t h hm
  have hkt : k * t = t * k := c16_K_comm_t h hk
  have hXR : m * k * m⁻¹ ∈ l41R t x₁ x₂ rho := m13_Y_le_R t x₁ x₂ rho hX
  have hcomm : (m * k * m⁻¹) * (m * t * m⁻¹) = (m * t * m⁻¹) * (m * k * m⁻¹) := by
    calc (m * k * m⁻¹) * (m * t * m⁻¹) = m * (k * t) * m⁻¹ := by group
      _ = m * (t * k) * m⁻¹ := by rw [hkt]
      _ = (m * t * m⁻¹) * (m * k * m⁻¹) := by group
  rw [hmt] at hcomm
  have hXr : (m * k * m⁻¹) * r = r * (m * k * m⁻¹) := m13_comm_R h.toL41GPh10 hXR hr
  have key : ((m * k * m⁻¹) * t) * r = (t * (m * k * m⁻¹)) * r := by
    calc ((m * k * m⁻¹) * t) * r = (m * k * m⁻¹) * (t * r) := by group
      _ = (t * r) * (m * k * m⁻¹) := hcomm
      _ = t * (r * (m * k * m⁻¹)) := by group
      _ = t * ((m * k * m⁻¹) * r) := by rw [hXr]
      _ = (t * (m * k * m⁻¹)) * r := by group
  exact mul_right_cancel key

theorem c16_mem_K_iff (h : L41GPh15 t L S x₁ x₂ lam rho) {k : G} :
    k ∈ fourGrp x₁ x₂ ↔ ∃ r ∈ l41R t x₁ x₂ rho, r * r = k := by
  constructor
  · intro hk
    have hy : x₁ ^ 2 * x₁ ^ 2 = 1 := (y_mul_self_ne_one h.wreath).1
    have hz : (x₁ * x₂) ^ 2 * (x₁ * x₂) ^ 2 = 1 := (z_mul_self_ne_one h.toCtx0).1
    have hc : Commute (x₁ ^ 2) ((x₁ * x₂) ^ 2) :=
      ((Commute.refl x₁).mul_right h.wreath.comm).pow_pow 2 2
    obtain ⟨hx₁, hx₂⟩ := m13_x_mem_R h.toL41GPh3
    rcases mem_closure_pair_cases hc.eq hy hz hk with rfl | rfl | rfl | rfl
    · exact ⟨1, Subgroup.one_mem _, mul_one 1⟩
    · exact ⟨x₁, hx₁, (pow_two x₁).symm⟩
    · exact ⟨x₁ * x₂, Subgroup.mul_mem _ hx₁ hx₂, (pow_two (x₁ * x₂)).symm⟩
    · refine ⟨x₂, hx₂, ?_⟩
      rw [← WreathRel.x₂_sq h.wreath]
      exact (pow_two x₂).symm
  · rintro ⟨r, hr, rfl⟩
    exact h.rfacts.sq_mem r hr

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
