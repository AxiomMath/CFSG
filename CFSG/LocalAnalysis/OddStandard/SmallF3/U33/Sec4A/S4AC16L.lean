module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC16C
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC16Q

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

private theorem c16_conj_comm_eq {r f : G} (h : r * t = t * r) :
    ⁅r * f * r⁻¹, t⁆ = r * ⁅f, t⁆ * r⁻¹ := by
  have hcomm : Commute r t := h
  have h1 : ⁅r, t⁆ = 1 := hcomm.commutator_eq
  have h2 : ⁅r⁻¹, t⁆ = 1 := hcomm.inv_left.commutator_eq
  calc ⁅r * f * r⁻¹, t⁆
      = ⁅r * (f * r⁻¹), t⁆ := by rw [mul_assoc]
    _ = r * ⁅f * r⁻¹, t⁆ * r⁻¹ * ⁅r, t⁆ :=
        commutatorElement_mul_left_eq_conj_mul r (f * r⁻¹) t
    _ = r * (f * ⁅r⁻¹, t⁆ * f⁻¹ * ⁅f, t⁆) * r⁻¹ * ⁅r, t⁆ := by
        rw [commutatorElement_mul_left_eq_conj_mul f r⁻¹ t]
    _ = r * ⁅f, t⁆ * r⁻¹ := by rw [h1, h2]; group

theorem c16_exists_zu (h : L41GPh15 t L S x₁ x₂ lam rho) :
    ∃ z u : G, C16KBasis (fourGrp x₁ x₂) z u ∧ rho * z * rho⁻¹ = u ∧ rho * u * rho⁻¹ = z * u := by
  let z : G := (x₁ * x₂) ^ 2
  let u : G := rho * z * rho⁻¹
  have hE := h.wreath.fourGrp_eq_omega
  have hcard : Nat.card (fourGrp x₁ x₂) = 4 := hE.2.2
  have hel : ∀ k ∈ fourGrp x₁ x₂, k * k = 1 := by
    intro k hk
    have hk2 := hE.2.1.2 k hk
    rwa [pow_two] at hk2
  have hcomm : ∀ a ∈ fourGrp x₁ x₂, ∀ b ∈ fourGrp x₁ x₂, a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val (isMulCommutative_iff.mp hE.2.1.1 ⟨a, ha⟩ ⟨b, hb⟩)
  have hz : z ∈ fourGrp x₁ x₂ := n4_z_mem_four x₁ x₂
  have hu : u ∈ fourGrp x₁ x₂ := rho_conj_mem_fourGrp h.toCtx0 hz
  have hz1 : z ≠ 1 := (z_mul_self_ne_one h.toCtx0).2
  have hu1 : u ≠ 1 := by
    intro h1
    have h1' : rho * z * rho⁻¹ = 1 := h1
    apply hz1
    calc z = rho⁻¹ * (rho * z * rho⁻¹) * rho := by group
      _ = rho⁻¹ * 1 * rho := by rw [h1']
      _ = 1 := by group
  have hzu : z ≠ u := by
    intro h1
    exact hz1 (eq_one_of_commute_rho_of_mem_fourGrp h.toCtx0 hz
      (n4_comm_of_conj_eq h1.symm).symm)
  have hB : C16KBasis (fourGrp x₁ x₂) z u :=
    c16_KBasis_of_card hcard hel hcomm hz hu hz1 hu1 hzu
  have hr3 : rho ^ 3 = 1 := q15_rho_cube h.toL41GPh1
  have hrK : ∀ k ∈ fourGrp x₁ x₂, rho * k * rho⁻¹ ∈ fourGrp x₁ x₂ :=
    fun k hk => rho_conj_mem_fourGrp h.toCtx0 hk
  have hmove : ∀ k ∈ fourGrp x₁ x₂, k ≠ 1 → rho * k * rho⁻¹ ≠ k := by
    intro k hk hk1 hconj
    exact hk1 (eq_one_of_commute_rho_of_mem_fourGrp h.toCtx0 hk
      (n4_comm_of_conj_eq hconj).symm)
  exact ⟨z, u, hB, rfl, c16_rho_zu hB hr3 hrK hmove rfl⟩

theorem c16_exists_fz (h : L41GPh15 t L S x₁ x₂ lam rho) {z : G} (hz : z ∈ fourGrp x₁ x₂) :
    ∃ fz ∈ l41Y t x₁ x₂ rho, ⁅fz, t⁆ = z := by
  have hY : ∀ a ∈ l41Y t x₁ x₂ rho, ∀ b ∈ l41Y t x₁ x₂ rho, a * b = b * a :=
    fun a ha b hb => m11_comm_Y h.toL41GPh10 ha hb
  have hKY : fourGrp x₁ x₂ ≤ l41Y t x₁ x₂ rho := m11_fourGrp_le_Y h.toL41GPh10
  have hcomm : ∀ f ∈ l41Y t x₁ x₂ rho, ⁅f, t⁆ ∈ fourGrp x₁ x₂ :=
    fun f hf => c16_comm_mem_K h (m13_Y_le_R t x₁ x₂ rho hf)
  have hker : ∀ f ∈ l41Y t x₁ x₂ rho, ⁅f, t⁆ = 1 → f ∈ fourGrp x₁ x₂ := by
    intro f hf h1
    have hft : f * t = t * f := commutatorElement_eq_one_iff_mul_comm.mp h1
    have hmem : f ∈ l41Y t x₁ x₂ rho ⊓ invCent t := ⟨hf, mem_invCent_iff.mpr hft⟩
    rwa [h.yfacts.cent_Y_t] at hmem
  have hKt : ∀ k ∈ fourGrp x₁ x₂, k * t = t * k := fun k hk => c16_K_comm_t h hk
  have hcard : Nat.card (l41Y t x₁ x₂ rho) =
      Nat.card (fourGrp x₁ x₂) * Nat.card (fourGrp x₁ x₂) := by
    rw [m11_card_Y h.toL41GPh10, n4_card_four h.toCtx0]
  exact c16_norm_onto hY hKY hcomm hker hKt hcard z hz

theorem c16_exists_ab (h : L41GPh15 t L S x₁ x₂ lam rho) :
    ∃ z u fz fu : G,
      C16Ab (fourGrp x₁ x₂) (l41Y t x₁ x₂ rho) (l41Q t x₁ x₂ rho) t rho z u fz fu := by
  obtain ⟨z, u, hB, hzu1, hzu2⟩ := c16_exists_zu h
  obtain ⟨fz, hfzY, hfz⟩ := c16_exists_fz h hB.z_mem
  let fu : G := rho * fz * rho⁻¹
  have hrhoM : rho ∈ l41M t x₁ x₂ rho := q14_rho_mem_M h.toL41GPh8
  have hrhoY : ∀ f ∈ l41Y t x₁ x₂ rho, rho * f * rho⁻¹ ∈ l41Y t x₁ x₂ rho := by
    intro f hf
    exact (Subgroup.mem_normalizer_iff.mp (q14_mem_normalizer_Y h.toL41GPh10 hrhoM) f).mp hf
  have hker : ∀ f ∈ l41Y t x₁ x₂ rho, ⁅f, t⁆ = 1 → f ∈ fourGrp x₁ x₂ := by
    intro f hf h1
    have hft : f * t = t * f := commutatorElement_eq_one_iff_mul_comm.mp h1
    have hmem : f ∈ l41Y t x₁ x₂ rho ⊓ invCent t := ⟨hf, mem_invCent_iff.mpr hft⟩
    rwa [h.yfacts.cent_Y_t] at hmem
  have hrt : rho * t = t * rho := (m13_t_comm_L h.toL41GPh5 h.rho_mem).symm
  have hfu_t : ⁅fu, t⁆ = u := by
    change ⁅rho * fz * rho⁻¹, t⁆ = u
    rw [c16_conj_comm_eq hrt, hfz, hzu1]
  exact ⟨z, u, fz, fu,
    { kb := hB
      K_le_Y := m11_fourGrp_le_Y h.toL41GPh10
      Y_comm := fun a ha b hb => m11_comm_Y h.toL41GPh10 ha hb
      fz_mem := hfzY
      fu_mem := hrhoY fz hfzY
      K_comm_t := fun k hk => c16_K_comm_t h hk
      comm_t := fun f hf => c16_comm_mem_K h (m13_Y_le_R t x₁ x₂ rho hf)
      ker_t := hker
      fz_t := hfz
      fu_t := hfu_t
      fu_def := rfl
      rho_z := hzu1
      rho_u := hzu2
      rho_cube := q15_rho_cube h.toL41GPh1
      rho_t := hrt
      rho_Y := hrhoY
      Q_comm_Y := fun q hq f hf => c16_Q_comm_Y h hq hf
      Q_cent_K := fun q hq k hk => c16_Q_cent_K h hq hk
      rho_Q := fun q hq => q14_conj_Q hrhoM hq }⟩

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
