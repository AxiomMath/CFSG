module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JA1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JA3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IR4C
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IR4D

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

namespace Ctx4Z


private lemma z4jSub_inf (hz : Ctx4Z t L S x₁ x₂ lam rho tau) (A B : Subgroup G) :
    hz.z4iSub (A ⊓ B) = hz.z4iSub A ⊓ hz.z4iSub B := by
  ext x; exact Iff.rfl

theorem z4jData (hz : Ctx4Z t L S x₁ x₂ lam rho tau) {Ng V' : Subgroup G} {v₁ v₂ : G}
    (hN : Z4IOdd t tau x₁ x₂ rho Ng) (hV : Ctx4ZV t tau x₁ x₂ lam rho V' v₁ v₂)
    (hv₁ : v₁ ∈ ctxQ t tau x₁ x₂ rho) (hv₂ : v₂ ∈ ctxQ t tau x₁ x₂ rho) :
    S4B.Z4JData (hz.z4iSub Ng) (hz.z4iSub (ctxQ t tau x₁ x₂ rho))
      (hz.z4iSub (ctxYq t tau x₁ x₂ rho)) (hz.z4iSub (fourGrp x₁ x₂)) (hz.z4iSub V')
      (hz.z4iSub (baseGrp x₁ x₂)) hz.z4iRho hz.z4iT hz.z4iTau hz.z4iLam hz.z4jY hz.z4jZ
      (hz.z4jV hv₁) (hz.z4jV hv₂) := by
  have hVQ : V' ≤ ctxQ t tau x₁ x₂ rho := by
    rw [hV.2.2.1]; exact le_sup_right
  have hV_L : V' ≤ ctxNQ t tau x₁ x₂ rho := hVQ.trans hz.z4i_Q_le_NQ
  have hVL : fourGrp x₁ x₂ ≤ ctxNQ t tau x₁ x₂ rho :=
    (hz.V_le_Y.trans hz.Y_le_Q).trans hz.z4i_Q_le_NQ
  have hB_L : baseGrp x₁ x₂ ≤ ctxNQ t tau x₁ x₂ rho :=
    hz.base_le_Q.trans hz.z4i_Q_le_NQ
  have hQC : ctxQ t tau x₁ x₂ rho ≤ ctxCQ t tau x₁ x₂ rho := by
    rw [← hN.sup_Q]; exact le_sup_right
  have hVB : fourGrp x₁ x₂ ≤ baseGrp x₁ x₂ := by
    rw [hz.wreath.fourGrp_eq_omega.1]
    exact (Subgroup.closure_le (K := baseGrp x₁ x₂)).mpr fun _ ha => ha.1
  have hinf : hz.z4iSub (fourGrp x₁ x₂) ⊓ hz.z4iSub V' = ⊥ := by
    rw [← z4jSub_inf hz (fourGrp x₁ x₂) V', Subgroup.eq_bot_iff_forall]
    intro x hx
    have hxB : (x : G) ∈ baseGrp x₁ x₂ := hVB hx.1
    have hxbot : (x : G) ∈ (⊥ : Subgroup G) := by
      rw [← hV.2.2.2.1]; exact ⟨hxB, hx.2⟩
    exact Subtype.ext (by simpa using hxbot)
  have h1 : Odd (Nat.card (hz.z4iSub Ng)) := by
    rw [z4i_card_sub hz hN.le_NQ]; exact hN.odd
  have h3 : ∀ a ∈ hz.z4iSub (ctxQ t tau x₁ x₂ rho),
      ∀ b ∈ hz.z4iSub (ctxQ t tau x₁ x₂ rho), a * b = b * a := by
    intro a ha b hb; exact Subtype.ext (hz.Q_comm a ha b hb)
  have h4 : Nat.card (hz.z4iSub (ctxQ t tau x₁ x₂ rho)) = 64 := by
    rw [z4i_card_sub hz hz.z4i_Q_le_NQ, hz.card_Q]; norm_num
  have h5 : ∀ g x : ↥(ctxNQ t tau x₁ x₂ rho),
      x ∈ hz.z4iSub (ctxQ t tau x₁ x₂ rho) →
      g * x * g⁻¹ ∈ hz.z4iSub (ctxQ t tau x₁ x₂ rho) := by
    intro g x hx
    show (g : G) * (x : G) * (g : G)⁻¹ ∈ ctxQ t tau x₁ x₂ rho
    exact (mem_set_normalizer_iff.mp g.2 x).mp hx
  have h6 : ∀ g : ↥(ctxNQ t tau x₁ x₂ rho),
      (∀ q ∈ hz.z4iSub (ctxQ t tau x₁ x₂ rho), g * q = q * g) →
      g ∈ hz.z4iSub (ctxQ t tau x₁ x₂ rho) ⊔ hz.z4iSub Ng := by
    intro g hg
    rw [z4i_sup_sub hz hN, z4i_mem_sub hz (ctxCQ t tau x₁ x₂ rho) g]
    rw [ctxCQ, mem_centralizer_iff]
    intro q hq
    exact (congrArg Subtype.val (hg ⟨q, hz.z4i_Q_le_NQ hq⟩ hq)).symm
  have h9 : hz.z4iSub (ctxQ t tau x₁ x₂ rho) =
      hz.z4iSub (baseGrp x₁ x₂) ⊔ hz.z4iSub V' := by
    rw [hV.2.2.1]
    exact Subgroup.subgroupOf_sup hB_L hV_L
  have h10 : hz.z4iSub (baseGrp x₁ x₂) ≤ hz.z4iSub (ctxQ t tau x₁ x₂ rho) := by
    intro x hx; exact hz.base_le_Q hx
  have h11 : hz.z4iSub (ctxYq t tau x₁ x₂ rho) ≤
      hz.z4iSub (ctxQ t tau x₁ x₂ rho) := by
    intro x hx; exact hz.Y_le_Q hx
  have h12 : hz.z4iSub (ctxYq t tau x₁ x₂ rho) =
      hz.z4iSub (fourGrp x₁ x₂) ⊔ hz.z4iSub V' := by
    rw [hV.2.2.2.2.1]
    exact Subgroup.subgroupOf_sup hVL hV_L
  have h13 : hz.z4iSub (fourGrp x₁ x₂) ⊓ hz.z4iSub V' = ⊥ := hinf
  have h14 : Nat.card (hz.z4iSub (fourGrp x₁ x₂)) = 4 := by
    rw [z4i_card_sub hz hVL, hz.wreath.fourGrp_eq_omega.2.2]
  have h15 : Nat.card (hz.z4iSub V') = 4 := by
    rw [z4i_card_sub hz hV_L, hV.2.1]
  have h16 : ∀ q ∈ hz.z4iSub (ctxQ t tau x₁ x₂ rho),
      q ^ 2 ∈ hz.z4iSub (fourGrp x₁ x₂) := by
    intro q hq
    show (q : G) ^ 2 ∈ fourGrp x₁ x₂
    exact hz.Q_quot.1 q hq
  have h19 : Nat.card (hz.z4iSub (baseGrp x₁ x₂)) = 16 := by
    rw [z4i_card_sub hz hB_L, hz.wreath.baseGrp_eq.2.2]
  have h20 : ∀ y ∈ hz.z4iSub (ctxYq t tau x₁ x₂ rho), y * y = 1 := by
    intro y hy
    refine Subtype.ext ?_
    show (y : G) * (y : G) = 1
    rw [← pow_two]
    exact ((hz.mem_Y_iff (y : G)).mp hy).2
  have h21 : ∀ g x : ↥(ctxNQ t tau x₁ x₂ rho),
      x ∈ hz.z4iSub (ctxYq t tau x₁ x₂ rho) →
      g * x * g⁻¹ ∈ hz.z4iSub (ctxYq t tau x₁ x₂ rho) := by
    intro g x hx
    show (g : G) * (x : G) * (g : G)⁻¹ ∈ ctxYq t tau x₁ x₂ rho
    exact hz.z4i_NQ_Y g.2 hx
  have h22 : ∀ g x : ↥(ctxNQ t tau x₁ x₂ rho),
      x ∈ hz.z4iSub (fourGrp x₁ x₂) →
      g * x * g⁻¹ ∈ hz.z4iSub (fourGrp x₁ x₂) := by
    intro g x hx
    show (g : G) * (x : G) * (g : G)⁻¹ ∈ fourGrp x₁ x₂
    exact hz.z4i_NQ_V g.2 hx
  have hC := hz.z4iPartC hN hV
  have hD := hz.z4iPartD (Ng := Ng) (V' := V')
  exact
    { odd_N := h1
      Q_comm := h3
      card_Q := h4
      normal_Q := h5
      cent_Q := h6
      Q_eq := h9
      B_le_Q := h10
      Y_le_Q := h11
      Y_eq := h12
      V_inf_V' := h13
      card_V := h14
      card_V' := h15
      card_B := h19
      sq_mem_V := h16
      Y_sq := h20
      Y_mem := hz.z4j_Y_mem
      normal_Y := h21
      normal_V := h22
      V_eq := hz.z4j_V_eq
      V'_eq := hz.z4j_V'_eq hV hv₁ hv₂
      y_ne_one := hz.z4j_y_ne_one
      z_ne_one := hz.z4j_z_ne_one
      y_ne_z := hz.z4j_y_ne_z
      v₁_ne_one := hz.z4j_v₁_ne_one hV hv₁
      v₂_ne_one := hz.z4j_v₂_ne_one hV hv₂
      v₁_ne_v₂ := hz.z4j_v₁_ne_v₂ hV hv₁ hv₂
      rho_pow_three := hC.rho_pow_three
      rho_norm_Q := hC.rho_norm_Q
      rho_norm_Y := hC.rho_norm_Y
      rho_norm_V := hC.rho_norm_V
      rho_norm_V' := hC.rho_norm_V'
      rho_norm_B := hC.rho_norm_B
      rho_fpf_Q := hC.rho_fpf_Q
      tau_inv := hC.tau_inv
      tau_not_mem_Q := hC.tau_not_mem_Q
      t_ne_one := hD.t_ne_one
      t_sq := hD.t_sq
      tau_sq := hD.tau_sq
      l_sq := hD.l_sq
      t_tau := hD.t_tau
      t_l := hD.t_l
      tau_l := hD.tau_l
      t_rho := hD.t_rho
      tau_rho := hD.tau_rho
      l_rho := hD.l_rho
      B_cent_t := hD.B_cent_t
      cent_t_Q := hD.cent_t_Q
      V_cent_t := hD.V_cent_t
      Y_cent_t := hD.Y_cent_t
      t_v₁ := hz.z4j_t_v₁ hV hv₁
      t_v₂ := hz.z4j_t_v₂ hV hv₂
      l_y := hz.z4j_l_y
      l_z := hz.z4j_l_z
      lt_v₁ := hz.z4j_lt_v₁ hV hv₁ hv₂ }

end Ctx4Z

end CFSG.OddStandard.SmallF3.HarrisU33
