module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IR4A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Wreath
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4I0E
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IR4P

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

namespace Ctx4Z

private lemma z4iSub_inf (hz : Ctx4Z t L S x₁ x₂ lam rho tau) (A B : Subgroup G) :
    hz.z4iSub (A ⊓ B) = hz.z4iSub A ⊓ hz.z4iSub B := by
  ext x; exact Iff.rfl

theorem z4iPartB (hz : Ctx4Z t L S x₁ x₂ lam rho tau) {Ng V' : Subgroup G} {v₁ v₂ : G}
    (hN : Z4IOdd t tau x₁ x₂ rho Ng) (hV : Ctx4ZV t tau x₁ x₂ lam rho V' v₁ v₂)
    (hrel : (ctxCQ t tau x₁ x₂ rho).relIndex (ctxKI t tau x₁ x₂ rho) = 4) :
    S4B.Z4IPartB (hz.z4iSub Ng) (hz.z4iSub (ctxQ t tau x₁ x₂ rho))
      (hz.z4iSub (ctxYq t tau x₁ x₂ rho)) (hz.z4iSub (fourGrp x₁ x₂)) (hz.z4iSub V')
      (hz.z4iSub (baseGrp x₁ x₂)) (hz.z4iSub (ctxKI t tau x₁ x₂ rho)) := by
  have hVQ : V' ≤ ctxQ t tau x₁ x₂ rho := by
    rw [hV.2.2.1]; exact le_sup_right
  have hV_L : V' ≤ ctxNQ t tau x₁ x₂ rho := hVQ.trans hz.z4i_Q_le_NQ
  have hVL : fourGrp x₁ x₂ ≤ ctxNQ t tau x₁ x₂ rho :=
    (hz.V_le_Y.trans hz.Y_le_Q).trans hz.z4i_Q_le_NQ
  have hB_L : baseGrp x₁ x₂ ≤ ctxNQ t tau x₁ x₂ rho :=
    hz.base_le_Q.trans hz.z4i_Q_le_NQ
  have hKI_L : ctxKI t tau x₁ x₂ rho ≤ ctxNQ t tau x₁ x₂ rho :=
    hz.z4i_KI_le_E.trans inf_le_left
  have hQC : ctxQ t tau x₁ x₂ rho ≤ ctxCQ t tau x₁ x₂ rho := by
    rw [← hN.sup_Q]; exact le_sup_right
  have hVB : fourGrp x₁ x₂ ≤ baseGrp x₁ x₂ := by
    rw [hz.wreath.fourGrp_eq_omega.1]
    exact (Subgroup.closure_le (K := baseGrp x₁ x₂)).mpr fun _ ha => ha.1
  have hinf : hz.z4iSub (fourGrp x₁ x₂) ⊓ hz.z4iSub V' = ⊥ := by
    rw [← z4iSub_inf hz (fourGrp x₁ x₂) V', Subgroup.eq_bot_iff_forall]
    intro x hx
    have hxB : (x : G) ∈ baseGrp x₁ x₂ := hVB hx.1
    have hxbot : (x : G) ∈ (⊥ : Subgroup G) := by
      rw [← hV.2.2.2.1]; exact ⟨hxB, hx.2⟩
    exact Subtype.ext (by simpa using hxbot)
  have h1 : Odd (Nat.card (hz.z4iSub Ng)) := by
    rw [z4i_card_sub hz hN.le_NQ]; exact hN.odd
  have h2 : hz.z4iSub Ng ≤ hz.z4iSub (ctxKI t tau x₁ x₂ rho) := by
    intro x hx; exact hz.z4i_C_le_KI (hN.le_C hx)
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
  have h7 : hz.z4iSub (ctxQ t tau x₁ x₂ rho) ≤
      hz.z4iSub (ctxKI t tau x₁ x₂ rho) := by
    intro x hx; exact hz.z4i_C_le_KI (hQC hx)
  have h8 : (hz.z4iSub (ctxQ t tau x₁ x₂ rho) ⊔ hz.z4iSub Ng).relIndex
      (hz.z4iSub (ctxKI t tau x₁ x₂ rho)) = 4 := by
    rw [z4i_sup_sub hz hN]
    exact (Subgroup.relIndex_subgroupOf hKI_L).trans hrel
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
  have h17 : ∀ k ∈ hz.z4iSub (ctxKI t tau x₁ x₂ rho),
      ∀ y ∈ hz.z4iSub (ctxYq t tau x₁ x₂ rho), k * y = y * k := by
    intro k hk y hy
    exact Subtype.ext ((mem_centralizer_iff.mp (hz.z4i_KI_le_E hk).2) y hy).symm
  have h18 : ∀ k ∈ hz.z4iSub (ctxKI t tau x₁ x₂ rho),
      ∀ q ∈ hz.z4iSub (ctxQ t tau x₁ x₂ rho),
      k * q * k⁻¹ * q⁻¹ ∈ hz.z4iSub (fourGrp x₁ x₂) := by
    intro k hk q hq
    show (k : G) * (q : G) * (k : G)⁻¹ * (q : G)⁻¹ ∈ fourGrp x₁ x₂
    exact hz.z4i_comm_mem_V hk hq
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
  exact
    { odd_N := h1
      N_le_K := h2
      Q_comm := h3
      card_Q := h4
      normal_Q := h5
      cent_Q := h6
      Q_le_K := h7
      relIndex_K := h8
      Q_eq := h9
      B_le_Q := h10
      Y_le_Q := h11
      Y_eq := h12
      V_inf_V' := h13
      card_V := h14
      card_V' := h15
      sq_mem_V := h16
      K_cent_Y := h17
      comm_KQ := h18
      card_B := h19
      Y_sq := h20
      normal_Y := h21
      normal_V := h22 }

end Ctx4Z

end CFSG.OddStandard.SmallF3.HarrisU33
