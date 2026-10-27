module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC13Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQab
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP12f

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G}

theorem c13_Q_comm (hc : Ctx13A t L S x₁ x₂ lam rho tau om) :
    ∀ a ∈ ctxQ t tau x₁ x₂ rho, ∀ b ∈ ctxQ t tau x₁ x₂ rho, a * b = b * a := by
  intro a ha b hb
  exact IsZ4Z4E4.comm hc.q_iso ha hb

theorem c13_sq_V (hc : Ctx13A t L S x₁ x₂ lam rho tau om) :
    ∀ a ∈ ctxQ t tau x₁ x₂ rho, a ^ 2 ∈ fourGrp x₁ x₂ := by
  intro a ha
  exact l12_sq_mem_V hc.toCtx11 (l12_Q_le_R hc.toCtx11 ha)

theorem c13_Y_elem (hc : Ctx13A t L S x₁ x₂ lam rho tau om) :
    CFSG.Open.IsElemAbelian 2 (ctxYq t tau x₁ x₂ rho) := by
  refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
  · intro a b
    exact Subtype.ext (c13_Q_comm hc a.1 (ctxYq_le_ctxQ a.2) b.1 (ctxYq_le_ctxQ b.2))
  · intro x hx
    exact ((mem_ctxYq_iff hc.q_iso x).mp hx).2

theorem c13_V_le_Y (hc : Ctx13A t L S x₁ x₂ lam rho tau om) :
    fourGrp x₁ x₂ ≤ ctxYq t tau x₁ x₂ rho := by
  rw [(hc.wreath.fourGrp_eq_omega).1, Subgroup.closure_le]
  rintro v ⟨hvB, hv2⟩
  exact (mem_ctxYq_iff hc.q_iso v).mpr ⟨hc.base_le_Q hvB, hv2⟩

theorem c13_normal_Y (hc : Ctx13A t L S x₁ x₂ lam rho tau om) :
    NormalIn (ctxYq t tau x₁ x₂ rho) (ctxM t tau x₁ x₂) := by
  refine ⟨ctxYq_le_ctxQ.trans hc.normal_Q.1, ?_⟩
  intro g hg k hk
  have hkQ : k ∈ ctxQ t tau x₁ x₂ rho := ctxYq_le_ctxQ hk
  have hk2 : k ^ 2 = 1 := ((mem_ctxYq_iff hc.q_iso k).mp hk).2
  refine (mem_ctxYq_iff hc.q_iso _).mpr ⟨hc.normal_Q.2 g hg k hkQ, ?_⟩
  have hid : (g * k * g⁻¹) ^ 2 = g * k ^ 2 * g⁻¹ := by
    simpa [MulAut.conj_apply] using (map_pow (MulAut.conj g) k 2).symm
  rw [hid, hk2]; group

private theorem comm_of_conj_eq {x : G} (h : rho * x * rho⁻¹ = x) : x * rho = rho * x := by
  have h' : rho * x = x * rho := by
    have := congrArg (fun u => u * rho) h
    simpa [mul_assoc] using this
  exact h'.symm

theorem c13_fpf_YV (hc : Ctx13A t L S x₁ x₂ lam rho tau om) :
    FpfSetting (ctxYq t tau x₁ x₂ rho) (fourGrp x₁ x₂) rho where
  QP := c13_V_le_Y hc
  cen := fun p hp q hq =>
    c13_Q_comm hc p (ctxYq_le_ctxQ hp) q (ctxYq_le_ctxQ ((c13_V_le_Y hc) hq))
  rho3 := by rw [← hc.ord_rho]; exact pow_orderOf_eq_one rho
  rhoP := fun x hx =>
    (c13_normal_Y hc).2 rho (l12_rho_lam_mem_M hc.toCtx11).1 x hx
  rhoQ := fun x hx => hc.normal_V.2 rho (l12_rho_lam_mem_M hc.toCtx11).1 x hx
  fix := fun x hx hfix =>
    l12_cent_Q_rho hc.toCtx11 x (ctxYq_le_ctxQ hx) (comm_of_conj_eq hfix)
  cardQ := by rw [(hc.wreath.fourGrp_eq_omega).2.2]
  idx := by
    have hinf : fourGrp x₁ x₂ ⊓ ctxYq t tau x₁ x₂ rho = fourGrp x₁ x₂ :=
      inf_eq_left.mpr (c13_V_le_Y hc)
    have h := Subgroup.relIndex_mul_card (H := fourGrp x₁ x₂) (K := ctxYq t tau x₁ x₂ rho)
    rw [hinf, (hc.wreath.fourGrp_eq_omega).2.2, card_ctxYq hc.q_iso] at h
    omega

theorem c13_fpf_QY (hc : Ctx13A t L S x₁ x₂ lam rho tau om) :
    FpfSetting (ctxQ t tau x₁ x₂ rho) (ctxYq t tau x₁ x₂ rho) rho where
  QP := ctxYq_le_ctxQ
  cen := fun p hp q hq => c13_Q_comm hc p hp q (ctxYq_le_ctxQ hq)
  rho3 := by rw [← hc.ord_rho]; exact pow_orderOf_eq_one rho
  rhoP := fun x hx => hc.normal_Q.2 rho (l12_rho_lam_mem_M hc.toCtx11).1 x hx
  rhoQ := fun x hx =>
    (c13_normal_Y hc).2 rho (l12_rho_lam_mem_M hc.toCtx11).1 x hx
  fix := fun x hx hfix => l12_cent_Q_rho hc.toCtx11 x hx (comm_of_conj_eq hfix)
  cardQ := by rw [card_ctxYq hc.q_iso]
  idx := by
    have hinf : ctxYq t tau x₁ x₂ rho ⊓ ctxQ t tau x₁ x₂ rho = ctxYq t tau x₁ x₂ rho :=
      inf_eq_left.mpr ctxYq_le_ctxQ
    have h := Subgroup.relIndex_mul_card (H := ctxYq t tau x₁ x₂ rho) (K := ctxQ t tau x₁ x₂ rho)
    rw [hinf, card_ctxYq hc.q_iso, IsZ4Z4E4.card hc.q_iso] at h
    omega

theorem c13_phi_Q (hc : Ctx13A t L S x₁ x₂ lam rho tau om) :
    ctxPhi (ctxQ t tau x₁ x₂ rho) = fourGrp x₁ x₂ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (IsPGroup 2 ↥(ctxQ t tau x₁ x₂ rho)) :=
    ⟨(l12_isPGroup_R hc.toCtx11).to_le (l12_Q_le_R hc.toCtx11)⟩
  apply le_antisymm
  · rw [ctxPhi]
    refine Subgroup.map_le_iff_le_comap.mpr ?_
    rw [frattini_eq_closure_commutator_union_powers (p := 2)]
    refine (Subgroup.closure_le (K := Subgroup.comap (ctxQ t tau x₁ x₂ rho).subtype
      (fourGrp x₁ x₂))).2 ?_
    intro z hz
    rcases hz with hz | hz
    · rw [commutator_eq_closure] at hz
      refine (Subgroup.closure_le (K := Subgroup.comap (ctxQ t tau x₁ x₂ rho).subtype
        (fourGrp x₁ x₂))).2 ?_ hz
      intro w hw
      rw [mem_commutatorSet_iff] at hw
      obtain ⟨u, v, rfl⟩ := hw
      refine Subgroup.mem_subgroupOf.mpr ?_
      have h1 : ((⁅u, v⁆ : ↥(ctxQ t tau x₁ x₂ rho)) : G) = 1 := by
        show (u : G) * (v : G) * (u : G)⁻¹ * (v : G)⁻¹ = 1
        rw [c13_Q_comm hc u.1 u.2 v.1 v.2]; group
      rw [h1]
      exact Subgroup.one_mem _
    · obtain ⟨x, rfl⟩ := hz
      exact c13_sq_V hc x.1 x.2
  · have hx₁B : x₁ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
    have hx₂B : x₂ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
    have hx₁Q : x₁ ∈ ctxQ t tau x₁ x₂ rho := hc.base_le_Q hx₁B
    have hx₂Q : x₂ ∈ ctxQ t tau x₁ x₂ rho := hc.base_le_Q hx₂B
    have hprodQ : x₁ * x₂ ∈ ctxQ t tau x₁ x₂ rho := Subgroup.mul_mem _ hx₁Q hx₂Q
    rw [fourGrp, Subgroup.closure_le]
    intro y hy
    rcases (by simpa using hy) with rfl | rfl
    · rw [ctxPhi]
      exact Subgroup.mem_map.mpr
        ⟨(⟨x₁, hx₁Q⟩ : ↥(ctxQ t tau x₁ x₂ rho)) ^ 2,
          pth_power_mem_frattini_of_isPGroup (p := 2) _, by simp⟩
    · rw [ctxPhi]
      exact Subgroup.mem_map.mpr
        ⟨(⟨x₁ * x₂, hprodQ⟩ : ↥(ctxQ t tau x₁ x₂ rho)) ^ 2,
          pth_power_mem_frattini_of_isPGroup (p := 2) _, by simp⟩

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
