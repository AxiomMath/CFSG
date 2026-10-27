module

public import CFSG.ClassicalInvolution.Solomon73.YamakiAmalgamModel

public section

namespace CFSG.ClassicalInvolution.Solomon73.Yamaki

open CFSG.Open

variable {G : Type*} [Group G] {N H : Subgroup G}

section Psi

variable (ν : ↥N ≃* ↥N0) (θ : ↥H ≃* ↥Hhat)

theorem theta_symm_mem_N
    (hθX : ∀ x (hx : x ∈ H), x ∈ N ↔ (θ ⟨x, hx⟩ : StatedSp 3 (ZMod 2)) ∈ X0) (y : ↥X0) :
    ((θ.symm ⟨y, X0_le_Hhat y.2⟩ : ↥H) : G) ∈ N := by
  rw [hθX _ (θ.symm ⟨y, X0_le_Hhat y.2⟩).2, Subtype.coe_eta, MulEquiv.apply_symm_apply]
  exact y.2

@[expose] noncomputable def psiOf
    (hθX : ∀ x (hx : x ∈ H), x ∈ N ↔ (θ ⟨x, hx⟩ : StatedSp 3 (ZMod 2)) ∈ X0) :
    ↥X0 →* StatedSp 3 (ZMod 2) :=
  N0.subtype.comp (ν.toMonoidHom.comp (MonoidHom.codRestrict
    (H.subtype.comp (θ.symm.toMonoidHom.comp (Subgroup.inclusion X0_le_Hhat))) N
    (theta_symm_mem_N θ hθX)))

variable (hθX : ∀ x (hx : x ∈ H), x ∈ N ↔ (θ ⟨x, hx⟩ : StatedSp 3 (ZMod 2)) ∈ X0)

theorem psiOf_apply (y : ↥X0) :
    psiOf ν θ hθX y =
      (ν ⟨(θ.symm ⟨y, X0_le_Hhat y.2⟩ : G), theta_symm_mem_N θ hθX y⟩ : StatedSp 3 (ZMod 2)) :=
  rfl

theorem psiOf_injective : Function.Injective (psiOf ν θ hθX) := by
  intro y z hyz
  rw [psiOf_apply, psiOf_apply] at hyz
  have h1 := ν.injective (Subtype.ext hyz)
  have h2 : θ.symm ⟨y, X0_le_Hhat y.2⟩ = θ.symm ⟨z, X0_le_Hhat z.2⟩ :=
    Subtype.ext (congrArg (Subtype.val : ↥N → G) h1)
  exact Subtype.ext (congrArg (Subtype.val : ↥Hhat → StatedSp 3 (ZMod 2)) (θ.symm.injective h2))

theorem psiOf_mem_X0
    (hνX : ∀ x (hx : x ∈ N), x ∈ H ↔ (ν ⟨x, hx⟩ : StatedSp 3 (ZMod 2)) ∈ X0) (y : ↥X0) :
    psiOf ν θ hθX y ∈ X0 := by
  rw [psiOf_apply, ← hνX]
  exact (θ.symm ⟨y, X0_le_Hhat y.2⟩).2

theorem psiOf_theta {x : G} (hN : x ∈ N) (hH : x ∈ H) :
    psiOf ν θ hθX ⟨θ ⟨x, hH⟩, (hθX x hH).mp hN⟩ = ν ⟨x, hN⟩ := by
  have hx : ((θ.symm ⟨(θ ⟨x, hH⟩ : StatedSp 3 (ZMod 2)), X0_le_Hhat ((hθX x hH).mp hN)⟩ :
      ↥H) : G) = x := by
    rw [Subtype.coe_eta, MulEquiv.symm_apply_apply]
  rw [psiOf_apply]
  exact congrArg (fun z => (ν z : StatedSp 3 (ZMod 2))) (Subtype.ext hx)

theorem isConj_of_fusionStep {x y : ↥X0} (h : FusionStep (psiOf ν θ hθX) x y) :
    IsConj ((θ.symm ⟨x, X0_le_Hhat x.2⟩ : ↥H) : G) ((θ.symm ⟨y, X0_le_Hhat y.2⟩ : ↥H) : G) := by
  rw [isConj_iff]
  cases h with
  | hhat c hc hcy =>
    have e : (⟨c, hc⟩ : ↥Hhat) * ⟨y, X0_le_Hhat y.2⟩ = ⟨x, X0_le_Hhat x.2⟩ * ⟨c, hc⟩ :=
      Subtype.ext hcy
    have e' := congrArg (fun z => ((θ.symm z : ↥H) : G)) e
    simp only [map_mul, Subgroup.coe_mul] at e'
    refine ⟨((θ.symm ⟨c, hc⟩ : ↥H) : G)⁻¹, ?_⟩
    rw [inv_inv, mul_assoc, ← e', inv_mul_cancel_left]
  | n0 c hc hcy =>
    rw [psiOf_apply, psiOf_apply] at hcy
    have e : ν (ν.symm ⟨c, hc⟩ * ⟨_, theta_symm_mem_N θ hθX y⟩) =
        ν (⟨_, theta_symm_mem_N θ hθX x⟩ * ν.symm ⟨c, hc⟩) := by
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact Subtype.ext hcy
    have e' := congrArg (Subtype.val : ↥N → G) (ν.injective e)
    simp only [Subgroup.coe_mul] at e'
    refine ⟨((ν.symm ⟨c, hc⟩ : ↥N) : G)⁻¹, ?_⟩
    rw [inv_inv, mul_assoc, ← e', inv_mul_cancel_left]

theorem isConj_of_chain {x y : ↥X0}
    (h : Relation.ReflTransGen (FusionStep (psiOf ν θ hθX)) x y) :
    IsConj ((θ.symm ⟨x, X0_le_Hhat x.2⟩ : ↥H) : G) ((θ.symm ⟨y, X0_le_Hhat y.2⟩ : ↥H) : G) := by
  induction h with
  | refl => exact IsConj.refl _
  | tail _ hst ih => exact ih.trans (isConj_of_fusionStep ν θ hθX hst)

end Psi

theorem exists_compat_of_rigid (ν : ↥N ≃* ↥N0) (θ : ↥H ≃* ↥Hhat)
    (hνX : ∀ x (hx : x ∈ N), x ∈ H ↔ (ν ⟨x, hx⟩ : StatedSp 3 (ZMod 2)) ∈ X0)
    (hθX : ∀ x (hx : x ∈ H), x ∈ N ↔ (θ ⟨x, hx⟩ : StatedSp 3 (ZMod 2)) ∈ X0)
    (hrig : ¬ IsConj ((θ.symm ⟨pi12, S0_le_Hhat pi12_mem_S0⟩ : ↥H) : G)
      ((θ.symm ⟨pi3, S0_le_Hhat pi3_mem_S0⟩ : ↥H) : G)) :
    ∃ (ν' : ↥N ≃* ↥N0) (θ' : ↥H ≃* ↥Hhat),
      (∀ x (hN : x ∈ N) (hH : x ∈ H), (ν' ⟨x, hN⟩ : StatedSp 3 (ZMod 2)) = θ' ⟨x, hH⟩) ∧
      (∀ x (hx : x ∈ N), x ∈ H ↔ (ν' ⟨x, hx⟩ : StatedSp 3 (ZMod 2)) ∈ X0) ∧
      (∀ x (hx : x ∈ H), x ∈ N ↔ (θ' ⟨x, hx⟩ : StatedSp 3 (ZMod 2)) ∈ X0) ∧
      ((θ'.symm ⟨alpha, S0_le_Hhat alpha_mem_S0⟩ : ↥H) : G) =
        θ.symm ⟨alpha, S0_le_Hhat alpha_mem_S0⟩ := by
  set ψ := psiOf ν θ hθX
  obtain ⟨k, hk, w, hw, hψw⟩ :=
    exists_rep_of_injective ψ (psiOf_injective ν θ hθX) (psiOf_mem_X0 ν θ hθX hνX)
  by_cases hk8 : 8 ≤ k
  · exact absurd (isConj_of_chain ν θ hθX (chain_of_twisted ψ hk8 hk hw hψw)) hrig
  have hk8' : k < 8 := by omega
  have hstd := eq_std_of_rep ψ hk8' hψw
  have hwN : w⁻¹ ∈ N0 := N0.inv_mem (X0_le_N0 hw)
  set φN : MulAut ↥N0 := MulAut.conj (⟨w⁻¹, hwN⟩ : ↥N0) * stdN k with hφN
  have hφN_apply : ∀ n : ↥N0,
      (φN n : StatedSp 3 (ZMod 2)) = w⁻¹ * (stdN k n : StatedSp 3 (ZMod 2)) * w := by
    intro n
    rw [hφN, MulAut.mul_apply, MulAut.conj_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
  have hφN_X0 : ∀ n : ↥N0, (φN n : StatedSp 3 (ZMod 2)) ∈ X0 ↔ (n : StatedSp 3 (ZMod 2)) ∈ X0 := by
    intro n
    rw [hφN_apply, X0.mul_mem_cancel_right hw, X0.mul_mem_cancel_left (X0.inv_mem hw),
      stdN_mem_X0_iff]
  refine ⟨ν.trans φN.symm, θ.trans (stdH k), fun x hN hH => ?_, fun x hx => ?_, fun x hx => ?_, ?_⟩
  ·
    set y : ↥X0 := ⟨θ ⟨x, hH⟩, (hθX x hH).mp hN⟩
    have h1 : (ν ⟨x, hN⟩ : StatedSp 3 (ZMod 2)) = w⁻¹ * stdHom k y * w := by
      rw [← psiOf_theta ν θ hθX hN hH]
      exact hstd y
    have h2 : ν ⟨x, hN⟩ = φN ⟨stdH k ⟨y, X0_le_Hhat y.2⟩, stdH_mem_N0 k y⟩ := by
      apply Subtype.ext
      rw [h1, hφN_apply, stdHom_apply]
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, h2, MulEquiv.symm_apply_apply]
  ·
    rw [hνX x hx, MulEquiv.trans_apply, ← hφN_X0 (φN.symm (ν ⟨x, hx⟩)),
      MulEquiv.apply_symm_apply]
  ·
    rw [hθX x hx, MulEquiv.trans_apply, stdH_mem_X0_iff]
  ·
    have h : (stdH k).symm ⟨alpha, S0_le_Hhat alpha_mem_S0⟩ = ⟨alpha, S0_le_Hhat alpha_mem_S0⟩ :=
      (MulEquiv.symm_apply_eq _).mpr (stdH_alpha k).symm
    rw [MulEquiv.symm_trans_apply, h]

end CFSG.ClassicalInvolution.Solomon73.Yamaki
