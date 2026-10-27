module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ATauA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL35c

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private lemma fzl_twoCore_eq_zpowers (h : Ctx t L S x₁ x₂ lam rho tau)
    (hK : Nat.card (twoCore t) = 2) : twoCore t = Subgroup.zpowers t := by
  have hle : Subgroup.zpowers t = twoCore t := by
    apply Subgroup.eq_of_le_of_card_ge
    · exact Subgroup.zpowers_le.mpr h.hyp.mem_twoCore
    · rw [hK, Nat.card_zpowers, h.hyp.ord_t]
  exact hle.symm

theorem fzl_tau_facts (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 2) :
    tau ∈ fzN2 t x₁ x₂ ∧ tau * t * tau⁻¹ = t ∧
      (∀ z ∈ fourGrp x₁ x₂, tau * z * tau⁻¹ = z) ∧
      (∀ w ∈ ctxW t x₁ x₂, tau * w * tau⁻¹ = w⁻¹) := by
  have hτH : tau ∈ invCent t := h.le_invCent h.tau_mem
  have hτt : tau * t * tau⁻¹ = t := by
    have hcomm : tau * t = t * tau := S4A.mem_invCent_iff.mp hτH
    calc tau * t * tau⁻¹ = (t * tau) * tau⁻¹ := by rw [hcomm]
      _ = t := by group
  have hτN2 : tau ∈ fzN2 t x₁ x₂ := fz_S_le_N2 h h.tau_mem
  have hτinv : ∀ b ∈ baseGrp x₁ x₂, tau * b * tau⁻¹ = b⁻¹ := fun b hb =>
    S4A.alpha_inv_of_mem_baseGrp (α := MulAut.conj tau) h.wreath
      (by simpa [MulAut.conj_apply] using h.tau_x₁)
      (by simpa [MulAut.conj_apply] using h.tau_x₂) hb
  have hZfix : ∀ z ∈ fourGrp x₁ x₂, tau * z * tau⁻¹ = z := by
    intro z hz
    have hb : z ∈ baseGrp x₁ x₂ := S4A.pt_four_le_base x₁ x₂ hz
    have hτz : tau * z * tau⁻¹ = z⁻¹ := hτinv z hb
    have hzz : z * z = 1 := by simpa [pow_two] using fzl_Z_sq_eq_one h hz
    rw [hτz, inv_eq_of_mul_eq_one_right hzz]
  have hWinv : ∀ w ∈ ctxW t x₁ x₂, tau * w * tau⁻¹ = w⁻¹ := by
    intro w hw
    obtain ⟨p, hp, b, hb, hpb⟩ :=
      (mem_sup_iff_of_commute (S4A.pt_comm_base h.toCtx0)).mp hw
    have hP : twoCore t = Subgroup.zpowers t := fzl_twoCore_eq_zpowers h hK
    have hp' : p = 1 ∨ p = t := S4A.pt_eq_one_or_of_mem_zpowers h.hyp.ord_t (hP ▸ hp)
    have hpb_comm : p * b = b * p := S4A.pt_comm_base h.toCtx0 p hp b hb
    have hτb : tau * b * tau⁻¹ = b⁻¹ := hτinv b hb
    have hpp : p * p = 1 := by
      rcases hp' with rfl | rfl
      · simp
      · exact S4A.t_mul_self h.hyp
    have hτp : tau * p * tau⁻¹ = p := by
      rcases hp' with rfl | rfl
      · simp
      · exact hτt
    rw [hpb]
    calc tau * (p * b) * tau⁻¹ = (tau * p * tau⁻¹) * (tau * b * tau⁻¹) := by group
      _ = p * b⁻¹ := by rw [hτp, hτb]
      _ = (p * b)⁻¹ := by
        rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hpp]
        have hcomm' : p * b⁻¹ = b⁻¹ * p := by
          have h := congrArg (fun x => b⁻¹ * x * b⁻¹) hpb_comm
          simpa [mul_assoc] using h.symm
        exact hcomm'
  exact ⟨hτN2, hτt, hZfix, hWinv⟩

theorem fzl_Wtau_act (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 2) {k : G}
    (hk : k ∈ ctxW t x₁ x₂ ⊔ zpowers tau) :
    k ∈ fzN2 t x₁ x₂ ∧ k * t * k⁻¹ = t ∧ (∀ z ∈ fourGrp x₁ x₂, k * z * k⁻¹ = z) ∧
      ((∀ w ∈ ctxW t x₁ x₂, k * w * k⁻¹ = w) ∨
        (∀ w ∈ ctxW t x₁ x₂, k * w * k⁻¹ = w⁻¹)) := by
  obtain ⟨hτN2, hτt, hτZ, hτW⟩ := fzl_tau_facts h hK
  have hkN2 : k ∈ fzN2 t x₁ x₂ :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hτN2) hk
  have hkt : k * t * k⁻¹ = t := by
    have hle : ctxW t x₁ x₂ ⊔ zpowers tau ≤ Subgroup.centralizer ({t} : Set G) := by
      refine sup_le (fun w hw => ?_) (Subgroup.zpowers_le.mpr ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (fzl_t_facts h).2.2.1 w hw
      · rw [Subgroup.mem_centralizer_singleton_iff]
        calc tau * t = (tau * t * tau⁻¹) * tau := by group
          _ = t * tau := by rw [hτt]
    have hc := hle hk
    rw [Subgroup.mem_centralizer_singleton_iff] at hc
    calc k * t * k⁻¹ = (t * k) * k⁻¹ := by rw [hc]
      _ = t := by group
  have hkZ : ∀ z ∈ fourGrp x₁ x₂, k * z * k⁻¹ = z := by
    intro z hz
    have hzW : z ∈ ctxW t x₁ x₂ := fzl_Z_le_W h hz
    have hle : ctxW t x₁ x₂ ⊔ zpowers tau ≤ Subgroup.centralizer ({z} : Set G) := by
      refine sup_le (fun w hw => ?_) (Subgroup.zpowers_le.mpr ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        haveI : IsMulCommutative (ctxW t x₁ x₂) := h.abelian_W
        exact congrArg Subtype.val
          (mul_comm' (⟨w, hw⟩ : ctxW t x₁ x₂) ⟨z, hzW⟩)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        calc tau * z = (tau * z * tau⁻¹) * tau := by group
          _ = z * tau := by rw [hτZ z hz]
    have hc := hle hk
    rw [Subgroup.mem_centralizer_singleton_iff] at hc
    calc k * z * k⁻¹ = (z * k) * k⁻¹ := by rw [hc]
      _ = z := by group
  have hWsupNorm : ctxW t x₁ x₂ ⊔ zpowers tau ≤
      Subgroup.normalizer ((ctxW t x₁ x₂ : Subgroup G) : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hτN2)
  let Sd : Subgroup G :=
    { carrier := {k : G | k ∈ ctxW t x₁ x₂ ⊔ zpowers tau ∧
        ((∀ w ∈ ctxW t x₁ x₂, k * w * k⁻¹ = w) ∨
          (∀ w ∈ ctxW t x₁ x₂, k * w * k⁻¹ = w⁻¹))}
      one_mem' := ⟨Subgroup.one_mem _, Or.inl (by intro w _; group)⟩
      mul_mem' := by
        rintro a b ⟨ha, hda⟩ ⟨hb, hdb⟩
        have haw : ∀ w ∈ ctxW t x₁ x₂, a * w * a⁻¹ ∈ ctxW t x₁ x₂ := fun w hw =>
          (Subgroup.mem_normalizer_iff.mp (hWsupNorm ha) w).mp hw
        have hbw : ∀ w ∈ ctxW t x₁ x₂, b * w * b⁻¹ ∈ ctxW t x₁ x₂ := fun w hw =>
          (Subgroup.mem_normalizer_iff.mp (hWsupNorm hb) w).mp hw
        refine ⟨Subgroup.mul_mem _ ha hb, ?_⟩
        rcases hda with hda | hda <;> rcases hdb with hdb | hdb
        · left; intro w hw
          calc (a * b) * w * (a * b)⁻¹ = a * (b * w * b⁻¹) * a⁻¹ := by group
            _ = a * w * a⁻¹ := by rw [hdb w hw]
            _ = w := hda w hw
        · right; intro w hw
          calc (a * b) * w * (a * b)⁻¹ = a * (b * w * b⁻¹) * a⁻¹ := by group
            _ = a * w⁻¹ * a⁻¹ := by rw [hdb w hw]
            _ = (a * w * a⁻¹)⁻¹ := by group
            _ = w⁻¹ := by rw [hda w hw]
        · right; intro w hw
          calc (a * b) * w * (a * b)⁻¹ = a * (b * w * b⁻¹) * a⁻¹ := by group
            _ = a * w * a⁻¹ := by rw [hdb w hw]
            _ = w⁻¹ := hda w hw
        · left; intro w hw
          calc (a * b) * w * (a * b)⁻¹ = a * (b * w * b⁻¹) * a⁻¹ := by group
            _ = a * w⁻¹ * a⁻¹ := by rw [hdb w hw]
            _ = (a * w * a⁻¹)⁻¹ := by group
            _ = (w⁻¹)⁻¹ := by rw [hda w hw]
            _ = w := by group
      inv_mem' := by
        rintro a ⟨ha, hda⟩
        refine ⟨Subgroup.inv_mem _ ha, ?_⟩
        rcases hda with hda | hda
        · left; intro w hw
          simp only [inv_inv]
          have hcomm : a * w = w * a := by
            calc a * w = (a * w * a⁻¹) * a := by group
              _ = w * a := by rw [hda w hw]
          calc a⁻¹ * w * a = a⁻¹ * (w * a) := by group
            _ = a⁻¹ * (a * w) := by rw [← hcomm]
            _ = w := by group
        · right; intro w hw
          simp only [inv_inv]
          have h1 : w = a⁻¹ * w⁻¹ * a := by
            calc w = a⁻¹ * (a * w * a⁻¹) * a := by group
              _ = a⁻¹ * w⁻¹ * a := by rw [hda w hw]
          calc a⁻¹ * w * a = (a⁻¹ * w⁻¹ * a)⁻¹ := by group
            _ = w⁻¹ := by rw [← h1] }
  have hWSd : ctxW t x₁ x₂ ≤ Sd := by
    intro w hw
    refine ⟨Subgroup.mem_sup_left hw, Or.inl ?_⟩
    intro v hv
    haveI : IsMulCommutative (ctxW t x₁ x₂) := h.abelian_W
    have hcomm : w * v = v * w := congrArg Subtype.val
      (mul_comm' (⟨w, hw⟩ : ctxW t x₁ x₂) ⟨v, hv⟩)
    rw [hcomm]; group
  have hτSd : tau ∈ Sd :=
    ⟨Subgroup.mem_sup_right (Subgroup.mem_zpowers tau), Or.inr hτW⟩
  have hsup : ctxW t x₁ x₂ ⊔ zpowers tau ≤ Sd :=
    sup_le hWSd (Subgroup.zpowers_le.mpr hτSd)
  exact ⟨hkN2, hkt, hkZ, (hsup hk).2⟩

end CFSG.OddStandard.SmallF3.FritzII
