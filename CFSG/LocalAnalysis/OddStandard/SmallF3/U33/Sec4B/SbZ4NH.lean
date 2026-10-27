module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4NF
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17FL
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17Sq
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4NE

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

namespace Ctx4Z

variable (hz : Ctx4Z t L S x₁ x₂ lam rho tau)
include hz

theorem card_CY_t :
    Nat.card {a : G // a ∈ ctxYq t tau x₁ x₂ rho ∧ t * a = a * t} ≤ 4 := by
  let f : {a : G // a ∈ ctxYq t tau x₁ x₂ rho ∧ t * a = a * t} →
      ↥(fourGrp x₁ x₂) := fun a =>
    ⟨a.1, by
      have hmem : a.1 ∈ ctxYq t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G) :=
        Subgroup.mem_inf.mpr
          ⟨a.2.1, Subgroup.mem_centralizer_singleton_iff.mpr a.2.2.symm⟩
      rwa [hz.CY_t] at hmem⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have h : (a.1 : G) = b.1 := by
      simpa only using congrArg (fun z : ↥(fourGrp x₁ x₂) => (z : G)) hab
    exact Subtype.ext h
  calc Nat.card {a : G // a ∈ ctxYq t tau x₁ x₂ rho ∧ t * a = a * t}
      ≤ Nat.card ↥(fourGrp x₁ x₂) := Nat.card_le_card_of_injective f hinj
    _ = 4 := hz.nPre.card_V

theorem card_CY_ttau :
    Nat.card {a : G // a ∈ ctxYq t tau x₁ x₂ rho ∧ (t * tau) * a = a * (t * tau)} ≤ 4 := by
  let f : {a : G // a ∈ ctxYq t tau x₁ x₂ rho ∧ (t * tau) * a = a * (t * tau)} →
      {a : G // a ∈ ctxYq t tau x₁ x₂ rho ∧ t * a = a * t} := fun a =>
    ⟨a.1, ⟨a.2.1, by
      have htau := hz.tau_cent_Y a.1 a.2.1
      have h := a.2.2
      have h1 : (t * tau) * a.1 = (t * a.1) * tau := by rw [mul_assoc, htau, mul_assoc]
      have h2 : a.1 * (t * tau) = (a.1 * t) * tau := by rw [mul_assoc]
      rw [h1, h2] at h
      exact mul_right_cancel h⟩⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have h : (a.1 : G) = b.1 := by
      simpa only using congrArg
        (fun z : {a : G // a ∈ ctxYq t tau x₁ x₂ rho ∧ t * a = a * t} => (z : G)) hab
    exact Subtype.ext h
  exact le_trans (Nat.card_le_card_of_injective f hinj) hz.card_CY_t

theorem card_CY_lam_eq :
    Nat.card ↥(ctxYq t tau x₁ x₂ rho ⊓ centralizer ({lam} : Set G)) = 4 := by
  classical
  let Y : Subgroup G := ctxYq t tau x₁ x₂ rho
  let C : Subgroup G := Y ⊓ centralizer ({lam} : Set G)
  have hYnorm : ∀ a ∈ Y, lam * a * lam⁻¹ ∈ Y :=
    fun a ha => hz.normal_Y.2 lam hz.lam_mem_M a ha
  have hYcomm : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a :=
    fun a ha b hb => hz.nPre.Y_comm a ha b hb
  have hlow : 4 ≤ Nat.card ↥C := by
    change 4 ≤ Nat.card ↥(Y ⊓ centralizer ({lam} : Set G))
    have h := S4B.card_le_sq_card_centralizer (A := Y) hz.Y_isElemAbelian
      hz.lam_mul_self hYnorm
    have hY16 : Nat.card Y = 16 := hz.card_Y
    rw [hY16] at h
    let c : ℕ := Nat.card ↥(Y ⊓ centralizer ({lam} : Set G))
    have hc : 16 ≤ c ^ 2 := by simpa [c] using h
    have hc4 : 4 ≤ c := by
      by_contra hlt
      have h3 : c ≤ 3 := by omega
      have hp : c ^ 2 ≤ 3 ^ 2 := Nat.pow_le_pow_left h3 2
      norm_num at hp
      omega
    simpa [c] using hc4
  have hup : Nat.card ↥C ≤ 4 := by
    obtain ⟨N, _hNle, himg, _hpre, hcardCN⟩ :=
      S4B.exists_comm_image (A := Y) hYcomm (g := lam) hYnorm
    obtain ⟨V', v₁, v₂, hV'⟩ := hz.data_V
    obtain ⟨hV'ea, _hV'card, _hQeq, hV'inf, hYeq, _hrhonorm, hv1V, hv2V, _hv1ne, hv2notzp,
      _hV'clos, htv1, _htv2, hltv1, _hQm⟩ := hV'
    let y : G := x₁ ^ 2
    let z : G := (x₁ * x₂) ^ 2
    let w : G := v₁ * v₂ * y * z
    have hyY : y ∈ Y := by
      change y ∈ ctxYq t tau x₁ x₂ rho
      rw [hYeq]
      exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp [y]))
    have hzY : z ∈ Y := by
      change z ∈ ctxYq t tau x₁ x₂ rho
      rw [hYeq]
      exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp [z]))
    have hv1Y : v₁ ∈ Y := by
      change v₁ ∈ ctxYq t tau x₁ x₂ rho
      rw [hYeq]
      exact Subgroup.mem_sup_right hv1V
    have hv2Y : v₂ ∈ Y := by
      change v₂ ∈ ctxYq t tau x₁ x₂ rho
      rw [hYeq]
      exact Subgroup.mem_sup_right hv2V
    have hy2 : y * y = 1 := by simpa [pow_two] using hz.nPre.Y_sq hyY
    have hz2 : z * z = 1 := by simpa [pow_two] using hz.nPre.Y_sq hzY
    have hv1sq : v₁ * v₁ = 1 := by simpa [pow_two] using hV'ea.2 v₁ hv1V
    have hv2sq : v₂ * v₂ = 1 := by simpa [pow_two] using hV'ea.2 v₂ hv2V
    have hyz_comm : y * z = z * y := hYcomm y hyY z hzY
    have hyz2 : (y * z) * (y * z) = 1 := by
      calc (y * z) * (y * z) = y * (z * y) * z := by group
        _ = y * (y * z) * z := by rw [hyz_comm]
        _ = (y * y) * (z * z) := by group
        _ = 1 := by rw [hy2, hz2, one_mul]
    have hyzinv : (y * z)⁻¹ = y * z := inv_eq_of_mul_eq_one_right hyz2
    have hlamy : lam * y * lam⁻¹ = y * z := by
      change lam * x₁ ^ 2 * lam⁻¹ = x₁ ^ 2 * (x₁ * x₂) ^ 2
      rw [hz.nGood.lam_conj_y, hz.x₂_sq]
    have hcomm_y : y * lam * y⁻¹ * lam⁻¹ = z := by
      have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
      have h1 : y * lam * y⁻¹ * lam⁻¹ = y * (lam * y * lam⁻¹)⁻¹ := by group
      rw [h1, hlamy, hyzinv]
      calc y * (y * z) = (y * y) * z := by group
        _ = z := by rw [hy2, one_mul]
    have hlamv1 : lam * v₁ * lam⁻¹ = v₂ * y * z := by
      have h1 : (lam * t) * v₁ * (lam * t)⁻¹ = lam * (t * v₁ * t⁻¹) * lam⁻¹ := by
        rw [mul_inv_rev]; group
      rw [h1, htv1] at hltv1
      have h2 : lam * (v₁ * y) * lam⁻¹ = (lam * v₁ * lam⁻¹) * (y * z) := by
        calc lam * (v₁ * y) * lam⁻¹
            = (lam * v₁ * lam⁻¹) * (lam * y * lam⁻¹) := by group
          _ = (lam * v₁ * lam⁻¹) * (y * z) := by rw [hlamy]
      have h3 : (lam * v₁ * lam⁻¹) * (y * z) = v₂ := by rw [← h2]; exact hltv1
      calc lam * v₁ * lam⁻¹
          = (lam * v₁ * lam⁻¹) * (y * z) * (y * z)⁻¹ := by group
        _ = v₂ * (y * z)⁻¹ := by rw [h3]
        _ = v₂ * (y * z) := by rw [hyzinv]
        _ = v₂ * y * z := by group
    have hcomm_v1 : v₁ * lam * v₁⁻¹ * lam⁻¹ = w := by
      show v₁ * lam * v₁⁻¹ * lam⁻¹ = v₁ * v₂ * y * z
      have hv1inv : v₁⁻¹ = v₁ := inv_eq_of_mul_eq_one_right hv1sq
      have h1 : v₁ * lam * v₁⁻¹ * lam⁻¹ = v₁ * (lam * v₁ * lam⁻¹)⁻¹ := by group
      have hyzY : y * z ∈ Y := Y.mul_mem hyY hzY
      have hvyz_comm : v₂ * (y * z) = (y * z) * v₂ := hYcomm v₂ hv2Y (y * z) hyzY
      have hvyz2 : (v₂ * (y * z)) * (v₂ * (y * z)) = 1 := by
        have hp : (v₂ * (y * z)) ^ 2 = v₂ ^ 2 * (y * z) ^ 2 :=
          ((commute_iff_eq v₂ (y * z)).mpr hvyz_comm).mul_pow 2
        rw [pow_two] at hp
        rw [hp, show v₂ ^ 2 = 1 by rw [pow_two]; exact hv2sq,
          show (y * z) ^ 2 = 1 by rw [pow_two]; exact hyz2, one_mul]
      have hvyzinv : (v₂ * (y * z))⁻¹ = v₂ * (y * z) := inv_eq_of_mul_eq_one_right hvyz2
      rw [h1, hlamv1, show v₂ * y * z = v₂ * (y * z) from by group, hvyzinv]
      group
    have hz_ne_one : z ≠ 1 := by
      change (x₁ * x₂) ^ 2 ≠ 1
      exact hz.z_ne_one
    have hmem_bot : ∀ {a : G}, a ∈ fourGrp x₁ x₂ → a ∈ V' → a = 1 := by
      intro a haV haV'
      have h : a ∈ baseGrp x₁ x₂ ⊓ V' := ⟨hz.nPre.V_le_B haV, haV'⟩
      rw [hV'inf] at h
      exact Subgroup.mem_bot.mp h
    have hv1v2V' : v₁ * v₂ ∈ V' := V'.mul_mem hv1V hv2V
    have hv1v2_ne_one : v₁ * v₂ ≠ 1 := by
      intro h
      have hv2eq : v₂ = v₁ := by
        rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right hv1sq]
      exact hv2notzp (by rw [hv2eq]; exact Subgroup.mem_zpowers v₁)
    have hw_ne_one : w ≠ 1 := by
      intro h
      have h1 : v₁ * v₂ = y * z := by
        calc v₁ * v₂ = v₁ * v₂ * y * z * (y * z)⁻¹ := by group
          _ = 1 * (y * z)⁻¹ := by rw [show v₁ * v₂ * y * z = 1 from h]
          _ = (y * z)⁻¹ := one_mul _
          _ = y * z := hyzinv
      have hmem : v₁ * v₂ ∈ fourGrp x₁ x₂ := by
        rw [h1]
        exact (fourGrp x₁ x₂).mul_mem
          (Subgroup.subset_closure (by simp [y])) (Subgroup.subset_closure (by simp [z]))
      exact hv1v2_ne_one (hmem_bot hmem hv1v2V')
    have hw_ne_z : w ≠ z := by
      intro h
      have h1 : v₁ * v₂ = y := by
        calc v₁ * v₂ = v₁ * v₂ * y * z * z⁻¹ * y⁻¹ := by group
          _ = z * z⁻¹ * y⁻¹ := by rw [show v₁ * v₂ * y * z = z from h]
          _ = 1 * y⁻¹ := by rw [mul_inv_cancel]
          _ = y := by rw [one_mul, inv_eq_of_mul_eq_one_right hy2]
      have hmem : v₁ * v₂ ∈ fourGrp x₁ x₂ := by
        rw [h1]
        exact Subgroup.subset_closure (by simp [y])
      exact hv1v2_ne_one (hmem_bot hmem hv1v2V')
    have hzw_ne_one : z * w ≠ 1 := by
      intro h
      have h2 : z * w = z * z := by rw [h, hz2]
      exact hw_ne_z (mul_left_cancel h2)
    have hzN : z ∈ N := by
      have h := himg y hyY
      rwa [hcomm_y] at h
    have hwN : w ∈ N := by
      have h := himg v₁ hv1Y
      rwa [hcomm_v1] at h
    letI : Fintype ↥N := Fintype.ofFinite ↥N
    let a0 : ↥N := ⟨1, N.one_mem⟩
    let a1 : ↥N := ⟨z, hzN⟩
    let a2 : ↥N := ⟨w, hwN⟩
    let a3 : ↥N := ⟨z * w, N.mul_mem hzN hwN⟩
    let S : Finset ↥N := {a0, a1, a2, a3}
    have ha01 : a0 ≠ a1 := fun hh => hz_ne_one (Subtype.ext_iff.mp hh).symm
    have ha02 : a0 ≠ a2 := fun hh => hw_ne_one (Subtype.ext_iff.mp hh).symm
    have ha03 : a0 ≠ a3 := fun hh => hzw_ne_one (Subtype.ext_iff.mp hh).symm
    have ha12 : a1 ≠ a2 := fun hh => hw_ne_z (Subtype.ext_iff.mp hh).symm
    have ha13 : a1 ≠ a3 := by
      intro hh
      have h2 : z * 1 = z * w := by rw [mul_one]; exact (Subtype.ext_iff.mp hh)
      exact hw_ne_one (mul_left_cancel h2).symm
    have ha23 : a2 ≠ a3 := by
      intro hh
      have h2 : 1 * w = z * w := by rw [one_mul]; exact (Subtype.ext_iff.mp hh)
      exact hz_ne_one (mul_right_cancel h2).symm
    have hcardS : S.card = 4 := by
      rw [Finset.card_eq_four]
      exact ⟨a0, a1, a2, a3, ha01, ha02, ha03, ha12, ha13, ha23, rfl⟩
    have h4N : 4 ≤ Nat.card ↥N := by
      rw [Nat.card_eq_fintype_card]
      calc 4 = S.card := hcardS.symm
        _ ≤ Fintype.card ↥N := Finset.card_le_univ S
    have hmul : 4 * Nat.card ↥C ≤ 4 * 4 := by
      calc 4 * Nat.card ↥C ≤ Nat.card N * Nat.card ↥C := Nat.mul_le_mul_right _ h4N
        _ = Nat.card Y := hcardCN.symm
        _ = 16 := hz.card_Y
        _ = 4 * 4 := by norm_num
    exact Nat.le_of_mul_le_mul_left hmul (by norm_num)
  exact le_antisymm hup hlow

theorem card_CY_lam :
    Nat.card {a : G // a ∈ ctxYq t tau x₁ x₂ rho ∧ lam * a = a * lam} ≤ 4 := by
  let f : {a : G // a ∈ ctxYq t tau x₁ x₂ rho ∧ lam * a = a * lam} →
      ↥(ctxYq t tau x₁ x₂ rho ⊓ centralizer ({lam} : Set G)) := fun a =>
    ⟨a.1, Subgroup.mem_inf.mpr
      ⟨a.2.1, Subgroup.mem_centralizer_singleton_iff.mpr a.2.2.symm⟩⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have h : (a.1 : G) = b.1 := by
      simpa only using congrArg
        (fun z : ↥(ctxYq t tau x₁ x₂ rho ⊓ centralizer ({lam} : Set G)) => (z : G)) hab
    exact Subtype.ext h
  calc Nat.card {a : G // a ∈ ctxYq t tau x₁ x₂ rho ∧ lam * a = a * lam}
      ≤ Nat.card ↥(ctxYq t tau x₁ x₂ rho ⊓ centralizer ({lam} : Set G)) :=
        Nat.card_le_card_of_injective f hinj
    _ = 4 := hz.card_CY_lam_eq

theorem card_CY_lamtau :
    Nat.card {a : G // a ∈ ctxYq t tau x₁ x₂ rho ∧ (lam * tau) * a = a * (lam * tau)} ≤ 4 := by
  let f : {a : G // a ∈ ctxYq t tau x₁ x₂ rho ∧ (lam * tau) * a = a * (lam * tau)} →
      {a : G // a ∈ ctxYq t tau x₁ x₂ rho ∧ lam * a = a * lam} := fun a =>
    ⟨a.1, ⟨a.2.1, by
      have htau := hz.tau_cent_Y a.1 a.2.1
      have h := a.2.2
      have h1 : (lam * tau) * a.1 = (lam * a.1) * tau := by rw [mul_assoc, htau, mul_assoc]
      have h2 : a.1 * (lam * tau) = (a.1 * lam) * tau := by rw [mul_assoc]
      rw [h1, h2] at h
      exact mul_right_cancel h⟩⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have h : (a.1 : G) = b.1 := by
      simpa only using congrArg
        (fun z : {a : G // a ∈ ctxYq t tau x₁ x₂ rho ∧ lam * a = a * lam} => (z : G)) hab
    exact Subtype.ext h
  exact le_trans (Nat.card_le_card_of_injective f hinj) hz.card_CY_lam

end Ctx4Z

namespace ZNW4

variable (hw : ZNW4 t L S x₁ x₂ lam rho tau)
include hw

theorem fl_t : ∀ x ∈ ctxWN t tau x₁ x₂ rho, (t * x) * (t * x) = 1 →
    ∃ p ∈ ctxWN t tau x₁ x₂ rho, t * x = p * t * p⁻¹ := by
  refine S4B.fl_group (P := ctxWN t tau x₁ x₂ rho) (Y := ctxYq t tau x₁ x₂ rho)
    hw.W_comm hw.W_pow_four hw.toCtx4Z.Y_le_ctxWN
    (fun x hx h => hw.toCtx4Z.W_invol_mem_Y hx h) hw.card_ctxWN
    hw.toCtx4Z.t_mul_self (fun x hx => hw.toCtx4Z.t_conj_ctxWN hx) hw.toCtx4Z.card_CY_t

theorem fl_ttau : ∀ x ∈ ctxWN t tau x₁ x₂ rho, ((t * tau) * x) * ((t * tau) * x) = 1 →
    ∃ p ∈ ctxWN t tau x₁ x₂ rho, (t * tau) * x = p * (t * tau) * p⁻¹ := by
  have hg2 : (t * tau) * (t * tau) = 1 := by
    calc (t * tau) * (t * tau) = (t * t) * (tau * tau) := by
          rw [show (t * tau) * (t * tau) = t * (tau * t) * tau from by group, ← hw.t_comm_tau]
          group
      _ = 1 := by rw [hw.t_mul_self, hw.tau_mul_self, one_mul]
  have hgP : ∀ x ∈ ctxWN t tau x₁ x₂ rho,
      (t * tau) * x * (t * tau)⁻¹ ∈ ctxWN t tau x₁ x₂ rho := by
    intro x hx
    have h1 : (t * tau) * x * (t * tau)⁻¹ = t * (tau * x * tau⁻¹) * t⁻¹ := by group
    rw [h1]
    exact hw.toCtx4Z.t_conj_ctxWN (hw.toCtx4Z.tau_conj_ctxWN hx)
  exact S4B.fl_group (P := ctxWN t tau x₁ x₂ rho) (Y := ctxYq t tau x₁ x₂ rho)
    hw.W_comm hw.W_pow_four hw.toCtx4Z.Y_le_ctxWN
    (fun x hx h => hw.toCtx4Z.W_invol_mem_Y hx h) hw.card_ctxWN
    hg2 hgP hw.toCtx4Z.card_CY_ttau

theorem fl_lam : ∀ x ∈ ctxWN t tau x₁ x₂ rho, (lam * x) * (lam * x) = 1 →
    ∃ p ∈ ctxWN t tau x₁ x₂ rho, lam * x = p * lam * p⁻¹ := by
  exact S4B.fl_group (P := ctxWN t tau x₁ x₂ rho) (Y := ctxYq t tau x₁ x₂ rho)
    hw.W_comm hw.W_pow_four hw.toCtx4Z.Y_le_ctxWN
    (fun x hx h => hw.toCtx4Z.W_invol_mem_Y hx h) hw.card_ctxWN
    hw.lam_mul_self (fun x hx => hw.toCtx4Z.lam_conj_ctxWN hx) hw.toCtx4Z.card_CY_lam

theorem fl_lamtau : ∀ x ∈ ctxWN t tau x₁ x₂ rho, ((lam * tau) * x) * ((lam * tau) * x) = 1 →
    ∃ p ∈ ctxWN t tau x₁ x₂ rho, (lam * tau) * x = p * (lam * tau) * p⁻¹ := by
  have hg2 : (lam * tau) * (lam * tau) = 1 := by
    calc (lam * tau) * (lam * tau) = lam * (tau * lam) * tau := by group
      _ = lam * (lam * tau) * tau := by rw [hw.tau_lam]
      _ = (lam * lam) * (tau * tau) := by group
      _ = 1 := by rw [hw.lam_mul_self, hw.tau_mul_self, one_mul]
  have hgP : ∀ x ∈ ctxWN t tau x₁ x₂ rho,
      (lam * tau) * x * (lam * tau)⁻¹ ∈ ctxWN t tau x₁ x₂ rho := by
    intro x hx
    have h1 : (lam * tau) * x * (lam * tau)⁻¹ = lam * (tau * x * tau⁻¹) * lam⁻¹ := by group
    rw [h1]
    exact hw.toCtx4Z.lam_conj_ctxWN (hw.toCtx4Z.tau_conj_ctxWN hx)
  exact S4B.fl_group (P := ctxWN t tau x₁ x₂ rho) (Y := ctxYq t tau x₁ x₂ rho)
    hw.W_comm hw.W_pow_four hw.toCtx4Z.Y_le_ctxWN
    (fun x hx h => hw.toCtx4Z.W_invol_mem_Y hx h) hw.card_ctxWN
    hg2 hgP hw.toCtx4Z.card_CY_lamtau

end ZNW4

end CFSG.OddStandard.SmallF3.HarrisU33
