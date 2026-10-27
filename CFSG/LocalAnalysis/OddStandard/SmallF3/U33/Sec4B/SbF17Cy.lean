module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbF17b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17Cm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17Sq
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQab

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

private lemma fourGrp_le_baseGrp' (x₁ x₂ : G) : fourGrp x₁ x₂ ≤ baseGrp x₁ x₂ := by
  rw [fourGrp, Subgroup.closure_le]
  rintro g (rfl | rfl)
  · have h₁ : x₁ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
    simpa [pow_two] using (baseGrp x₁ x₂).mul_mem h₁ h₁
  · have h₁ : x₁ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
    have h₂ : x₂ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
    have h₁₂ : x₁ * x₂ ∈ baseGrp x₁ x₂ := (baseGrp x₁ x₂).mul_mem h₁ h₂
    simpa [pow_two] using (baseGrp x₁ x₂).mul_mem h₁₂ h₁₂

private lemma lam_mul_self (hc : Ctx13 t L S x₁ x₂ lam rho tau om) : lam * lam = 1 := by
  have h := pow_orderOf_eq_one lam
  rw [hc.wreath.ord_lam] at h
  simpa [pow_two] using h

private lemma lam_normalizes_Yq (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    ∀ a ∈ ctxYq t tau x₁ x₂ rho, lam * a * lam⁻¹ ∈ ctxYq t tau x₁ x₂ rho := by
  intro a ha
  have hlamM : lam ∈ ctxM t tau x₁ x₂ := by
    rw [hc.M_eq]
    exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  exact hc.normal_Y.2 lam hlamM a ha

private lemma Yq_elemAbelian (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    CFSG.Open.IsElemAbelian 2 (ctxYq t tau x₁ x₂ rho) := by
  have hcomm : ∀ a ∈ ctxYq t tau x₁ x₂ rho, ∀ b ∈ ctxYq t tau x₁ x₂ rho, a * b = b * a :=
    fun a ha b hb => IsZ4Z4E4.comm hc.q_iso (ctxYq_le_ctxQ ha) (ctxYq_le_ctxQ hb)
  refine ⟨IsMulCommutative.of_comm (fun a b => Subtype.ext (hcomm a a.2 b b.2)), ?_⟩
  intro a ha
  exact ((mem_ctxYq_iff hc.q_iso a).mp ha).2

private lemma four_le_card_CY (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    4 ≤ Nat.card ↥(ctxYq t tau x₁ x₂ rho ⊓ centralizer ({lam} : Set G)) := by
  let c : ℕ := Nat.card ↥(ctxYq t tau x₁ x₂ rho ⊓ centralizer ({lam} : Set G))
  have hlow : 16 ≤ c ^ 2 := by
    have h := card_le_sq_card_centralizer (Yq_elemAbelian hc) (lam_mul_self hc)
      (lam_normalizes_Yq hc)
    rw [card_ctxYq hc.q_iso] at h
    exact h
  have hgoal : 4 ≤ c := by
    by_contra h
    have h3 : c ≤ 3 := by omega
    have hp : c ^ 2 ≤ 3 ^ 2 := Nat.pow_le_pow_left h3 2
    norm_num at hp
    omega
  exact hgoal

private lemma card_CY_le_four (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    Nat.card ↥(ctxYq t tau x₁ x₂ rho ⊓ centralizer ({lam} : Set G)) ≤ 4 := by
  classical
  let Y : Subgroup G := ctxYq t tau x₁ x₂ rho
  let C : Subgroup G := Y ⊓ centralizer ({lam} : Set G)
  have hYcomm : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a :=
    fun a ha b hb => IsZ4Z4E4.comm hc.q_iso (ctxYq_le_ctxQ ha) (ctxYq_le_ctxQ hb)
  have hYnorm : ∀ a ∈ Y, lam * a * lam⁻¹ ∈ Y := lam_normalizes_Yq hc
  obtain ⟨N, _hNle, himg, _hpre, hcardCN⟩ := exists_comm_image (A := Y) hYcomm (g := lam) hYnorm
  letI : Fintype ↥N := Fintype.ofFinite ↥N
  obtain ⟨V', v₁, v₂, hV'⟩ := hc.data_V
  obtain ⟨hV'el, _hV'card, _hQeq, hV'inf, _hrho_norm, _hlamt_norm, hYeq, _hCv1, hv1V, hv1ne,
    htv1, hv2V, _hv2ne, _hV'clos, htv2, hltv2, _hCttau, _hom1, _hom2⟩ := hV'
  let y : G := x₁ ^ 2
  let z : G := (x₁ * x₂) ^ 2
  let w : G := v₁ * y * z
  have hyY : y ∈ Y := by
    change y ∈ ctxYq t tau x₁ x₂ rho
    rw [hYeq]
    exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp [y]))
  have hzY : z ∈ Y := by
    change z ∈ ctxYq t tau x₁ x₂ rho
    rw [hYeq]
    exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp [z]))
  have hyV : y ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp [y])
  have hzV : z ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp [z])
  have hy2 : y * y = 1 := by
    have h := ((mem_ctxYq_iff hc.q_iso y).mp hyY).2
    simpa [pow_two] using h
  have hz2 : z * z = 1 := by
    have h := ((mem_ctxYq_iff hc.q_iso z).mp hzY).2
    simpa [pow_two] using h
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hlamy : lam * y * lam⁻¹ = y * z := l17_lam_y hc
  have hyz_comm : y * z = z * y := hYcomm y hyY z hzY
  have hyz_inv : (y * z)⁻¹ = y * z := by
    have hyz_sq : (y * z) * (y * z) = 1 := by
      calc (y * z) * (y * z) = y * (z * y) * z := by group
        _ = y * (y * z) * z := by rw [hyz_comm]
        _ = (y * y) * (z * z) := by group
        _ = 1 := by rw [hy2, hz2, one_mul]
    exact inv_eq_of_mul_eq_one_right hyz_sq
  have hzN : z ∈ N := by
    have h : y * lam * y⁻¹ * lam⁻¹ ∈ N := himg y hyY
    have heq : y * lam * y⁻¹ * lam⁻¹ = z := by
      calc y * lam * y⁻¹ * lam⁻¹ = y * (lam * y * lam⁻¹) := by rw [hyinv]; group
        _ = y * (y * z) := by rw [hlamy]
        _ = z := by rw [← mul_assoc, hy2, one_mul]
    rwa [heq] at h
  have hv2sq : v₂ * v₂ = 1 := by
    have h := hV'el.2 v₂ hv2V
    simpa [pow_two] using h
  have hv2inv : v₂⁻¹ = v₂ := inv_eq_of_mul_eq_one_right hv2sq
  have hyV' : v₂ ∈ Y := by
    change v₂ ∈ ctxYq t tau x₁ x₂ rho
    rw [hYeq]
    exact Subgroup.mem_sup_right hv2V
  have hlt : (lam * t) * v₂ * (lam * t)⁻¹ = lam * (t * v₂ * t⁻¹) * lam⁻¹ := by
    rw [mul_inv_rev]; group
  have hstep1 : lam * (t * v₂ * t⁻¹) * lam⁻¹ = v₂ * v₁ := by
    rw [← hlt]; exact hltv2
  have hstep2 : lam * (v₂ * y) * lam⁻¹ = v₂ * v₁ := by
    rw [htv2] at hstep1; exact hstep1
  have hstep3 : (lam * v₂ * lam⁻¹) * (lam * y * lam⁻¹) = v₂ * v₁ := by
    rw [conj_mul]; exact hstep2
  have hstep4 : (lam * v₂ * lam⁻¹) * (y * z) = v₂ * v₁ := by
    rw [hlamy] at hstep3; exact hstep3
  have hlamv2 : lam * v₂ * lam⁻¹ = v₂ * v₁ * y * z := by
    calc lam * v₂ * lam⁻¹
        = (lam * v₂ * lam⁻¹) * (y * z) * (y * z)⁻¹ := by group
      _ = (lam * v₂ * lam⁻¹) * (y * z) * (y * z) := by rw [hyz_inv]
      _ = (v₂ * v₁) * (y * z) := by rw [hstep4]
      _ = v₂ * v₁ * y * z := by group
  have hwN : w ∈ N := by
    have h : v₂ * lam * v₂⁻¹ * lam⁻¹ ∈ N := himg v₂ hyV'
    have heq : v₂ * lam * v₂⁻¹ * lam⁻¹ = w := by
      calc v₂ * lam * v₂⁻¹ * lam⁻¹ = v₂ * (lam * v₂ * lam⁻¹) := by rw [hv2inv]; group
        _ = v₂ * (v₂ * v₁ * y * z) := by rw [hlamv2]
        _ = v₁ * y * z := by
          calc v₂ * (v₂ * v₁ * y * z) = (v₂ * v₂) * (v₁ * y * z) := by group
            _ = v₁ * y * z := by rw [hv2sq, one_mul]
    rwa [heq] at h
  have hz_ne_one : z ≠ 1 := (l17_yz_ne hc).2.1
  have hw_ne_z_aux : w ≠ z := by
    intro h
    have h1 : v₁ * y * z = z := h
    have hv1y : v₁ * y = 1 := by
      have h2 : v₁ * y * z = 1 * z := by rw [one_mul]; exact h1
      exact mul_right_cancel h2
    have hv1_eq : v₁ = y := by
      rw [eq_inv_of_mul_eq_one_left hv1y, hyinv]
    have hv1b : v₁ ∈ baseGrp x₁ x₂ := by
      rw [hv1_eq]
      exact fourGrp_le_baseGrp' x₁ x₂ hyV
    have hmem : v₁ ∈ (⊥ : Subgroup G) := by
      have hthis : v₁ ∈ baseGrp x₁ x₂ ⊓ V' := ⟨hv1b, hv1V⟩
      rwa [hV'inf] at hthis
    exact hv1ne (Subgroup.mem_bot.mp hmem)
  have hzw_ne_one : z * w ≠ 1 := by
    intro h
    have hwz : w = z := by
      calc w = 1 * w := by rw [one_mul]
        _ = (z * z) * w := by rw [hz2]
        _ = z * (z * w) := by rw [mul_assoc]
        _ = z * 1 := by rw [h]
        _ = z := by rw [mul_one]
    exact hw_ne_z_aux hwz
  have hw_ne_one : w ≠ 1 := by
    intro h
    have h1 : v₁ * y * z = 1 := h
    have h' : v₁ * (y * z) = 1 := by rwa [mul_assoc] at h1
    have hv1_eq : v₁ = y * z := by
      rw [eq_inv_of_mul_eq_one_left h', hyz_inv]
    have hyzV : y * z ∈ fourGrp x₁ x₂ := (fourGrp x₁ x₂).mul_mem hyV hzV
    have hv1b : v₁ ∈ baseGrp x₁ x₂ := by
      rw [hv1_eq]
      exact fourGrp_le_baseGrp' x₁ x₂ hyzV
    have hmem : v₁ ∈ (⊥ : Subgroup G) := by
      have hthis : v₁ ∈ baseGrp x₁ x₂ ⊓ V' := ⟨hv1b, hv1V⟩
      rwa [hV'inf] at hthis
    exact hv1ne (Subgroup.mem_bot.mp hmem)
  let a0 : ↥N := ⟨1, N.one_mem⟩
  let a1 : ↥N := ⟨z, hzN⟩
  let a2 : ↥N := ⟨w, hwN⟩
  let a3 : ↥N := ⟨z * w, N.mul_mem hzN hwN⟩
  let S : Finset ↥N := {a0, a1, a2, a3}
  have ha01 : a0 ≠ a1 := fun hh => hz_ne_one (Subtype.ext_iff.mp hh).symm
  have ha02 : a0 ≠ a2 := fun hh => hw_ne_one (Subtype.ext_iff.mp hh).symm
  have ha03 : a0 ≠ a3 := fun hh => hzw_ne_one (Subtype.ext_iff.mp hh).symm
  have ha12 : a1 ≠ a2 := fun hh => hw_ne_z_aux (Subtype.ext_iff.mp hh).symm
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
      _ = 16 := card_ctxYq hc.q_iso
      _ = 4 * 4 := by norm_num
  exact Nat.le_of_mul_le_mul_left hmul (by norm_num)

theorem l17_card_CY_lam (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    Nat.card ↥(ctxYq t tau x₁ x₂ rho ⊓ centralizer ({lam} : Set G)) = 4 := by
  apply le_antisymm (card_CY_le_four hc)
  exact four_le_card_CY hc

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
