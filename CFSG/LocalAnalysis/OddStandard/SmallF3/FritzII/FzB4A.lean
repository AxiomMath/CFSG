module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzB0A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL35d

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private lemma fzbs4a_lam_x2 (h : Ctx t L S x₁ x₂ lam rho tau) :
    lam * x₂ * lam⁻¹ = x₁ := by
  have hlam2 : lam ^ 2 = 1 := (fzl_lam_Z h).2.2.1
  have hll : lam * lam = 1 := by rw [← pow_two]; exact hlam2
  have hllinv : lam⁻¹ * lam⁻¹ = 1 := by rw [← mul_inv_rev, hll, inv_one]
  calc lam * x₂ * lam⁻¹ = lam * (lam * x₁ * lam⁻¹) * lam⁻¹ := by rw [h.wreath.conj_x₁]
    _ = (lam * lam) * x₁ * (lam⁻¹ * lam⁻¹) := by group
    _ = x₁ := by rw [hll, hllinv, one_mul, mul_one]

private lemma fzbs4a_mem_base_exists (h : Ctx t L S x₁ x₂ lam rho tau) {e : G}
    (he : e ∈ baseGrp x₁ x₂) : ∃ a b : ℤ, e = x₁ ^ a * x₂ ^ b := by
  have hE : baseGrp x₁ x₂ = zpowers x₁ ⊔ zpowers x₂ := (h.wreath.baseGrp_eq).2.1
  have hcommE : ∀ u ∈ zpowers x₁, ∀ v ∈ zpowers x₂, u * v = v * u := by
    intro u hu v hv
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact ((show Commute x₁ x₂ from h.wreath.comm).zpow_zpow i j).eq
  rw [hE] at he
  obtain ⟨u, hu, v, hv, rfl⟩ := (mem_sup_iff_of_commute hcommE).mp he
  obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  exact ⟨a, b, rfl⟩

private lemma fzbs4a_lam_conj_zpow (h : Ctx t L S x₁ x₂ lam rho tau) (a b : ℤ) :
    lam * (x₁ ^ a * x₂ ^ b) * lam⁻¹ = x₂ ^ a * x₁ ^ b := by
  have h1 : lam * x₁ ^ a * lam⁻¹ = x₂ ^ a := by
    rw [← conj_zpow (a := lam) (b := x₁) (i := a), h.wreath.conj_x₁]
  have h2 : lam * x₂ ^ b * lam⁻¹ = x₁ ^ b := by
    rw [← conj_zpow (a := lam) (b := x₂) (i := b), fzbs4a_lam_x2 h]
  calc lam * (x₁ ^ a * x₂ ^ b) * lam⁻¹
      = (lam * x₁ ^ a * lam⁻¹) * (lam * x₂ ^ b * lam⁻¹) := by group
    _ = x₂ ^ a * x₁ ^ b := by rw [h1, h2]

theorem fzbs_E_sq (h : Ctx t L S x₁ x₂ lam rho tau) {e : G} (he : e ∈ baseGrp x₁ x₂) :
    e ^ 2 ∈ fourGrp x₁ x₂ := by
  have hmem : e ^ 2 ∈ Subgroup.closure {g : G | ∃ a ∈ baseGrp x₁ x₂, g = a ^ 2} :=
    Subgroup.subset_closure ⟨e, he, rfl⟩
  rwa [← WreathRel.fourGrp_eq_mho h.wreath] at hmem

theorem fzbs_X_split (h : Ctx t L S x₁ x₂ lam rho tau) {x : G} (hx : x ∈ fzbsX t x₁ x₂) :
    x ∈ baseGrp x₁ x₂ ∨ t * x ∈ baseGrp x₁ x₂ := by
  have hcomm : ∀ a ∈ zpowers t, ∀ b ∈ baseGrp x₁ x₂, a * b = b * a :=
    fun a ha b hb => S4A.pt_comm_base h.toCtx0 a
      (Subgroup.zpowers_le.mpr h.hyp.mem_twoCore ha) b hb
  obtain ⟨p, hp, e, he, hxpe⟩ := (mem_sup_iff_of_commute hcomm).mp hx
  rcases S4A.pt_eq_one_or_of_mem_zpowers h.hyp.ord_t hp with h1 | h1
  · left
    rw [hxpe, h1, one_mul]
    exact he
  · right
    rw [hxpe, h1, ← mul_assoc, S4A.t_mul_self h.hyp, one_mul]
    exact he

theorem fzbs_u_lam (h : Ctx t L S x₁ x₂ lam rho tau) : lam * (x₁ * x₂) * lam⁻¹ = x₁ * x₂ := by
  calc lam * (x₁ * x₂) * lam⁻¹
      = (lam * x₁ * lam⁻¹) * (lam * x₂ * lam⁻¹) := by group
    _ = x₂ * x₁ := by rw [h.wreath.conj_x₁, fzbs4a_lam_x2 h]
    _ = x₁ * x₂ := h.wreath.comm.symm

theorem fzbs_lam_E_fix (h : Ctx t L S x₁ x₂ lam rho tau) {e : G} (he : e ∈ baseGrp x₁ x₂)
    (hfix : lam * e * lam⁻¹ = e) : e ∈ zpowers (x₁ * x₂) := by
  have hEcomm : IsMulCommutative (baseGrp x₁ x₂) := (h.wreath.baseGrp_eq).1
  have hcomm_e : ∀ b ∈ baseGrp x₁ x₂, b * e = e * b := fun b hb =>
    congrArg Subtype.val (isMulCommutative_iff.mp hEcomm ⟨b, hb⟩ ⟨e, he⟩)
  have hle : wreathGrp x₁ x₂ lam ≤ Subgroup.centralizer ({e} : Set G) := by
    rw [wreathGrp, Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with h1 | h2 | h3
    · rw [h1]
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (hcomm_e x₁ (Subgroup.subset_closure (by simp)))
    · rw [h2]
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (hcomm_e x₂ (Subgroup.subset_closure (by simp)))
    · rw [h3]
      exact Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hfix)
  have heC : e ∈ Subgroup.centralizer (wreathGrp x₁ x₂ lam : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hb)
  have hmem : e ∈ wreathGrp x₁ x₂ lam ⊓
      Subgroup.centralizer (wreathGrp x₁ x₂ lam : Set G) :=
    ⟨S4A.pt_base_le_wreath x₁ x₂ lam he, heC⟩
  rwa [(WreathRel.center_eq h.wreath).1] at hmem

theorem fzbs_lam_E_inv (h : Ctx t L S x₁ x₂ lam rho tau) {e : G} (he : e ∈ baseGrp x₁ x₂)
    (hinv : lam * e * lam⁻¹ = e⁻¹) :
    ∃ e' ∈ baseGrp x₁ x₂, e = e' * (lam * e' * lam⁻¹)⁻¹ := by
  obtain ⟨a, b, rfl⟩ := fzbs4a_mem_base_exists h he
  have hcomm : Commute x₁ x₂ := h.wreath.comm
  have hconj := fzbs4a_lam_conj_zpow h a b
  have heq : x₂ ^ a * x₁ ^ b = (x₁ ^ a * x₂ ^ b)⁻¹ := hconj.symm.trans hinv
  have hR : (x₁ ^ a * x₂ ^ b)⁻¹ = x₂ ^ (-b) * x₁ ^ (-a) := by
    rw [mul_inv_rev, ← zpow_neg x₂ b, ← zpow_neg x₁ a]
  have heq' : x₁ ^ b * x₂ ^ a = x₁ ^ (-a) * x₂ ^ (-b) := by
    calc x₁ ^ b * x₂ ^ a = x₂ ^ a * x₁ ^ b := (hcomm.zpow_zpow b a).eq
      _ = (x₁ ^ a * x₂ ^ b)⁻¹ := heq
      _ = x₂ ^ (-b) * x₁ ^ (-a) := hR
      _ = x₁ ^ (-a) * x₂ ^ (-b) := (hcomm.zpow_zpow (-a) (-b)).eq.symm
  have h3 : x₂ ^ a = x₁ ^ (-(a + b)) * x₂ ^ (-b) := by
    calc x₂ ^ a = x₁ ^ (-b) * (x₁ ^ b * x₂ ^ a) := by
          rw [← mul_assoc, ← zpow_add x₁ (-b) b, neg_add_cancel, zpow_zero, one_mul]
      _ = x₁ ^ (-b) * (x₁ ^ (-a) * x₂ ^ (-b)) := by rw [heq']
      _ = x₁ ^ (-(a + b)) * x₂ ^ (-b) := by
          rw [← mul_assoc, ← zpow_add x₁ (-b) (-a),
            show -b + -a = -(a + b) by ring]
  have h4 : x₂ ^ (a + b) = x₁ ^ (-(a + b)) := by
    calc x₂ ^ (a + b) = x₂ ^ a * x₂ ^ b := by rw [zpow_add]
      _ = (x₁ ^ (-(a + b)) * x₂ ^ (-b)) * x₂ ^ b := by rw [h3]
      _ = x₁ ^ (-(a + b)) * (x₂ ^ (-b) * x₂ ^ b) := by rw [mul_assoc]
      _ = x₁ ^ (-(a + b)) := by
          rw [← zpow_add x₂ (-b) b, neg_add_cancel, zpow_zero, mul_one]
  have hswap : x₁ ^ (a + b) = x₂ ^ (-(a + b)) := by
    calc x₁ ^ (a + b) = (x₁ ^ (-(a + b)))⁻¹ := by
          rw [zpow_neg x₁ (a + b), inv_inv]
      _ = (x₂ ^ (a + b))⁻¹ := by rw [h4]
      _ = x₂ ^ (-(a + b)) := by rw [zpow_neg x₂ (a + b)]
  have hx1ab : x₁ ^ (a + b) = 1 := by
    have hmem : x₁ ^ (a + b) ∈ zpowers x₁ ⊓ zpowers x₂ :=
      ⟨Subgroup.zpow_mem _ (Subgroup.mem_zpowers x₁) (a + b),
        by rw [hswap]; exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x₂) (-(a + b))⟩
    rwa [h.wreath.inf_eq_bot, Subgroup.mem_bot] at hmem
  have hx2sum : x₂ ^ (a + b) = 1 := by
    have h1 : x₂ ^ (-(a + b)) = 1 := by rw [← hswap, hx1ab]
    calc x₂ ^ (a + b) = (x₂ ^ (-(a + b)))⁻¹ := by
          rw [zpow_neg x₂ (a + b), inv_inv]
      _ = 1 := by rw [h1, inv_one]
  have hx2 : x₂ ^ a = x₂ ^ (-b) := by
    calc x₂ ^ a = x₂ ^ (a + b) * x₂ ^ (-b) := by
          rw [← zpow_add x₂ (a + b) (-b), show (a + b) + (-b) = a by ring]
      _ = 1 * x₂ ^ (-b) := by rw [hx2sum]
      _ = x₂ ^ (-b) := one_mul _
  have hx1E : x₁ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  refine ⟨x₁ ^ a, Subgroup.zpow_mem (baseGrp x₁ x₂) hx1E a, ?_⟩
  have hconj_a : lam * x₁ ^ a * lam⁻¹ = x₂ ^ a := by
    rw [← conj_zpow (a := lam) (b := x₁) (i := a), h.wreath.conj_x₁]
  rw [hconj_a, hx2, zpow_neg x₂ b, inv_inv]

theorem fzbs_lam_X_inv (h : Ctx t L S x₁ x₂ lam rho tau) {x : G} (hx : x ∈ fzbsX t x₁ x₂)
    (hinv : lam * x * lam⁻¹ = x⁻¹) :
    ∃ e ∈ baseGrp x₁ x₂, x = e * (lam * e * lam⁻¹)⁻¹ ∨
      x = t * (e * (lam * e * lam⁻¹)⁻¹) := by
  have hcommXt : ∀ a ∈ zpowers t, ∀ b ∈ baseGrp x₁ x₂, a * b = b * a :=
    fun a ha b hb => S4A.pt_comm_base h.toCtx0 a
      (Subgroup.zpowers_le.mpr h.hyp.mem_twoCore ha) b hb
  obtain ⟨p, hp, e, he, hxpe⟩ := (mem_sup_iff_of_commute hcommXt).mp hx
  have hlt : lam * t * lam⁻¹ = t := (fzl_lam_Z h).2.1
  have hte : t * e = e * t :=
    ((fzl_t_facts h).2.2.1 e (Subgroup.mem_sup_right he)).symm
  rcases S4A.pt_eq_one_or_of_mem_zpowers h.hyp.ord_t hp with h1 | h1
  · rw [hxpe, h1, one_mul] at hinv ⊢
    obtain ⟨e', he', heq'⟩ := fzbs_lam_E_inv h he hinv
    exact ⟨e', he', Or.inl heq'⟩
  · rw [hxpe, h1] at hinv ⊢
    have hL : lam * (t * e) * lam⁻¹ = t * (lam * e * lam⁻¹) := by
      calc lam * (t * e) * lam⁻¹ = (lam * t * lam⁻¹) * (lam * e * lam⁻¹) := by group
        _ = t * (lam * e * lam⁻¹) := by rw [hlt]
    have hR : (t * e)⁻¹ = t * e⁻¹ := by
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (S4A.t_mul_self h.hyp)]
      exact (show Commute t e from hte).inv_right.eq.symm
    have hei : lam * e * lam⁻¹ = e⁻¹ := by
      have h2 : t * (lam * e * lam⁻¹) = t * e⁻¹ := by
        rw [← hL, ← hR]; exact hinv
      exact mul_left_cancel h2
    obtain ⟨e', he', heq'⟩ := fzbs_lam_E_inv h he hei
    exact ⟨e', he', Or.inr (by rw [heq'])⟩

end CFSG.OddStandard.SmallF3.FritzII
