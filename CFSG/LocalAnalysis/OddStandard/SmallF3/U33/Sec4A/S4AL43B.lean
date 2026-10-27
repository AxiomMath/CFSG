module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC0A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC0C
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.WreathB

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private lemma ctxW_mul_comm (h : Ctx t L S x₁ x₂ lam rho tau) {a b : G}
    (ha : a ∈ ctxW t x₁ x₂) (hb : b ∈ ctxW t x₁ x₂) : a * b = b * a := by
  haveI : IsMulCommutative (ctxW t x₁ x₂) := h.toCtx0.abelian_W
  exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥(ctxW t x₁ x₂)) ⟨b, hb⟩)

private lemma lam_mem_S (h : Ctx t L S x₁ x₂ lam rho tau) : lam ∈ S := by
  have hmem : lam ∈ S ⊓ L := by
    rw [h.toCtx0.inf_eq]
    exact Subgroup.subset_closure (by simp)
  exact hmem.1

private lemma x₁_mem_S (h : Ctx t L S x₁ x₂ lam rho tau) : x₁ ∈ S := by
  have hmem : x₁ ∈ S ⊓ L := by
    rw [h.toCtx0.inf_eq]
    exact Subgroup.subset_closure (by simp)
  exact hmem.1

private lemma lam_tau_zpow_mul (h : Ctx t L S x₁ x₂ lam rho tau) (a b c d : ℤ) :
    lam ^ a * tau ^ b * (lam ^ c * tau ^ d) = lam ^ (a + c) * tau ^ (b + d) := by
  have hcomm : Commute lam tau := h.tau_lam.symm
  calc lam ^ a * tau ^ b * (lam ^ c * tau ^ d)
      = lam ^ a * (tau ^ b * lam ^ c) * tau ^ d := by group
    _ = lam ^ a * (lam ^ c * tau ^ b) * tau ^ d := by rw [(hcomm.symm.zpow_zpow b c).eq]
    _ = lam ^ a * lam ^ c * tau ^ b * tau ^ d := by group
    _ = lam ^ (a + c) * tau ^ (b + d) := by rw [← zpow_add, mul_assoc, ← zpow_add]

private lemma commutatorElement_eq_mul_mul_inv (a b : G) : ⁅a, b⁆ = a * b * (b * a)⁻¹ := by
  rw [commutatorElement_def]
  group

private lemma mem_S_iff_zpow_form (h : Ctx t L S x₁ x₂ lam rho tau) {s : G} (hs : s ∈ S) :
    ∃ w ∈ ctxW t x₁ x₂, ∃ a b : ℤ, s = w * lam ^ a * tau ^ b := by
  have hlamS : lam ∈ S := lam_mem_S h
  have hx₁W : x₁ ∈ ctxW t x₁ x₂ :=
    Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have hx₂W : x₂ ∈ ctxW t x₁ x₂ :=
    Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have hPleW : twoCore t ≤ ctxW t x₁ x₂ := le_sup_left
  have hcomm : Commute lam tau := h.tau_lam.symm
  let K : Subgroup G :=
    { carrier := {s : G | ∃ w ∈ ctxW t x₁ x₂, ∃ a b : ℤ, s = w * lam ^ a * tau ^ b}
      one_mem' := ⟨1, (ctxW t x₁ x₂).one_mem, 0, 0, by simp⟩
      mul_mem' := by
        rintro s₁ s₂ ⟨w₁, hw₁, a, b, rfl⟩ ⟨w₂, hw₂, c, d, rfl⟩
        have huS : lam ^ a * tau ^ b ∈ S :=
          S.mul_mem (S.zpow_mem hlamS a) (S.zpow_mem h.tau_mem b)
        have hwu : (lam ^ a * tau ^ b) * w₂ * (lam ^ a * tau ^ b)⁻¹ ∈ ctxW t x₁ x₂ :=
          h.normal_W.2 _ huS w₂ hw₂
        refine ⟨w₁ * ((lam ^ a * tau ^ b) * w₂ * (lam ^ a * tau ^ b)⁻¹),
          (ctxW t x₁ x₂).mul_mem hw₁ hwu, a + c, b + d, ?_⟩
        rw [show w₁ * ((lam ^ a * tau ^ b) * w₂ * (lam ^ a * tau ^ b)⁻¹) * lam ^ (a + c)
              * tau ^ (b + d)
              = w₁ * ((lam ^ a * tau ^ b) * w₂ * (lam ^ a * tau ^ b)⁻¹)
                * (lam ^ (a + c) * tau ^ (b + d)) by group,
          (lam_tau_zpow_mul h a b c d).symm]
        group
      inv_mem' := by
        rintro s ⟨w, hw, a, b, rfl⟩
        have huS : lam ^ a * tau ^ b ∈ S :=
          S.mul_mem (S.zpow_mem hlamS a) (S.zpow_mem h.tau_mem b)
        have hwu : (lam ^ a * tau ^ b)⁻¹ * w⁻¹ * (lam ^ a * tau ^ b) ∈ ctxW t x₁ x₂ := by
          simpa only [inv_inv] using
            h.normal_W.2 _ (S.inv_mem huS) w⁻¹ ((ctxW t x₁ x₂).inv_mem hw)
        refine ⟨(lam ^ a * tau ^ b)⁻¹ * w⁻¹ * (lam ^ a * tau ^ b), hwu, -a, -b, ?_⟩
        have hu_inv : (lam ^ a * tau ^ b)⁻¹ = lam ^ (-a) * tau ^ (-b) := by
          rw [mul_inv_rev, ← zpow_neg, ← zpow_neg]
          exact (hcomm.symm.zpow_zpow (-b) (-a)).eq
        have hLT : (lam ^ a * tau ^ b) * lam ^ (-a) * tau ^ (-b) = 1 := by
          rw [show (lam ^ a * tau ^ b) * lam ^ (-a) * tau ^ (-b)
                = (lam ^ a * tau ^ b) * (lam ^ (-a) * tau ^ (-b)) by group,
            lam_tau_zpow_mul h a b (-a) (-b), add_neg_cancel, add_neg_cancel,
            zpow_zero, zpow_zero, mul_one]
        rw [hu_inv]
        rw [show (w * lam ^ a * tau ^ b)⁻¹ = (lam ^ a * tau ^ b)⁻¹ * w⁻¹ by group]
        rw [hu_inv]
        rw [show ((lam ^ (-a) * tau ^ (-b)) * w⁻¹ * (lam ^ a * tau ^ b)) * lam ^ (-a)
              * tau ^ (-b)
              = (lam ^ (-a) * tau ^ (-b)) * w⁻¹
                * ((lam ^ a * tau ^ b) * lam ^ (-a) * tau ^ (-b)) by group]
        rw [hLT, mul_one] }
  have hWK : ctxW t x₁ x₂ ≤ K := fun w hw => ⟨w, hw, 0, 0, by simp⟩
  have hx₁K : x₁ ∈ K := ⟨x₁, hx₁W, 0, 0, by simp⟩
  have hx₂K : x₂ ∈ K := ⟨x₂, hx₂W, 0, 0, by simp⟩
  have hlamK : lam ∈ K := ⟨1, (ctxW t x₁ x₂).one_mem, 1, 0, by simp⟩
  have htauK : tau ∈ K := ⟨1, (ctxW t x₁ x₂).one_mem, 0, 1, by simp⟩
  have hm12K : m12Grp x₁ x₂ lam tau ≤ K := by
    rw [m12Grp, Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact hx₁K
    · exact hx₂K
    · exact hlamK
    · exact htauK
  have hSK : S ≤ K := by
    rw [h.S_eq]
    exact sup_le (le_trans hPleW hWK) hm12K
  exact hSK hs

theorem exists_coset_form (h : Ctx t L S x₁ x₂ lam rho tau) {s : G} (hs : s ∈ S) :
    ∃ w ∈ ctxW t x₁ x₂, s = w ∨ s = w * lam ∨ s = w * tau ∨ s = w * (lam * tau) := by
  obtain ⟨w, hw, a, b, hsab⟩ := mem_S_iff_zpow_form h hs
  have hlam2 : lam ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, ← h.wreath.ord_lam]
    exact pow_orderOf_eq_one lam
  have hlam_a : lam ^ a = 1 ∨ lam ^ a = lam := by
    have h1 : lam ^ a = lam ^ (a % 2) := by
      conv_lhs => rw [← Int.mul_ediv_add_emod a 2]
      rw [zpow_add, zpow_mul, hlam2, one_zpow, one_mul]
    rcases Int.emod_two_eq_zero_or_one a with h2 | h2
    · left; rw [h1, h2, zpow_zero]
    · right; rw [h1, h2, zpow_one]
  have htau2W : tau ^ (2 : ℤ) ∈ ctxW t x₁ x₂ := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast]
    exact Subgroup.mem_sup_left h.tau_sq_mem
  have htau_b : ∃ w_t ∈ ctxW t x₁ x₂, tau ^ b = w_t ∨ tau ^ b = w_t * tau := by
    refine ⟨(tau ^ (2 : ℤ)) ^ (b / 2), (ctxW t x₁ x₂).zpow_mem htau2W (b / 2), ?_⟩
    have h1 : tau ^ b = (tau ^ (2 : ℤ)) ^ (b / 2) * tau ^ (b % 2) := by
      conv_lhs => rw [← Int.mul_ediv_add_emod b 2]
      rw [zpow_add, zpow_mul]
    rcases Int.emod_two_eq_zero_or_one b with h2 | h2
    · left; rw [h1, h2, zpow_zero, mul_one]
    · right; rw [h1, h2, zpow_one]
  rcases hlam_a with hla | hla <;> rcases htau_b with ⟨w_t, hwt, htb | htb⟩
  · refine ⟨w * w_t, (ctxW t x₁ x₂).mul_mem hw hwt, Or.inl ?_⟩
    rw [hsab, hla, htb]; group
  · refine ⟨w * w_t, (ctxW t x₁ x₂).mul_mem hw hwt, Or.inr (Or.inr (Or.inl ?_))⟩
    rw [hsab, hla, htb]; group
  · refine ⟨w * (lam * w_t * lam⁻¹),
      (ctxW t x₁ x₂).mul_mem hw (h.normal_W.2 lam (lam_mem_S h) w_t hwt), Or.inr (Or.inl ?_)⟩
    rw [hsab, hla, htb]; group
  · refine ⟨w * (lam * w_t * lam⁻¹),
      (ctxW t x₁ x₂).mul_mem hw (h.normal_W.2 lam (lam_mem_S h) w_t hwt),
      Or.inr (Or.inr (Or.inr ?_))⟩
    rw [hsab, hla, htb]; group

theorem commutator_le_ctxW (h : Ctx t L S x₁ x₂ lam rho tau) : ⁅S, S⁆ ≤ ctxW t x₁ x₂ := by
  rw [Subgroup.commutator_le]
  intro s₁ hs₁ s₂ hs₂
  obtain ⟨w₁, hw₁, a₁, b₁, rfl⟩ := mem_S_iff_zpow_form h hs₁
  obtain ⟨w₂, hw₂, a₂, b₂, rfl⟩ := mem_S_iff_zpow_form h hs₂
  have hlamS : lam ∈ S := lam_mem_S h
  have hu₁S : lam ^ a₁ * tau ^ b₁ ∈ S :=
    S.mul_mem (S.zpow_mem hlamS a₁) (S.zpow_mem h.tau_mem b₁)
  have hu₂S : lam ^ a₂ * tau ^ b₂ ∈ S :=
    S.mul_mem (S.zpow_mem hlamS a₂) (S.zpow_mem h.tau_mem b₂)
  have hA : w₁ * ((lam ^ a₁ * tau ^ b₁) * w₂ * (lam ^ a₁ * tau ^ b₁)⁻¹) ∈ ctxW t x₁ x₂ :=
    (ctxW t x₁ x₂).mul_mem hw₁ (h.normal_W.2 _ hu₁S w₂ hw₂)
  have hB : w₂ * ((lam ^ a₂ * tau ^ b₂) * w₁ * (lam ^ a₂ * tau ^ b₂)⁻¹) ∈ ctxW t x₁ x₂ :=
    (ctxW t x₁ x₂).mul_mem hw₂ (h.normal_W.2 _ hu₂S w₁ hw₁)
  have hκ : (lam ^ a₁ * tau ^ b₁) * (lam ^ a₂ * tau ^ b₂) =
      lam ^ (a₁ + a₂) * tau ^ (b₁ + b₂) := lam_tau_zpow_mul h a₁ b₁ a₂ b₂
  have hκ' : (lam ^ a₂ * tau ^ b₂) * (lam ^ a₁ * tau ^ b₁) =
      lam ^ (a₁ + a₂) * tau ^ (b₁ + b₂) := by
    rw [lam_tau_zpow_mul h a₂ b₂ a₁ b₁, Int.add_comm a₂ a₁, Int.add_comm b₂ b₁]
  have hs₁s₂ : w₁ * lam ^ a₁ * tau ^ b₁ * (w₂ * lam ^ a₂ * tau ^ b₂) =
      (w₁ * ((lam ^ a₁ * tau ^ b₁) * w₂ * (lam ^ a₁ * tau ^ b₁)⁻¹)) *
        (lam ^ (a₁ + a₂) * tau ^ (b₁ + b₂)) := by
    rw [← hκ]; group
  have hs₂s₁ : w₂ * lam ^ a₂ * tau ^ b₂ * (w₁ * lam ^ a₁ * tau ^ b₁) =
      (w₂ * ((lam ^ a₂ * tau ^ b₂) * w₁ * (lam ^ a₂ * tau ^ b₂)⁻¹)) *
        (lam ^ (a₁ + a₂) * tau ^ (b₁ + b₂)) := by
    rw [← hκ']; group
  rw [commutatorElement_eq_mul_mul_inv, hs₁s₂, hs₂s₁]
  have heq : ((w₁ * ((lam ^ a₁ * tau ^ b₁) * w₂ * (lam ^ a₁ * tau ^ b₁)⁻¹)) *
        (lam ^ (a₁ + a₂) * tau ^ (b₁ + b₂))) *
      ((w₂ * ((lam ^ a₂ * tau ^ b₂) * w₁ * (lam ^ a₂ * tau ^ b₂)⁻¹)) *
        (lam ^ (a₁ + a₂) * tau ^ (b₁ + b₂)))⁻¹ =
      (w₁ * ((lam ^ a₁ * tau ^ b₁) * w₂ * (lam ^ a₁ * tau ^ b₁)⁻¹)) *
        (w₂ * ((lam ^ a₂ * tau ^ b₂) * w₁ * (lam ^ a₂ * tau ^ b₂)⁻¹))⁻¹ := by
    group
  rw [heq]
  exact (ctxW t x₁ x₂).mul_mem hA ((ctxW t x₁ x₂).inv_mem hB)

theorem sq_x₁_mem_commutator (h : Ctx t L S x₁ x₂ lam rho tau) : x₁ ^ 2 ∈ ⁅S, S⁆ := by
  have hmem : ⁅tau, x₁⁆ ∈ ⁅S, S⁆ :=
    Subgroup.commutator_mem_commutator h.tau_mem (x₁_mem_S h)
  have heq : ⁅tau, x₁⁆ = x₁ ^ 2 := by
    rw [commutatorElement_def, h.tau_x₁]
    rw [← mul_inv_rev, ← pow_two, inv_eq_of_mul_eq_one_right (y_mul_self_ne_one h.wreath).1]
  rwa [heq] at hmem

theorem x₁_mul_x₂_mem_commutator (h : Ctx t L S x₁ x₂ lam rho tau) :
    x₁ * x₂ ∈ ⁅S, S⁆ := by
  have hmem1 : ⁅lam, x₁⁆ ∈ ⁅S, S⁆ :=
    Subgroup.commutator_mem_commutator (lam_mem_S h) (x₁_mem_S h)
  have hmem2 : x₁ ^ 2 ∈ ⁅S, S⁆ := sq_x₁_mem_commutator h
  have heq : ⁅lam, x₁⁆ * x₁ ^ 2 = x₁ * x₂ := by
    rw [commutatorElement_def, h.wreath.conj_x₁]
    calc x₂ * x₁⁻¹ * x₁ ^ 2 = x₂ * x₁ := by group
      _ = x₁ * x₂ := h.wreath.comm.symm
  rw [← heq]
  exact (⁅S, S⁆).mul_mem hmem1 hmem2

private lemma false_of_coset_y (h : Ctx t L S x₁ x₂ lam rho tau) {w k : G}
    (hw : w ∈ ctxW t x₁ x₂) (hkS : k ∈ S)
    (hc : ∀ s ∈ ⁅S, S⁆, (w * k) * s = s * (w * k))
    (hky : k * x₁ ^ 2 * k⁻¹ = x₁ ^ 2 * (x₁ * x₂) ^ 2) : False := by
  have hyW : x₁ ^ 2 ∈ ctxW t x₁ x₂ :=
    (ctxW t x₁ x₂).pow_mem (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))) 2
  have hy_comm : x₁ ^ 2 ∈ ⁅S, S⁆ := sq_x₁_mem_commutator h
  have hgy : (w * k) * x₁ ^ 2 * (w * k)⁻¹ = x₁ ^ 2 := by
    rw [hc (x₁ ^ 2) hy_comm]; group
  have hkyW : k * x₁ ^ 2 * k⁻¹ ∈ ctxW t x₁ x₂ := h.normal_W.2 k hkS (x₁ ^ 2) hyW
  have hgy' : (w * k) * x₁ ^ 2 * (w * k)⁻¹ = k * x₁ ^ 2 * k⁻¹ := by
    calc (w * k) * x₁ ^ 2 * (w * k)⁻¹
        = w * (k * x₁ ^ 2 * k⁻¹) * w⁻¹ := by group
      _ = (k * x₁ ^ 2 * k⁻¹) * w * w⁻¹ := by rw [ctxW_mul_comm h hw hkyW]
      _ = k * x₁ ^ 2 * k⁻¹ := by group
  have hky_eq : k * x₁ ^ 2 * k⁻¹ = x₁ ^ 2 := hgy'.symm.trans hgy
  have hz1 : (x₁ * x₂) ^ 2 = 1 := by
    have h1 : x₁ ^ 2 * (x₁ * x₂) ^ 2 = x₁ ^ 2 := by rw [← hky, hky_eq]
    exact mul_left_cancel (by rw [h1, mul_one])
  exact (z_mul_self_ne_one h.toCtx0).2 hz1

private lemma false_of_coset_tau (h : Ctx t L S x₁ x₂ lam rho tau) {w k : G}
    (hw : w ∈ ctxW t x₁ x₂) (hkS : k ∈ S)
    (hc : ∀ s ∈ ⁅S, S⁆, (w * k) * s = s * (w * k))
    (hkxy : k * (x₁ * x₂) * k⁻¹ = (x₁ * x₂)⁻¹) : False := by
  have hxyW : x₁ * x₂ ∈ ctxW t x₁ x₂ :=
    (ctxW t x₁ x₂).mul_mem (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))
      (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))
  have hxy_comm : x₁ * x₂ ∈ ⁅S, S⁆ := x₁_mul_x₂_mem_commutator h
  have hgy : (w * k) * (x₁ * x₂) * (w * k)⁻¹ = x₁ * x₂ := by
    rw [hc (x₁ * x₂) hxy_comm]; group
  have hkxyW : k * (x₁ * x₂) * k⁻¹ ∈ ctxW t x₁ x₂ := h.normal_W.2 k hkS (x₁ * x₂) hxyW
  have hgy' : (w * k) * (x₁ * x₂) * (w * k)⁻¹ = k * (x₁ * x₂) * k⁻¹ := by
    calc (w * k) * (x₁ * x₂) * (w * k)⁻¹
        = w * (k * (x₁ * x₂) * k⁻¹) * w⁻¹ := by group
      _ = (k * (x₁ * x₂) * k⁻¹) * w * w⁻¹ := by rw [ctxW_mul_comm h hw hkxyW]
      _ = k * (x₁ * x₂) * k⁻¹ := by group
  have hkxy_eq : k * (x₁ * x₂) * k⁻¹ = x₁ * x₂ := hgy'.symm.trans hgy
  have hinv : (x₁ * x₂)⁻¹ = x₁ * x₂ := by rw [← hkxy, hkxy_eq]
  have hz1 : (x₁ * x₂) ^ 2 = 1 := by
    calc (x₁ * x₂) ^ 2 = (x₁ * x₂) * (x₁ * x₂) := by rw [pow_two]
      _ = (x₁ * x₂) * (x₁ * x₂)⁻¹ := by rw [hinv]
      _ = 1 := mul_inv_cancel _
  exact (z_mul_self_ne_one h.toCtx0).2 hz1

theorem mem_ctxW_of_commute_commutator (h : Ctx t L S x₁ x₂ lam rho tau) {g : G} (hg : g ∈ S)
    (hc : ∀ s ∈ ⁅S, S⁆, g * s = s * g) : g ∈ ctxW t x₁ x₂ := by
  obtain ⟨w, hw, hgform⟩ := exists_coset_form h hg
  have hlam_y : lam * x₁ ^ 2 * lam⁻¹ = x₁ ^ 2 * (x₁ * x₂) ^ 2 := by
    rw [← conj_pow (a := lam) (b := x₁) (i := 2), h.wreath.conj_x₁, WreathRel.x₂_sq h.wreath]
  have htau_xy : tau * (x₁ * x₂) * tau⁻¹ = (x₁ * x₂)⁻¹ := by
    calc tau * (x₁ * x₂) * tau⁻¹
        = (tau * x₁ * tau⁻¹) * (tau * x₂ * tau⁻¹) := by group
      _ = x₁⁻¹ * x₂⁻¹ := by rw [h.tau_x₁, h.tau_x₂]
      _ = (x₂ * x₁)⁻¹ := by rw [mul_inv_rev]
      _ = (x₁ * x₂)⁻¹ := by rw [h.wreath.comm]
  have hlt_y : (lam * tau) * x₁ ^ 2 * (lam * tau)⁻¹ = x₁ ^ 2 * (x₁ * x₂) ^ 2 := by
    have hty : tau * x₁ ^ 2 * tau⁻¹ = x₁ ^ 2 := by
      rw [tau_commute_y h, mul_assoc, mul_inv_cancel, mul_one]
    calc (lam * tau) * x₁ ^ 2 * (lam * tau)⁻¹
        = lam * (tau * x₁ ^ 2 * tau⁻¹) * lam⁻¹ := by group
      _ = lam * x₁ ^ 2 * lam⁻¹ := by rw [hty]
      _ = x₁ ^ 2 * (x₁ * x₂) ^ 2 := hlam_y
  rcases hgform with hg | hg | hg | hg
  · rw [hg]; exact hw
  · exfalso
    exact false_of_coset_y h hw (lam_mem_S h) (fun s hs => by rw [← hg]; exact hc s hs) hlam_y
  · exfalso
    exact false_of_coset_tau h hw h.tau_mem (fun s hs => by rw [← hg]; exact hc s hs) htau_xy
  · exfalso
    exact false_of_coset_y h hw (S.mul_mem (lam_mem_S h) h.tau_mem)
      (fun s hs => by rw [← hg]; exact hc s hs) hlt_y

theorem conj_mem_ctxW_of_mem_normalizer (h : Ctx t L S x₁ x₂ lam rho tau) {n : G}
    (hn : n ∈ normalizer (S : Set G)) {w : G} (hw : w ∈ ctxW t x₁ x₂) :
    n * w * n⁻¹ ∈ ctxW t x₁ x₂ := by
  have hwS : w ∈ S := h.normal_W.1 hw
  have hgS : n * w * n⁻¹ ∈ S := (Subgroup.mem_set_normalizer_iff.mp hn w).mp hwS
  refine mem_ctxW_of_commute_commutator h hgS ?_
  intro s hs
  have hninv : n⁻¹ ∈ normalizer (S : Set G) := (normalizer (S : Set G)).inv_mem hn
  have hmapS : S.map (MulAut.conj n⁻¹).toMonoidHom = S := by
    simpa using (Subgroup.mem_normalizer_iff_map_conj_eq (H := S)).mp hninv
  have hs' : n⁻¹ * s * n ∈ ⁅S, S⁆ := by
    have hmap := Subgroup.map_commutator (f := (MulAut.conj n⁻¹).toMonoidHom) (H₁ := S) (H₂ := S)
    rw [hmapS] at hmap
    rw [← hmap]
    exact Subgroup.mem_map.mpr ⟨s, hs, by simp [MulAut.conj_apply]⟩
  have hs'W : n⁻¹ * s * n ∈ ctxW t x₁ x₂ := commutator_le_ctxW h hs'
  have hcomm : w * (n⁻¹ * s * n) = (n⁻¹ * s * n) * w := ctxW_mul_comm h hw hs'W
  calc (n * w * n⁻¹) * s = n * (w * (n⁻¹ * s * n)) * n⁻¹ := by group
    _ = n * ((n⁻¹ * s * n) * w) * n⁻¹ := by rw [hcomm]
    _ = s * (n * w * n⁻¹) := by group

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
