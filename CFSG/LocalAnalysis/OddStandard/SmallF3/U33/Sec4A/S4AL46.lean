module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AConcl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AProd
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Lemma31Elem
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.WreathB
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private theorem t_commute_of_mem_S (h : Ctx t L S x₁ x₂ lam rho tau) {g : G} (hg : g ∈ S) :
    t * g = g * t :=
  (mem_invCent_iff.mp (h.le_invCent hg)).symm

private theorem t_mem_S_of (h : Ctx t L S x₁ x₂ lam rho tau) : t ∈ S := by
  rw [h.S_eq]
  exact Subgroup.mem_sup_left h.hyp.mem_twoCore

private theorem zpowers_t_le_S_of (h : Ctx t L S x₁ x₂ lam rho tau) : zpowers t ≤ S :=
  Subgroup.zpowers_le.mpr (t_mem_S_of h)

private theorem zpowers_t_eq_one_or_t (h : Ctx t L S x₁ x₂ lam rho tau) {p : G}
    (hp : p ∈ zpowers t) : p = 1 ∨ p = t := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hp
  have ht : t * t = 1 := t_mul_self h.hyp
  have ht2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two, ht]
  rcases Int.even_or_odd' k with ⟨m, hm | hm⟩
  · left
    rw [← hk, hm, zpow_mul, ht2, one_zpow]
  · right
    rw [← hk, hm, zpow_add, zpow_mul, ht2, one_zpow, one_mul, zpow_one]

private theorem zpowers_t_commute_S (h : Ctx t L S x₁ x₂ lam rho tau) {p : G}
    (hp : p ∈ zpowers t) {g : G} (hg : g ∈ S) : p * g = g * p := by
  have hc : Commute t g := t_commute_of_mem_S h hg
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hp
  rw [← hk]
  exact hc.zpow_left k

private theorem t_not_mem_m12Grp_of (h : Ctx t L S x₁ x₂ lam rho tau)
    (h43 : twoCore t = zpowers t) (h44 : tau ^ 2 = 1) :
    t ∉ m12Grp x₁ x₂ lam tau := by
  intro htM
  have hmem : t ∈ zpowers t ⊓ m12Grp x₁ x₂ lam tau :=
    ⟨Subgroup.mem_zpowers t, htM⟩
  rw [(S_eq_prod_of h h43 h44).2] at hmem
  exact t_ne_one h.hyp (Subgroup.mem_bot.mp hmem)

private theorem fourGrp_le_m12Grp' : fourGrp x₁ x₂ ≤ m12Grp x₁ x₂ lam tau := by
  rw [fourGrp, m12Grp, Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · exact pow_mem (Subgroup.subset_closure (by simp)) 2
  · exact pow_mem (mul_mem (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))) 2

private theorem x1x2_pow_four_of (h : Ctx t L S x₁ x₂ lam rho tau) :
    (x₁ * x₂) ^ 4 = 1 := by
  have hc : Commute x₁ x₂ := h.wreath.comm
  have h4₁ : x₁ ^ 4 = 1 := by
    have := pow_orderOf_eq_one x₁
    rwa [h.wreath.ord_x₁] at this
  have h4₂ : x₂ ^ 4 = 1 := by
    have := pow_orderOf_eq_one x₂
    rwa [h.wreath.ord_x₂] at this
  rw [hc.mul_pow, h4₁, h4₂, mul_one]

private theorem tau_conj_x1x2_of (h : Ctx t L S x₁ x₂ lam rho tau) :
    tau * (x₁ * x₂) * tau⁻¹ = (x₁ * x₂)⁻¹ := by
  have hcomm_inv : x₁⁻¹ * x₂⁻¹ = (x₁ * x₂)⁻¹ := by
    have := congrArg Inv.inv h.wreath.comm.symm
    simpa [mul_inv_rev] using this
  calc tau * (x₁ * x₂) * tau⁻¹
      = (tau * x₁ * tau⁻¹) * (tau * x₂ * tau⁻¹) := by group
    _ = x₁⁻¹ * x₂⁻¹ := by rw [h.tau_x₁, h.tau_x₂]
    _ = (x₁ * x₂)⁻¹ := hcomm_inv

private theorem tau_mul_x1x2_eq_of (h : Ctx t L S x₁ x₂ lam rho tau) :
    tau * (x₁ * x₂) = (x₁ * x₂) ^ 2 * (x₁ * x₂ * tau) := by
  have h4 : (x₁ * x₂) ^ 4 = 1 := x1x2_pow_four_of h
  have hconj : tau * (x₁ * x₂) * tau⁻¹ = (x₁ * x₂)⁻¹ := tau_conj_x1x2_of h
  have hta : tau * (x₁ * x₂) = (x₁ * x₂)⁻¹ * tau := by
    calc tau * (x₁ * x₂) = tau * (x₁ * x₂) * tau⁻¹ * tau := by group
      _ = (x₁ * x₂)⁻¹ * tau := by rw [hconj]
  have hinv : (x₁ * x₂)⁻¹ = (x₁ * x₂) ^ 3 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ']
    exact h4
  calc tau * (x₁ * x₂)
      = (x₁ * x₂)⁻¹ * tau := hta
    _ = (x₁ * x₂) ^ 3 * tau := by rw [hinv]
    _ = (x₁ * x₂) ^ 2 * (x₁ * x₂ * tau) := by
          rw [show (x₁ * x₂) ^ 3 = (x₁ * x₂) ^ 2 * (x₁ * x₂) from by
                simpa using pow_succ (x₁ * x₂) 2]
          rw [mul_assoc]

private theorem t_tau_mul_x1x2_eq_of (h : Ctx t L S x₁ x₂ lam rho tau) :
    t * tau * (x₁ * x₂) = (x₁ * x₂) ^ 2 * (t * (x₁ * x₂ * tau)) := by
  have h4 : (x₁ * x₂) ^ 4 = 1 := x1x2_pow_four_of h
  have hconj : tau * (x₁ * x₂) * tau⁻¹ = (x₁ * x₂)⁻¹ := tau_conj_x1x2_of h
  have hta : tau * (x₁ * x₂) = (x₁ * x₂)⁻¹ * tau := by
    calc tau * (x₁ * x₂) = tau * (x₁ * x₂) * tau⁻¹ * tau := by group
      _ = (x₁ * x₂)⁻¹ * tau := by rw [hconj]
  have hinv : (x₁ * x₂)⁻¹ = (x₁ * x₂) ^ 3 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ']
    exact h4
  have hx1x2M : x₁ * x₂ ∈ m12Grp x₁ x₂ lam tau :=
    Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))
  have htc : t * (x₁ * x₂) = (x₁ * x₂) * t :=
    t_commute_of_mem_S h (m12Grp_le_S h hx1x2M)
  have htc_inv : t * (x₁ * x₂)⁻¹ = (x₁ * x₂)⁻¹ * t :=
    (show Commute t (x₁ * x₂) from htc).inv_right
  calc t * tau * (x₁ * x₂)
      = t * (tau * (x₁ * x₂)) := by rw [mul_assoc]
    _ = t * ((x₁ * x₂)⁻¹ * tau) := by rw [hta]
    _ = (x₁ * x₂)⁻¹ * (t * tau) := by
          conv_lhs => rw [← mul_assoc]
          rw [htc_inv, mul_assoc]
    _ = (x₁ * x₂) ^ 2 * (t * (x₁ * x₂ * tau)) := by
          rw [hinv]
          rw [show t * (x₁ * x₂ * tau) = (x₁ * x₂) * (t * tau) by
            calc t * (x₁ * x₂ * tau) = (t * (x₁ * x₂)) * tau :=
                  (mul_assoc t (x₁ * x₂) tau).symm
              _ = ((x₁ * x₂) * t) * tau := by rw [htc]
              _ = (x₁ * x₂) * (t * tau) := mul_assoc (x₁ * x₂) t tau]
          rw [show (x₁ * x₂) ^ 3 = (x₁ * x₂) ^ 2 * (x₁ * x₂) from by
                simpa using pow_succ (x₁ * x₂) 2]
          rw [mul_assoc]

private theorem closure_insert_eq_fourGrp_sup (e : G) :
    closure ({x₁ ^ 2, (x₁ * x₂) ^ 2, e} : Set G) = fourGrp x₁ x₂ ⊔ zpowers e := by
  rw [fourGrp, Subgroup.zpowers_eq_closure e, ← Subgroup.closure_union]
  congr 1
  ext g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
  tauto

private theorem closure_three_congr (e u : G) (hu : u ∈ fourGrp x₁ x₂) :
    closure ({x₁ ^ 2, (x₁ * x₂) ^ 2, u * e} : Set G) =
      closure ({x₁ ^ 2, (x₁ * x₂) ^ 2, e} : Set G) := by
  rw [closure_insert_eq_fourGrp_sup (u * e), closure_insert_eq_fourGrp_sup e]
  refine le_antisymm ?_ ?_
  · refine sup_le le_sup_left ?_
    rw [Subgroup.zpowers_le]
    exact Subgroup.mul_mem_sup hu (Subgroup.mem_zpowers e)
  · refine sup_le le_sup_left ?_
    rw [Subgroup.zpowers_le]
    have h := Subgroup.mul_mem_sup (Subgroup.inv_mem (fourGrp x₁ x₂) hu)
      (Subgroup.mem_zpowers (u * e))
    rwa [inv_mul_cancel_left] at h

private theorem closure_tau_mul_x1x2_of (h : Ctx t L S x₁ x₂ lam rho tau) :
    closure ({x₁ ^ 2, (x₁ * x₂) ^ 2, tau * (x₁ * x₂)} : Set G) =
      closure ({x₁ ^ 2, (x₁ * x₂) ^ 2, x₁ * x₂ * tau} : Set G) := by
  have hz : (x₁ * x₂) ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hh := closure_three_congr (x₁ * x₂ * tau) ((x₁ * x₂) ^ 2) hz
  rwa [← tau_mul_x1x2_eq_of h] at hh

private theorem closure_t_tau_mul_x1x2_of (h : Ctx t L S x₁ x₂ lam rho tau) :
    closure ({x₁ ^ 2, (x₁ * x₂) ^ 2, t * tau * (x₁ * x₂)} : Set G) =
      closure ({x₁ ^ 2, (x₁ * x₂) ^ 2, t * (x₁ * x₂ * tau)} : Set G) := by
  have hz : (x₁ * x₂) ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hh := closure_three_congr (t * (x₁ * x₂ * tau)) ((x₁ * x₂) ^ 2) hz
  rwa [← t_tau_mul_x1x2_eq_of h] at hh

private theorem mem_or_t_mul_mem_of_mem_sup (h : Ctx t L S x₁ x₂ lam rho tau)
    {V : Subgroup G} (hVS : V ≤ S) {e : G} (he : e ∈ V ⊔ zpowers t) :
    e ∈ V ∨ t * e ∈ V := by
  have hcomm : ∀ a ∈ V, ∀ b ∈ zpowers t, a * b = b * a :=
    fun a ha b hb => (zpowers_t_commute_S h hb (hVS ha)).symm
  obtain ⟨v, hv, p, hp, hev⟩ := (mem_sup_iff_of_commute hcomm).mp he
  rcases zpowers_t_eq_one_or_t h hp with hp1 | hpt
  · left
    rw [hev, hp1, mul_one]
    exact hv
  · right
    rw [hev, hpt]
    have htv : t * v = v * t := t_commute_of_mem_S h (hVS hv)
    have heq : t * (v * t) = v := by
      rw [← mul_assoc, htv, mul_assoc, t_mul_self h.hyp, mul_one]
    rw [heq]
    exact hv

private theorem card_eq_eight_of_four_le {V D : Subgroup G} (hVD : D ≤ V)
    (hFD : fourGrp x₁ x₂ ≤ D) (hV8 : Nat.card V = 8)
    (hF4 : Nat.card (fourGrp x₁ x₂) = 4) (hne : D ≠ fourGrp x₁ x₂) :
    Nat.card D = 8 := by
  have hdvd1 : Nat.card (fourGrp x₁ x₂) ∣ Nat.card D := Subgroup.card_dvd_of_le hFD
  have hdvd2 : Nat.card D ∣ Nat.card V := Subgroup.card_dvd_of_le hVD
  rw [hF4] at hdvd1
  rw [hV8] at hdvd2
  have hD4 : 4 ≤ Nat.card D := by
    haveI : Nonempty ↥D := ⟨⟨1, D.one_mem⟩⟩
    exact Nat.le_of_dvd Nat.card_pos hdvd1
  have hle8 : Nat.card D ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd2
  have hne4 : Nat.card D ≠ 4 := by
    intro h4
    exact hne (Subgroup.eq_of_le_of_card_ge hFD (by omega)).symm
  omega

theorem lemma4_6_of (h : Ctx t L S x₁ x₂ lam rho tau) (h43 : twoCore t = zpowers t)
    (h44 : tau ^ 2 = 1) : Lemma4_6Concl t S x₁ x₂ tau := by
  intro V hV hVe hV8
  have hM := m12Rel_of_ctx h h44
  have hVS : V ≤ S := hV.1
  have hFcard : Nat.card (fourGrp x₁ x₂) = 4 := (WreathRel.fourGrp_eq_omega h.wreath).2.2
  have hVM_normal : NormalIn (V ⊓ m12Grp x₁ x₂ lam tau) (m12Grp x₁ x₂ lam tau) :=
    normalIn_inf_m12Grp h hV
  have hVM_elem : CFSG.Open.IsElemAbelian 2 (V ⊓ m12Grp x₁ x₂ lam tau) :=
    CFSG.Open.IsElemAbelian.mono hVe inf_le_left
  have hVM_card : 4 ≤ Nat.card (V ⊓ m12Grp x₁ x₂ lam tau : Subgroup G) := by
    have hc := card_le_two_mul_inf h h43 h44 hVS
    rw [hV8] at hc
    omega
  have hF_le_VM : fourGrp x₁ x₂ ≤ V ⊓ m12Grp x₁ x₂ lam tau :=
    (hM.fourGrp_le_of_normal_elemAbelian hVM_elem hVM_normal hVM_card).1
  have hF_le_V : fourGrp x₁ x₂ ≤ V := hF_le_VM.trans inf_le_left
  by_cases htV : t ∈ V
  ·
    have hVeq : V = zpowers t ⊔ (V ⊓ m12Grp x₁ x₂ lam tau) :=
      (eq_sup_inf_of_t_mem h h43 h44 hVS htV).1
    have hVc : Nat.card V = 2 * Nat.card (V ⊓ m12Grp x₁ x₂ lam tau : Subgroup G) :=
      (eq_sup_inf_of_t_mem h h43 h44 hVS htV).2
    have hVMinf : Nat.card (V ⊓ m12Grp x₁ x₂ lam tau : Subgroup G) = 4 := by
      rw [hV8] at hVc
      omega
    have hFeq : fourGrp x₁ x₂ = V ⊓ m12Grp x₁ x₂ lam tau :=
      Subgroup.eq_of_le_of_card_ge hF_le_VM (by omega)
    left
    rw [hVeq, ← hFeq, sup_comm, ← closure_insert_eq_fourGrp_sup t]
  ·
    have hV'_le_S : V ⊔ zpowers t ≤ S := sup_le hVS (zpowers_t_le_S_of h)
    have hV'_normal : NormalIn (V ⊔ zpowers t) S := normalIn_sup_zpowers h hV
    have hV'_elem : CFSG.Open.IsElemAbelian 2 (V ⊔ zpowers t) :=
      isElemAbelian_sup_zpowers h hVS hVe
    have hV'_card : Nat.card (V ⊔ zpowers t : Subgroup G) = 16 := by
      rw [card_sup_zpowers_of_t_not_mem h hVS htV, hV8]
    have htV' : t ∈ V ⊔ zpowers t := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
    have hE'_card : Nat.card ((V ⊔ zpowers t) ⊓ m12Grp x₁ x₂ lam tau : Subgroup G) = 8 := by
      have hc := (eq_sup_inf_of_t_mem h h43 h44 hV'_le_S htV').2
      rw [hV'_card] at hc
      omega
    have hE'_normal : NormalIn ((V ⊔ zpowers t) ⊓ m12Grp x₁ x₂ lam tau)
        (m12Grp x₁ x₂ lam tau) := normalIn_inf_m12Grp h hV'_normal
    have hE'_elem : CFSG.Open.IsElemAbelian 2
        ((V ⊔ zpowers t) ⊓ m12Grp x₁ x₂ lam tau) :=
      CFSG.Open.IsElemAbelian.mono hV'_elem inf_le_left
    rcases hM.eq_of_normal_elemAbelian_eight inf_le_right hE'_elem hE'_card hE'_normal with
      hE' | hE'
    ·
      have he₀V' : tau ∈ V ⊔ zpowers t := by
        have h1 : tau ∈ (V ⊔ zpowers t) ⊓ m12Grp x₁ x₂ lam tau := by
          rw [hE']
          exact Subgroup.subset_closure (by simp)
        exact h1.1
      rcases mem_or_t_mul_mem_of_mem_sup h hVS he₀V' with htauV | httauV
      ·
        right; left
        have hle : closure ({x₁ ^ 2, (x₁ * x₂) ^ 2, tau} : Set G) ≤ V := by
          rw [closure_insert_eq_fourGrp_sup tau]
          exact sup_le hF_le_V (Subgroup.zpowers_le.mpr htauV)
        have hcl : Nat.card (closure ({x₁ ^ 2, (x₁ * x₂) ^ 2, tau} : Set G)) = 8 := by
          rw [← hE']
          exact hE'_card
        exact (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm
      ·
        right; right; left
        have hDle : closure ({x₁ ^ 2, (x₁ * x₂) ^ 2, t * tau} : Set G) ≤ V := by
          rw [closure_insert_eq_fourGrp_sup (t * tau)]
          exact sup_le hF_le_V (Subgroup.zpowers_le.mpr httauV)
        have hne : closure ({x₁ ^ 2, (x₁ * x₂) ^ 2, t * tau} : Set G) ≠ fourGrp x₁ x₂ := by
          intro hD
          have httauM : t * tau ∈ m12Grp x₁ x₂ lam tau :=
            fourGrp_le_m12Grp' (hD ▸ Subgroup.subset_closure (by simp))
          have htauM : tau ∈ m12Grp x₁ x₂ lam tau := Subgroup.subset_closure (by simp)
          have htM : t ∈ m12Grp x₁ x₂ lam tau := by
            have hmem := Subgroup.mul_mem (m12Grp x₁ x₂ lam tau) httauM
              (Subgroup.inv_mem (m12Grp x₁ x₂ lam tau) htauM)
            rwa [show (t * tau) * tau⁻¹ = t by group] at hmem
          exact t_not_mem_m12Grp_of h h43 h44 htM
        have hFD : fourGrp x₁ x₂ ≤ closure ({x₁ ^ 2, (x₁ * x₂) ^ 2, t * tau} : Set G) := by
          rw [fourGrp, Subgroup.closure_le]
          intro g hg
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
          rcases hg with rfl | rfl
          · exact Subgroup.subset_closure (by simp)
          · exact Subgroup.subset_closure (by simp)
        have hDcard : Nat.card (closure ({x₁ ^ 2, (x₁ * x₂) ^ 2, t * tau} : Set G)) = 8 :=
          card_eq_eight_of_four_le hDle hFD hV8 hFcard hne
        exact (Subgroup.eq_of_le_of_card_ge hDle (by omega)).symm
    ·
      have he₀V' : x₁ * x₂ * tau ∈ V ⊔ zpowers t := by
        have h1 : x₁ * x₂ * tau ∈ (V ⊔ zpowers t) ⊓ m12Grp x₁ x₂ lam tau := by
          rw [hE']
          exact Subgroup.subset_closure (by simp)
        exact h1.1
      rcases mem_or_t_mul_mem_of_mem_sup h hVS he₀V' with he₀V | hte₀V
      ·
        right; right; right; left
        have hle : closure ({x₁ ^ 2, (x₁ * x₂) ^ 2, x₁ * x₂ * tau} : Set G) ≤ V := by
          rw [closure_insert_eq_fourGrp_sup (x₁ * x₂ * tau)]
          exact sup_le hF_le_V (Subgroup.zpowers_le.mpr he₀V)
        have hcl : Nat.card (closure ({x₁ ^ 2, (x₁ * x₂) ^ 2, x₁ * x₂ * tau} : Set G)) = 8 := by
          rw [← hE']
          exact hE'_card
        have hVeq : V = closure ({x₁ ^ 2, (x₁ * x₂) ^ 2, x₁ * x₂ * tau} : Set G) :=
          (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm
        rw [hVeq, ← closure_tau_mul_x1x2_of h]
      ·
        right; right; right; right
        have hDle : closure ({x₁ ^ 2, (x₁ * x₂) ^ 2, t * (x₁ * x₂ * tau)} : Set G) ≤ V := by
          rw [closure_insert_eq_fourGrp_sup (t * (x₁ * x₂ * tau))]
          exact sup_le hF_le_V (Subgroup.zpowers_le.mpr hte₀V)
        have hne : closure ({x₁ ^ 2, (x₁ * x₂) ^ 2, t * (x₁ * x₂ * tau)} : Set G) ≠
            fourGrp x₁ x₂ := by
          intro hD
          have heM : t * (x₁ * x₂ * tau) ∈ m12Grp x₁ x₂ lam tau :=
            fourGrp_le_m12Grp' (hD ▸ Subgroup.subset_closure (by simp))
          have hx1x2M : x₁ * x₂ ∈ m12Grp x₁ x₂ lam tau :=
            Subgroup.mul_mem (m12Grp x₁ x₂ lam tau) (Subgroup.subset_closure (by simp))
              (Subgroup.subset_closure (by simp))
          have hteltauM : t * tau ∈ m12Grp x₁ x₂ lam tau := by
            have hmem := Subgroup.mul_mem (m12Grp x₁ x₂ lam tau)
              (Subgroup.inv_mem (m12Grp x₁ x₂ lam tau) hx1x2M) heM
            rwa [show (x₁ * x₂)⁻¹ * (t * (x₁ * x₂ * tau)) = t * tau by
              have htc : t * (x₁ * x₂) = (x₁ * x₂) * t :=
                t_commute_of_mem_S h (m12Grp_le_S h hx1x2M)
              calc (x₁ * x₂)⁻¹ * (t * (x₁ * x₂ * tau))
                  = (x₁ * x₂)⁻¹ * ((x₁ * x₂) * (t * tau)) := by
                    rw [show t * (x₁ * x₂ * tau) = (x₁ * x₂) * (t * tau) by
                      calc t * (x₁ * x₂ * tau) = (t * (x₁ * x₂)) * tau :=
                            (mul_assoc t (x₁ * x₂) tau).symm
                        _ = ((x₁ * x₂) * t) * tau := by rw [htc]
                        _ = (x₁ * x₂) * (t * tau) := mul_assoc (x₁ * x₂) t tau]
                _ = t * tau := inv_mul_cancel_left (x₁ * x₂) (t * tau)] at hmem
          have htauM : tau ∈ m12Grp x₁ x₂ lam tau := Subgroup.subset_closure (by simp)
          have htM : t ∈ m12Grp x₁ x₂ lam tau := by
            have hmem := Subgroup.mul_mem (m12Grp x₁ x₂ lam tau) hteltauM
              (Subgroup.inv_mem (m12Grp x₁ x₂ lam tau) htauM)
            rwa [show (t * tau) * tau⁻¹ = t by group] at hmem
          exact t_not_mem_m12Grp_of h h43 h44 htM
        have hFD : fourGrp x₁ x₂ ≤
            closure ({x₁ ^ 2, (x₁ * x₂) ^ 2, t * (x₁ * x₂ * tau)} : Set G) := by
          rw [fourGrp, Subgroup.closure_le]
          intro g hg
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
          rcases hg with rfl | rfl
          · exact Subgroup.subset_closure (by simp)
          · exact Subgroup.subset_closure (by simp)
        have hDcard :
            Nat.card (closure ({x₁ ^ 2, (x₁ * x₂) ^ 2, t * (x₁ * x₂ * tau)} : Set G)) = 8 :=
          card_eq_eight_of_four_le hDle hFD hV8 hFcard hne
        have hVeq : V = closure ({x₁ ^ 2, (x₁ * x₂) ^ 2, t * (x₁ * x₂ * tau)} : Set G) :=
          (Subgroup.eq_of_le_of_card_ge hDle (by omega)).symm
        rw [hVeq, ← closure_t_tau_mul_x1x2_of h]

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
