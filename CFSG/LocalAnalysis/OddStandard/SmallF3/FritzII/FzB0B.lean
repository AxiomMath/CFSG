module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzB0A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ATauA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzDefs

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem fzbs_tau_facts (h : Ctx t L S x₁ x₂ lam rho tau) :
    tau ∈ fzN2 t x₁ x₂ ∧ tau * t * tau⁻¹ = t ∧
      (∀ z ∈ fourGrp x₁ x₂, tau * z * tau⁻¹ = z) ∧
      (∀ x ∈ fzbsX t x₁ x₂, tau * x * tau⁻¹ = x⁻¹) ∧
      (∀ k ∈ twoCore t, tau * k * tau⁻¹ ∈ twoCore t) := by
  have hτH : tau ∈ invCent t := h.le_invCent h.tau_mem
  have hτN2 : tau ∈ fzN2 t x₁ x₂ := fz_S_le_N2 h h.tau_mem
  have hτt : tau * t * tau⁻¹ = t := by
    have hcomm : tau * t = t * tau := S4A.mem_invCent_iff.mp hτH
    calc tau * t * tau⁻¹ = (t * tau) * tau⁻¹ := by rw [hcomm]
      _ = t := by group
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
  have hXinv : ∀ x ∈ fzbsX t x₁ x₂, tau * x * tau⁻¹ = x⁻¹ := by
    intro x hx
    change x ∈ zpowers t ⊔ baseGrp x₁ x₂ at hx
    have hcommXt : ∀ a ∈ zpowers t, ∀ b ∈ baseGrp x₁ x₂, a * b = b * a :=
      fun a ha b hb =>
        S4A.pt_comm_base h.toCtx0 a (Subgroup.zpowers_le.mpr h.hyp.mem_twoCore ha) b hb
    obtain ⟨p, hp, e, he, rfl⟩ := (mem_sup_iff_of_commute hcommXt).mp hx
    have hpc : Commute p e :=
      S4A.pt_comm_base h.toCtx0 p
        (Subgroup.zpowers_le.mpr h.hyp.mem_twoCore hp) e he
    have hpp : p * p = 1 := by
      rcases S4A.pt_eq_one_or_of_mem_zpowers h.hyp.ord_t hp with h1 | h1
      · rw [h1]; simp
      · rw [h1]; exact S4A.t_mul_self h.hyp
    have hτp : tau * p * tau⁻¹ = p := by
      rcases S4A.pt_eq_one_or_of_mem_zpowers h.hyp.ord_t hp with h1 | h1
      · rw [h1]; simp
      · rw [h1]; exact hτt
    have hτe : tau * e * tau⁻¹ = e⁻¹ := hτinv e he
    calc tau * (p * e) * tau⁻¹ = (tau * p * tau⁻¹) * (tau * e * tau⁻¹) := by group
      _ = p * e⁻¹ := by rw [hτp, hτe]
      _ = (p * e)⁻¹ := by
        rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hpp]
        exact (hpc.inv_right).eq
  have hτK : ∀ k ∈ twoCore t, tau * k * tau⁻¹ ∈ twoCore t :=
    fun k hk => S4A.twoCore_conj_mem t hτH hk
  exact ⟨hτN2, hτt, hZfix, hXinv, hτK⟩

theorem fzbs_tau_q (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 4) {q : G}
    (hq : zpowers q = twoCore t) : tau * q * tau⁻¹ = q ∨ tau * q * tau⁻¹ = q⁻¹ := by
  obtain ⟨-, hτt, -, -, hτK⟩ := fzbs_tau_facts h
  obtain ⟨hq4, hq2⟩ := fzbs_q_facts h hK hq
  have hq'K : tau * q * tau⁻¹ ∈ twoCore t :=
    hτK q (by rw [← hq]; exact Subgroup.mem_zpowers q)
  have hq'mem : tau * q * tau⁻¹ ∈ zpowers q := by rw [hq]; exact hq'K
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hq'mem
  have hq'2 : (tau * q * tau⁻¹) ^ 2 = t := by
    rw [conj_pow, hq2, hτt]
  have ht_ne_one : t ≠ 1 := by
    intro h1
    have h2 := h.hyp.ord_t
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hkmod : q ^ (k % 4) = tau * q * tau⁻¹ := by
    have hmod := zpow_mod_orderOf q k
    rw [hq4] at hmod
    exact hmod.trans hk
  have hq3inv : q ^ (3 : ℤ) = q⁻¹ := by
    have h1 : q ^ (1 : ℤ) * q ^ (3 : ℤ) = 1 := by
      rw [← zpow_add]
      rw [show (1 : ℤ) + 3 = 4 by norm_num]
      rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast, ← hq4,
        pow_orderOf_eq_one]
    have h2 : q * q ^ (3 : ℤ) = 1 := by simpa using h1
    exact (inv_eq_of_mul_eq_one_right h2).symm
  have hzpow2 : q ^ (2 : ℤ) = t := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, hq2]
  rcases (by omega : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3) with h0 | h1 | h2 | h3
  · exfalso
    have hq'1 : (tau * q * tau⁻¹) = 1 := by rw [← hkmod, h0]; simp
    rw [hq'1] at hq'2
    simp at hq'2
    exact ht_ne_one hq'2.symm
  · left
    rw [← hkmod, h1]; simp
  · exfalso
    have hq't : tau * q * tau⁻¹ = t := by rw [← hkmod, h2, hzpow2]
    rw [hq't, pow_two, S4A.t_mul_self h.hyp] at hq'2
    exact ht_ne_one hq'2.symm
  · right
    rw [← hkmod, h3, hq3inv]

theorem fzbs_card_Wtau (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 4) :
    tau ∉ ctxW t x₁ x₂ ∧ Nat.card (ctxW t x₁ x₂ ⊔ zpowers tau : Subgroup G) = 128 := by
  obtain ⟨hτN2, -, -, -, -⟩ := fzbs_tau_facts h
  have hτW : tau ∉ ctxW t x₁ x₂ := by
    intro hmem
    apply h.tau_not_mem
    have hWle : ctxW t x₁ x₂ ≤ twoCore t ⊔ L :=
      sup_le le_sup_left ((S4A.pt_base_le_L h.toCtx0).trans le_sup_right)
    exact hWle hmem
  refine ⟨hτW, ?_⟩
  have hzK : zpowers tau ≤ ctxW t x₁ x₂ ⊔ zpowers tau := le_sup_right
  have hsupEq : (ctxW t x₁ x₂).subgroupOf (ctxW t x₁ x₂ ⊔ zpowers tau) ⊔
      (zpowers tau).subgroupOf (ctxW t x₁ x₂ ⊔ zpowers tau) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left hzK]
    exact Subgroup.subgroupOf_self _
  have hN : ((ctxW t x₁ x₂).subgroupOf (ctxW t x₁ x₂ ⊔ zpowers tau)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
    exact sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hτN2)
  have hrel : (ctxW t x₁ x₂).relIndex (ctxW t x₁ x₂ ⊔ zpowers tau) = 2 := by
    rw [Subgroup.relIndex_eq_two_iff_exists_notMem_and']
    refine ⟨tau, Subgroup.mem_sup_right (Subgroup.mem_zpowers tau), hτW, ?_⟩
    intro b hb
    haveI : ((ctxW t x₁ x₂).subgroupOf (ctxW t x₁ x₂ ⊔ zpowers tau)).Normal := hN
    have hbK : (⟨b, hb⟩ : ↥(ctxW t x₁ x₂ ⊔ zpowers tau)) ∈
        (ctxW t x₁ x₂).subgroupOf (ctxW t x₁ x₂ ⊔ zpowers tau) ⊔
        (zpowers tau).subgroupOf (ctxW t x₁ x₂ ⊔ zpowers tau) := by
      rw [hsupEq]; exact Subgroup.mem_top _
    obtain ⟨y, hy, z, hz, hyz⟩ :=
      (Subgroup.mem_sup_of_normal_left
        (x := (⟨b, hb⟩ : ↥(ctxW t x₁ x₂ ⊔ zpowers tau)))).mp hbK
    have hyW : (y : ↥(ctxW t x₁ x₂ ⊔ zpowers tau)).1 ∈ ctxW t x₁ x₂ :=
      Subgroup.mem_subgroupOf.mp hy
    have hzτ : (z : ↥(ctxW t x₁ x₂ ⊔ zpowers tau)).1 ∈ zpowers tau :=
      Subgroup.mem_subgroupOf.mp hz
    have hyzb : (y : ↥(ctxW t x₁ x₂ ⊔ zpowers tau)).1 *
        (z : ↥(ctxW t x₁ x₂ ⊔ zpowers tau)).1 = b := congrArg Subtype.val hyz
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hzτ
    have hyτW : tau * (y : ↥(ctxW t x₁ x₂ ⊔ zpowers tau)).1 * tau⁻¹ ∈
        ctxW t x₁ x₂ := (Subgroup.mem_normalizer_iff.mp hτN2 _).mp hyW
    have hτ2W : tau ^ (2 : ℤ) ∈ ctxW t x₁ x₂ := by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast]
      exact Subgroup.mem_sup_left h.tau_sq_mem
    have hpow2 : ∀ j : ℤ, tau ^ (2 * j) ∈ ctxW t x₁ x₂ := by
      intro j
      rw [zpow_mul]
      exact Subgroup.zpow_mem _ hτ2W j
    obtain ⟨j, hj | hj⟩ := Int.even_or_odd' m
    · right
      have hzW : (z : ↥(ctxW t x₁ x₂ ⊔ zpowers tau)).1 ∈ ctxW t x₁ x₂ := by
        rw [← hm, hj]; exact hpow2 j
      rw [← hyzb]
      exact Subgroup.mul_mem _ hyW hzW
    · left
      have hzW : tau * (z : ↥(ctxW t x₁ x₂ ⊔ zpowers tau)).1 ∈ ctxW t x₁ x₂ := by
        rw [← hm, hj]
        have hτ : tau * tau ^ (2 * j + 1) = tau ^ (2 * (j + 1)) := by
          calc tau * tau ^ (2 * j + 1) = tau ^ (1 : ℤ) * tau ^ (2 * j + 1) := by
                rw [zpow_one]
            _ = tau ^ ((1 : ℤ) + (2 * j + 1)) := by rw [← zpow_add]
            _ = tau ^ (2 * (j + 1)) := by congr 1; ring
        rw [hτ]
        exact hpow2 (j + 1)
      rw [← hyzb]
      have hcalc : tau * ((y : ↥(ctxW t x₁ x₂ ⊔ zpowers tau)).1 *
          (z : ↥(ctxW t x₁ x₂ ⊔ zpowers tau)).1) =
          (tau * (y : ↥(ctxW t x₁ x₂ ⊔ zpowers tau)).1 * tau⁻¹) *
          (tau * (z : ↥(ctxW t x₁ x₂ ⊔ zpowers tau)).1) := by group
      rw [hcalc]
      exact Subgroup.mul_mem _ hyτW hzW
  have hcardW : Nat.card (ctxW t x₁ x₂) = 64 := fzbs_card_W h hK
  have hcm := Subgroup.card_mul_index
    (H := (ctxW t x₁ x₂).subgroupOf (ctxW t x₁ x₂ ⊔ zpowers tau))
  have hcard_sub : Nat.card ((ctxW t x₁ x₂).subgroupOf
      (ctxW t x₁ x₂ ⊔ zpowers tau)) = 64 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv]
    exact hcardW
  have hidx : ((ctxW t x₁ x₂).subgroupOf (ctxW t x₁ x₂ ⊔ zpowers tau)).index = 2 := hrel
  rw [hcard_sub, hidx] at hcm
  have h128 : Nat.card ↥(ctxW t x₁ x₂ ⊔ zpowers tau) = 128 := hcm.symm
  exact h128

theorem fzbs_Wtau_act (h : Ctx t L S x₁ x₂ lam rho tau) {k : G}
    (hk : k ∈ ctxW t x₁ x₂ ⊔ zpowers tau) :
    k ∈ fzN2 t x₁ x₂ ∧ k * t * k⁻¹ = t ∧ (∀ z ∈ fourGrp x₁ x₂, k * z * k⁻¹ = z) ∧
      ((∀ x ∈ fzbsX t x₁ x₂, k * x * k⁻¹ = x) ∨
        (∀ x ∈ fzbsX t x₁ x₂, k * x * k⁻¹ = x⁻¹)) := by
  obtain ⟨hτN2, hτt, hτZ, hτX, -⟩ := fzbs_tau_facts h
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
  let Sd : Subgroup G :=
    { carrier := {k : G | k ∈ ctxW t x₁ x₂ ⊔ zpowers tau ∧
        ((∀ x ∈ fzbsX t x₁ x₂, k * x * k⁻¹ = x) ∨
          (∀ x ∈ fzbsX t x₁ x₂, k * x * k⁻¹ = x⁻¹))}
      one_mem' := ⟨Subgroup.one_mem _, Or.inl (by intro x _; group)⟩
      mul_mem' := by
        rintro a b ⟨ha, hda⟩ ⟨hb, hdb⟩
        refine ⟨Subgroup.mul_mem _ ha hb, ?_⟩
        rcases hda with hda | hda <;> rcases hdb with hdb | hdb
        · left; intro x hx
          calc (a * b) * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
            _ = a * x * a⁻¹ := by rw [hdb x hx]
            _ = x := hda x hx
        · right; intro x hx
          calc (a * b) * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
            _ = a * x⁻¹ * a⁻¹ := by rw [hdb x hx]
            _ = (a * x * a⁻¹)⁻¹ := by group
            _ = x⁻¹ := by rw [hda x hx]
        · right; intro x hx
          calc (a * b) * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
            _ = a * x * a⁻¹ := by rw [hdb x hx]
            _ = x⁻¹ := hda x hx
        · left; intro x hx
          calc (a * b) * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
            _ = a * x⁻¹ * a⁻¹ := by rw [hdb x hx]
            _ = (a * x * a⁻¹)⁻¹ := by group
            _ = (x⁻¹)⁻¹ := by rw [hda x hx]
            _ = x := by group
      inv_mem' := by
        rintro a ⟨ha, hda⟩
        refine ⟨Subgroup.inv_mem _ ha, ?_⟩
        rcases hda with hda | hda
        · left; intro x hx
          simp only [inv_inv]
          have hcomm : a * x = x * a := by
            calc a * x = (a * x * a⁻¹) * a := by group
              _ = x * a := by rw [hda x hx]
          calc a⁻¹ * x * a = a⁻¹ * (x * a) := by group
            _ = a⁻¹ * (a * x) := by rw [← hcomm]
            _ = x := by group
        · right; intro x hx
          simp only [inv_inv]
          have h1 : x = a⁻¹ * x⁻¹ * a := by
            calc x = a⁻¹ * (a * x * a⁻¹) * a := by group
              _ = a⁻¹ * x⁻¹ * a := by rw [hda x hx]
          calc a⁻¹ * x * a = (a⁻¹ * x⁻¹ * a)⁻¹ := by group
            _ = x⁻¹ := by rw [← h1] }
  have hWSd : ctxW t x₁ x₂ ≤ Sd := by
    intro w hw
    refine ⟨Subgroup.mem_sup_left hw, Or.inl ?_⟩
    intro x hx
    have hxW : x ∈ ctxW t x₁ x₂ := (fzbs_X_le h).2.2.2 hx
    have hcomm : w * x = x * w :=
      congrArg Subtype.val (isMulCommutative_iff.mp h.abelian_W ⟨w, hw⟩ ⟨x, hxW⟩)
    rw [hcomm]; group
  have hτSd : tau ∈ Sd :=
    ⟨Subgroup.mem_sup_right (Subgroup.mem_zpowers tau), Or.inr hτX⟩
  have hsup : ctxW t x₁ x₂ ⊔ zpowers tau ≤ Sd :=
    sup_le hWSd (Subgroup.zpowers_le.mpr hτSd)
  exact ⟨hkN2, hkt, hkZ, (hsup hk).2⟩

theorem fzbs_cent_X (h : Ctx t L S x₁ x₂ lam rho tau) {n : G}
    (hc : ∀ x ∈ fzbsX t x₁ x₂, n * x * n⁻¹ = x) : n ∈ ctxW t x₁ x₂ := by
  obtain ⟨htX, -, hBX, -⟩ := fzbs_X_le h
  have hnH : n ∈ invCent t := by
    rw [S4A.mem_invCent_iff]
    have h := hc t htX
    calc n * t = (n * t * n⁻¹) * n := by group
      _ = t * n := by rw [h]
  have hmem : n ∈ invCent t ⊓ Subgroup.centralizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) := by
    refine ⟨hnH, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro b hb
    have hbn : n * b = b * n := by
      have h := hc b (hBX hb)
      calc n * b = (n * b * n⁻¹) * n := by group
        _ = b * n := by rw [h]
    exact hbn.symm
  rwa [h.cent_baseGrp] at hmem

end CFSG.OddStandard.SmallF3.FritzII
