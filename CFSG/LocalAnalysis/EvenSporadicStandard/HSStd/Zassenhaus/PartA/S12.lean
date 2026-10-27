module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S12Cent2

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup Wreath Open CFSG.EvenSporadicStandard.HSStd.Zassenhaus

set_option linter.unusedSectionVars false

section Decomp

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}

theorem PA11.L₁_comm_conj (a : PA11 L t E z) {n m : G} (hn : n ∈ a.L₁) (hm : m ∈ conjSub t a.L₁) :
    n * m = m * n := by
  obtain ⟨m₀, hm₀, rfl⟩ := mem_conjSub.1 hm
  exact (a.L₁_comm n hn m₀ hm₀).eq

theorem PA11.conjSub_le_Cen (hb : PAB G L t E W z) (a : PA11 L t E z) :
    conjSub t a.L₁ ≤ Cen a.ub := by
  have ht : t ∈ Cen a.ub := mem_Cen.2 (PA5.comm_t_ub hb a.toPA10.toPA9.toPA8.toPA7.toPA6.toPA5).symm
  rintro _ ⟨l, hl, rfl⟩
  exact mul_mem (mul_mem ht (a.L₁_comp.1 hl)) (inv_mem ht)

theorem PA11.w_decomp (hb : PAB G L t E W z) (a : PA11 L t E z) {w : G} (hwK : w ∈ a.K₁)
    (hw3 : w * (w * w) = 1) (hwu : w * a.ub = a.ub * w) :
    ∃ b ∈ a.X, ∃ c ∈ conjSub t a.X, w = b * c := by
  have htt : t * t = 1 := hb.t_mul_t
  have hwx : w * a.x = a.x * w := a.K₁_comm_O hwK a.x_O
  have hwxt : w * (t * a.x * t⁻¹) = (t * a.x * t⁻¹) * w := a.K₁_comm_O hwK a.xt_mem_O
  have hwCen : w ∈ Cen a.ub := mem_Cen.2 hwu
  have hw3' : w ^ 3 = 1 := by rw [pow_three]; exact hw3
  have hwN1 : w ∈ normalizer (a.L₁ : Set G) := a.mem_normalizer_L₁ hb hwCen hwx
  obtain ⟨b, hbX, hb_eq⟩ := a.frame.exists_conj_of_cube hwN1 hw3' hwx
  have hwN2 : w ∈ normalizer ((a.swapL hb).L₁ : Set G) :=
    (a.swapL hb).mem_normalizer_L₁ hb hwCen hwxt
  obtain ⟨c, hcX, hc_eq⟩ := (a.swapL hb).frame.exists_conj_of_cube hwN2 hw3' hwxt
  have hcX' : c ∈ conjSub t a.X := hcX
  have hbL : b ∈ a.L₁ := a.frame.X_mem_N hbX
  have hcL : c ∈ conjSub t a.L₁ := (a.swapL hb).frame.X_mem_N hcX
  have hbc : b * c = c * b := a.L₁_comm_conj hbL hcL
  have hb3 : b ^ 3 = 1 := a.frame.exp_three hbX
  have hc3 : c ^ 3 = 1 := (a.swapL hb).frame.exp_three hcX
  have hcent1 : ∀ n ∈ a.L₁, (w * b⁻¹ * c⁻¹) * n = n * (w * b⁻¹ * c⁻¹) := by
    intro n hn
    have hcn : c⁻¹ * n * c = n := by
      have := a.L₁_comm_conj hn hcL
      rw [mul_assoc, this, ← mul_assoc, inv_mul_cancel, one_mul]
    have hbn := hb_eq (b⁻¹ * n * b) (a.L₁.mul_mem (a.L₁.mul_mem (a.L₁.inv_mem hbL) hn) hbL)
    have : (w * b⁻¹ * c⁻¹) * n * (w * b⁻¹ * c⁻¹)⁻¹ = n := by
      calc (w * b⁻¹ * c⁻¹) * n * (w * b⁻¹ * c⁻¹)⁻¹
          = w * b⁻¹ * (c⁻¹ * n * c) * b * w⁻¹ := by group
        _ = w * (b⁻¹ * n * b) * w⁻¹ := by rw [hcn]; group
        _ = b * (b⁻¹ * n * b) * b⁻¹ := hbn
        _ = n := by group
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  have hcent2 : ∀ n ∈ conjSub t a.L₁, (w * b⁻¹ * c⁻¹) * n = n * (w * b⁻¹ * c⁻¹) := by
    intro n hn
    have hm : c⁻¹ * n * c ∈ conjSub t a.L₁ :=
      (conjSub t a.L₁).mul_mem ((conjSub t a.L₁).mul_mem ((conjSub t a.L₁).inv_mem hcL) hn) hcL
    have hbm : b⁻¹ * (c⁻¹ * n * c) * b = c⁻¹ * n * c := by
      have := a.L₁_comm_conj hbL hm
      rw [mul_assoc, ← this, ← mul_assoc, inv_mul_cancel, one_mul]
    have hcn := hc_eq (c⁻¹ * n * c) hm
    have : (w * b⁻¹ * c⁻¹) * n * (w * b⁻¹ * c⁻¹)⁻¹ = n := by
      calc (w * b⁻¹ * c⁻¹) * n * (w * b⁻¹ * c⁻¹)⁻¹
          = w * (b⁻¹ * (c⁻¹ * n * c) * b) * w⁻¹ := by group
        _ = w * (c⁻¹ * n * c) * w⁻¹ := by rw [hbm]
        _ = c * (c⁻¹ * n * c) * c⁻¹ := hcn
        _ = n := by group
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  have hw''Cen : w * b⁻¹ * c⁻¹ ∈ Cen a.ub :=
    mul_mem (mul_mem hwCen (inv_mem (a.L₁_comp.1 hbL)))
      (inv_mem (a.conjSub_le_Cen hb hcL))
  have hw''F : w * b⁻¹ * c⁻¹ ∈ a.F₀ := by
    rw [← a.CPE_eq]
    refine Subgroup.mem_inf.2 ⟨hw''Cen, ?_⟩
    rw [mem_centralizer_iff]
    intro g hg
    have hle : a.L₁ ⊔ conjSub t a.L₁ ≤ centralizer ({w * b⁻¹ * c⁻¹} : Set G) := by
      refine sup_le ?_ ?_
      · intro n hn
        exact mem_centralizer_singleton_iff.2 (hcent1 n hn).symm
      · intro n hn
        exact mem_centralizer_singleton_iff.2 (hcent2 n hn).symm
    exact mem_centralizer_singleton_iff.1 (hle hg)
  have hwb : Commute w b⁻¹ := by
    have := hb_eq b hbL
    have h2 : w * b * w⁻¹ = b := by rw [this]; group
    have h3 : w * b = b * w := by rw [mul_inv_eq_iff_eq_mul] at h2; exact h2
    exact (Commute.inv_right (h3 : Commute w b))
  have hwc : Commute w c⁻¹ := by
    have := hc_eq c hcL
    have h2 : w * c * w⁻¹ = c := by rw [this]; group
    have h3 : w * c = c * w := by rw [mul_inv_eq_iff_eq_mul] at h2; exact h2
    exact (Commute.inv_right (h3 : Commute w c))
  have hbc' : Commute b⁻¹ c⁻¹ := Commute.inv_inv (hbc : Commute b c)
  have hpow : (w * b⁻¹ * c⁻¹) ^ 3 = 1 := by
    rw [(hwc.mul_left hbc').mul_pow, hwb.mul_pow, inv_pow, inv_pow, hb3, hc3, hw3']
    simp
  have hord : orderOf (w * b⁻¹ * c⁻¹) ∣ 3 := orderOf_dvd_of_pow_eq_one hpow
  have hord4 : orderOf (w * b⁻¹ * c⁻¹) ∣ 4 := by
    have := Subgroup.orderOf_dvd_natCard a.F₀ hw''F
    rwa [a.F₀_card a.d8_case] at this
  have h1 : orderOf (w * b⁻¹ * c⁻¹) = 1 := by
    have := Nat.dvd_gcd hord hord4
    simpa using this
  have h2 := orderOf_eq_one_iff.1 h1
  refine ⟨b, hbX, c, hcX', ?_⟩
  have h3 : w = c * b := by
    have h4 : w * b⁻¹ = c := by
      have := congrArg (· * c) h2
      simp only [one_mul] at this
      rw [mul_assoc, inv_mul_cancel, mul_one] at this
      exact this
    rw [← h4]
    group
  rw [h3, hbc]

theorem PA11.decomp_unique (a : PA11 L t E z) {b₁ b₂ c₁ c₂ : G} (hb₁ : b₁ ∈ a.X) (hb₂ : b₂ ∈ a.X)
    (hc₁ : c₁ ∈ conjSub t a.X) (hc₂ : c₂ ∈ conjSub t a.X) (h : b₁ * c₁ = b₂ * c₂) :
    b₁ = b₂ ∧ c₁ = c₂ := by
  have h1 : b₂⁻¹ * b₁ = c₂ * c₁⁻¹ := by
    calc b₂⁻¹ * b₁ = b₂⁻¹ * (b₁ * c₁) * c₁⁻¹ := by group
      _ = b₂⁻¹ * (b₂ * c₂) * c₁⁻¹ := by rw [h]
      _ = c₂ * c₁⁻¹ := by group
  have h2 : b₂⁻¹ * b₁ = 1 :=
    a.X_inf_Xt (a.X.mul_mem (a.X.inv_mem hb₂) hb₁)
      (h1 ▸ (conjSub t a.X).mul_mem hc₂ ((conjSub t a.X).inv_mem hc₁))
  have hbb : b₁ = b₂ := (inv_mul_eq_one.1 h2).symm
  refine ⟨hbb, ?_⟩
  rw [hbb] at h
  exact mul_left_cancel h

end Decomp


section Core

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}

theorem PA11.exists_PA12_of_wj (hb : PAB G L t E W z) (a : PA11 L t E z) (h : a.FirstType)
    {w j : G} (hwK : w ∈ a.K₁) (hwX : w ∈ a.X) (hw3 : w * (w * w) = 1) (hw1 : w ≠ 1)
    (hjK : j ∈ a.K₁) (hj2 : j * j = 1) (hj1 : j ≠ 1) (hju : j * a.ub = a.ub * j)
    (hjw : j * w * j⁻¹ = w⁻¹) : Nonempty (PA12 L t E z) := by
  have htt : t * t = 1 := hb.t_mul_t
  have hjx : j * a.x = a.x * j := a.K₁_comm_O hjK a.x_O
  have hjxt : j * (t * a.x * t⁻¹) = (t * a.x * t⁻¹) * j := a.K₁_comm_O hjK a.xt_mem_O
  have hjCen : j ∈ Cen a.ub := mem_Cen.2 hju
  have hjN : j ∈ normalizer (a.L₁ : Set G) := a.mem_normalizer_L₁ hb hjCen hjx
  have hjN' : j ∈ normalizer ((a.swapL hb).L₁ : Set G) :=
    (a.swapL hb).mem_normalizer_L₁ hb hjCen hjxt
  have hjX : ∀ g ∈ a.X, j * g * j⁻¹ ∈ a.X := fun g hg => a.conj_mem_X hjN hjx hg
  have hw3' : w ^ 3 = 1 := by rw [pow_three]; exact hw3
  have hww : ¬ (w * w = 1) := by
    intro hww
    rw [hww, mul_one] at hw3
    exact hw1 hw3
  have hjw_ne : j * w * j⁻¹ ≠ w := by
    rw [hjw]
    intro h2
    exact hww (eq_inv_iff_mul_eq_one.1 h2.symm)
  have hw_nx : w ∉ zpowers a.x := by
    intro hm
    obtain ⟨n, hn⟩ := mem_zpowers_iff.1 hm
    have hc : Commute j w := by
      rw [← hn]
      exact Commute.zpow_right (show Commute j a.x from hjx) n
    exact hjw_ne (hc.mul_inv_cancel)
  have hxtX : t * a.x * t⁻¹ ∈ conjSub t a.X := conj_mem_conjSub a.frame.x_mem
  have hwtX : t * w * t⁻¹ ∈ conjSub t a.X := conj_mem_conjSub hwX
  have hwtj : (t * w * t⁻¹) * j = j * (t * w * t⁻¹) :=
    (mem_centralizer_iff.1 (a.K₁_K₁t hjK) _ (conj_mem_conjSub hwK))
  have hHeq : conjSub t a.X ⊓ Cen j = conjSub t a.X := by
    refine eq_of_card_nine (X := conjSub t a.X) (by rw [card_conjSub]; exact a.X_card)
      inf_le_left (y := t * a.x * t⁻¹) (z := t * w * t⁻¹) ?_ ?_ ?_ ?_
    · exact Subgroup.mem_inf.2 ⟨hxtX, mem_Cen.2 hjxt.symm⟩
    · rw [orderOf_conj_eq]; exact a.x_ord
    · exact Subgroup.mem_inf.2 ⟨hwtX, mem_Cen.2 hwtj⟩
    · intro hm
      obtain ⟨n, hn⟩ := mem_zpowers_iff.1 hm
      have h1 : (MulAut.conj t) w = (MulAut.conj t) (a.x ^ n) := by
        rw [map_zpow]
        exact hn.symm
      exact hw_nx (mem_zpowers_iff.2 ⟨n, ((MulAut.conj t).injective h1).symm⟩)
  have hfix : ∀ g ∈ (a.swapL hb).X, j * g * j⁻¹ = g := by
    intro g hg
    have hg' : g ∈ conjSub t a.X ⊓ Cen j := by rw [hHeq]; exact hg
    have := mem_Cen.1 (Subgroup.mem_inf.1 hg').2
    rw [mul_inv_eq_iff_eq_mul]
    exact this.symm
  have hcentt := (a.swapL hb).frame.centralizes_of_fix hjN' hj2 hfix
  have hk_L₁t : ∀ l ∈ a.L₁, j * (t * l * t⁻¹) = (t * l * t⁻¹) * j := by
    intro l hl
    have := hcentt (t * l * t⁻¹) (conj_mem_conjSub hl)
    rwa [mul_inv_eq_iff_eq_mul] at this
  have hord3 : orderOf w = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime hw3' hw1
  have hord2 : orderOf j = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hj2) hj1
  exact ⟨{ toPA11 := a
           c₃ := w
           k := j
           c₃_K₁ := hwK
           c₃_L₁ := a.frame.X_mem_N hwX
           c₃_ord := hord3
           c₃_x := a.frame.X_comm hwX
           c₃_nx := hw_nx
           k_K₁ := hjK
           k_ord := hord2
           k_u := by rw [← a.ub_eq]; exact hju
           k_norm := hjN
           k_outer := a.frame.outer_of_not_fix hjN hjx hjX hwX hjw_ne
           k_L₁t := hk_L₁t
           K₁_x := fun b hb => a.K₁_comm_O hb a.x_O
           K₁_xt := fun b hb => a.K₁_comm_O hb a.xt_mem_O
           u₁_norm := a.u₁_norm h
           u₁_S5 := a.u₁_S5 h
           u₁_K₁t := fun b hb => a.u₁_K₁t htt h hb
           cent_x_xt := a.cent_x_xt htt h }⟩

end Core


section Dichotomy

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}

theorem PA11.exists_PA12_of_firstType (hb : PAB G L t E W z) (a : PA11 L t E z)
    (h : a.FirstType) : Nonempty (PA12 L t E z) := by
  have htt : t * t = 1 := hb.t_mul_t
  obtain ⟨w, j, hw3, hw1, hj2, hj1, hwu, hju, hjw⟩ := a.exists_wj
  have hw3g : (w : G) * ((w : G) * (w : G)) = 1 := congrArg Subtype.val hw3
  have hw1g : (w : G) ≠ 1 := fun h => hw1 (Subtype.ext h)
  have hj2g : (j : G) * (j : G) = 1 := congrArg Subtype.val hj2
  have hj1g : (j : G) ≠ 1 := fun h => hj1 (Subtype.ext h)
  have hjwg : (j : G) * (w : G) * (j : G)⁻¹ = (w : G)⁻¹ := congrArg Subtype.val hjw
  obtain ⟨b, hbX, c, hcX, hwbc⟩ := a.w_decomp hb w.2 hw3g hwu
  have hjx : (j : G) * a.x = a.x * j := a.K₁_comm_O j.2 a.x_O
  have hjxt : (j : G) * (t * a.x * t⁻¹) = (t * a.x * t⁻¹) * j := a.K₁_comm_O j.2 a.xt_mem_O
  have hjCen : (j : G) ∈ Cen a.ub := mem_Cen.2 hju
  have hjN : (j : G) ∈ normalizer (a.L₁ : Set G) := a.mem_normalizer_L₁ hb hjCen hjx
  have hjN' : (j : G) ∈ normalizer ((a.swapL hb).L₁ : Set G) :=
    (a.swapL hb).mem_normalizer_L₁ hb hjCen hjxt
  have hjX : ∀ g ∈ a.X, (j : G) * g * (j : G)⁻¹ ∈ a.X := fun g hg => a.conj_mem_X hjN hjx hg
  have hjXt : ∀ g ∈ conjSub t a.X, (j : G) * g * (j : G)⁻¹ ∈ conjSub t a.X :=
    fun g hg => (a.swapL hb).conj_mem_X hjN' hjxt hg
  have hbL : b ∈ a.L₁ := a.frame.X_mem_N hbX
  have hcL : c ∈ conjSub t a.L₁ := (a.swapL hb).frame.X_mem_N hcX
  have hbc : b * c = c * b := a.L₁_comm_conj hbL hcL
  have hb3 : b ^ 3 = 1 := a.frame.exp_three hbX
  have hc3 : c ^ 3 = 1 := (a.swapL hb).frame.exp_three hcX
  have hjbc : ((j : G) * b * (j : G)⁻¹) * ((j : G) * c * (j : G)⁻¹) = b⁻¹ * c⁻¹ := by
    calc ((j : G) * b * (j : G)⁻¹) * ((j : G) * c * (j : G)⁻¹)
        = (j : G) * (b * c) * (j : G)⁻¹ := by group
      _ = (j : G) * (w : G) * (j : G)⁻¹ := by rw [hwbc]
      _ = (w : G)⁻¹ := hjwg
      _ = b⁻¹ * c⁻¹ := by
        rw [hwbc, mul_inv_rev]
        exact ((Commute.inv_inv (show Commute b c from hbc)).eq).symm
  obtain ⟨hjb, hjc⟩ := a.decomp_unique (hjX b hbX) (a.X.inv_mem hbX) (hjXt c hcX)
    ((conjSub t a.X).inv_mem hcX) hjbc
  obtain ⟨c₀, hc₀, hcc₀⟩ := mem_conjSub.1 hcX
  have htc : t * c * t⁻¹ = c₀ := by rw [← hcc₀]; exact conj_conj_of_sq htt c₀
  have htb : t * b * t⁻¹ ∈ conjSub t a.X := conj_mem_conjSub hbX
  have hcomm_c0 : c₀ * (t * b * t⁻¹) = (t * b * t⁻¹) * c₀ :=
    a.L₁_comm_conj (a.frame.X_mem_N hc₀) (conj_mem_conjSub hbL)
  have htw : t * (w : G) * t⁻¹ = c₀ * (t * b * t⁻¹) := by
    rw [hwbc]
    calc t * (b * c) * t⁻¹ = (t * b * t⁻¹) * (t * c * t⁻¹) := by group
      _ = (t * b * t⁻¹) * c₀ := by rw [htc]
      _ = c₀ * (t * b * t⁻¹) := hcomm_c0.symm
  have hjtw : (j : G) * (t * (w : G) * t⁻¹) * (j : G)⁻¹ = t * (w : G) * t⁻¹ := by
    have := mem_centralizer_iff.1 (a.K₁_K₁t j.2) (t * (w : G) * t⁻¹) (conj_mem_conjSub w.2)
    rw [mul_inv_eq_iff_eq_mul]
    exact this.symm
  have hjcb : ((j : G) * c₀ * (j : G)⁻¹) * ((j : G) * (t * b * t⁻¹) * (j : G)⁻¹) =
      c₀ * (t * b * t⁻¹) := by
    calc ((j : G) * c₀ * (j : G)⁻¹) * ((j : G) * (t * b * t⁻¹) * (j : G)⁻¹)
        = (j : G) * (c₀ * (t * b * t⁻¹)) * (j : G)⁻¹ := by group
      _ = (j : G) * (t * (w : G) * t⁻¹) * (j : G)⁻¹ := by rw [htw]
      _ = c₀ * (t * b * t⁻¹) := by rw [hjtw, htw]
  obtain ⟨hjc₀, -⟩ := a.decomp_unique (hjX c₀ hc₀) hc₀ (hjXt _ htb) htb hjcb
  have hdich : b = 1 ∨ c = 1 := by
    by_contra hcon
    obtain ⟨hb1, hc1⟩ := not_or.1 hcon
    have hFix : a.X ⊓ Cen (j : G) = zpowers a.x := by
      refine eq_zpowers_of_card_nine a.X_card inf_le_left (y := a.x) (b := b) ?_ a.x_ord hbX ?_
      · exact Subgroup.mem_inf.2 ⟨a.frame.x_mem, mem_Cen.2 hjx.symm⟩
      · intro hbH
        have hbj := mem_Cen.1 (Subgroup.mem_inf.1 hbH).2
        have h1 : (j : G) * b * (j : G)⁻¹ = b := by
          rw [mul_inv_eq_iff_eq_mul]
          exact hbj.symm
        rw [hjb] at h1
        have hbb : b * b = 1 := eq_inv_iff_mul_eq_one.1 h1.symm
        apply hb1
        have := hb3
        rw [pow_three, hbb, mul_one] at this
        exact this
    have hc₀fix : c₀ ∈ a.X ⊓ Cen (j : G) :=
      Subgroup.mem_inf.2 ⟨hc₀, mem_Cen.2 (mul_inv_eq_iff_eq_mul.1 hjc₀).symm⟩
    rw [hFix] at hc₀fix
    obtain ⟨n, hn⟩ := mem_zpowers_iff.1 hc₀fix
    have hcxt : c = (t * a.x * t⁻¹) ^ n := by
      rw [← hcc₀, ← hn]
      exact map_zpow (MulAut.conj t) a.x n
    have hjc' : Commute (j : G) c := by
      rw [hcxt]
      exact Commute.zpow_right (show Commute (j : G) (t * a.x * t⁻¹) from hjxt) n
    have h5 : (j : G) * c * (j : G)⁻¹ = c := hjc'.mul_inv_cancel
    rw [hjc] at h5
    have hcc : c * c = 1 := eq_inv_iff_mul_eq_one.1 h5.symm
    apply hc1
    have := hc3
    rw [pow_three, hcc, mul_one] at this
    exact this
  rcases hdich with hb1 | hc1
  · have hwc : (w : G) = c := by rw [hwbc, hb1, one_mul]
    exact (a.swapL hb).exists_PA12_of_wj hb h (w := (w : G)) (j := (j : G)) w.2
      (by rw [hwc]; exact hcX) hw3g hw1g j.2 hj2g hj1g hju hjwg
  · have hwb : (w : G) = b := by rw [hwbc, hc1, mul_one]
    exact a.exists_PA12_of_wj hb h (w := (w : G)) (j := (j : G)) w.2
      (by rw [hwb]; exact hbX) hw3g hw1g j.2 hj2g hj1g hju hjwg

end Dichotomy

theorem s12 : StepS12 := by
  intro G _ _ L t E W z hb a
  rcases a.firstType_or hb with h | h
  · exact a.exists_PA12_of_firstType hb h
  · exact (a.swapU hb).exists_PA12_of_firstType hb h

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
