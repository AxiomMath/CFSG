module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbF17Y
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17Prod
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC18
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbF17b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17Cm

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

private lemma comm_of_conj_eq_self {a x : G} (h : a * x * a⁻¹ = x) : a * x = x * a := by
  calc a * x = (a * x * a⁻¹) * a := by group
    _ = x * a := by rw [h]

private lemma fourGrp_le_baseGrp (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    fourGrp x₁ x₂ ≤ baseGrp x₁ x₂ := by
  rw [(hc.wreath.fourGrp_eq_omega).1]
  exact (Subgroup.closure_le _).mpr (fun a ha => ha.1)

private lemma closure_pair_eq_sup_zpowers (a b : G) :
    Subgroup.closure ({a, b} : Set G) = Subgroup.zpowers a ⊔ Subgroup.zpowers b := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x (hx | hx)
    · rw [hx]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
    · rw [hx]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
  · rw [sup_le_iff]
    exact ⟨Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)),
      Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))⟩

private lemma u_z (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    (lam * t) * (x₁ * x₂) ^ 2 * (lam * t)⁻¹ = (x₁ * x₂) ^ 2 := by
  have ht : t * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * t :=
    (l17_cent_V hc ((x₁ * x₂) ^ 2) (Subgroup.subset_closure (by simp))).1
  calc (lam * t) * (x₁ * x₂) ^ 2 * (lam * t)⁻¹
      = lam * (t * (x₁ * x₂) ^ 2 * t⁻¹) * lam⁻¹ := by group
    _ = lam * (x₁ * x₂) ^ 2 * lam⁻¹ := by
          rw [show t * (x₁ * x₂) ^ 2 * t⁻¹ = (x₁ * x₂) ^ 2 by rw [ht]; group]
    _ = (x₁ * x₂) ^ 2 := l17_lam_z hc

private lemma u_y (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    (lam * t) * x₁ ^ 2 * (lam * t)⁻¹ = x₁ ^ 2 * (x₁ * x₂) ^ 2 := by
  have ht : t * x₁ ^ 2 = x₁ ^ 2 * t :=
    (l17_cent_V hc (x₁ ^ 2) (Subgroup.subset_closure (by simp))).1
  calc (lam * t) * x₁ ^ 2 * (lam * t)⁻¹ = lam * (t * x₁ ^ 2 * t⁻¹) * lam⁻¹ := by group
    _ = lam * x₁ ^ 2 * lam⁻¹ := by
          rw [show t * x₁ ^ 2 * t⁻¹ = x₁ ^ 2 by rw [ht]; group]
    _ = x₁ ^ 2 * (x₁ * x₂) ^ 2 := l17_lam_y hc

private lemma u_normalizes_V (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    ∀ v ∈ fourGrp x₁ x₂, (lam * t) * v * (lam * t)⁻¹ ∈ fourGrp x₁ x₂ := by
  intro v hv
  have htM : t ∈ ctxM t tau x₁ x₂ := by
    rw [hc.M_eq]
    exact Subgroup.mem_sup_left (l17_mem_O hc).1
  have hlamM : lam ∈ ctxM t tau x₁ x₂ := by
    rw [hc.M_eq]
    exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  exact hc.normal_V.2 (lam * t) (Subgroup.mul_mem _ hlamM htM) v hv

theorem k18_W_eq (hc : Ctx13 t L S x₁ x₂ lam rho tau om) {V' : Subgroup G} {v₁ v₂ : G}
    (hV : Ctx13V t tau x₁ x₂ lam rho om V' v₁ v₂) :
    ctxYq t tau x₁ x₂ rho ⊓ centralizer ({lam * t} : Set G) = closure {(x₁ * x₂) ^ 2, v₁} := by
  obtain ⟨_, _, hVQ, hVbase, _, hVu, hVY, hVfix, hv₁V, hv₁ne, _, _, _, _, _, _, _, _, _⟩ := hV
  have hV_le_base : fourGrp x₁ x₂ ≤ baseGrp x₁ x₂ := fourGrp_le_baseGrp hc
  have hzV : (x₁ * x₂) ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hyV : x₁ ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hz_ne : (x₁ * x₂) ^ 2 ≠ 1 := (l17_yz_ne hc).2.1
  have hzY : (x₁ * x₂) ^ 2 ∈ ctxYq t tau x₁ x₂ rho := l17_V_le_Y hc hzV
  have hzcent : (x₁ * x₂) ^ 2 ∈ centralizer ({lam * t} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact comm_of_conj_eq_self (u_z hc)
  have hzW : (x₁ * x₂) ^ 2 ∈
      ctxYq t tau x₁ x₂ rho ⊓ centralizer ({lam * t} : Set G) := ⟨hzY, hzcent⟩
  have hv₁Y : v₁ ∈ ctxYq t tau x₁ x₂ rho := by
    rw [hVY]
    exact Subgroup.mem_sup_right hv₁V
  have hv₁cent : v₁ ∈ centralizer ({lam * t} : Set G) := by
    have h : v₁ ∈ V' ⊓ centralizer ({lam * t} : Set G) := by
      rw [hVfix]
      exact Subgroup.mem_zpowers v₁
    exact h.2
  have hv₁W : v₁ ∈ ctxYq t tau x₁ x₂ rho ⊓ centralizer ({lam * t} : Set G) :=
    ⟨hv₁Y, hv₁cent⟩
  have hcl : closure ({(x₁ * x₂) ^ 2, v₁} : Set G) =
      zpowers ((x₁ * x₂) ^ 2) ⊔ zpowers v₁ := closure_pair_eq_sup_zpowers _ _
  refine le_antisymm ?_ ?_
  · intro w hw
    have hwY : w ∈ ctxYq t tau x₁ x₂ rho := hw.1
    have hwcent : w ∈ centralizer ({lam * t} : Set G) := hw.2
    have hnorm : ∀ k ∈ V', ∀ h ∈ fourGrp x₁ x₂, k * h * k⁻¹ ∈ fourGrp x₁ x₂ := by
      intro k hk h hh
      have hkQ : k ∈ ctxQ t tau x₁ x₂ rho := by
        rw [hVQ]
        exact Subgroup.mem_sup_right hk
      have hhQ : h ∈ ctxQ t tau x₁ x₂ rho := hc.base_le_Q (hV_le_base hh)
      have hcomm := IsZ4Z4E4.comm hc.q_iso hkQ hhQ
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
      exact hh
    have hw_sup : w ∈ fourGrp x₁ x₂ ⊔ V' := by rwa [hVY] at hwY
    obtain ⟨a, ha, b, hb, hwab⟩ :=
      (mem_sup_iff_of_normalizes (H := fourGrp x₁ x₂) (K := V') hnorm).mp hw_sup
    have huw : lam * t * w = w * (lam * t) :=
      (Subgroup.mem_centralizer_iff.mp hwcent) (lam * t) (Set.mem_singleton _)
    have huwconj : (lam * t) * w * (lam * t)⁻¹ = w := by rw [huw]; group
    have h1 : ((lam * t) * a * (lam * t)⁻¹) * ((lam * t) * b * (lam * t)⁻¹) = a * b := by
      have h : (lam * t) * (a * b) * (lam * t)⁻¹ = a * b := by
        rw [← hwab]
        exact huwconj
      calc ((lam * t) * a * (lam * t)⁻¹) * ((lam * t) * b * (lam * t)⁻¹)
          = (lam * t) * (a * b) * (lam * t)⁻¹ := by group
        _ = a * b := h
    set a' : G := (lam * t) * a * (lam * t)⁻¹ with ha'_def
    set b' : G := (lam * t) * b * (lam * t)⁻¹ with hb'_def
    have ha'V : a' ∈ fourGrp x₁ x₂ := by rw [ha'_def]; exact u_normalizes_V hc a ha
    have hb'V : b' ∈ V' := by
      rw [hb'_def]
      exact (Subgroup.mem_normalizer_iff.mp hVu b).mp hb
    have h1' : a' * b' = a * b := by rw [ha'_def, hb'_def]; exact h1
    have hVV'bot : fourGrp x₁ x₂ ⊓ V' ≤ (⊥ : Subgroup G) :=
      (inf_le_inf hV_le_base le_rfl).trans (le_of_eq hVbase)
    have haa : a' = a := by
      have hmemV : a⁻¹ * a' ∈ fourGrp x₁ x₂ :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ ha) ha'V
      have hmemV' : a⁻¹ * a' ∈ V' := by
        have heq : a⁻¹ * a' = b * b'⁻¹ := by
          calc a⁻¹ * a' = a⁻¹ * (a' * b') * b'⁻¹ := by group
            _ = a⁻¹ * (a * b) * b'⁻¹ := by rw [h1']
            _ = b * b'⁻¹ := by group
        rw [heq]
        exact Subgroup.mul_mem _ hb (Subgroup.inv_mem _ hb'V)
      have hbot : a⁻¹ * a' = 1 := Subgroup.mem_bot.mp (hVV'bot ⟨hmemV, hmemV'⟩)
      exact (inv_mul_eq_one.mp hbot).symm
    have hbb : b' = b := by
      have h := h1'
      rw [haa] at h
      exact mul_left_cancel h
    have hbzpow : b ∈ zpowers v₁ := by
      have hub : (lam * t) * b * (lam * t)⁻¹ = b := by rw [← hb'_def]; exact hbb
      have hbu : (lam * t) * b = b * (lam * t) := comm_of_conj_eq_self hub
      have hbc : b ∈ centralizer ({lam * t} : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact hbu
      have hmem : b ∈ V' ⊓ centralizer ({lam * t} : Set G) := ⟨hb, hbc⟩
      rwa [hVfix] at hmem
    have hyz_comm : x₁ ^ 2 * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * x₁ ^ 2 := by
      haveI : IsMulCommutative ↥(fourGrp x₁ x₂) := (l17_V_elem hc).1
      have h := mul_comm' (⟨x₁ ^ 2, hyV⟩ : ↥(fourGrp x₁ x₂))
        (⟨(x₁ * x₂) ^ 2, hzV⟩ : ↥(fourGrp x₁ x₂))
      simpa using congrArg Subtype.val h
    have hy2 : (x₁ ^ 2) * (x₁ ^ 2) = 1 := by
      simpa [pow_two] using (l17_V_elem hc).2 (x₁ ^ 2) hyV
    have hz2 : (x₁ * x₂) ^ 2 * (x₁ * x₂) ^ 2 = 1 := by
      simpa [pow_two] using (l17_V_elem hc).2 ((x₁ * x₂) ^ 2) hzV
    have hcases : a = 1 ∨ a = x₁ ^ 2 ∨ a = (x₁ * x₂) ^ 2 ∨
        a = x₁ ^ 2 * (x₁ * x₂) ^ 2 :=
      (mem_closure_pair_of_invol (a := x₁ ^ 2) (b := (x₁ * x₂) ^ 2) (x := a)
        hy2 hz2 hyz_comm).mp ha
    have ha_zpow : a ∈ zpowers ((x₁ * x₂) ^ 2) := by
      rcases hcases with rfl | rfl | rfl | rfl
      · exact Subgroup.one_mem _
      · exfalso
        have huy : (lam * t) * x₁ ^ 2 * (lam * t)⁻¹ = x₁ ^ 2 * (x₁ * x₂) ^ 2 := u_y hc
        have hconj : (lam * t) * x₁ ^ 2 * (lam * t)⁻¹ = x₁ ^ 2 := by
          rw [← ha'_def]; exact haa
        rw [huy] at hconj
        exact hz_ne (mul_left_cancel (by rw [hconj, mul_one]))
      · exact Subgroup.mem_zpowers _
      · exfalso
        have hconj : (lam * t) * (x₁ ^ 2 * (x₁ * x₂) ^ 2) * (lam * t)⁻¹ =
            x₁ ^ 2 * (x₁ * x₂) ^ 2 := by rw [← ha'_def]; exact haa
        have huy : (lam * t) * x₁ ^ 2 * (lam * t)⁻¹ = x₁ ^ 2 * (x₁ * x₂) ^ 2 := u_y hc
        have huz : (lam * t) * (x₁ * x₂) ^ 2 * (lam * t)⁻¹ = (x₁ * x₂) ^ 2 := u_z hc
        have hmul : (lam * t) * (x₁ ^ 2 * (x₁ * x₂) ^ 2) * (lam * t)⁻¹ =
            (x₁ ^ 2 * (x₁ * x₂) ^ 2) * (x₁ * x₂) ^ 2 := by
          rw [show (lam * t) * (x₁ ^ 2 * (x₁ * x₂) ^ 2) * (lam * t)⁻¹ =
            ((lam * t) * x₁ ^ 2 * (lam * t)⁻¹) *
              ((lam * t) * (x₁ * x₂) ^ 2 * (lam * t)⁻¹) by group, huy, huz]
        rw [hmul] at hconj
        exact hz_ne (mul_left_cancel (by rw [hconj, mul_one]))
    have hwz : w ∈ zpowers ((x₁ * x₂) ^ 2) ⊔ zpowers v₁ := by
      rw [hwab]
      exact Subgroup.mul_mem_sup ha_zpow hbzpow
    rw [hcl]
    exact hwz
  · rw [hcl]
    refine sup_le ?_ ?_
    · exact Subgroup.zpowers_le.mpr hzW
    · exact Subgroup.zpowers_le.mpr hv₁W

theorem k18_W_card (hc : Ctx13 t L S x₁ x₂ lam rho tau om) {V' : Subgroup G} {v₁ v₂ : G}
    (hV : Ctx13V t tau x₁ x₂ lam rho om V' v₁ v₂) :
    Nat.card ↥(ctxYq t tau x₁ x₂ rho ⊓ centralizer ({lam * t} : Set G)) = 4 := by
  have hVc : Ctx13V t tau x₁ x₂ lam rho om V' v₁ v₂ := hV
  obtain ⟨hV1, _, hVQ, hVbase, _, _, _, _, hv₁V, hv₁ne, _, _, _, _, _, _, _, _, _⟩ := hV
  have hV_le_base : fourGrp x₁ x₂ ≤ baseGrp x₁ x₂ := fourGrp_le_baseGrp hc
  have hzV : (x₁ * x₂) ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hz_ne : (x₁ * x₂) ^ 2 ≠ 1 := (l17_yz_ne hc).2.1
  have hz2 : (x₁ * x₂) ^ 2 * (x₁ * x₂) ^ 2 = 1 := by
    simpa [pow_two] using (l17_V_elem hc).2 ((x₁ * x₂) ^ 2) hzV
  have hv2 : v₁ * v₁ = 1 := by simpa [pow_two] using hV1.2 v₁ hv₁V
  have hzord : orderOf ((x₁ * x₂) ^ 2) = 2 :=
    orderOf_eq_prime (p := 2) (by simpa [pow_two] using hz2) hz_ne
  have hvord : orderOf v₁ = 2 :=
    orderOf_eq_prime (p := 2) (by simpa [pow_two] using hv2) hv₁ne
  have hzpowV : zpowers ((x₁ * x₂) ^ 2) ≤ fourGrp x₁ x₂ := Subgroup.zpowers_le.mpr hzV
  have hvpowV' : zpowers v₁ ≤ V' := Subgroup.zpowers_le.mpr hv₁V
  have hbot : zpowers ((x₁ * x₂) ^ 2) ⊓ zpowers v₁ = ⊥ := by
    apply le_bot_iff.mp
    exact (inf_le_inf (hzpowV.trans hV_le_base) hvpowV').trans (le_of_eq hVbase)
  have hnorm : ∀ k ∈ zpowers v₁, ∀ h ∈ zpowers ((x₁ * x₂) ^ 2),
      k * h * k⁻¹ ∈ zpowers ((x₁ * x₂) ^ 2) := by
    intro k hk h hh
    have hkQ : k ∈ ctxQ t tau x₁ x₂ rho := by
      rw [hVQ]
      exact Subgroup.mem_sup_right (hvpowV' hk)
    have hhQ : h ∈ ctxQ t tau x₁ x₂ rho := hc.base_le_Q (hV_le_base (hzpowV hh))
    have hcomm := IsZ4Z4E4.comm hc.q_iso hkQ hhQ
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    exact hh
  rw [k18_W_eq hc hVc, closure_pair_eq_sup_zpowers]
  rw [card_sup_eq_mul (H := zpowers ((x₁ * x₂) ^ 2)) (K := zpowers v₁) hnorm hbot]
  rw [Nat.card_zpowers, Nat.card_zpowers, hzord, hvord]

theorem k18_W_elem (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    CFSG.Open.IsElemAbelian 2 (ctxYq t tau x₁ x₂ rho ⊓ centralizer ({lam * t} : Set G)) := by
  have hY := l17_Y_elem hc
  refine ⟨?_, ?_⟩
  · refine IsMulCommutative.of_comm ?_
    intro x y
    apply Subtype.ext
    show (x : G) * (y : G) = (y : G) * (x : G)
    have hxY : (x : G) ∈ ctxYq t tau x₁ x₂ rho := x.2.1
    have hyY : (y : G) ∈ ctxYq t tau x₁ x₂ rho := y.2.1
    haveI : IsMulCommutative ↥(ctxYq t tau x₁ x₂ rho) := hY.1
    have hcomm := mul_comm' (⟨x, hxY⟩ : ↥(ctxYq t tau x₁ x₂ rho))
      (⟨y, hyY⟩ : ↥(ctxYq t tau x₁ x₂ rho))
    simpa using congrArg Subtype.val hcomm
  · intro x hx
    exact hY.2 x hx.1

theorem k18_W_ne_V (hc : Ctx13 t L S x₁ x₂ lam rho tau om) {V' : Subgroup G} {v₁ v₂ : G}
    (hV : Ctx13V t tau x₁ x₂ lam rho om V' v₁ v₂) :
    ctxYq t tau x₁ x₂ rho ⊓ centralizer ({lam * t} : Set G) ≠ fourGrp x₁ x₂ := by
  obtain ⟨_, _, _, hVbase, _, _, hVY, hVfix, hv₁V, hv₁ne, _, _, _, _, _, _, _, _, _⟩ := hV
  intro hEq
  have hV_le_base : fourGrp x₁ x₂ ≤ baseGrp x₁ x₂ := fourGrp_le_baseGrp hc
  have hv₁Y : v₁ ∈ ctxYq t tau x₁ x₂ rho := by
    rw [hVY]
    exact Subgroup.mem_sup_right hv₁V
  have hv₁cent : v₁ ∈ centralizer ({lam * t} : Set G) := by
    have h : v₁ ∈ V' ⊓ centralizer ({lam * t} : Set G) := by
      rw [hVfix]
      exact Subgroup.mem_zpowers v₁
    exact h.2
  have hv₁W : v₁ ∈ ctxYq t tau x₁ x₂ rho ⊓ centralizer ({lam * t} : Set G) :=
    ⟨hv₁Y, hv₁cent⟩
  rw [hEq] at hv₁W
  have hbot : v₁ ∈ (⊥ : Subgroup G) := by
    rw [← hVbase]
    exact ⟨hV_le_base hv₁W, hv₁V⟩
  exact hv₁ne (Subgroup.mem_bot.mp hbot)

theorem k18_W_tG (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    ∀ g : G, ∀ w ∈ ctxYq t tau x₁ x₂ rho ⊓ centralizer ({lam * t} : Set G),
      g * t * g⁻¹ ≠ w := by
  intro g w hw h
  have hwY : w ∈ ctxYq t tau x₁ x₂ rho := (Subgroup.mem_inf.mp hw).1
  rw [← h] at hwY
  exact l17_tG_not_mem_Y hc g hwY

theorem k18_W_normal (hc : Ctx18S t L S x₁ x₂ lam rho tau om 𝒮) :
    ctxYq t tau x₁ x₂ rho ⊓ centralizer ({lam * t} : Set G) ≤
        𝒮 ⊓ centralizer ({lam * t} : Set G) ∧
      ∀ d ∈ 𝒮 ⊓ centralizer ({lam * t} : Set G),
        ∀ w ∈ ctxYq t tau x₁ x₂ rho ⊓ centralizer ({lam * t} : Set G),
          d * w * d⁻¹ ∈ ctxYq t tau x₁ x₂ rho ⊓ centralizer ({lam * t} : Set G) := by
  have hYS : ctxYq t tau x₁ x₂ rho ≤ 𝒮 :=
    ctxYq_le_ctxQ.trans ((l17_Q_le_O hc.toCtx13).trans (le_sup_left.trans hc.U_le))
  refine ⟨le_inf (inf_le_left.trans hYS) inf_le_right, ?_⟩
  intro d hd w hw
  have hdS : d ∈ 𝒮 := hd.1
  have hdcent : d ∈ centralizer ({lam * t} : Set G) := hd.2
  have hwY : w ∈ ctxYq t tau x₁ x₂ rho := hw.1
  have hwcent : w ∈ centralizer ({lam * t} : Set G) := hw.2
  have hdK : d ∈ ctxK t tau x₁ x₂ rho := hc.sylow.1 hdS
  have hdwY : d * w * d⁻¹ ∈ ctxYq t tau x₁ x₂ rho :=
    l17_K_normalizes_Y hc.toCtx13 d hdK w hwY
  have hdcomm : (lam * t) * d = d * (lam * t) :=
    (Subgroup.mem_centralizer_iff.mp hdcent) (lam * t) (Set.mem_singleton _)
  have hwcomm : (lam * t) * w = w * (lam * t) :=
    (Subgroup.mem_centralizer_iff.mp hwcent) (lam * t) (Set.mem_singleton _)
  have hdconj : (lam * t) * d * (lam * t)⁻¹ = d := by rw [hdcomm]; group
  have hwconj : (lam * t) * w * (lam * t)⁻¹ = w := by rw [hwcomm]; group
  have hconj : (lam * t) * (d * w * d⁻¹) * (lam * t)⁻¹ = d * w * d⁻¹ := by
    rw [show (lam * t) * (d * w * d⁻¹) * (lam * t)⁻¹ =
      ((lam * t) * d * (lam * t)⁻¹) * ((lam * t) * w * (lam * t)⁻¹) *
        ((lam * t) * d * (lam * t)⁻¹)⁻¹ by group]
    rw [hdconj, hwconj]
  have hdwcent : d * w * d⁻¹ ∈ centralizer ({lam * t} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact comm_of_conj_eq_self hconj
  exact ⟨hdwY, hdwcent⟩

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
