module

public import CFSG.LargeExtraspecial.S12InspFamER3a
public import CFSG.LargeExtraspecial.S12InspFamEF3

public section

namespace CFSG.LargeExtraspecial

namespace S12InspF3

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Fischer.Classification

variable {m : ℕ} {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}

variable (f) in
@[expose] def HIso : Prop :=
  ∀ a b, f a a = 1 → f b b = 1 → f a b = 0 → ∃ z, z ≠ 0 ∧ f z z = 0 ∧ f z a = 0 ∧ f z b = 0

theorem eq_or_eq_neg_of_refl_mul_refl_eq_one {w w' : Fin m → ZMod 3} (hw : f w w = 1)
    (hw' : f w' w' = 1) (h : F3.refl f w * F3.refl f w' = 1) : w' = w ∨ w' = -w := by
  refine (F3.refl_eq_refl_iff hw hw').1 ?_
  calc F3.refl f w = F3.refl f w * (F3.refl f w' * F3.refl f w') := by
        rw [F3.refl_mul_self, mul_one]
    _ = F3.refl f w' := by rw [← mul_assoc, h, one_mul]

theorem normal_two_eq_bot (hf : IsF3Form f) (hm : 4 ≤ m) (hiso : HIso f) (N : Subgroup (R3 f))
    (hN : N.Normal) (h2 : IsPGroup 2 N) : N = ⊥ := by
  classical
  set R := F3.reflGroup f with hRdef
  set π : R →* R3 f := QuotientGroup.mk' (Subgroup.center R) with hπdef
  have hZ : ∀ z : R, z ∈ Subgroup.center R → (z : GL (Fin m) (ZMod 3)) = 1 ∨
      (z : GL (Fin m) (ZMod 3)) = -1 := fun z hz => F3.coe_eq_of_mem_center hf hm hz
  have hker : ∀ z : R, π z = 1 ↔ z ∈ Subgroup.center R := fun z => by
    rw [hπdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hconj : ∀ g c : R, π c ∈ N → π (g * c * g⁻¹) ∈ N := fun g c hc => by
    rw [map_mul, map_mul, map_inv]
    exact hN.conj_mem _ hc _
  have h3el : ∀ c : R, π c ∈ N → c ^ 3 = 1 → c = 1 := by
    intro c hc hc3
    obtain ⟨k, hk⟩ := h2 ⟨π c, hc⟩
    have hk' : c ^ 2 ^ k ∈ Subgroup.center R := by
      rw [← hker, map_pow]
      exact congrArg Subtype.val hk
    have hc2 : c ^ 2 ^ (k + 1) = 1 := by
      rw [pow_succ, pow_mul]
      apply Subtype.ext
      rw [Subgroup.coe_pow, OneMemClass.coe_one]
      rcases hZ _ hk' with h | h
      · rw [h, one_pow]
      · rw [h, neg_one_sq]
    have hd : orderOf c ∣ Nat.gcd 3 (2 ^ (k + 1)) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hc3) (orderOf_dvd_of_pow_eq_one hc2)
    rw [(Nat.Coprime.pow_right _ (by norm_num : Nat.Coprime 3 2)).gcd_eq_one,
      Nat.dvd_one, orderOf_eq_one_iff] at hd
    exact hd
  have hr : ∀ v, (reflElt f v)⁻¹ = reflElt f v := fun v =>
    inv_eq_of_mul_eq_one_right (Subtype.ext (F3.refl_mul_self v))
  have key : ∀ y : R, π y ∈ N → (y : GL (Fin m) (ZMod 3)) = 1 ∨ (y : GL (Fin m) (ZMod 3)) = -1 := by
    intro y hy
    have hiy := F3.isIsom_of_mem hf y.2
    refine F3.eq_one_or_eq_neg_one hf hm hiy fun w hw => ?_
    by_contra hne
    push Not at hne
    obtain ⟨hne1, hne2⟩ := hne
    set w' := F3.act (y : GL (Fin m) (ZMod 3)) w with hw'def
    have hw' : f w' w' = 1 := by rw [hw'def, hiy.norm, hw]
    obtain ⟨c₁, hc₁def⟩ : ∃ c₁ : R, c₁ = reflElt f w * y * reflElt f w * y⁻¹ := ⟨_, rfl⟩
    have hc₁ : π c₁ ∈ N := by
      have h1 := hconj (reflElt f w) y hy
      rw [hr] at h1
      rw [hc₁def, map_mul]
      exact N.mul_mem h1 (by rw [map_inv]; exact N.inv_mem hy)
    have hc₁GL : (c₁ : GL (Fin m) (ZMod 3)) = F3.refl f w * F3.refl f w' := by
      rw [hc₁def]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_reflElt]
      rw [mul_assoc (F3.refl f w * _), mul_assoc (F3.refl f w), ← mul_assoc _ (F3.refl f w),
        F3.conj_refl hiy]
    rcases eq_or_ne (f w w') 0 with h0 | h0
    ·
      obtain ⟨z, hz0, hzz, hzw, hzw'⟩ := hiso w w' hw hw' h0
      have hw'w : f w' w = 0 := by rw [hf.symm]; exact h0
      have hc : f (w' + z) (w' + z) = 1 := by
        rw [F3.norm_add hf, hw', hzz, hf.symm w' z, hzw']
        ring
      have hcw : f (w' + z) w = 0 := by
        rw [LinearMap.BilinForm.add_left, hw'w, hzw, add_zero]
      have hw'c : f w' (w' + z) = 1 := by
        rw [LinearMap.BilinForm.add_right, hw', hf.symm w' z, hzw', add_zero]
      set c := w' + z with hcdef
      set b' := F3.act (F3.refl f c) w' with hb'def
      have hb' : f b' b' = 1 := by
        rw [hb'def, (F3.isIsom_refl hf c).norm, hw']
      have hb'eq : b' = w' + c := by
        rw [hb'def, F3.act_refl hc, hf.symm w' c, show f c w' = 1 by rw [hf.symm]; exact hw'c,
          one_smul]
      have hw'b' : f w' b' = 2 := by
        rw [hb'eq, LinearMap.BilinForm.add_right, hw', hw'c]
        rfl
      have hc₂ := hconj (reflElt f c) _ hc₁
      have hc₃ := N.mul_mem hc₁ hc₂
      rw [← map_mul] at hc₃
      have hc₃GL : ((c₁ * (reflElt f c * c₁ * (reflElt f c)⁻¹) : R) :
            GL (Fin m) (ZMod 3)) = F3.refl f w' * F3.refl f b' := by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, hc₁GL, hr, coe_reflElt]
        have e1 : F3.refl f c * (F3.refl f w * F3.refl f w') * F3.refl f c =
            F3.refl f w * F3.refl f b' := by
          have h1 := F3.conj_refl (F3.isIsom_refl hf c) w
          have h2 := F3.conj_refl (F3.isIsom_refl hf c) w'
          rw [F3.refl_inv] at h1 h2
          have hwc : f w c = 0 := by rw [hf.symm]; exact hcw
          rw [F3.act_refl hc, hwc, zero_smul, add_zero] at h1
          rw [← hb'def] at h2
          calc F3.refl f c * (F3.refl f w * F3.refl f w') * F3.refl f c =
              (F3.refl f c * F3.refl f w * F3.refl f c) *
                (F3.refl f c * F3.refl f w' * F3.refl f c) := by
                rw [show F3.refl f c * F3.refl f w * F3.refl f c * (F3.refl f c *
                  F3.refl f w' * F3.refl f c) = F3.refl f c * F3.refl f w *
                  (F3.refl f c * F3.refl f c) * F3.refl f w' * F3.refl f c by group,
                  F3.refl_mul_self, mul_one]
                group
            _ = F3.refl f w * F3.refl f b' := by rw [h1, h2]
        rw [e1]
        have hcomm : F3.refl f w * F3.refl f w' = F3.refl f w' * F3.refl f w :=
          (F3.refl_commute_iff hf hw hw').2 (Or.inl h0)
        calc F3.refl f w * F3.refl f w' * (F3.refl f w * F3.refl f b') =
            F3.refl f w' * (F3.refl f w * F3.refl f w) * F3.refl f b' := by
              rw [hcomm]
              group
          _ = F3.refl f w' * F3.refl f b' := by rw [F3.refl_mul_self, mul_one]
      have h3 := h3el _ hc₃ (Subtype.ext (by
        rw [Subgroup.coe_pow, hc₃GL, OneMemClass.coe_one]
        exact F3.refl_mul_refl_pow_three hf hw' hb' (by rw [hw'b']; decide)))
      have h4 : F3.refl f w' * F3.refl f b' = 1 := by
        rw [← hc₃GL, h3]
        rfl
      obtain ⟨u, hu⟩ : ∃ u, f u z ≠ 0 := by
        by_contra! hu
        exact hz0 (hf.nondeg z fun u => by rw [hf.symm]; exact hu u)
      have hub' : f u b' = f u w' + f u w' + f u z := by
        rw [hb'eq, hcdef, LinearMap.BilinForm.add_right, LinearMap.BilinForm.add_right, add_assoc]
      rcases eq_or_eq_neg_of_refl_mul_refl_eq_one hw' hb' h4 with h | h
      · rw [h, hw'] at hw'b'
        exact absurd hw'b' (by decide)
      · rw [h, LinearMap.BilinForm.neg_right] at hub'
        apply hu
        linear_combination -hub' - f u w' * F3.three_eq_zero
    ·
      have h3 := h3el _ hc₁ (Subtype.ext (by
        rw [Subgroup.coe_pow, hc₁GL, OneMemClass.coe_one]
        exact F3.refl_mul_refl_pow_three hf hw hw' h0))
      have h4 : F3.refl f w * F3.refl f w' = 1 := by
        rw [← hc₁GL, h3]
        rfl
      rcases eq_or_eq_neg_of_refl_mul_refl_eq_one hw hw' h4 with h | h
      · exact hne1 h
      · exact hne2 h
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center R) x
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  refine Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  rcases key y hx with h | h
  · rw [h, one_mul, mul_one]
  · rw [h, neg_one_mul, mul_neg_one]

theorem reflBar_eq_of_refl_eq {v w : Fin m → ZMod 3} (h : F3.refl f v = F3.refl f w) :
    reflBar f v = reflBar f w := by
  rw [reflBar_def, reflBar_def]
  congr 1
  exact Subtype.ext h

theorem mul_mem_fischerQ_D3 (hf : IsF3Form f) (hm : 4 ≤ m) (hiso : HIso f) :
    ∀ d ∈ D3 f, ∀ e ∈ D3 f, d * e ∈ fischerQ (D3 f) := by
  have hP := pair_R3 hf hm
  obtain ⟨a₀, ha₀⟩ := F3.exists_norm_eq hf (by omega) (one_ne_zero (α := ZMod 3))
  obtain ⟨c, hc, hca⟩ := F3.exists_norm_eq_perp hf (by omega) ha₀ (one_ne_zero (α := ZMod 3))
  obtain ⟨z, hz0, hzz, hza, hzc⟩ := hiso a₀ c ha₀ hc (by rw [hf.symm]; exact hca)
  have hb₀ : f (a₀ + z) (a₀ + z) = 1 := by
    rw [F3.norm_add hf, ha₀, hzz, hf.symm a₀ z, hza]
    ring
  have hab₀ : f a₀ (a₀ + z) = 1 := by
    rw [LinearMap.BilinForm.add_right, ha₀, hf.symm a₀ z, hza, add_zero]
  have hcb₀ : f c (a₀ + z) = 0 := by
    rw [LinearMap.BilinForm.add_right, hca, hf.symm c z, hzc, add_zero]
  have hne : ∀ {u v : Fin m → ZMod 3}, f u u = 1 → f v v = 1 → f u v = 0 →
      reflBar f u ≠ reflBar f v := fun {u v} hu hv huv h => by
    rcases (reflBar_eq_reflBar_iff hf hm hu hv).1 h with h' | h'
    · rw [h', hu] at huv
      exact one_ne_zero huv
    · rw [h', LinearMap.BilinForm.neg_right, hu] at huv
      exact one_ne_zero (neg_eq_zero.1 huv)
  have hgood : reflBar f a₀ * reflBar f (a₀ + z) ∈ fischerQ (D3 f) := by
    have hac : f a₀ c = 0 := by rw [hf.symm]; exact hca
    have h1 := mul_mem_fischerQ (reflBar_mem_D3 ha₀) (reflBar_mem_D3 hc) (hne ha₀ hc hac)
      ((reflBar_commute_iff hf hm ha₀ hc).2 (Or.inl hac))
    have h2 := mul_mem_fischerQ (reflBar_mem_D3 hc) (reflBar_mem_D3 hb₀) (hne hc hb₀ hcb₀)
      ((reflBar_commute_iff hf hm hc hb₀).2 (Or.inl hcb₀))
    have h3 := (fischerQ (D3 f)).mul_mem h1 h2
    rwa [mul_assoc, ← mul_assoc (reflBar f c), reflBar_mul_self, one_mul] at h3
  have hnc₀ : F3.refl f a₀ * F3.refl f (a₀ + z) ≠ F3.refl f (a₀ + z) * F3.refl f a₀ := by
    rw [Ne, F3.refl_commute_iff hf ha₀ hb₀]
    push Not
    refine ⟨by rw [hab₀]; exact one_ne_zero, fun h => hz0 ?_, fun h => ?_⟩
    · have := congrArg (· - a₀) h
      simpa using this
    · have := congrArg (fun x => f x a₀) h
      simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.neg_left, ha₀, hza,
        add_zero] at this
      exact absurd this (by decide)
  intro d hd e he
  obtain ⟨a, ha, rfl⟩ := mem_D3_iff.1 hd
  obtain ⟨b, hb, rfl⟩ := mem_D3_iff.1 he
  by_cases hab : reflBar f a * reflBar f b = reflBar f b * reflBar f a
  · by_cases hne' : reflBar f a = reflBar f b
    · rw [hne', reflBar_mul_self]
      exact one_mem _
    · exact mul_mem_fischerQ (reflBar_mem_D3 ha) (reflBar_mem_D3 hb) hne' hab
  · have hnc : F3.refl f a * F3.refl f b ≠ F3.refl f b * F3.refl f a := by
      intro h
      apply hab
      rw [reflBar_def, reflBar_def, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext h
    obtain ⟨g, hg, hga, hgb⟩ :=
      Recognition.R3.exists_conj_refl_pair hf hm ha₀ hb₀ ha hb hnc₀ hnc
    have hiso_g := F3.isIsom_of_mem hf hg
    have h1 := conj_mem_fischerQ (m := ((⟨g, hg⟩ : F3.reflGroup f) : R3 f))
      (fun e he => CFSG.Fischer.Pair.conj_mem hP he _) hgood
    have ha' : reflBar f (F3.act g a₀) = reflBar f a :=
      reflBar_eq_of_refl_eq (by rw [← F3.conj_refl hiso_g, hga])
    have hb' : reflBar f (F3.act g (a₀ + z)) = reflBar f b :=
      reflBar_eq_of_refl_eq (by rw [← F3.conj_refl hiso_g, hgb])
    have hsplit : ((⟨g, hg⟩ : F3.reflGroup f) : R3 f) * (reflBar f a₀ * reflBar f (a₀ + z)) *
        ((⟨g, hg⟩ : F3.reflGroup f) : R3 f)⁻¹ = reflBar f a * reflBar f b := by
      rw [← ha', ← hb', ← mk_conj_reflBar hf ⟨g, hg⟩ a₀, ← mk_conj_reflBar hf ⟨g, hg⟩ (a₀ + z)]
      group
    rwa [hsplit] at h1

theorem T_iterate_one_left : Recognition.R3.T^[1] (1, 2, 0) = (1, 4, 4) := by
  decide

theorem T_iterate_one_right : Recognition.R3.T^[1] (1, 0, 2) = (5, 2, 2) := by
  decide

theorem T_iterate_two_left : Recognition.R3.T^[2] (1, 2, 0) = (9, 6, 12) := by
  decide

theorem T_iterate_two_right : Recognition.R3.T^[2] (1, 0, 2) = (9, 12, 6) := by
  decide

theorem hIso_of_four {f : LinearMap.BilinForm (ZMod 3) (Fin 4 → ZMod 3)} (hf : IsF3Form f)
    (h15 : (D3 f).ncard = 15) : HIso f := by
  intro a b ha hb hab
  have h30 : Recognition.R3.normCount f 1 = 30 := by rw [← two_mul_ncard_D3 hf le_rfl, h15]
  let e₁ : F3.perpOne f b ≃ₗ[ZMod 3] (Fin 3 → ZMod 3) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [F3.finrank_perpOne hb, Module.finrank_fin_fun])
  have hf₁ := isF3Form_restrictForm hf hb e₁
  have hs₁ := Recognition.R3.normCount_eq (n := 3) hf hb e₁ 1
  rw [h30, show (1 : ZMod 3) - 1 = 0 by decide] at hs₁
  have hN₁ : Recognition.R3.normCount (restrictForm f e₁) 1 = 12 := by
    rcases Recognition.R3.normTriple_eq 2 _ hf₁ with h | h
    · rw [T_iterate_two_left] at h
      simp only [Prod.mk.injEq] at h
      omega
    · rw [T_iterate_two_right] at h
      simp only [Prod.mk.injEq] at h
      omega
  have haP : a ∈ F3.perpOne f b := F3.mem_perpOne.2 hab
  have ha₁ : restrictForm f e₁ (e₁ ⟨a, haP⟩) (e₁ ⟨a, haP⟩) = 1 := by
    rw [restrictForm_apply]
    exact ha
  let e₂ : F3.perpOne (restrictForm f e₁) (e₁ ⟨a, haP⟩) ≃ₗ[ZMod 3] (Fin 2 → ZMod 3) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [F3.finrank_perpOne ha₁, Module.finrank_fin_fun])
  have hf₂ := isF3Form_restrictForm hf₁ ha₁ e₂
  have hs₂ := Recognition.R3.normCount_eq (n := 2) hf₁ ha₁ e₂ 1
  rw [hN₁, show (1 : ZMod 3) - 1 = 0 by decide] at hs₂
  have hN₂ : Recognition.R3.normCount (restrictForm (restrictForm f e₁) e₂) 0 = 5 := by
    rcases Recognition.R3.normTriple_eq 1 _ hf₂ with h | h
    · rw [T_iterate_one_left] at h
      simp only [Prod.mk.injEq] at h
      omega
    · rw [T_iterate_one_right] at h
      simp only [Prod.mk.injEq] at h
      omega
  obtain ⟨x, hx, hx0⟩ : ∃ x : Fin 2 → ZMod 3,
      restrictForm (restrictForm f e₁) e₂ x x = 0 ∧ x ≠ 0 := by
    rw [Recognition.R3.normCount_def] at hN₂
    by_contra h
    push Not at h
    have : Nat.card {x : Fin 2 → ZMod 3 // restrictForm (restrictForm f e₁) e₂ x x = 0} ≤ 1 :=
      Finite.card_le_one_iff_subsingleton.mpr
        ⟨fun p q => Subtype.ext ((h p p.2).trans (h q q.2).symm)⟩
    omega
  have hz₁ : restrictForm f e₁ (e₂.symm x : Fin 3 → ZMod 3) (e₂.symm x) = 0 := by
    rw [← restrictForm_apply e₂, LinearEquiv.apply_symm_apply]
    exact hx
  have hz₁a : restrictForm f e₁ (e₂.symm x : Fin 3 → ZMod 3) (e₁ ⟨a, haP⟩) = 0 :=
    F3.mem_perpOne.1 (e₂.symm x).2
  refine ⟨(e₁.symm (e₂.symm x : Fin 3 → ZMod 3) : Fin 4 → ZMod 3), fun h => hx0 ?_, ?_, ?_,
    F3.mem_perpOne.1 (e₁.symm _).2⟩
  · have h1 : e₁.symm (e₂.symm x : Fin 3 → ZMod 3) = 0 := Subtype.ext h
    rw [LinearEquiv.map_eq_zero_iff] at h1
    have h2 : e₂.symm x = 0 := Subtype.ext h1
    rwa [LinearEquiv.map_eq_zero_iff] at h2
  · rw [← restrictForm_apply e₁, LinearEquiv.apply_symm_apply]
    exact hz₁
  · have h1 := restrictForm_apply e₁ (e₁.symm (e₂.symm x : Fin 3 → ZMod 3)) ⟨a, haP⟩
    rw [LinearEquiv.apply_symm_apply] at h1
    exact h1.symm.trans hz₁a

theorem isSimpleGroup_commutator_R3 (hf : IsF3Form f) (hm : 4 ≤ m) (hiso : HIso f) :
    IsSimpleGroup (commutator (R3 f)) :=
  (isSimpleGroup_commutator_iff (pair_R3 hf hm) (center_R3_eq_bot hf hm)
    (fun N hN h2 => normal_two_eq_bot hf hm hiso N hN h2)
    (fun N hN h3 => normal_three_eq_bot hf hm N hN h3)).2 (mul_mem_fischerQ_D3 hf hm hiso)

end S12InspF3

theorem r3SimpleInput : R3SimpleInput := by
  intro n f hf hn h4
  refine S12InspF3.isSimpleGroup_commutator_R3 hf hn ?_
  rcases Nat.lt_or_ge n 5 with h | h
  · obtain rfl : n = 4 := by omega
    exact S12InspF3.hIso_of_four hf (h4 rfl)
  · exact fun a b ha hb hab =>
      CFSG.Fischer.Classification.F3.exists_isotropic_perp_two hf h ha hb hab

theorem inspF3_of_inspPSU4 (hPSU : InspPSU4) : InspF3 :=
  inspF3_of r3SimpleInput hPSU

theorem inspF3_of_inspPSU (hPSU : InspPSU) : InspF3 :=
  inspF3_of_inspPSU4 (inspPSU4_of hPSU)

end CFSG.LargeExtraspecial
