module

public import CFSG.Fischer.Classification.Recognition.R3Count

public section

namespace CFSG.Fischer.Classification.Recognition.R3

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Fischer.Classification F3

variable {m n : ℕ}

section Orbit

variable {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}

theorem exists_mem_act_eq (hf : IsF3Form f) (hm : 4 ≤ m) {v w : Fin m → ZMod 3}
    (hv : f v v = 1) (hw : f w w = 1) : ∃ g ∈ F3.reflGroup f, F3.act g v = w := by
  obtain ⟨g, hg, hgc⟩ := F3.exists_conj_refl hf hm hv hw
  have hiso := F3.isIsom_of_mem hf hg
  rw [F3.conj_refl hiso, F3.refl_eq_refl_iff (by rw [hiso.norm, hv]) hw] at hgc
  rcases hgc with h | h
  · exact ⟨g, hg, h.symm⟩
  · refine ⟨F3.refl f w * g, mul_mem (F3.refl_mem_reflGroup w) hg, ?_⟩
    rw [F3.act_mul, show F3.act g v = -w by rw [h, neg_neg], F3.act_neg, F3.act_refl_self hw,
      neg_neg]

theorem normCount_mul_card_dvd (hf : IsF3Form f) (hm : 4 ≤ m) {v : Fin m → ZMod 3}
    (hv : f v v = 1) (e : F3.perpOne f v ≃ₗ[ZMod 3] (Fin n → ZMod 3)) :
    normCount f 1 * Nat.card (F3.reflGroup (restrictForm f e)) ∣ Nat.card (F3.reflGroup f) := by
  have horb : MulAction.orbit (F3.reflGroup f) v = {w | f w w = 1} := by
    ext w
    constructor
    · rintro ⟨g, rfl⟩
      change f (F3.act (g : GL (Fin m) (ZMod 3)) v) (F3.act (g : GL (Fin m) (ZMod 3)) v) = 1
      rw [(F3.isIsom_of_mem hf g.2).norm, hv]
    · intro hw
      obtain ⟨g, hg, hgw⟩ := exists_mem_act_eq hf hm hv hw
      exact ⟨⟨g, hg⟩, hgw⟩
  have hcard : (MulAction.stabilizer (F3.reflGroup f) v).index = normCount f 1 := by
    rw [MulAction.index_stabilizer, horb, ← Nat.card_coe_set_eq, normCount_def]
    rfl
  have hperp : Nat.card (F3.reflGroup (restrictForm f e)) = Nat.card (F3.reflGroupPerp f v) := by
    rw [← range_perpToGL e (restrictForm_apply e)]
    exact (Nat.card_congr (MonoidHom.ofInjective (perpToGL_injective e hf hv)).toEquiv).symm
  have hle : (F3.reflGroupPerp f v).subgroupOf (F3.reflGroup f) ≤
      MulAction.stabilizer (F3.reflGroup f) v := fun g hg =>
    F3.act_eq_of_mem_reflGroupPerp hf (Subgroup.mem_subgroupOf.1 hg)
  have hdvd : Nat.card (F3.reflGroupPerp f v) ∣
      Nat.card (MulAction.stabilizer (F3.reflGroup f) v) := by
    rw [← Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (F3.reflGroupPerp_le_reflGroup v)).toEquiv]
    exact Subgroup.card_dvd_of_le hle
  rw [← (MulAction.stabilizer (F3.reflGroup f) v).index_mul_card, hcard, hperp]
  exact mul_dvd_mul_left _ hdvd

end Orbit

section Eleven

variable {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}

noncomputable def normPerm {g : GL (Fin m) (ZMod 3)} (hg : F3.IsIsom f g) (c : ZMod 3) :
    Equiv.Perm {x : Fin m → ZMod 3 // f x x = c} where
  toFun x := ⟨F3.act g x, by rw [hg.norm]; exact x.2⟩
  invFun x := ⟨F3.act g⁻¹ x, by rw [hg.inv.norm]; exact x.2⟩
  left_inv x := Subtype.ext (F3.act_inv_act g x)
  right_inv x := Subtype.ext (F3.act_act_inv g x)

theorem coe_normPerm_pow {g : GL (Fin m) (ZMod 3)} (hg : F3.IsIsom f g) (c : ZMod 3) (k : ℕ)
    (x : {x : Fin m → ZMod 3 // f x x = c}) :
    (((normPerm hg c) ^ k) x : Fin m → ZMod 3) = F3.act (g ^ k) x := by
  induction k generalizing x with
  | zero => rw [pow_zero, pow_zero, F3.act_one]; rfl
  | succ k ih =>
    rw [pow_succ, Equiv.Perm.mul_apply, ih, pow_succ, F3.act_mul]
    rfl

theorem exists_fixed_of_orderOf_eq_eleven {g : GL (Fin m) (ZMod 3)} (hg : F3.IsIsom f g)
    (h11 : orderOf g = 11) (hN : ¬ 11 ∣ normCount f 1) :
    ∃ v, f v v = 1 ∧ F3.act g v = v := by
  classical
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  set σ := normPerm hg 1
  have hσ : σ ^ 11 ^ 1 = 1 := by
    refine Equiv.ext fun x => Subtype.ext ?_
    rw [pow_one, coe_normPerm_pow, ← h11, pow_orderOf_eq_one, F3.act_one]
    rfl
  have hmod := Equiv.Perm.card_compl_support_modEq hσ
  obtain ⟨x, hx⟩ : σ.supportᶜ.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h0
    rw [h0, Finset.card_empty, ← Nat.card_eq_fintype_card] at hmod
    exact hN (by rw [normCount_def]; exact Nat.modEq_zero_iff_dvd.1 hmod.symm)
  rw [Finset.mem_compl, Equiv.Perm.notMem_support] at hx
  exact ⟨x, x.2, congrArg Subtype.val hx⟩

theorem mem_stabSub {g : GL (Fin m) (ZMod 3)} (hg : F3.IsIsom f g) {v : Fin m → ZMod 3}
    (hgv : F3.act g v = v) : g ∈ F3.stabSub f v := fun x => by
  calc f (F3.act g x) v = f (F3.act g x) (F3.act g v) := by rw [hgv]
    _ = f x v := hg x v

theorem isIsom_restrGL {g : GL (Fin m) (ZMod 3)} (hg : F3.IsIsom f g) {v : Fin m → ZMod 3}
    (e : F3.perpOne f v ≃ₗ[ZMod 3] (Fin n → ZMod 3)) (hgs : g ∈ F3.stabSub f v) :
    F3.IsIsom (restrictForm f e) (F3.restrGL e ⟨g, hgs⟩) := fun y y' => by
  rw [F3.act_restrGL, F3.act_restrGL, restrictForm_apply, F3.coe_restrPerp, F3.coe_restrPerp, hg,
    ← restrictForm_apply e, e.apply_symm_apply, e.apply_symm_apply]

theorem eq_one_of_restrGL_eq_one {v : Fin m → ZMod 3} (hv : f v v = 1) {g : GL (Fin m) (ZMod 3)}
    (e : F3.perpOne f v ≃ₗ[ZMod 3] (Fin n → ZMod 3)) (hgs : g ∈ F3.stabSub f v)
    (hgv : F3.act g v = v) (h1 : F3.restrGL e ⟨g, hgs⟩ = 1) : g = 1 := by
  have hW : ∀ x : F3.perpOne f v, F3.act g x = x := fun x => by
    have := F3.coe_restrPerp_symm e ⟨g, hgs⟩ (e x)
    rw [h1, F3.act_one, e.symm_apply_apply] at this
    exact this.symm
  refine F3.gl_ext fun x => ?_
  have hx : x - f x v • v ∈ F3.perpOne f v := F3.mem_perpOne.2 (by
    rw [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hv, mul_one, sub_self])
  have := hW ⟨_, hx⟩
  simp only at this
  rw [F3.act_sub, F3.act_smul, hgv] at this
  rw [F3.act_one]
  linear_combination (norm := module) this

theorem orderOf_ne_eleven : ∀ n, 4 ≤ n → n ≤ 9 →
    ∀ f : LinearMap.BilinForm (ZMod 3) (Fin n → ZMod 3), IsF3Form f →
      ∀ g : GL (Fin n) (ZMod 3), F3.IsIsom f g → orderOf g ≠ 11 := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    intro _ f _ g _ h
    have := orderOf_dvd_natCard g
    rw [h, Matrix.card_GL_field, ZMod.card, Fin.prod_univ_four] at this
    norm_num at this
  | succ n hn ih =>
    intro hn' f hf g hg h11
    obtain ⟨v, hv, hgv⟩ := exists_fixed_of_orderOf_eq_eleven hg h11
      (not_eleven_dvd_normCount hf (by omega) hn')
    let e : F3.perpOne f v ≃ₗ[ZMod 3] (Fin n → ZMod 3) :=
      LinearEquiv.ofFinrankEq _ _ (by rw [F3.finrank_perpOne hv, Module.finrank_fin_fun]; omega)
    have hgs := mem_stabSub hg hgv
    have hdvd : orderOf (F3.restrGL e ⟨g, hgs⟩) ∣ 11 := by
      rw [← h11, ← Subgroup.orderOf_mk g hgs]
      exact orderOf_map_dvd _ _
    rcases (Nat.dvd_prime (by norm_num)).1 hdvd with h | h
    · rw [orderOf_eq_one_iff] at h
      have := eq_one_of_restrGL_eq_one hv e hgs hgv h
      rw [this, orderOf_one] at h11
      exact absurd h11 (by norm_num)
    · exact ih (by omega) _ (isF3Form_restrictForm hf hv e) _ (isIsom_restrGL hg e hgs) h

end Eleven

@[expose] def threeExp (n : ℕ) : ℕ :=
  if n ≤ 6 then 0 else if n = 7 then 3 else if n = 8 then 6 else if n = 9 then 10 else 14

theorem pow_threeExp_dvd : ∀ (n : ℕ) (f : LinearMap.BilinForm (ZMod 3) (Fin n → ZMod 3)),
    IsF3Form f → 3 ^ threeExp n ∣ Nat.card (F3.reflGroup f)
  | 0, _, _ => by simp [threeExp]
  | n + 1, f, hf => by
    by_cases h6 : n + 1 ≤ 6
    · simp [threeExp, h6]
    obtain ⟨v, hv⟩ := F3.exists_norm_eq hf (by omega) (one_ne_zero (α := ZMod 3))
    let e : F3.perpOne f v ≃ₗ[ZMod 3] (Fin n → ZMod 3) :=
      LinearEquiv.ofFinrankEq _ _ (by rw [F3.finrank_perpOne hv, Module.finrank_fin_fun]; omega)
    have hdvd := normCount_mul_card_dvd hf (by omega) hv e
    have ih := pow_threeExp_dvd n _ (isF3Form_restrictForm hf hv e)
    obtain ⟨h34, h4⟩ := pow_dvd_normCount hf
    refine dvd_trans ?_ hdvd
    rcases (show n + 1 = 7 ∨ n + 1 = 8 ∨ n + 1 = 9 ∨ n + 1 = 10 ∨ 11 ≤ n + 1 by omega) with
      h | h | h | h | h
    · have h' : threeExp (n + 1) = 3 + threeExp n := by
        rw [h, show n = 6 by omega]; rfl
      rw [h', pow_add]
      exact mul_dvd_mul (h34 (Or.inl h)) ih
    · have h' : threeExp (n + 1) = 3 + threeExp n := by
        rw [h, show n = 7 by omega]; rfl
      rw [h', pow_add]
      exact mul_dvd_mul (h34 (Or.inr h)) ih
    · have h' : threeExp (n + 1) = 4 + threeExp n := by
        rw [h, show n = 8 by omega]; rfl
      rw [h', pow_add]
      exact mul_dvd_mul (h4 (Or.inl h)) ih
    · have h' : threeExp (n + 1) = 4 + threeExp n := by
        rw [h, show n = 9 by omega]; rfl
      rw [h', pow_add]
      exact mul_dvd_mul (h4 (Or.inr h)) ih
    · have h' : threeExp (n + 1) = threeExp n := by
        unfold threeExp
        split_ifs <;> omega
      rw [h']
      exact dvd_mul_of_dvd_right ih _

theorem pow_dvd_card_of_eleven_dvd {f : LinearMap.BilinForm (ZMod 3) (Fin n → ZMod 3)}
    (hf : IsF3Form f) (hn : 4 ≤ n) (h : 11 ∣ Nat.card (F3.reflGroup f)) :
    3 ^ 14 ∣ Nat.card (F3.reflGroup f) := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := F3.reflGroup f) 11 h
  have h10 : 10 ≤ n := by
    by_contra h'
    exact orderOf_ne_eleven n hn (by omega) f hf g (F3.isIsom_of_mem hf g.2)
      (by rw [Subgroup.orderOf_coe, hg])
  have h14 : threeExp n = 14 := by
    unfold threeExp
    split_ifs <;> omega
  have := pow_threeExp_dvd n f hf
  rwa [h14] at this

end CFSG.Fischer.Classification.Recognition.R3
