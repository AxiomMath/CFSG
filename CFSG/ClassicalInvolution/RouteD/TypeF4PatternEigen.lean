module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCFrame

public section

open Matrix CFSG.ClassicalInvolution.Models.SymplecticPairs

namespace CFSG.ClassicalInvolution.RouteD.SpAdapt

variable {F : Type} [Field F] {n : ℕ}

structure EigData (Am : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (κ : F) : Prop where
  two : (2 : F) ≠ 0
  ne : κ ≠ 0
  sq : Am * Am = (κ ^ 2) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
  sim : ∀ u v, form (Am *ᵥ u) (Am *ᵥ v) = (-κ ^ 2) * form u v

namespace EigData

variable {Am : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F} {κ : F} (h : EigData Am κ)
include h

theorem mulVec_sq (v : Fin n ⊕ Fin n → F) : Am *ᵥ (Am *ᵥ v) = (κ ^ 2) • v := by
  rw [Matrix.mulVec_mulVec, h.sq, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem iso_plus {x y : Fin n ⊕ Fin n → F} (hx : Am *ᵥ x = κ • x) (hy : Am *ᵥ y = κ • y) :
    form x y = 0 := by
  have h1 := h.sim x y
  rw [hx, hy, form_smul_left, form_smul_right] at h1
  have h2 : (2 * κ ^ 2) * form x y = 0 := by linear_combination h1
  exact (mul_eq_zero.1 h2).resolve_left (mul_ne_zero h.two (pow_ne_zero 2 h.ne))

theorem iso_minus {x y : Fin n ⊕ Fin n → F} (hx : Am *ᵥ x = (-κ) • x)
    (hy : Am *ᵥ y = (-κ) • y) : form x y = 0 := by
  have h1 := h.sim x y
  rw [hx, hy, form_smul_left, form_smul_right] at h1
  have h2 : (2 * κ ^ 2) * form x y = 0 := by linear_combination h1
  exact (mul_eq_zero.1 h2).resolve_left (mul_ne_zero h.two (pow_ne_zero 2 h.ne))

theorem plus_eigen (x : Fin n ⊕ Fin n → F) :
    Am *ᵥ (x + κ⁻¹ • (Am *ᵥ x)) = κ • (x + κ⁻¹ • (Am *ᵥ x)) := by
  have e1 : κ⁻¹ * κ ^ 2 = κ := by field_simp [h.ne]
  have e2 : κ * κ⁻¹ = 1 := mul_inv_cancel₀ h.ne
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, h.mulVec_sq, smul_smul, e1, smul_add, smul_smul, e2,
    one_smul, add_comm]

theorem minus_eigen (x : Fin n ⊕ Fin n → F) :
    Am *ᵥ (x - κ⁻¹ • (Am *ᵥ x)) = (-κ) • (x - κ⁻¹ • (Am *ᵥ x)) := by
  have e1 : κ⁻¹ * κ ^ 2 = κ := by field_simp [h.ne]
  have e3 : -κ * κ⁻¹ = -1 := by field_simp [h.ne]
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul, h.mulVec_sq, smul_smul, e1, smul_sub, smul_smul, e3]
  simp [sub_eq_add_neg, add_comm]

theorem exists_eigenpair {U : Submodule F (Fin n ⊕ Fin n → F)}
    (hU : ∀ v ∈ U, Am *ᵥ v ∈ U) {x y : Fin n ⊕ Fin n → F} (hx : x ∈ U) (hy : y ∈ U)
    (hxy : form x y ≠ 0) :
    ∃ a ∈ U, ∃ b ∈ U, Am *ᵥ a = κ • a ∧ Am *ᵥ b = (-κ) • b ∧ form a b = 1 := by
  obtain ⟨xp, hxp⟩ : ∃ v, v = x + κ⁻¹ • (Am *ᵥ x) := ⟨_, rfl⟩
  obtain ⟨xm, hxm⟩ : ∃ v, v = x - κ⁻¹ • (Am *ᵥ x) := ⟨_, rfl⟩
  obtain ⟨yp, hyp⟩ : ∃ v, v = y + κ⁻¹ • (Am *ᵥ y) := ⟨_, rfl⟩
  obtain ⟨ym, hym⟩ : ∃ v, v = y - κ⁻¹ • (Am *ᵥ y) := ⟨_, rfl⟩
  have hxpU : xp ∈ U := hxp ▸ U.add_mem hx (U.smul_mem _ (hU x hx))
  have hxmU : xm ∈ U := hxm ▸ U.sub_mem hx (U.smul_mem _ (hU x hx))
  have hypU : yp ∈ U := hyp ▸ U.add_mem hy (U.smul_mem _ (hU y hy))
  have hymU : ym ∈ U := hym ▸ U.sub_mem hy (U.smul_mem _ (hU y hy))
  have hxpe : Am *ᵥ xp = κ • xp := hxp ▸ h.plus_eigen x
  have hxme : Am *ᵥ xm = (-κ) • xm := hxm ▸ h.minus_eigen x
  have hype : Am *ᵥ yp = κ • yp := hyp ▸ h.plus_eigen y
  have hyme : Am *ᵥ ym = (-κ) • ym := hym ▸ h.minus_eigen y
  have hsum : form xp yp + form xp ym + form xm yp + form xm ym = 2 * 2 * form x y := by
    have e1 : xp + xm = (2 : F) • x := by
      rw [hxp, hxm, two_smul]; abel
    have e2 : yp + ym = (2 : F) • y := by
      rw [hyp, hym, two_smul]; abel
    have := congrArg₂ form e1 e2
    rw [form_add_left, form_add_right, form_add_right, form_smul_left, form_smul_right] at this
    linear_combination this
  have h1 : form xp yp = 0 := h.iso_plus hxpe hype
  have h4 : form xm ym = 0 := h.iso_minus hxme hyme
  have h22 : (2 * 2 : F) ≠ 0 := mul_ne_zero h.two h.two
  by_cases hc : form xp ym = 0
  · have hc' : form xm yp ≠ 0 := by
      intro hc'
      apply hxy
      have : 2 * 2 * form x y = 0 := by rw [← hsum, h1, hc, hc', h4]; ring
      exact (mul_eq_zero.1 this).resolve_left h22
    have hc'' : form yp xm ≠ 0 := by
      rw [form_antisymm]; exact neg_ne_zero.2 hc'
    refine ⟨yp, hypU, (form yp xm)⁻¹ • xm, U.smul_mem _ hxmU, hype, ?_, ?_⟩
    · rw [Matrix.mulVec_smul, hxme, smul_comm]
    · rw [form_smul_right, inv_mul_cancel₀ hc'']
  · refine ⟨xp, hxpU, (form xp ym)⁻¹ • ym, U.smul_mem _ hymU, hxpe, ?_, ?_⟩
    · rw [Matrix.mulVec_smul, hyme, smul_comm]
    · rw [form_smul_right, inv_mul_cancel₀ hc]


end EigData

section Three

@[expose] def Vfour (F : Type) [Field F] : Submodule F (Fin 3 ⊕ Fin 3 → F) where
  carrier := {v | v (Sum.inl 2) = 0 ∧ v (Sum.inr 2) = 0}
  add_mem' := by
    rintro v w ⟨hv1, hv2⟩ ⟨hw1, hw2⟩
    exact ⟨by simp [hv1, hw1], by simp [hv2, hw2]⟩
  zero_mem' := ⟨rfl, rfl⟩
  smul_mem' := by
    rintro c v ⟨hv1, hv2⟩
    exact ⟨by simp [hv1], by simp [hv2]⟩

theorem mem_Vfour {v : Fin 3 ⊕ Fin 3 → F} :
    v ∈ Vfour F ↔ v (Sum.inl 2) = 0 ∧ v (Sum.inr 2) = 0 := Iff.rfl

@[expose] def orthSub (U : Submodule F (Fin 3 ⊕ Fin 3 → F)) (a b : Fin 3 ⊕ Fin 3 → F) :
    Submodule F (Fin 3 ⊕ Fin 3 → F) where
  carrier := {v | v ∈ U ∧ form v a = 0 ∧ form v b = 0}
  add_mem' := by
    rintro v w ⟨hv, hva, hvb⟩ ⟨hw, hwa, hwb⟩
    exact ⟨U.add_mem hv hw, by rw [form_add_left, hva, hwa, add_zero],
      by rw [form_add_left, hvb, hwb, add_zero]⟩
  zero_mem' := ⟨U.zero_mem, form_zero_left _, form_zero_left _⟩
  smul_mem' := by
    rintro c v ⟨hv, hva, hvb⟩
    exact ⟨U.smul_mem c hv, by rw [form_smul_left, hva, mul_zero],
      by rw [form_smul_left, hvb, mul_zero]⟩

@[expose] def pr (a b x : Fin 3 ⊕ Fin 3 → F) : Fin 3 ⊕ Fin 3 → F :=
  x + (-form x b) • a + (form x a) • b

theorem form_pr_left {a b : Fin 3 ⊕ Fin 3 → F} (hab : form a b = 1) (x : Fin 3 ⊕ Fin 3 → F) :
    form (pr a b x) a = 0 ∧ form (pr a b x) b = 0 := by
  have h1 : form b a = -1 := by rw [form_antisymm, hab]
  constructor
  · simp only [pr, form_add_left, form_smul_left, form_self, h1]
    ring
  · simp only [pr, form_add_left, form_smul_left, form_self, hab]
    ring

theorem form_pr_pr {a b : Fin 3 ⊕ Fin 3 → F} (hab : form a b = 1) (x y : Fin 3 ⊕ Fin 3 → F) :
    form (pr a b x) (pr a b y) =
      form x y - form x a * form y b + form x b * form y a := by
  have h1 : form b a = -1 := by rw [form_antisymm, hab]
  have h2 : form a y = -form y a := form_antisymm y a
  have h3 : form b y = -form y b := form_antisymm y b
  simp only [pr, form_add_left, form_add_right, form_smul_left, form_smul_right, form_self, hab,
    h1, h2, h3]
  ring

theorem form_single_inl_left (a : Fin 3 ⊕ Fin 3 → F) (k : Fin 3) :
    form (Pi.single (Sum.inl k) (1 : F)) a = a (Sum.inr k) := by
  rw [← neg_neg (form (Pi.single (Sum.inl k) (1 : F)) a), ← form_antisymm, form_single_right]
  simp [par, sgn]

theorem form_single_inr_left (a : Fin 3 ⊕ Fin 3 → F) (k : Fin 3) :
    form (Pi.single (Sum.inr k) (1 : F)) a = - a (Sum.inl k) := by
  rw [← neg_neg (form (Pi.single (Sum.inr k) (1 : F)) a), ← form_antisymm, form_single_right]
  simp [par, sgn]

theorem trace_identity {a b : Fin 3 ⊕ Fin 3 → F} (ha : a ∈ Vfour F) (hb : b ∈ Vfour F)
    (hab : form a b = 1) :
    form (pr a b (Pi.single (Sum.inl 0) 1)) (pr a b (Pi.single (Sum.inr 0) 1)) +
      form (pr a b (Pi.single (Sum.inl 1) 1)) (pr a b (Pi.single (Sum.inr 1) 1)) = 1 := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  rw [form_pr_pr hab, form_pr_pr hab, form_single_inl_inr, form_single_inl_inr,
    form_single_inl_left, form_single_inl_left, form_single_inr_left, form_single_inr_left,
    form_single_inl_left, form_single_inl_left, form_single_inr_left, form_single_inr_left]
  rw [form_apply] at hab
  simp [Fintype.sum_sum_type, Fin.sum_univ_three, sgn, par, ha1, ha2, hb1, hb2] at hab
  linear_combination (-1 : F) * hab

theorem single_inl_mem_Vfour {k : Fin 3} (hk : k ≠ 2) :
    (Pi.single (Sum.inl k) (1 : F) : Fin 3 ⊕ Fin 3 → F) ∈ Vfour F := by
  simp [mem_Vfour, Ne.symm hk]

theorem single_inr_mem_Vfour {k : Fin 3} (hk : k ≠ 2) :
    (Pi.single (Sum.inr k) (1 : F) : Fin 3 ⊕ Fin 3 → F) ∈ Vfour F := by
  simp [mem_Vfour, Ne.symm hk]

theorem exists_frame_three {Am : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F} {κ : F}
    (h : EigData Am κ) (hAV : ∀ v ∈ Vfour F, Am *ᵥ v ∈ Vfour F) {u₂ w₂ : Fin 3 ⊕ Fin 3 → F}
    (hu₂ : ∀ a, a ∉ coords (2 : Fin 3) → u₂ a = 0) (hw₂ : ∀ a, a ∉ coords (2 : Fin 3) → w₂ a = 0)
    (hAu₂ : Am *ᵥ u₂ = κ • u₂) (hAw₂ : Am *ᵥ w₂ = (-κ) • w₂) (huw₂ : form u₂ w₂ = 1) :
    ∃ u w : Fin 3 → Fin 3 ⊕ Fin 3 → F, IsPlaneFrame u w ∧ (∀ k, Am *ᵥ u k = κ • u k) ∧
      (∀ k, Am *ᵥ w k = (-κ) • w k) ∧ u 2 = u₂ ∧ w 2 = w₂ := by
  classical
  have he : ∀ k : Fin 3, k ≠ 2 → (Pi.single (Sum.inl k) (1 : F) : Fin 3 ⊕ Fin 3 → F) ∈ Vfour F :=
    fun k hk => single_inl_mem_Vfour hk
  have hf : ∀ k : Fin 3, k ≠ 2 → (Pi.single (Sum.inr k) (1 : F) : Fin 3 ⊕ Fin 3 → F) ∈ Vfour F :=
    fun k hk => single_inr_mem_Vfour hk
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  obtain ⟨a₁, ha₁, b₁, hb₁, hAa₁, hAb₁, hab₁⟩ := h.exists_eigenpair hAV (he 0 h02) (hf 0 h02)
    (by rw [form_single_inl_inr]; exact one_ne_zero)
  have hne : form (pr a₁ b₁ (Pi.single (Sum.inl 0) 1)) (pr a₁ b₁ (Pi.single (Sum.inr 0) 1)) ≠ 0 ∨
      form (pr a₁ b₁ (Pi.single (Sum.inl 1) 1)) (pr a₁ b₁ (Pi.single (Sum.inr 1) 1)) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have := trace_identity ha₁ hb₁ hab₁
    rw [hcon.1, hcon.2, add_zero] at this
    exact zero_ne_one this
  have hprV : ∀ x ∈ Vfour F, pr a₁ b₁ x ∈ Vfour F := fun x hx =>
    (Vfour F).add_mem ((Vfour F).add_mem hx ((Vfour F).smul_mem _ ha₁))
      ((Vfour F).smul_mem _ hb₁)
  have hprO : ∀ x ∈ Vfour F, pr a₁ b₁ x ∈ orthSub (Vfour F) a₁ b₁ := fun x hx =>
    ⟨hprV x hx, (form_pr_left hab₁ x).1, (form_pr_left hab₁ x).2⟩
  have hstable : ∀ v ∈ orthSub (Vfour F) a₁ b₁, Am *ᵥ v ∈ orthSub (Vfour F) a₁ b₁ := by
    rintro v ⟨hv, hva, hvb⟩
    refine ⟨hAV v hv, ?_, ?_⟩
    · have : a₁ = κ⁻¹ • (Am *ᵥ a₁) := by rw [hAa₁, smul_smul, inv_mul_cancel₀ h.ne, one_smul]
      rw [this, form_smul_right, h.sim, hva]
      · ring
    · have : b₁ = (-κ)⁻¹ • (Am *ᵥ b₁) := by
        rw [hAb₁, smul_smul, inv_mul_cancel₀ (neg_ne_zero.2 h.ne), one_smul]
      rw [this, form_smul_right, h.sim, hvb]
      · ring
  obtain ⟨a₂, ha₂, b₂, hb₂, hAa₂, hAb₂, hab₂⟩ : ∃ a ∈ orthSub (Vfour F) a₁ b₁,
      ∃ b ∈ orthSub (Vfour F) a₁ b₁, Am *ᵥ a = κ • a ∧ Am *ᵥ b = (-κ) • b ∧ form a b = 1 := by
    rcases hne with hne | hne
    · exact h.exists_eigenpair hstable (hprO _ (he 0 h02)) (hprO _ (hf 0 h02)) hne
    · exact h.exists_eigenpair hstable (hprO _ (he 1 h12)) (hprO _ (hf 1 h12)) hne
  have hperp : ∀ v ∈ Vfour F, form v u₂ = 0 ∧ form v w₂ = 0 := by
    rintro v ⟨hv1, hv2⟩
    refine ⟨Models.SymplecticPairs.form_eq_zero_of_supp (parClosed_coords 2) ?_ hu₂,
      Models.SymplecticPairs.form_eq_zero_of_supp (parClosed_coords 2) ?_ hw₂⟩ <;>
    · intro a ha
      rcases mem_coords.1 ha with rfl | rfl <;> assumption
  refine ⟨![a₁, a₂, u₂], ![b₁, b₂, w₂], ⟨?_, ?_, ?_⟩, ?_, ?_, rfl, rfl⟩
  · intro k l
    have hba : ∀ x y : Fin 3 ⊕ Fin 3 → F, form x y = 0 → form y x = 0 := fun x y hxy => by
      rw [form_antisymm, hxy, neg_zero]
    have h01 : form a₁ b₂ = 0 := hba _ _ hb₂.2.1
    have h10 : form a₂ b₁ = 0 := ha₂.2.2
    have hp₁ := hperp a₁ ha₁
    have hp₂ := hperp a₂ ha₂.1
    have hq₁ : form u₂ b₁ = 0 := hba _ _ (hperp b₁ hb₁).1
    have hq₂ : form u₂ b₂ = 0 := hba _ _ (hperp b₂ hb₂.1).1
    fin_cases k <;> fin_cases l <;> simp [hab₁, hab₂, huw₂, h01, h10, hp₁.2, hp₂.2, hq₁, hq₂]
  · intro k l
    exact h.iso_plus (by fin_cases k <;> simp [hAa₁, hAa₂, hAu₂])
      (by fin_cases l <;> simp [hAa₁, hAa₂, hAu₂])
  · intro k l
    exact h.iso_minus (by fin_cases k <;> simp [hAb₁, hAb₂, hAw₂])
      (by fin_cases l <;> simp [hAb₁, hAb₂, hAw₂])
  · intro k
    fin_cases k <;> simp [hAa₁, hAa₂, hAu₂]
  · intro k
    fin_cases k <;> simp [hAb₁, hAb₂, hAw₂]

end Three

end CFSG.ClassicalInvolution.RouteD.SpAdapt
