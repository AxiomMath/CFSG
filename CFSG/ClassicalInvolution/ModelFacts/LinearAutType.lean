module

public import CFSG.ClassicalInvolution.ModelFacts.LinearAutBlock

public section

namespace CFSG.ClassicalInvolution.ModelFacts.LinearAut

open Matrix.SpecialLinearGroup (transvection)
open CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ComponentClassification.CatalogueBHigherLinearAction
open scoped MatrixGroups Matrix

variable {F : Type} [Field F] {n : ℕ}

@[expose] def IsU (α : SL(n, F) →* SL(n, F)) (i j : Fin n) (hij : i ≠ j) : Prop :=
  ∀ s : F, ∃ b : F, α (transvection hij s) = transvection hij b

@[expose] def IsL (α : SL(n, F) →* SL(n, F)) (i j : Fin n) (hij : i ≠ j) : Prop :=
  ∀ s : F, ∃ c : F, α (transvection hij s) = transvection hij.symm c

theorem transvection_ne_one {i j : Fin n} (hij : i ≠ j) {s : F} (hs : s ≠ 0) :
    (transvection hij s : SL(n, F)) ≠ 1 := fun h => hs (by
  have := congrArg (fun g : SL(n, F) => (g : Matrix (Fin n) (Fin n) F) i j) h
  simpa [transvection_apply_self, Matrix.one_apply_ne hij] using this)

theorem coe_transvection_mul_apply {i j : Fin n} (hij : i ≠ j) (b c : F) :
    ((transvection hij.symm c * transvection hij b : SL(n, F)) : Matrix (Fin n) (Fin n) F) j j =
      1 + c * b := by
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_transvection_eq hij.symm, coe_transvection_eq hij]
  simp [Matrix.add_mul, Matrix.mul_add, Matrix.single_mul_single_same, hij]

theorem transvection_apply_diag {i j : Fin n} (hij : i ≠ j) (s : F) (e : Fin n) :
    ((transvection hij s : SL(n, F)) : Matrix (Fin n) (Fin n) F) e e = 1 := by
  rw [coe_transvection_eq hij]
  by_cases h : i = e ∧ j = e
  · exact absurd (h.1.trans h.2.symm) hij
  · simp [h]

theorem coe_transvection_mul_apply' {i j : Fin n} (hij : i ≠ j) (b c : F) :
    ((transvection hij b * transvection hij.symm c : SL(n, F)) : Matrix (Fin n) (Fin n) F) j j =
      1 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_transvection_eq hij.symm, coe_transvection_eq hij]
  simp [Matrix.add_mul, Matrix.mul_add, Matrix.single_mul_single_same, hij]

theorem not_commute_transvection_swap {i j : Fin n} (hij : i ≠ j) :
    ¬ Commute (transvection hij (1 : F)) (transvection hij.symm (1 : F)) := by
  intro h
  have h1 := congrArg (fun g : SL(n, F) => (g : Matrix (Fin n) (Fin n) F) j j) h.eq
  simp only [coe_transvection_mul_apply', coe_transvection_mul_apply] at h1
  have : (1 : F) + 1 * 1 = 1 := h1.symm
  simp at this

theorem const_of_cyclic {β : Sort*} (Ψ : ∀ i j : Fin n, i ≠ j → β)
    (h1 : ∀ i j k (hij : i ≠ j) (hjk : j ≠ k) (_ : i ≠ k), Ψ i j hij = Ψ j k hjk)
    (hsym : ∀ i j (hij : i ≠ j), Ψ i j hij = Ψ j i hij.symm) :
    ∀ a b (hab : a ≠ b) c d (hcd : c ≠ d), Ψ a b hab = Ψ c d hcd := by
  have F1 : ∀ a b x (hab : a ≠ b) (hax : a ≠ x) (hbx : b ≠ x), Ψ a b hab = Ψ a x hax := by
    intro a b x hab hax hbx
    calc Ψ a b hab = Ψ b x hbx := h1 a b x hab hbx hax
      _ = Ψ x a hax.symm := h1 b x a hbx hax.symm hab.symm
      _ = Ψ a x hax := (hsym a x hax).symm
  have F2 : ∀ a c x (hax : a ≠ x) (hcx : c ≠ x) (hac : a ≠ c), Ψ a x hax = Ψ c x hcx := by
    intro a c x hax hcx hac
    calc Ψ a x hax = Ψ x c hcx.symm := h1 a x c hax hcx.symm hac
      _ = Ψ c x hcx := (hsym c x hcx).symm
  intro a b hab c d hcd
  by_cases had : a = d
  · subst had
    by_cases hbc : b = c
    · subst hbc
      exact hsym a b hab
    · calc Ψ a b hab = Ψ a c hcd.symm := F1 a b c hab hcd.symm hbc
        _ = Ψ c a hcd := hsym a c hcd.symm
  · by_cases hbd : b = d
    · subst hbd
      by_cases hac : a = c
      · subst hac
        rfl
      · exact F2 a c b hab hcd hac
    · calc Ψ a b hab = Ψ a d had := F1 a b d hab had hbd
        _ = Ψ c d hcd := by
          by_cases hac : a = c
          · subst hac
            rfl
          · exact F2 a c d had hcd hac

section Types

variable [Finite F]

omit [Finite F] in
theorem map_transvection_ne_one {α : SL(n, F) →* SL(n, F)} (hα : Function.Injective α)
    {i j : Fin n} (hij : i ≠ j) {s : F} (hs : s ≠ 0) : α (transvection hij s) ≠ 1 := fun h =>
  transvection_ne_one hij hs (hα (h.trans (map_one α).symm))

theorem isU_or_isL (h2 : (2 : F) ≠ 0) (hn : 3 ≤ n) (α : SL(n, F) →* SL(n, F))
    (hz : ∀ T : Pair n, α (zElt F T) = zElt F T)
    (hL : ∀ T : Pair n, ∀ g ∈ Lc F T, α g ∈ Lc F T) {i j : Fin n} (hij : i ≠ j) :
    IsU α i j hij ∨ IsL α i j hij := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hU, hL'⟩ := hcon
  unfold IsU at hU
  unfold IsL at hL'
  push Not at hU hL'
  obtain ⟨s₁, hs₁⟩ := hU
  obtain ⟨s₂, hs₂⟩ := hL'
  obtain ⟨c₁, hc₁⟩ : ∃ c, α (transvection hij s₁) = transvection hij.symm c := by
    rcases exists_transvection_of_fixes_signs h2 hn α hz hL hij s₁ with ⟨b, hb⟩ | h
    · exact absurd hb (hs₁ b)
    · exact h
  obtain ⟨b₂, hb₂⟩ : ∃ b, α (transvection hij s₂) = transvection hij b := by
    rcases exists_transvection_of_fixes_signs h2 hn α hz hL hij s₂ with h | ⟨c, hc⟩
    · exact h
    · exact absurd hc (hs₂ c)
  have hc₁0 : c₁ ≠ 0 := by
    rintro rfl
    exact hs₁ 0 (by rw [hc₁, Matrix.SpecialLinearGroup.transvection_coeff_zero,
      Matrix.SpecialLinearGroup.transvection_coeff_zero])
  have hb₂0 : b₂ ≠ 0 := by
    rintro rfl
    exact hs₂ 0 (by rw [hb₂, Matrix.SpecialLinearGroup.transvection_coeff_zero,
      Matrix.SpecialLinearGroup.transvection_coeff_zero])
  have hprod : α (transvection hij (s₁ + s₂)) = transvection hij.symm c₁ * transvection hij b₂ := by
    rw [Matrix.SpecialLinearGroup.transvection_add, map_mul, hc₁, hb₂]
  have h1 := congrArg (fun g : SL(n, F) => (g : Matrix (Fin n) (Fin n) F) j j) hprod
  simp only [coe_transvection_mul_apply] at h1
  rcases exists_transvection_of_fixes_signs h2 hn α hz hL hij (s₁ + s₂) with ⟨b, hb⟩ | ⟨c, hc⟩
  · rw [hb, transvection_apply_diag] at h1
    exact mul_ne_zero hc₁0 hb₂0 (by linear_combination -h1)
  · rw [hc, transvection_apply_diag] at h1
    exact mul_ne_zero hc₁0 hb₂0 (by linear_combination -h1)

omit [Finite F] in
theorem not_isU_and_isL {α : SL(n, F) →* SL(n, F)} (hα : Function.Injective α) {i j : Fin n}
    (hij : i ≠ j) : ¬ (IsU α i j hij ∧ IsL α i j hij) := by
  rintro ⟨hU, hL⟩
  obtain ⟨b, hb⟩ := hU 1
  obtain ⟨c, hc⟩ := hL 1
  have h1 := congrArg (fun g : SL(n, F) => (g : Matrix (Fin n) (Fin n) F) i j) (hb.symm.trans hc)
  have hb0 : b = 0 := by
    simpa [transvection_apply_self, coe_transvection_eq hij.symm, Matrix.single_apply,
      Matrix.one_apply_ne hij, hij, hij.symm] using h1
  subst hb0
  rw [Matrix.SpecialLinearGroup.transvection_coeff_zero] at hb
  exact map_transvection_ne_one hα hij one_ne_zero hb

theorem isU_trans (h2 : (2 : F) ≠ 0) (hn : 3 ≤ n) (α : SL(n, F) →* SL(n, F))
    (hα : Function.Injective α) (hz : ∀ T : Pair n, α (zElt F T) = zElt F T)
    (hL : ∀ T : Pair n, ∀ g ∈ Lc F T, α g ∈ Lc F T) {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (h : IsU α i j hij) : IsU α j k hjk := by
  by_contra hcon
  have hLjk : IsL α j k hjk := (isU_or_isL h2 hn α hz hL hjk).resolve_left hcon
  obtain ⟨b, hb⟩ := h 1
  obtain ⟨c, hc⟩ := hLjk 1
  have hcomm : Commute (transvection hij b) (transvection hjk.symm c) :=
    Matrix.SpecialLinearGroup.commute_transvection hij hjk.symm hjk hij.symm b c
  have h1 := congrArg α (Matrix.SpecialLinearGroup.commutatorElement_transvection hij hjk hik
    (1 : F) 1)
  rw [map_commutatorElement, hb, hc, commutatorElement_eq_one_iff_mul_comm.mpr hcomm] at h1
  exact map_transvection_ne_one hα hik (by simp : (1 : F) * 1 ≠ 0) h1.symm

theorem isL_trans (h2 : (2 : F) ≠ 0) (hn : 3 ≤ n) (α : SL(n, F) →* SL(n, F))
    (hα : Function.Injective α) (hz : ∀ T : Pair n, α (zElt F T) = zElt F T)
    (hL : ∀ T : Pair n, ∀ g ∈ Lc F T, α g ∈ Lc F T) {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (h : IsL α i j hij) : IsL α j k hjk := by
  by_contra hcon
  have hUjk : IsU α j k hjk := (isU_or_isL h2 hn α hz hL hjk).resolve_right hcon
  obtain ⟨b, hb⟩ := h 1
  obtain ⟨c, hc⟩ := hUjk 1
  have hcomm : Commute (transvection hij.symm b) (transvection hjk c) :=
    Matrix.SpecialLinearGroup.commute_transvection hij.symm hjk hij hjk.symm b c
  have h1 := congrArg α (Matrix.SpecialLinearGroup.commutatorElement_transvection hij hjk hik
    (1 : F) 1)
  rw [map_commutatorElement, hb, hc, commutatorElement_eq_one_iff_mul_comm.mpr hcomm] at h1
  exact map_transvection_ne_one hα hik (by simp : (1 : F) * 1 ≠ 0) h1.symm

theorem isU_iff_isU_trans (h2 : (2 : F) ≠ 0) (hn : 3 ≤ n) (α : SL(n, F) →* SL(n, F))
    (hα : Function.Injective α) (hz : ∀ T : Pair n, α (zElt F T) = zElt F T)
    (hL : ∀ T : Pair n, ∀ g ∈ Lc F T, α g ∈ Lc F T) {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) : IsU α i j hij ↔ IsU α j k hjk := by
  refine ⟨isU_trans h2 hn α hα hz hL hij hjk hik, fun h => ?_⟩
  by_contra hcon
  have hLij : IsL α i j hij := (isU_or_isL h2 hn α hz hL hij).resolve_left hcon
  exact not_isU_and_isL hα hjk ⟨h, isL_trans h2 hn α hα hz hL hij hjk hik hLij⟩

theorem isU_iff_isU_swap (h2 : (2 : F) ≠ 0) (hn : 3 ≤ n) (α : SL(n, F) →* SL(n, F))
    (hα : Function.Injective α) (hz : ∀ T : Pair n, α (zElt F T) = zElt F T)
    (hL : ∀ T : Pair n, ∀ g ∈ Lc F T, α g ∈ Lc F T) {i j : Fin n} (hij : i ≠ j) :
    IsU α i j hij ↔ IsU α j i hij.symm := by
  have key : ∀ {i j : Fin n} (hij : i ≠ j), IsU α i j hij → IsU α j i hij.symm := by
    intro i j hij h
    by_contra hcon
    have hLji : IsL α j i hij.symm := (isU_or_isL h2 hn α hz hL hij.symm).resolve_left hcon
    obtain ⟨b, hb⟩ := h 1
    obtain ⟨c, hc⟩ := hLji 1
    have hcomm : α (transvection hij (1 : F)) * α (transvection hij.symm (1 : F)) =
        α (transvection hij.symm (1 : F)) * α (transvection hij (1 : F)) := by
      rw [hb, hc]
      show transvection hij b * transvection hij c = transvection hij c * transvection hij b
      rw [← Matrix.SpecialLinearGroup.transvection_add, ← Matrix.SpecialLinearGroup.transvection_add,
        add_comm]
    rw [← map_mul, ← map_mul] at hcomm
    exact not_commute_transvection_swap hij (hα hcomm)
  exact ⟨key hij, key hij.symm⟩

theorem isU_iff_isU (h2 : (2 : F) ≠ 0) (hn : 3 ≤ n) (α : SL(n, F) →* SL(n, F))
    (hα : Function.Injective α) (hz : ∀ T : Pair n, α (zElt F T) = zElt F T)
    (hL : ∀ T : Pair n, ∀ g ∈ Lc F T, α g ∈ Lc F T) :
    ∀ a b (hab : a ≠ b) c d (hcd : c ≠ d), IsU α a b hab ↔ IsU α c d hcd := by
  intro a b hab c d hcd
  exact Iff.of_eq (const_of_cyclic (fun i j h => IsU α i j h)
    (fun i j k hij hjk hik => propext (isU_iff_isU_trans h2 hn α hα hz hL hij hjk hik))
    (fun i j hij => propext (isU_iff_isU_swap h2 hn α hα hz hL hij)) a b hab c d hcd)

end Types

@[expose] def invTranspose (n : ℕ) (F : Type) [Field F] : SL(n, F) →* SL(n, F) where
  toFun x := Matrix.SpecialLinearGroup.transpose x⁻¹
  map_one' := Subtype.ext (by simp [Matrix.SpecialLinearGroup.transpose])
  map_mul' x y := Subtype.ext (by
    simp only [mul_inv_rev, Matrix.SpecialLinearGroup.coe_transpose,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul])

theorem coe_invTranspose (x : SL(n, F)) :
    ((invTranspose n F x : SL(n, F)) : Matrix (Fin n) (Fin n) F) =
      (((x⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F))ᵀ := rfl

theorem invTranspose_invTranspose (x : SL(n, F)) : invTranspose n F (invTranspose n F x) = x := by
  set y := invTranspose n F x with hy
  have h1 : y * Matrix.SpecialLinearGroup.transpose x = 1 := by
    refine Subtype.ext ?_
    rw [Matrix.SpecialLinearGroup.coe_mul, hy, coe_invTranspose,
      Matrix.SpecialLinearGroup.coe_transpose, ← Matrix.transpose_mul,
      ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one,
      Matrix.transpose_one]
  have h2 : y⁻¹ = Matrix.SpecialLinearGroup.transpose x := inv_eq_of_mul_eq_one_right h1
  show Matrix.SpecialLinearGroup.transpose y⁻¹ = x
  rw [h2]
  exact Subtype.ext (by simp [Matrix.SpecialLinearGroup.transpose])

theorem invTranspose_injective : Function.Injective (invTranspose n F) := fun x y h => by
  rw [← invTranspose_invTranspose x, h, invTranspose_invTranspose]

theorem invTranspose_transvection {i j : Fin n} (hij : i ≠ j) (c : F) :
    invTranspose n F (transvection hij c) = transvection hij.symm (-c) := by
  refine Subtype.ext ?_
  rw [coe_invTranspose, Matrix.SpecialLinearGroup.transvection_inv, coe_transvection_eq,
    coe_transvection_eq]
  simp

section Main

variable [Finite F]

theorem aut_form_of_fixes_signs (h2 : (2 : F) ≠ 0) (hn : 3 ≤ n) (α : SL(n, F) →* SL(n, F))
    (hα : Function.Injective α) (hz : ∀ T : Pair n, α (zElt F T) = zElt F T)
    (hL : ∀ T : Pair n, ∀ g ∈ Lc F T, α g ∈ Lc F T) :
    ∃ (g : GL (Fin n) F) (φ : F ≃+* F) (ε : Bool), ∀ x : SL(n, F),
      ((α x : SL(n, F)) : Matrix (Fin n) (Fin n) F) =
        (g : Matrix (Fin n) (Fin n) F) *
          φ.mapMatrix (if ε then (((x⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F))ᵀ
            else (x : Matrix (Fin n) (Fin n) F)) *
          ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := fun e => by
    have := congrArg Fin.val e
    simp at this
  by_cases hU : IsU α ⟨0, by omega⟩ ⟨1, by omega⟩ h01
  · have hroot : ∀ (i j : Fin n) (hij : i ≠ j) (s : F),
        ∃ t, α (transvection hij s) = transvection hij t := fun i j hij =>
      (isU_iff_isU h2 hn α hα hz hL _ _ h01 i j hij).mp hU
    obtain ⟨D, φ, hD⟩ := exists_conj_mapMatrix_of_root_stable hn α hα hroot
    exact ⟨D, φ, false, by simpa using hD⟩
  · have hroot : ∀ (i j : Fin n) (hij : i ≠ j) (s : F),
        ∃ t, ((invTranspose n F).comp α) (transvection hij s) = transvection hij t := by
      intro i j hij s
      have hLij : IsL α i j hij := (isU_or_isL h2 hn α hz hL hij).resolve_left fun h =>
        hU ((isU_iff_isU h2 hn α hα hz hL i j hij _ _ h01).mp h)
      obtain ⟨c, hc⟩ := hLij s
      exact ⟨-c, by simp only [MonoidHom.comp_apply, hc, invTranspose_transvection]⟩
    obtain ⟨D, φ, hD⟩ := exists_conj_mapMatrix_of_root_stable hn ((invTranspose n F).comp α)
      (invTranspose_injective.comp hα) hroot
    let g : GL (Fin n) F :=
      ⟨(((D⁻¹ : GL (Fin n) F)) : Matrix (Fin n) (Fin n) F)ᵀ, (D : Matrix (Fin n) (Fin n) F)ᵀ,
        by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one],
        by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩
    refine ⟨g, φ, true, fun x => ?_⟩
    have h1 : α x = invTranspose n F (((invTranspose n F).comp α) x) :=
      (invTranspose_invTranspose _).symm
    rw [h1, coe_invTranspose, ← map_inv, hD (x⁻¹)]
    simp only [↓reduceIte, Matrix.transpose_mul]
    have e : (φ.mapMatrix (((x⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F)))ᵀ =
        φ.mapMatrix ((((x⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F))ᵀ) := by
      simp only [RingEquiv.mapMatrix_apply, Matrix.transpose_map]
    rw [e]
    exact (Matrix.mul_assoc _ _ _).symm

end Main

end CFSG.ClassicalInvolution.ModelFacts.LinearAut
