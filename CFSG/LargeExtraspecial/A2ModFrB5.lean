module

public import CFSG.LargeExtraspecial.A2ModFrBMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.A2Mod.FrB

open Module Matrix CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.RankThree.OrthogonalInvolutions

section Tinv

variable {m : ℕ} {R : Type*} [CommRing R]

@[expose] def tinv : SpecialLinearGroup (Fin m) R →* SpecialLinearGroup (Fin m) R where
  toFun g := SpecialLinearGroup.transpose g⁻¹
  map_one' := by
    apply Subtype.ext
    show ((1 : SpecialLinearGroup (Fin m) R)⁻¹).1ᵀ = (1 : SpecialLinearGroup (Fin m) R).1
    rw [inv_one]
    exact transpose_one
  map_mul' g h := by
    apply Subtype.ext
    show ((g * h)⁻¹ : SpecialLinearGroup (Fin m) R).1ᵀ =
      (g⁻¹ : SpecialLinearGroup (Fin m) R).1ᵀ * (h⁻¹ : SpecialLinearGroup (Fin m) R).1ᵀ
    rw [_root_.mul_inv_rev]
    exact transpose_mul _ _

theorem coe_tinv (g : SpecialLinearGroup (Fin m) R) :
    (tinv g : SpecialLinearGroup (Fin m) R).1 = (g⁻¹ : SpecialLinearGroup (Fin m) R).1ᵀ := rfl

theorem tinv_tv (v φ : Fin m → ZMod 2) : tinv (tv v φ) = tv φ v := by
  by_cases h : φ ⬝ᵥ v = 0
  · have h' : v ⬝ᵥ φ = 0 := by rwa [dotProduct_comm]
    refine Subtype.ext ?_
    rw [coe_tinv, tv_inv h]
    have e1 := coe_tv (v := v) (φ := -φ) (by rw [neg_dotProduct, h, neg_zero])
    have e2 := coe_tv (v := φ) (φ := v) h'
    refine (congrArg transpose e1).trans ((?_ : _ = _).trans e2.symm)
    rw [transpose_add, transpose_one, transpose_vecMulVec, ZModModule.neg_eq_self]
  · have h' : v ⬝ᵥ φ ≠ 0 := by rwa [dotProduct_comm]
    rw [tv_of_dotProduct_ne_zero h, tv_of_dotProduct_ne_zero h', map_one]

end Tinv

section J

variable {K : Type} [Field K] {b c : K}

noncomputable def wSwap {n : ℕ} {i j : Fin (n - 1)} (hij : i ≠ j) : spinGroup (quadMinus n K b c) :=
  (minusFrame n b c).longWeyl hij true true * (minusFrame n b c).longWeyl hij true false

omit [Field K] in
theorem longWeylSign_eq_one [Field K] (h2 : (2 : K) = 0) {n : ℕ} (i m : Fin n) :
    (longWeylSign i m : K) = 1 := by
  by_cases hm : m = i
  · rw [hm, longWeylSign_self, neg_one_eq_one_of_two_eq_zero h2]
  · exact longWeylSign_of_ne hm

theorem spinAction_wSwap_vec (h2 : (2 : K) = 0) {n : ℕ} {i j : Fin (n - 1)} (hij : i ≠ j)
    (m : Fin (n - 1)) (r : Bool) :
    spinAction (quadMinus n K b c) (wSwap (b := b) (c := c) hij) (minusVec n m r) =
      minusVec n m (if m = i ∨ m = j then !r else r) := by
  have e := (minusFrame n b c).spinAction_longWeyl_vec hij true false m r
  have e' := (minusFrame n b c).spinAction_longWeyl_vec hij true true (Equiv.swap i j m)
    (longWeylBool i j true false m r)
  simp only [minusFrame_vec, longWeylSign_eq_one h2, one_smul, Equiv.swap_apply_self] at e e'
  rw [wSwap, map_mul, LinearEquiv.mul_apply, e, e']
  congr 1
  by_cases hmi : m = i
  · subst hmi
    simp [longWeylBool]
  · by_cases hmj : m = j
    · subst hmj
      simp [longWeylBool]
    · simp [longWeylBool, hmi, hmj, Equiv.swap_apply_of_ne_of_ne hmi hmj]

noncomputable def jFive : spinGroup (quadMinus 5 K b c) :=
  wSwap (b := b) (c := c) (by decide : (0 : Fin (5 - 1)) ≠ 1) *
    wSwap (b := b) (c := c) (by decide : (2 : Fin (5 - 1)) ≠ 3)

theorem spinAction_jFive_vec (h2 : (2 : K) = 0) (m : Fin (5 - 1)) (r : Bool) :
    spinAction (quadMinus 5 K b c) (jFive (b := b) (c := c)) (minusVec 5 m r) =
      minusVec 5 m (!r) := by
  rw [jFive, map_mul, LinearEquiv.mul_apply, spinAction_wSwap_vec h2, spinAction_wSwap_vec h2]
  fin_cases m <;> simp

theorem jFive_conj_lr (h2 : (2 : K) = 0) {i j : Fin (5 - 1)} (hij : i ≠ j) (s t : Bool) :
    jFive * lr 5 b c hij s t * jFive⁻¹ = lr 5 b c hij (!s) (!t) := by
  have hi := spinAction_jFive_vec (b := b) (c := c) h2 i s
  have hj := spinAction_jFive_vec (b := b) (c := c) h2 j t
  rw [← one_smul K (minusVec 5 i (!s))] at hi
  rw [← one_smul K (minusVec 5 j (!t))] at hj
  rw [lr, (minusFrame 5 b c).conj_longRoot _ hij s t hij (!s) (!t) hi hj, one_mul, one_mul]

variable [Finite K] (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hK : Nat.card K = 2)

theorem jFive_conj_leviZ (g : SpecialLinearGroup (Fin (5 - 1)) (ZMod 2)) :
    jFive * leviZ 5 b c (by omega) hirr hK g * jFive⁻¹ =
      leviZ 5 b c (by omega) hirr hK (tinv g) := by
  have h2 := two_eq_zero_of_card hK
  set f₁ : SpecialLinearGroup (Fin (5 - 1)) (ZMod 2) →* spinGroup (quadMinus 5 K b c) :=
    (MulAut.conj (jFive (b := b) (c := c))).toMonoidHom.comp (leviZ 5 b c (by omega) hirr hK)
  set f₂ : SpecialLinearGroup (Fin (5 - 1)) (ZMod 2) →* spinGroup (quadMinus 5 K b c) :=
    (leviZ 5 b c (by omega) hirr hK).comp tinv
  have hf : f₁ = f₂ := by
    refine MonoidHom.eq_of_eqOn_dense
      (SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field) ?_
    rintro _ ⟨⟨i, j, hij, a⟩, rfl⟩
    rw [TransvectionStruct.toSpecialLinearGroup_mk]
    rcases zmodTwo_eq_zero_or_one a with rfl | rfl
    · have h1 : SpecialLinearGroup.transvection hij (0 : ZMod 2) = 1 :=
        Subtype.ext (by rw [SpecialLinearGroup.transvection_coe, single_zero, add_zero]; rfl)
      rw [h1, map_one, map_one]
    · rw [← elemTv_eq_transvection hij]
      change jFive * leviZ 5 b c (by omega) hirr hK (elemTv i j) * jFive⁻¹ =
        leviZ 5 b c (by omega) hirr hK (tinv (elemTv i j))
      rw [tinv_tv, leviZ_elemTv_eq_lr 5 (by omega) hirr hK hij, jFive_conj_lr h2, Bool.not_true,
        Bool.not_false, lr_swap h2]
      exact (leviZ_elemTv_eq_lr 5 (by omega) hirr hK hij.symm).symm
  exact congrArg (fun f => f g) hf

end J

section Strong

variable {X : Type} [Group X] {D : Set X} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V} {ρ : X →* (V ≃ₗ[ZMod 2] V)}

theorem finrank_commSpaceOf_le_eight_of_swap (hA : A2Action D Q ρ)
    {Ψ : SpecialLinearGroup (Fin 4) (ZMod 2) →* X} {a b : X} (h : IsLeviNode D Ψ a b) (J : X)
    (hJ : ∀ v φ : Fin 4 → ZMod 2, φ ⬝ᵥ v = 0 → Ψ (tv φ v) = J * Ψ (tv v φ) * J⁻¹) :
    finrank (ZMod 2) (commSpaceOf ρ (Ψ.range ⊔ Subgroup.zpowers a ⊔ Subgroup.zpowers b)) ≤
      8 := by
  obtain ⟨-, hA'⟩ := hA.comp_sl (by omega) h.map_mem
  set e : Fin 4 → ZMod 2 := Pi.single 0 1 with he_def
  have he : e ≠ 0 := Pi.single_ne_zero_iff.mpr one_ne_zero
  have hAB : (∃ P : V, P ≠ 0 ∧ ∀ g ∈ pointGroup e, g ≠ 1 → P ∈ commSpace ((ρ.comp Ψ) g)) →
      ∃ P : V, P ≠ 0 ∧ ∀ g ∈ hyperplaneGroup e, g ≠ 1 → P ∈ commSpace ((ρ.comp Ψ) g) := by
    rintro ⟨P, hP0, hP⟩
    refine ⟨ρ J P, fun h0 => hP0 ((LinearEquiv.map_eq_zero_iff _).mp h0), fun g hg hg1 => ?_⟩
    obtain ⟨v, hv, rfl⟩ := mem_hyperplaneGroup.mp hg
    have hv0 : v ≠ 0 := by
      rintro rfl
      exact hg1 (tv_zero_left _)
    have hve : v ⬝ᵥ e = 0 := by rwa [dotProduct_comm]
    have hmem := apply_mem_commSpace_conj ρ J
      (hP (tv e v) (tv_mem_pointGroup e v) (tv_ne_one he hv0 hve))
    rw [← hJ e v hve] at hmem
    exact hmem
  have hBA : (∃ P : V, P ≠ 0 ∧ ∀ g ∈ hyperplaneGroup e, g ≠ 1 → P ∈ commSpace ((ρ.comp Ψ) g)) →
      ∃ P : V, P ≠ 0 ∧ ∀ g ∈ pointGroup e, g ≠ 1 → P ∈ commSpace ((ρ.comp Ψ) g) := by
    rintro ⟨P, hP0, hP⟩
    refine ⟨ρ J P, fun h0 => hP0 ((LinearEquiv.map_eq_zero_iff _).mp h0), fun g hg hg1 => ?_⟩
    obtain ⟨φ, hφ, rfl⟩ := mem_pointGroup.mp hg
    have hφ0 : φ ≠ 0 := by
      rintro rfl
      exact hg1 (tv_zero_right _)
    have heφ : e ⬝ᵥ φ = 0 := by rwa [dotProduct_comm]
    have hmem := apply_mem_commSpace_conj ρ J
      (hP (tv φ e) (tv_mem_hyperplaneGroup φ e) (tv_ne_one hφ0 he heφ))
    rw [← hJ φ e heφ] at hmem
    exact hmem
  by_cases hc : (∃ P : V, P ≠ 0 ∧ ∀ g ∈ pointGroup e, g ≠ 1 → P ∈ commSpace ((ρ.comp Ψ) g)) ∧
      ∃ P : V, P ≠ 0 ∧ ∀ g ∈ hyperplaneGroup e, g ≠ 1 → P ∈ commSpace ((ρ.comp Ψ) g)
  · obtain ⟨P, Pd, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
      exists_pointMaps_of_concurrent hA' le_rfl he he hc.1 hc.2
    have hP : IsPointMaps (ρ.comp Ψ) Q P Pd := ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    rw [h.commSpaceOf_eq_of_isPointMaps hA rfl hP, finrank_range_sup_range_eq h1 h2 h6]
  · have hnA := fun hcA => hc ⟨hcA, hAB hcA⟩
    have hnB := fun hcB => hc ⟨hBA hcB, hcB⟩
    have h1 := (hA'.common_point_or_finrank_le_three (A := pointGroup e)
      forall_mem_pointGroup_mem_transvectionSet).resolve_left hnA
    have h2 := (hA'.common_point_or_finrank_le_three (A := hyperplaneGroup e)
      forall_mem_hyperplaneGroup_mem_transvectionSet).resolve_left hnB
    have h3 := finrank_commSpaceOf_top_le_add (ρ := ρ.comp Ψ) (0 : Fin 4)
    rw [← he_def] at h3
    have h4 := h.finrank_commSpaceOf_le_add hA le_rfl
    rw [commSpaceOf_range] at h4
    omega

end Strong

section Five

variable {X : Type} [Group X] {D : Set X} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V} {ρ : X →* (V ≃ₗ[ZMod 2] V)}
  {K : Type} [Field K] [Finite K] {b c : K}

theorem finrank_commSpaceOf_top_le_ten (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hK : Nat.card K = 2) (Ψ : spinGroup (quadMinus 5 K b c) →* X)
    (hsurj : Function.Surjective Ψ) (hDc : ∀ g, ∀ e ∈ D, g * e * g⁻¹ ∈ D)
    (hA : A2Action D Q ρ) {i₀ j₀ : Fin (5 - 1)} (h₀ : i₀ ≠ j₀)
    (hmem : Ψ (lr 5 b c h₀ true false) ∈ D) :
    finrank (ZMod 2) (commSpaceOf ρ ⊤) ≤ 10 := by
  have hcls : ∀ x ∈ D, ∀ g : X, g * x * g⁻¹ ∈ D := fun x hx g => hDc g x hx
  have hall := fun {i j : Fin (5 - 1)} (hij : i ≠ j) (s t : Bool) =>
    map_lr_mem Ψ hcls (by omega) hirr hK h₀ hmem hij s t
  have h := finrank_commSpaceOf_top_le_add_two (by omega) hirr hK Ψ hsurj hDc hA hall
  have h8 := finrank_commSpaceOf_le_eight_of_swap hA (isLeviNode (by omega) hirr hK Ψ hcls hall)
    (Ψ jFive) fun v φ _ => by
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, ← tinv_tv, ← jFive_conj_leviZ hirr hK,
        map_mul, map_mul, map_inv]
  rw [longSub] at h
  omega

end Five

end CFSG.LargeExtraspecial.A2Mod.FrB
