module

public import CFSG.GroupTheory.ABGLocalTools.FrobeniusFixedPoints

public section

namespace CFSG.LinearPGroup

open Module Matrix

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K] [IsAlgClosed K]

private noncomputable def linHom (P : Subgroup (GL ι K)) : P →* Module.End K (ι → K) :=
  (Matrix.toLinAlgEquiv' : Matrix ι ι K ≃ₐ[K] Module.End K (ι → K)).toRingEquiv.toMonoidHom.comp
    ((Units.coeHom (Matrix ι ι K)).comp P.subtype)

private theorem linHom_apply (P : Subgroup (GL ι K)) (x : P) (v : ι → K) :
    linHom P x v = ((x : GL ι K) : Matrix ι ι K) *ᵥ v := by
  simp [linHom, Matrix.toLinAlgEquiv'_apply]

private theorem linHom_injective (P : Subgroup (GL ι K)) : Function.Injective (linHom P) := by
  intro x y h
  apply Subtype.ext
  apply Units.ext
  exact (Matrix.toLinAlgEquiv' : Matrix ι ι K ≃ₐ[K] Module.End K (ι → K)).injective h

private theorem linHom_apply_eq_zero_iff (P : Subgroup (GL ι K)) (x : P) (v : ι → K) :
    linHom P x v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have h1 : linHom P (x⁻¹) (linHom P x v) = 0 := by rw [h, map_zero]
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at h1
  · intro h
    rw [h, map_zero]

private noncomputable def weightSpace (P : Subgroup (GL ι K)) (A : Subgroup P) (χ : A → K) :
    Submodule K (ι → K) :=
  ⨅ a : A, Module.End.eigenspace (linHom P (a : P)) (χ a)

private theorem mem_weightSpace (P : Subgroup (GL ι K)) (A : Subgroup P) (χ : A → K)
    (v : ι → K) :
    v ∈ weightSpace P A χ ↔ ∀ a : A, linHom P (a : P) v = χ a • v := by
  simp [weightSpace, Module.End.mem_eigenspace_iff]

private abbrev Weight (P : Subgroup (GL ι K)) (A : Subgroup P) : Type _ :=
  {χ : A → K // weightSpace P A χ ≠ ⊥}

private def actFun {H : Type*} [Group H] (β : MulAut H) (χ : H → K) : H → K := fun a => χ (β.symm a)

variable (P : Subgroup (GL ι K)) (A : Subgroup P)

section Decomposition

private theorem isFinitelySemisimple_linHom (hcard : (Nat.card A : K) ≠ 0) (a : A) :
    Module.End.IsFinitelySemisimple (linHom P (a : P)) := by
  apply CFSG.ABGLocalTools.isFinitelySemisimple_of_pow_eq_one (m := Nat.card A)
  · rw [← map_pow]
    have ha : (a : P) ^ Nat.card A = 1 := by
      rw [← Subgroup.coe_pow, pow_card_eq_one', Subgroup.coe_one]
    rw [ha, map_one]
  · exact hcard

private theorem commute_linHom (hA : ∀ a b : A, a * b = b * a) (a b : A) :
    Commute (linHom P (a : P)) (linHom P (b : P)) := by
  show linHom P (a : P) * linHom P (b : P) = linHom P (b : P) * linHom P (a : P)
  rw [← map_mul, ← map_mul, ← Subgroup.coe_mul, ← Subgroup.coe_mul, hA a b]

private theorem iSupIndep_weightSpace_and_iSup_eq_top
    (hA : ∀ a b : A, a * b = b * a) (hcard : (Nat.card A : K) ≠ 0) :
    iSupIndep (weightSpace P A) ∧ ⨆ χ : A → K, weightSpace P A χ = ⊤ := by
  have hcomm : ∀ a b : A, Commute (linHom P (a : P)) (linHom P (b : P)) :=
    commute_linHom P A hA
  have hss : ∀ a : A, Module.End.IsFinitelySemisimple (linHom P (a : P)) :=
    isFinitelySemisimple_linHom P A hcard
  exact CFSG.ABGLocalTools.iSupIndep_iInf_eigenspace_and_iSup_eq_top
    (fun a : A => linHom P (a : P)) hcomm hss

end Decomposition

section Weights

private theorem weight_one {χ : A → K} (hχ : weightSpace P A χ ≠ ⊥) : χ 1 = 1 := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
  have h1 : linHom P ((1 : A) : P) v = χ 1 • v := (mem_weightSpace P A χ v).1 hv 1
  rw [Subgroup.coe_one, map_one, Module.End.one_apply] at h1
  have h2 : χ 1 • v = (1 : K) • v := by
    rw [one_smul]
    exact h1.symm
  exact smul_left_injective K hv0 h2

private theorem weight_mul {χ : A → K} (hχ : weightSpace P A χ ≠ ⊥) (a b : A) :
    χ (a * b) = χ a * χ b := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
  have ha : linHom P (a : P) v = χ a • v := (mem_weightSpace P A χ v).1 hv a
  have hb : linHom P (b : P) v = χ b • v := (mem_weightSpace P A χ v).1 hv b
  have hab : linHom P ((a * b : A) : P) v = χ (a * b) • v :=
    (mem_weightSpace P A χ v).1 hv (a * b)
  have h1 : linHom P ((a * b : A) : P) v = (χ a * χ b) • v := by
    rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hb, map_smul, ha, smul_smul, mul_comm]
  rw [hab] at h1
  exact smul_left_injective K hv0 h1

private theorem weight_ne_zero {χ : A → K} (hχ : weightSpace P A χ ≠ ⊥) (a : A) : χ a ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
  have ha : linHom P (a : P) v = χ a • v := (mem_weightSpace P A χ v).1 hv a
  rw [h0, zero_smul] at ha
  exact hv0 ((linHom_apply_eq_zero_iff P (a : P) v).1 ha)

private noncomputable def weightUnits {χ : A → K} (hχ : weightSpace P A χ ≠ ⊥) : A →* Kˣ :=
  MonoidHom.mk' (fun a => Units.mk0 (χ a) (weight_ne_zero P A hχ a)) fun a b => by
    apply Units.ext
    simp only [Units.val_mk0]
    exact weight_mul P A hχ a b

private theorem weightUnits_apply {χ : A → K} (hχ : weightSpace P A χ ≠ ⊥) (a : A) :
    ((weightUnits P A hχ a : Kˣ) : K) = χ a := rfl

private theorem eq_of_forall_weight_eq (htop : ⨆ χ : A → K, weightSpace P A χ = ⊤)
    {a b : A} (h : ∀ χ : A → K, weightSpace P A χ ≠ ⊥ → χ a = χ b) : a = b := by
  have hfun : linHom P (a : P) = linHom P (b : P) := by
    apply LinearMap.ext
    intro v
    have hv : v ∈ ⨆ χ : A → K, weightSpace P A χ := by rw [htop]; exact Submodule.mem_top
    refine Submodule.iSup_induction _ (motive := fun v => linHom P (a : P) v = linHom P (b : P) v)
      hv ?_ ?_ ?_
    · intro χ w hw
      by_cases hχ : weightSpace P A χ = ⊥
      · rw [hχ, Submodule.mem_bot] at hw
        subst hw
        simp
      · rw [(mem_weightSpace P A χ w).1 hw a, (mem_weightSpace P A χ w).1 hw b, h χ hχ]
    · simp
    · intro x y hx hy
      rw [map_add, map_add, hx, hy]
  exact Subtype.ext (linHom_injective P hfun)

end Weights

section Action

variable [A.Normal]

private theorem weightSpace_actFun_ne_bot (x : P) {χ : A → K}
    (hχ : weightSpace P A χ ≠ ⊥) :
    weightSpace P A (actFun (MulAut.conjNormal x) χ) ≠ ⊥ := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
  refine (Submodule.ne_bot_iff _).2 ⟨linHom P x v, ?_, ?_⟩
  · rw [mem_weightSpace]
    intro a
    have hβ : ((MulAut.conjNormal x).symm a : P) = x⁻¹ * (a : P) * x :=
      MulAut.conjNormal_symm_apply x a
    have hcomm : (a : P) * x = x * ((MulAut.conjNormal x).symm a : P) := by
      rw [hβ]
      group
    have hva : linHom P ((MulAut.conjNormal x).symm a : P) v =
        actFun (MulAut.conjNormal x) χ a • v :=
      (mem_weightSpace P A χ v).1 hv ((MulAut.conjNormal x).symm a)
    calc
      linHom P (a : P) (linHom P x v) = linHom P ((a : P) * x) v := by
        rw [← Module.End.mul_apply, ← map_mul]
      _ = linHom P (x * ((MulAut.conjNormal x).symm a : P)) v := by rw [hcomm]
      _ = linHom P x (linHom P ((MulAut.conjNormal x).symm a : P) v) := by
        rw [map_mul, Module.End.mul_apply]
      _ = linHom P x (actFun (MulAut.conjNormal x) χ a • v) := by rw [hva]
      _ = actFun (MulAut.conjNormal x) χ a • linHom P x v := by rw [map_smul]
  · intro h0
    exact hv0 ((linHom_apply_eq_zero_iff P x v).1 h0)

private noncomputable def weightPerm (x : P) : Equiv.Perm (Weight P A) where
  toFun χ := ⟨actFun (MulAut.conjNormal x) χ.1, weightSpace_actFun_ne_bot P A x χ.2⟩
  invFun χ := ⟨actFun (MulAut.conjNormal x⁻¹) χ.1, weightSpace_actFun_ne_bot P A x⁻¹ χ.2⟩
  left_inv χ := by
    apply Subtype.ext
    funext a
    change χ.1 ((MulAut.conjNormal x).symm ((MulAut.conjNormal x⁻¹).symm a)) = χ.1 a
    rw [show (MulAut.conjNormal x⁻¹).symm = MulAut.conjNormal x from by
      rw [show MulAut.conjNormal x⁻¹ = (MulAut.conjNormal x)⁻¹ from map_inv _ _]
      rfl]
    exact congrArg χ.1 (MulEquiv.symm_apply_apply (MulAut.conjNormal x) a)
  right_inv χ := by
    apply Subtype.ext
    funext a
    change χ.1 ((MulAut.conjNormal x⁻¹).symm ((MulAut.conjNormal x).symm a)) = χ.1 a
    rw [show (MulAut.conjNormal x⁻¹).symm = MulAut.conjNormal x from by
      rw [show MulAut.conjNormal x⁻¹ = (MulAut.conjNormal x)⁻¹ from map_inv _ _]
      rfl]
    exact congrArg χ.1 (MulEquiv.apply_symm_apply (MulAut.conjNormal x) a)

private noncomputable def weightAction : P →* Equiv.Perm (Weight P A) where
  toFun := weightPerm P A
  map_one' := by
    apply Equiv.ext
    intro χ
    apply Subtype.ext
    funext a
    change actFun (MulAut.conjNormal (1 : P)) χ.1 a = χ.1 a
    rw [map_one]
    rfl
  map_mul' := by
    intro x y
    apply Equiv.ext
    intro χ
    apply Subtype.ext
    funext a
    change actFun (MulAut.conjNormal (x * y)) χ.1 a =
      actFun (MulAut.conjNormal x) (actFun (MulAut.conjNormal y) χ.1) a
    rw [map_mul]
    simp only [actFun, ← MulAut.inv_def]
    rw [_root_.mul_inv_rev, MulAut.mul_apply]

private theorem weightAction_eq_one_iff (htop : ⨆ χ : A → K, weightSpace P A χ = ⊤) (x : P) :
    weightAction P A x = 1 ↔ ∀ a : A, x * (a : P) = (a : P) * x := by
  constructor
  · intro hx a
    have h1 : ∀ χ : Weight P A, (weightPerm P A x χ).1 = χ.1 := fun χ =>
      congrArg Subtype.val (Equiv.congr_fun hx χ)
    have h2 : ∀ χ : A → K, weightSpace P A χ ≠ ⊥ →
        χ ((MulAut.conjNormal x).symm a) = χ a := by
      intro χ hχ
      exact congrFun (h1 ⟨χ, hχ⟩) a
    have h3 : (MulAut.conjNormal x).symm a = a :=
      eq_of_forall_weight_eq P A htop fun χ hχ => h2 χ hχ
    have h4 : ((MulAut.conjNormal x).symm a : P) = (a : P) := congrArg Subtype.val h3
    have h5 : (a : P) * x = x * (a : P) := by
      calc
        (a : P) * x = x * (x⁻¹ * (a : P) * x) := by group
        _ = x * ((MulAut.conjNormal x).symm a : P) := by
          rw [← MulAut.conjNormal_symm_apply x a]
        _ = x * (a : P) := by rw [h4]
    exact h5.symm
  · intro hx
    apply Equiv.ext
    intro χ
    apply Subtype.ext
    funext a
    change χ.1 ((MulAut.conjNormal x).symm a) = χ.1 a
    have hβ : ((MulAut.conjNormal x).symm a : A) = a := by
      apply Subtype.ext
      rw [MulAut.conjNormal_symm_apply x a]
      calc
        x⁻¹ * (a : P) * x = x⁻¹ * (x * (a : P)) := by
          rw [hx a]
          group
        _ = (a : P) := by group
    rw [hβ]

end Action

section Main

theorem exists_weights_of_normal_commutative
    (P : Subgroup (GL ι K)) [Finite P] (A : Subgroup P) [A.Normal]
    (hA : ∀ a b : A, a * b = b * a) (hcard : (Nat.card A : K) ≠ 0) :
    ∃ (k : ℕ) (_ : k ≤ Fintype.card ι) (χ : Fin k → (A →* Kˣ))
      (π : P →* Equiv.Perm (Fin k)),
      (∀ a : A, (∀ i, χ i a = 1) → a = 1) ∧
      (∀ x : P, π x = 1 → ∀ a : A, x * (a : P) = (a : P) * x) := by
  classical
  obtain ⟨hind, htop⟩ := iSupIndep_weightSpace_and_iSup_eq_top P A hA hcard
  let W := Weight P A
  haveI : Fintype W := hind.fintypeNeBotOfFiniteDimensional
  let k := Fintype.card W
  let e : W ≃ Fin k := Fintype.equivFin W
  have hk : k ≤ Fintype.card ι := by
    have h := hind.subtype_ne_bot_le_finrank
    rw [Module.finrank_fintype_fun_eq_card] at h
    simpa [k, W] using h
  let χ : Fin k → (A →* Kˣ) := fun i => weightUnits P A (e.symm i).2
  let π : P →* Equiv.Perm (Fin k) :=
    (Equiv.permCongrHom e).toMonoidHom.comp (weightAction P A)
  refine ⟨k, hk, χ, π, ?_, ?_⟩
  · intro a ha
    apply eq_of_forall_weight_eq P A htop
    intro ψ hψ
    have h1 : weightUnits P A hψ a = 1 := by
      have h2 := ha (e ⟨ψ, hψ⟩)
      simpa [χ] using h2
    have h3 : ψ a = 1 := by
      have h4 := congrArg Units.val h1
      rwa [weightUnits_apply] at h4
    rw [h3, weight_one P A hψ]
  · intro x hx
    have hπ : weightAction P A x = 1 := by
      have h2 : (Equiv.permCongrHom e).symm ((Equiv.permCongrHom e) (weightAction P A x)) =
          (Equiv.permCongrHom e).symm 1 :=
        congrArg (Equiv.permCongrHom e).symm (by simpa [π] using hx)
      rwa [MulEquiv.symm_apply_apply, map_one] at h2
    exact (weightAction_eq_one_iff P A htop x).1 hπ

end Main

end CFSG.LinearPGroup

end
