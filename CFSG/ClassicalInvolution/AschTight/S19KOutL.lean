module

public import CFSG.ClassicalInvolution.AschTight.S19KLin
public import CFSG.ClassicalInvolution.AschTight.S19KOutG

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19K

open CFSG.ClassicalInvolution
open scoped MatrixGroups commutatorElement

variable {F : Type} [Field F]

@[expose] def conjSL (M : GL (Fin 3) F) : SL(3, F) →* SL(3, F) where
  toFun x := ⟨(M : Matrix (Fin 3) (Fin 3) F) * (x : Matrix (Fin 3) (Fin 3) F) *
      ((M⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F), by
    rw [Matrix.det_mul, Matrix.det_mul, x.2, mul_one, ← Matrix.det_mul, Units.mul_inv,
      Matrix.det_one]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by
    change (M : Matrix (Fin 3) (Fin 3) F) * ((x : Matrix (Fin 3) (Fin 3) F) *
        (y : Matrix (Fin 3) (Fin 3) F)) * ((M⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((M : Matrix (Fin 3) (Fin 3) F) * (x : Matrix (Fin 3) (Fin 3) F) *
        ((M⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) *
      ((M : Matrix (Fin 3) (Fin 3) F) * (y : Matrix (Fin 3) (Fin 3) F) *
        ((M⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))
    calc (M : Matrix (Fin 3) (Fin 3) F) * ((x : Matrix (Fin 3) (Fin 3) F) *
          (y : Matrix (Fin 3) (Fin 3) F)) * ((M⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        (M : Matrix (Fin 3) (Fin 3) F) * (x : Matrix (Fin 3) (Fin 3) F) *
          (((M⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (M : Matrix (Fin 3) (Fin 3) F)) *
          (y : Matrix (Fin 3) (Fin 3) F) * ((M⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
          rw [Units.inv_mul, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc])

theorem toGL_conjSL (M : GL (Fin 3) F) (x : SL(3, F)) :
    Matrix.SpecialLinearGroup.toGL (conjSL M x) = M * Matrix.SpecialLinearGroup.toGL x * M⁻¹ :=
  Units.ext rfl

theorem isBlockDiag_of_isBlockScalar {M : Matrix (Fin 3) (Fin 3) F} (hM : IsBlockScalar M) :
    IsBlockDiag M :=
  ⟨hM.2.1, hM.2.2.2.1, hM.2.2.2.2.1, hM.2.2.2.2.2.1⟩

theorem toGL_lift {α : SL(3, F) →* SL(3, F)} {G : GL (Fin 3) F} {ε : Bool}
    (hform : ∀ x, ((α x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      (G : Matrix (Fin 3) (Fin 3) F) * twist ε x * ((G⁻¹ : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F)) (x : SL(3, F)) :
    Matrix.SpecialLinearGroup.toGL (α x) =
      (MulAut.conj G * dpow ε : MulAut (GL (Fin 3) F)) (Matrix.SpecialLinearGroup.toGL x) := by
  apply Units.ext
  rw [MulAut.mul_apply, MulAut.conj_apply, Units.val_mul, Units.val_mul]
  change ((α x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = _
  rw [hform]
  congr 2
  cases ε
  · rfl
  · show (((x⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)).transpose =
      (((Matrix.SpecialLinearGroup.toGL x)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).transpose
    rw [← map_inv]
    rfl

variable [Finite F]

theorem lift_surjective {α : SL(3, F) →* SL(3, F)} {G : GL (Fin 3) F} {ε : Bool}
    (hform : ∀ x, ((α x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      (G : Matrix (Fin 3) (Fin 3) F) * twist ε x * ((G⁻¹ : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F)) : Function.Surjective α := by
  refine Finite.injective_iff_surjective.mp fun x y hxy => ?_
  have h1 := toGL_lift hform x
  rw [hxy, toGL_lift hform y] at h1
  exact Matrix.SpecialLinearGroup.toGL_injective ((MulAut.conj G * dpow ε).injective h1).symm

omit [Finite F] in
theorem conjSL_mul (M₁ M₂ : GL (Fin 3) F) (x : SL(3, F)) :
    conjSL (M₁ * M₂) x = conjSL M₁ (conjSL M₂ x) := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [toGL_conjSL, toGL_conjSL, toGL_conjSL]
  group

omit [Finite F] in
theorem hyp_of_mem_fixingSubgroup {E : Type} [Group E] (θ : SL(3, F) →* E)
    (hker : θ.ker ≤ Subgroup.center SL(3, F)) {h : MulAut E}
    (hh : h ∈ fixingSubgroup (MulAut E)
      (((Models.rootSL2 F (n := 3) (by norm_num)).map θ : Subgroup E) : Set E)) :
    ∃ (ι : ↥((Models.rootSL2 F (n := 3) (by norm_num)).map θ) ≃* SL(2, F))
        (g : GL (Fin 2) F),
      ∀ x : ↥((Models.rootSL2 F (n := 3) (by norm_num)).map θ),
        ((ι.symm (Asc77.AscL62.semilinHom g (RingEquiv.refl _) (ι x)) :
          ↥((Models.rootSL2 F (n := 3) (by norm_num)).map θ)) : E) = h x := by
  have hR : ∀ r ∈ Models.rootSL2 F (n := 3) (by norm_num), r ∈ Subgroup.center SL(3, F) →
      r = 1 := fun r hr hc => eq_one_of_mem_center_rootSL2 hr hc
  refine ⟨(restrictEquiv θ hker hR).symm.trans stdEquiv, 1, fun x => ?_⟩
  have h1 : ∀ A : SL(2, F), Asc77.AscL62.semilinHom 1 (RingEquiv.refl F) A = A := fun A =>
    Subtype.ext (by rw [Asc77.AscL62.coe_semilinHom]; simp)
  rw [h1, MulEquiv.symm_apply_apply]
  exact ((mem_fixingSubgroup_iff (MulAut E)).mp hh x x.2).symm

theorem fg2Lin (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hcl : RouteD.Gaps.LinearAutClassification F 3) {E : Type} [Group E] (θ : SL(3, F) →* E)
    (hθ : Function.Surjective θ) (hker : θ.ker ≤ Subgroup.center SL(3, F)) :
    ⁅⁅fixingSubgroup (MulAut E)
        (((Models.rootSL2 F (n := 3) (by norm_num)).map θ : Subgroup E) : Set E),
      fixingSubgroup (MulAut E)
        (((Models.rootSL2 F (n := 3) (by norm_num)).map θ : Subgroup E) : Set E)⁆,
      ⁅fixingSubgroup (MulAut E)
        (((Models.rootSL2 F (n := 3) (by norm_num)).map θ : Subgroup E) : Set E),
      fixingSubgroup (MulAut E)
        (((Models.rootSL2 F (n := 3) (by norm_num)).map θ : Subgroup E) : Set E)⁆⁆ = ⊥ := by
  set H := fixingSubgroup (MulAut E)
    (((Models.rootSL2 F (n := 3) (by norm_num)).map θ : Subgroup E) : Set E)
  have h2 : (2 : F) ≠ 0 := Models.two_ne_zero_of_odd_natCard hodd
  have : Group.IsPerfect (Models.rootSL2 F (n := 3) (by norm_num)) :=
    (Models.isClassicalSL2_rootSL2 (K := F) h2 (n := 3) (by norm_num)).isPerfect (by omega)
  set N := innerDiag θ Matrix.SpecialLinearGroup.toGL Matrix.SpecialLinearGroup.toGL_injective ⊤
    (fun M _ x => ⟨conjSL M x, toGL_conjSL M x⟩)
  refine derived_derived_eq_bot (A := H ⊓ N) ?_ ?_
  · rw [Subgroup.commutator_le]
    intro h₁ hh₁ h₂ hh₂
    refine ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      exact H.mul_mem (H.mul_mem (H.mul_mem hh₁ hh₂) (H.inv_mem hh₁)) (H.inv_mem hh₂)
    obtain ⟨α₁, G₁, ε₁, hα₁, hf₁, -⟩ :=
      lin_lift_data hodd h5 hcl θ hθ hker h₁ (hyp_of_mem_fixingSubgroup θ hker hh₁)
    obtain ⟨α₂, G₂, ε₂, hα₂, hf₂, -⟩ :=
      lin_lift_data hodd h5 hcl θ hθ hker h₂ (hyp_of_mem_fixingSubgroup θ hker hh₂)
    have hsurj : Function.Surjective (α₂.comp α₁) := by
      rw [MonoidHom.coe_comp]
      exact (lift_surjective hf₂).comp (lift_surjective hf₁)
    exact commutator_mem_innerDiag θ _ _ ⊤ _ (fun _ _ => trivial) trivial trivial hα₁ hα₂
      (toGL_lift hf₁) (toGL_lift hf₂) hsurj
  ·
    have key : ∀ a ∈ H ⊓ N, ∃ M : GL (Fin 3) F,
        IsBlockScalar (M : Matrix (Fin 3) (Fin 3) F) ∧ ∀ x, a (θ x) = θ (conjSL M x) := by
      rintro a ⟨haH, M, -, hM⟩
      have hconj : ∀ x, a (θ x) = θ (conjSL M x) := fun x => hM x _ (toGL_conjSL M x)
      have hab := ModelFacts.UnitaryAut.hom_eq_of_central_ker_perfect hker
        ((conjSL M).comp (Models.rootSL2 F (n := 3) _).subtype)
        (Models.rootSL2 F (n := 3) _).subtype fun r => by
          rw [MonoidHom.comp_apply, ← hconj]
          exact (mem_fixingSubgroup_iff (MulAut E)).mp haH _ ⟨r, r.2, rfl⟩
      refine ⟨M, blockSL3_mem_commute fun x hx => ?_, hconj⟩
      have h1 := congrArg (fun y : SL(3, F) => (y : Matrix (Fin 3) (Fin 3) F))
        (DFunLike.congr_fun hab ⟨x, hx⟩)
      change (M : Matrix (Fin 3) (Fin 3) F) * (x : Matrix (Fin 3) (Fin 3) F) *
        ((M⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = x at h1
      calc (M : Matrix (Fin 3) (Fin 3) F) * (x : Matrix (Fin 3) (Fin 3) F) =
          (M : Matrix (Fin 3) (Fin 3) F) * (x : Matrix (Fin 3) (Fin 3) F) *
            (((M⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
              (M : Matrix (Fin 3) (Fin 3) F)) := by rw [Units.inv_mul, Matrix.mul_one]
        _ = _ := by rw [← Matrix.mul_assoc, h1]
    intro a ha b hb
    obtain ⟨M₁, hM₁, ha'⟩ := key a ha
    obtain ⟨M₂, hM₂, hb'⟩ := key b hb
    have hMM : M₁ * M₂ = M₂ * M₁ :=
      Units.ext (commute_of_isBlockDiag (isBlockDiag_of_isBlockScalar hM₁) hM₂)
    ext e
    obtain ⟨x, rfl⟩ := hθ e
    rw [MulAut.mul_apply, MulAut.mul_apply, hb', ha', ha', hb', ← conjSL_mul, ← conjSL_mul, hMM]

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19K
