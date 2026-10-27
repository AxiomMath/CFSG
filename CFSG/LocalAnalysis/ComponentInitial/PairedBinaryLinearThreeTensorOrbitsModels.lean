module

public import CFSG.LocalAnalysis.ComponentInitial.PairedBinaryLinearThreeTensorOrbitsGeneral

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.PairedTensorOrbits

open Module Matrix CFSG.ProperTwoGeneratedCore.PairedTensor
open CFSG.ProperTwoGeneratedCore.BinaryThreeSpace (Mat3 traceZero)

scoped instance addCommGroupSubV (p : Submodule (ZMod 2) V) : AddCommGroup p :=
  @Submodule.addCommGroup (ZMod 2) V _ (inferInstance : AddCommGroup V) _ p

scoped instance addCommGroupSubT (p : Submodule (ZMod 2) T) : AddCommGroup p :=
  @Submodule.addCommGroup (ZMod 2) T _ (inferInstance : AddCommGroup T) _ p

section Scalar

variable {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]

theorem eq_zero_or_eq_id_of_fixed {ρ : Representation (ZMod 2) G W} (hρ : ρ.IsIrreducible)
    (B : Set G) {x₀ : W} (hx₀ : x₀ ≠ 0) (hx₀fix : ∀ b ∈ B, ρ b x₀ = x₀)
    (hfix : ∀ x : W, (∀ b ∈ B, ρ b x = x) → x = 0 ∨ x = x₀) (f : W →ₗ[ZMod 2] W)
    (hf : ∀ g x, f (ρ g x) = ρ g (f x)) : f = 0 ∨ f = LinearMap.id := by
  obtain ⟨-, hirr⟩ := (isIrreducible_iff ρ).1 hρ
  have hker : ∀ F : W →ₗ[ZMod 2] W, (∀ g x, F (ρ g x) = ρ g (F x)) → F x₀ = 0 → F = 0 := by
    intro F hF h0
    have hinv : IsInv ρ (LinearMap.ker F) := fun g x hx => by
      rw [LinearMap.mem_ker] at hx ⊢
      rw [hF, hx, map_zero]
    rcases hirr _ hinv with h | h
    · have h1 : x₀ ∈ LinearMap.ker F := h0
      rw [h, Submodule.mem_bot] at h1
      exact absurd h1 hx₀
    · exact LinearMap.ker_eq_top.1 h
  rcases hfix (f x₀) fun b hb => by rw [← hf, hx₀fix b hb] with h | h
  · exact Or.inl (hker f hf h)
  · right
    have h1 := hker (f - LinearMap.id) (fun g x => by
      simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub, hf]) (by
      rw [LinearMap.sub_apply, h, LinearMap.id_apply, sub_self])
    exact sub_eq_zero.1 h1

theorem eq_smul_of_fixed {ρ : Representation (ZMod 2) G W} (hρ : ρ.IsIrreducible)
    (B : Set G) {x₀ : W} (hx₀ : x₀ ≠ 0) (hx₀fix : ∀ b ∈ B, ρ b x₀ = x₀)
    (hfix : ∀ x : W, (∀ b ∈ B, ρ b x = x) → x = 0 ∨ x = x₀) (f : W →ₗ[ZMod 2] W)
    (hf : ∀ g x, f (ρ g x) = ρ g (f x)) : ∃ c : ZMod 2, f = c • LinearMap.id := by
  rcases eq_zero_or_eq_id_of_fixed hρ B hx₀ hx₀fix hfix f hf with h | h
  · exact ⟨0, by rw [h, zero_smul]⟩
  · exact ⟨1, by rw [h, one_smul]⟩

end Scalar

theorem repN_eq_one_iff {g : S} : repN g = 1 ↔ g = 1 := by
  constructor
  · intro h
    have h1 : ((g⁻¹ : S) : Mat3) = 1 := by
      ext i j
      have h2 := congrArg (fun f : Module.End (ZMod 2) N => f (Pi.single i 1) j) h
      simp only [repN_apply, Module.End.one_apply] at h2
      rw [Matrix.single_vecMul, one_smul] at h2
      change ((g⁻¹ : S) : Mat3) i j = (Pi.single i (1 : ZMod 2) : N) j at h2
      rw [h2, Matrix.one_apply, Pi.single_apply]
      by_cases hij : i = j
      · subst hij
        simp
      · simp [hij, Ne.symm hij]
    have h2 : g⁻¹ = 1 := Units.ext h1
    rwa [inv_eq_one] at h2
  · rintro rfl
    exact map_one repN

@[expose] def glNHom : S →* (N ≃ₗ[ZMod 2] N) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) N).toMonoidHom.comp repN.asGroupHom

theorem glNHom_apply (g : S) (v : N) : glNHom g v = repN g v :=
  rfl

theorem glNHom_injective : Function.Injective glNHom := by
  rw [injective_iff_map_eq_one]
  intro g hg
  rw [← repN_eq_one_iff]
  refine LinearMap.ext fun v => ?_
  have h1 := congrArg (fun e : N ≃ₗ[ZMod 2] N => e v) hg
  exact h1

theorem glNHom_surjective : Function.Surjective glNHom := by
  intro e
  set M : Mat3 := (LinearMap.toMatrix' (e : N →ₗ[ZMod 2] N))ᵀ with hM
  set M' : Mat3 := (LinearMap.toMatrix' (e.symm : N →ₗ[ZMod 2] N))ᵀ with hM'
  have he : ∀ v : N, e v = v ᵥ* M := fun v => by
    rw [hM, Matrix.vecMul_transpose, LinearMap.toMatrix'_mulVec]
    rfl
  have he' : ∀ v : N, e.symm v = v ᵥ* M' := fun v => by
    rw [hM', Matrix.vecMul_transpose, LinearMap.toMatrix'_mulVec]
    rfl
  have h1 : M * M' = 1 := by
    rw [hM, hM', ← Matrix.transpose_mul, ← LinearMap.toMatrix'_mul]
    have h2 : (e.symm : N →ₗ[ZMod 2] N) * (e : N →ₗ[ZMod 2] N) = 1 := by
      ext v
      simp
    rw [h2, LinearMap.toMatrix'_one, Matrix.transpose_one]
  have h2 : M' * M = 1 := by
    rw [hM, hM', ← Matrix.transpose_mul, ← LinearMap.toMatrix'_mul]
    have h3 : (e : N →ₗ[ZMod 2] N) * (e.symm : N →ₗ[ZMod 2] N) = 1 := by
      ext v
      simp
    rw [h3, LinearMap.toMatrix'_one, Matrix.transpose_one]
  refine ⟨⟨M', M, h2, h1⟩, LinearEquiv.ext fun v => ?_⟩
  rw [glNHom_apply, repN_apply, he]
  rfl

@[expose] def glN : S ≃* (N ≃ₗ[ZMod 2] N) :=
  MulEquiv.ofBijective glNHom ⟨glNHom_injective, glNHom_surjective⟩

theorem glN_apply (g : S) (v : N) : glN g v = v ᵥ* ((g⁻¹ : S) : Mat3) :=
  rfl

theorem glN_symm_apply (g : S) (v : N) : (glN g).symm v = v ᵥ* (g : Mat3) := by
  apply (glN g).injective
  rw [LinearEquiv.apply_symm_apply, glN_apply, Matrix.vecMul_vecMul, ← Units.val_mul,
    mul_inv_cancel, Units.val_one, Matrix.vecMul_one]

abbrev rep0 : Representation (ZMod 2) S (ZMod 2) := Representation.trivial (ZMod 2) S (ZMod 2)

theorem finrank_N_three : finrank (ZMod 2) N = 3 := finrank_N

theorem natRep_comp_glN :
    (CFSG.ProperTwoGeneratedCore.BinaryThreeSpace.natRep N).comp glN.toMonoidHom = repN :=
  rfl

@[expose] def dualEquivNd :
    (repNd).Equiv ((CFSG.ProperTwoGeneratedCore.BinaryThreeSpace.dualRep N).comp
      glN.toMonoidHom) :=
  equivOf (dotProductEquiv (ZMod 2) (Fin 3)) fun g f => by
    refine LinearMap.ext fun v => ?_
    change dotProduct (repNd g f) v = dotProduct f ((glN g).symm v)
    rw [glN_symm_apply, repNd_apply, tau_apply_val, inv_inv, dotProduct_comm,
      Matrix.vecMul_transpose, Matrix.dotProduct_mulVec, dotProduct_comm]

theorem vecMulLinear_eq_toLin' (X : Mat3) : Matrix.vecMulLinear X = Matrix.toLin' Xᵀ :=
  LinearMap.ext fun v => by
    rw [Matrix.vecMulLinear_apply, Matrix.toLin'_apply, Matrix.mulVec_transpose]

@[expose] def endALin :
    A →ₗ[ZMod 2] CFSG.ProperTwoGeneratedCore.BinaryThreeSpace.traceZeroEnd N where
  toFun X := ⟨Matrix.vecMulLinear (X : Mat3), by
    change LinearMap.trace (ZMod 2) N (Matrix.vecMulLinear (X : Mat3)) = 0
    rw [vecMulLinear_eq_toLin', Matrix.trace_toLin'_eq, Matrix.trace_transpose]
    exact X.2⟩
  map_add' X Y := Subtype.ext (LinearMap.ext fun v => by
    change v ᵥ* ((X : Mat3) + (Y : Mat3)) = v ᵥ* (X : Mat3) + v ᵥ* (Y : Mat3)
    exact Matrix.vecMul_add _ _ _)
  map_smul' c X := Subtype.ext (LinearMap.ext fun v => by
    change v ᵥ* (c • (X : Mat3)) = c • (v ᵥ* (X : Mat3))
    exact Matrix.vecMul_smul _ _ _)

@[expose] def endAInv (F : CFSG.ProperTwoGeneratedCore.BinaryThreeSpace.traceZeroEnd N) : A :=
  ⟨(LinearMap.toMatrix' (F : Module.End (ZMod 2) N))ᵀ, by
    change Matrix.trace (LinearMap.toMatrix' (F : Module.End (ZMod 2) N))ᵀ = 0
    rw [Matrix.trace_transpose, ← LinearMap.toMatrix_eq_toMatrix',
      ← LinearMap.trace_eq_matrix_trace]
    exact F.2⟩

@[expose] def endA : A ≃ₗ[ZMod 2] CFSG.ProperTwoGeneratedCore.BinaryThreeSpace.traceZeroEnd N :=
  { endALin with
    invFun := endAInv
    left_inv := fun X => Subtype.ext (by
      change (LinearMap.toMatrix' (Matrix.vecMulLinear (X : Mat3)))ᵀ = (X : Mat3)
      rw [vecMulLinear_eq_toLin', LinearMap.toMatrix'_toLin', Matrix.transpose_transpose])
    right_inv := fun F => Subtype.ext (by
      change Matrix.vecMulLinear (LinearMap.toMatrix' (F : Module.End (ZMod 2) N))ᵀ =
        (F : Module.End (ZMod 2) N)
      rw [vecMulLinear_eq_toLin', Matrix.transpose_transpose, Matrix.toLin'_toMatrix']) }

@[expose] def adjEquivA :
    repA.Equiv ((CFSG.ProperTwoGeneratedCore.BinaryThreeSpace.adjRep N).comp glN.toMonoidHom) :=
  equivOf endA fun g X => by
    apply Subtype.ext
    refine LinearMap.ext fun v => ?_
    change v ᵥ* ((repA g X : A) : Mat3) = (glN g) (((glN g).symm v) ᵥ* (X : Mat3))
    rw [glN_symm_apply, glN_apply, repA_apply, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul,
      Matrix.mul_assoc]

@[expose] def labelSubrep (i : Fin 4) : Subrepresentation rho :=
  ⟨labelSub i, fun g _ hx => rho_mem_labelSub g i _ hx⟩

@[expose] def labelRep (i : Fin 4) : Representation (ZMod 2) S (labelSub i) :=
  (labelSubrep i).toRepresentation

theorem labelRep_apply (i : Fin 4) (g : S) (x : labelSub i) :
    ((labelRep i g x : labelSub i) : V) = rho g x :=
  rfl

@[expose] def labelEquivOf {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    {σ : Representation (ZMod 2) S M} (i : Fin 4) (ι : M →ₗ[ZMod 2] V)
    (hι : Function.Injective ι) (hrange : LinearMap.range ι = labelSub i)
    (hρ : ∀ g m, rho g (ι m) = ι (σ g m)) : (labelRep i).Equiv σ :=
  equivOf ((LinearEquiv.ofEq _ _ hrange.symm).trans (LinearEquiv.ofInjective ι hι).symm)
    fun g x => by
      have hF : ∀ (y : labelSub i) (m : M), ι m = y →
          ((LinearEquiv.ofEq _ _ hrange.symm).trans (LinearEquiv.ofInjective ι hι).symm) y = m := by
        intro y m hm
        rw [LinearEquiv.trans_apply, LinearEquiv.symm_apply_eq]
        exact Subtype.ext hm.symm
      obtain ⟨m, hm⟩ : (x : V) ∈ LinearMap.range ι := by
        rw [hrange]
        exact x.2
      rw [hF x m hm]
      apply hF
      rw [labelRep_apply, ← hm, hρ]

theorem inc0_injective : Function.Injective inc0 := LinearMap.inl_injective
theorem inc1_injective : Function.Injective inc1 :=
  LinearMap.inr_injective.comp LinearMap.inl_injective
theorem inc2_injective : Function.Injective inc2 :=
  LinearMap.inr_injective.comp (LinearMap.inr_injective.comp LinearMap.inl_injective)
theorem inc3_injective : Function.Injective inc3 :=
  LinearMap.inr_injective.comp (LinearMap.inr_injective.comp LinearMap.inr_injective)

@[expose] def labelEquiv0 : (labelRep 0).Equiv rep0 :=
  labelEquivOf 0 inc0 inc0_injective rfl fun g _ =>
    Prod.ext rfl (Prod.ext (map_zero (repN g)) (Prod.ext (map_zero (repNd g)) (map_zero (repA g))))

@[expose] def labelEquiv1 : (labelRep 1).Equiv repN :=
  labelEquivOf 1 inc1 inc1_injective rfl fun g _ =>
    Prod.ext rfl (Prod.ext rfl (Prod.ext (map_zero (repNd g)) (map_zero (repA g))))

@[expose] def labelEquiv2 : (labelRep 2).Equiv repNd :=
  labelEquivOf 2 inc2 inc2_injective rfl fun g _ =>
    Prod.ext rfl (Prod.ext (map_zero (repN g)) (Prod.ext rfl (map_zero (repA g))))

@[expose] def labelEquiv3 : (labelRep 3).Equiv repA :=
  labelEquivOf 3 inc3 inc3_injective rfl fun g _ =>
    Prod.ext rfl (Prod.ext (map_zero (repN g)) (Prod.ext (map_zero (repNd g)) rfl))

theorem rep0_isIrreducible : rep0.IsIrreducible :=
  (isIrreducible_comp_iff (CFSG.ProperTwoGeneratedCore.BinaryThreeSpace.trivRep N) glN).2
    CFSG.ProperTwoGeneratedCore.BinaryThreeSpace.trivRep_isIrreducible

theorem repN_isIrreducible : repN.IsIrreducible :=
  natRep_comp_glN ▸ (isIrreducible_comp_iff _ glN).2
    (CFSG.ProperTwoGeneratedCore.BinaryThreeSpace.natRep_isIrreducible finrank_N_three)

theorem repNd_isIrreducible : repNd.IsIrreducible :=
  IsIrreducible.of_equiv dualEquivNd ((isIrreducible_comp_iff _ glN).2
    (CFSG.ProperTwoGeneratedCore.BinaryThreeSpace.dualRep_isIrreducible finrank_N_three))

theorem repA_isIrreducible : repA.IsIrreducible :=
  IsIrreducible.of_equiv adjEquivA ((isIrreducible_comp_iff _ glN).2
    (CFSG.ProperTwoGeneratedCore.BinaryThreeSpace.adjRep_isIrreducible finrank_N_three))

open CFSG.ProperTwoGeneratedCore.BinaryThreeSpace (unitri unitriGL E13)

theorem repN_unitri (a b c : ZMod 2) (x : N) :
    repN (unitriGL a b c) x = x ᵥ* unitri a (a * c + b) c :=
  rfl

theorem fixN : ∀ x : N, (∀ a b c : ZMod 2, x ᵥ* unitri a (a * c + b) c = x) →
    x = 0 ∨ x = ![0, 0, 1] := by
  decide

theorem fixN₀ : ∀ a b c : ZMod 2, (![0, 0, 1] : N) ᵥ* unitri a (a * c + b) c = ![0, 0, 1] := by
  decide

theorem repNd_unitri (a b c : ZMod 2) (f : Nd) :
    repNd (unitriGL a b c) f = f ᵥ* (unitri a b c)ᵀ := by
  rw [repNd_apply, tau_apply_val, inv_inv]
  rfl

theorem fixNd : ∀ f : Nd, (∀ a b c : ZMod 2, f ᵥ* (unitri a b c)ᵀ = f) →
    f = 0 ∨ f = ![1, 0, 0] := by
  decide

theorem fixNd₀ : ∀ a b c : ZMod 2, (![1, 0, 0] : Nd) ᵥ* (unitri a b c)ᵀ = ![1, 0, 0] := by
  decide

theorem E13_mem_traceZero : E13 ∈ traceZero := by
  rw [CFSG.ProperTwoGeneratedCore.BinaryThreeSpace.traceZero, LinearMap.mem_ker,
    Matrix.traceLinearMap_apply]
  decide

theorem conj_E13 : ∀ a b c : ZMod 2, unitri a b c * E13 * unitri a (a * c + b) c = E13 := by
  decide

theorem rep0_end (f : ZMod 2 →ₗ[ZMod 2] ZMod 2) (_hf : ∀ g x, f (rep0 g x) = rep0 g (f x)) :
    ∃ c : ZMod 2, f = c • LinearMap.id :=
  ⟨f 1, LinearMap.ext_ring (by rw [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul,
    mul_one])⟩

theorem repN_end (f : N →ₗ[ZMod 2] N) (hf : ∀ g x, f (repN g x) = repN g (f x)) :
    ∃ c : ZMod 2, f = c • LinearMap.id :=
  eq_smul_of_fixed repN_isIrreducible (U3 : Set S) (x₀ := ![0, 0, 1]) (by decide)
    (fun _ ⟨a, b, c, h⟩ => by rw [h, repN_unitri]; exact fixN₀ a b c)
    (fun x hx => fixN x fun a b c => by rw [← repN_unitri]; exact hx _ ⟨a, b, c, rfl⟩) f hf

theorem repNd_end (f : Nd →ₗ[ZMod 2] Nd) (hf : ∀ g x, f (repNd g x) = repNd g (f x)) :
    ∃ c : ZMod 2, f = c • LinearMap.id :=
  eq_smul_of_fixed repNd_isIrreducible (U3 : Set S) (x₀ := ![1, 0, 0]) (by decide)
    (fun _ ⟨a, b, c, h⟩ => by rw [h, repNd_unitri]; exact fixNd₀ a b c)
    (fun x hx => fixNd x fun a b c => by rw [← repNd_unitri]; exact hx _ ⟨a, b, c, rfl⟩) f hf

theorem repA_end (f : A →ₗ[ZMod 2] A) (hf : ∀ g x, f (repA g x) = repA g (f x)) :
    ∃ c : ZMod 2, f = c • LinearMap.id :=
  eq_smul_of_fixed repA_isIrreducible (U3 : Set S) (x₀ := ⟨E13, E13_mem_traceZero⟩)
    (fun h => by
      have h1 := congrArg (fun X : A => (X : Mat3) 0 2) h
      simp at h1)
    (fun _ ⟨a, b, c, h⟩ => Subtype.ext (by rw [h, repA_apply]; exact conj_E13 a b c))
    (fun X hX => by
      rcases CFSG.ProperTwoGeneratedCore.BinaryThreeSpace.eq_zero_or_eq_E13 X.2 (fun t ht => by
        have h1 := congrArg Subtype.val (hX t ht)
        rw [repA_apply] at h1
        exact h1) with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)) f hf

theorem rep0_absIrr : AbsIrr rep0 := AbsIrr.of_isIrreducible rep0_isIrreducible rep0_end

theorem repN_absIrr : AbsIrr repN := AbsIrr.of_isIrreducible repN_isIrreducible repN_end

theorem repNd_absIrr : AbsIrr repNd := AbsIrr.of_isIrreducible repNd_isIrreducible repNd_end

theorem repA_absIrr : AbsIrr repA := AbsIrr.of_isIrreducible repA_isIrreducible repA_end

theorem labelRep_absIrr (i : Fin 4) : AbsIrr (labelRep i) := by
  fin_cases i
  · exact AbsIrr.of_equiv labelEquiv0 rep0_absIrr
  · exact AbsIrr.of_equiv labelEquiv1 repN_absIrr
  · exact AbsIrr.of_equiv labelEquiv2 repNd_absIrr
  · exact AbsIrr.of_equiv labelEquiv3 repA_absIrr

@[expose] def labelDim : Fin 4 → ℕ := ![1, 3, 3, 8]

theorem finrank_labelSub (i : Fin 4) : finrank (ZMod 2) (labelSub i) = labelDim i := by
  fin_cases i
  · exact labelEquiv0.toLinearEquiv.finrank_eq.trans (Module.finrank_self _)
  · exact labelEquiv1.toLinearEquiv.finrank_eq.trans finrank_N
  · exact labelEquiv2.toLinearEquiv.finrank_eq.trans finrank_Nd
  · exact labelEquiv3.toLinearEquiv.finrank_eq.trans finrank_A

theorem exists_equiv_labelRep {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E] (ρ : Representation (ZMod 2) S E) (hρ : ρ.IsIrreducible) :
    ∃ i, Nonempty (ρ.Equiv (labelRep i)) := by
  have hρ' := (isIrreducible_comp_iff ρ glN.symm).2 hρ
  obtain ⟨i, hi, -⟩ :=
    (CFSG.ProperTwoGeneratedCore.BinaryThreeSpace.irreducible_binary_GL3_module_production
      finrank_N_three).1 E (ρ.comp glN.symm.toMonoidHom) hρ'
  fin_cases i
  · obtain ⟨e⟩ := hi
    exact ⟨0, ⟨(equivOfCompSymm glN e).trans labelEquiv0.symm⟩⟩
  · obtain ⟨e⟩ := hi
    exact ⟨1, ⟨(equivOfCompSymm glN e).trans labelEquiv1.symm⟩⟩
  · obtain ⟨e⟩ := hi
    exact ⟨2, ⟨(equivOfCompSymm glN e).trans (dualEquivNd.symm.trans labelEquiv2.symm)⟩⟩
  · obtain ⟨e⟩ := hi
    exact ⟨3, ⟨(equivOfCompSymm glN e).trans (adjEquivA.symm.trans labelEquiv3.symm)⟩⟩

end CFSG.LocalAnalysis.ComponentInitial.PairedTensorOrbits
