module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33OCSpHom
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedGraphSymm
public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquareSymplectic
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.OC

open CFSG Subgroup Matrix Module CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquare QuaternionMatrices
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher FourGroupOddUnitary

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

@[expose] def SpWit (B : LinearMap.BilinForm K V) (A : LinearMap.GeneralLinearGroup K V) : Prop :=
  ∃ (G : Type) (_ : Group G) (S : Set G) (ψ : G →* LinearMap.GeneralLinearGroup K V),
    closure S = ⊤ ∧ (∀ s ∈ S, Odd (orderOf s)) ∧ (∀ g, ψ g ∈ similitudeCentralizer B A) ∧
      ∃ x : G, x ^ 4 = 1 ∧ ψ x ≠ 1 ∧ ψ x ≠ -1

variable {B : LinearMap.BilinForm K V} {A : LinearMap.GeneralLinearGroup K V}

theorem exists_odd_of_spWit (h : SpWit B A) :
    ∃ T : Set (SymplecticProj B),
      T ⊆ ((Subgroup.centralizer {A}).subgroupOf (sesqUnitaryGroup B)).map (symplecticProj B) ∧
        (∀ t ∈ T, Odd (orderOf t)) ∧ 2 ∣ Nat.card (closure T) := by
  obtain ⟨G, _, S, ψ, hS, hSo, hψ, x, hx4, hx1, hxn⟩ := h
  let ψ' : G →* sesqUnitaryGroup B := ψ.codRestrict _ fun g => (hψ g).1
  have hθx : (symplecticProj B).comp ψ' x ≠ 1 := fun h => by
    rcases (mem_symplecticSignScalars B).1 ((QuotientGroup.eq_one_iff _).1 h) with h' | h'
    · exact hx1 h'
    · exact hxn h'
  obtain ⟨hTo, hT2⟩ := odd_closure_image _ hS hSo hx4 hθx
  refine ⟨_, ?_, hTo, hT2⟩
  rintro _ ⟨s, -, rfl⟩
  exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 (hψ s).2)

theorem one_ne_neg_one_GL {F : Type*} [Field F] (hF : ringChar F ≠ 2) {W : Type*}
    [AddCommGroup W] [Module F W] [Nontrivial W] :
    (1 : LinearMap.GeneralLinearGroup F W) ≠ -1 := fun h => by
  obtain ⟨v, hv⟩ := exists_ne (0 : W)
  have h1 := congrArg (fun u : LinearMap.GeneralLinearGroup F W => (u : Module.End F W) v) h
  simp only [Units.val_one, Units.val_neg, Module.End.one_apply, LinearMap.neg_apply] at h1
  have h2 : (2 : F) • v = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h1]
    exact neg_add_cancel v
  exact hv ((smul_eq_zero.1 h2).resolve_left (Ring.two_ne_zero hF))

theorem spWit_split [Finite K] (hK : ringChar K ≠ 2) [FiniteDimensional K V]
    {Vp Vm : Submodule K V} (hVp : Vp ≠ ⊥) (hVm : Vm ≠ ⊥)
    (hAp : (B.domRestrict₁₂ Vp Vp).IsAlt) (hNp : (B.domRestrict₁₂ Vp Vp).Nondegenerate)
    (e : similitudeCentralizer B A ≃*
      sesqUnitaryGroup (B.domRestrict₁₂ Vp Vp) × sesqUnitaryGroup (B.domRestrict₁₂ Vm Vm))
    (he : ∀ g : similitudeCentralizer B A,
      Vp.subtype ∘ₗ (((e g).1 : LinearMap.GeneralLinearGroup K Vp) : Module.End K Vp) =
          ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) ∘ₗ Vp.subtype ∧
        Vm.subtype ∘ₗ (((e g).2 : LinearMap.GeneralLinearGroup K Vm) : Module.End K Vm) =
          ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) ∘ₗ Vm.subtype) :
    SpWit B A := by
  have : Nontrivial Vp := Submodule.nontrivial_iff_ne_bot.2 hVp
  have : Nontrivial Vm := Submodule.nontrivial_iff_ne_bot.2 hVm
  obtain ⟨ψp, hψp, -, hψps⟩ := exists_sl2_sp _ hAp hNp
  let np : sesqUnitaryGroup (B.domRestrict₁₂ Vp Vp) := ⟨-1, neg_one_mem_sesqUnitaryGroup _⟩
  let nm : sesqUnitaryGroup (B.domRestrict₁₂ Vm Vm) := ⟨-1, neg_one_mem_sesqUnitaryGroup _⟩
  have hnn : e ⟨-1, neg_one_mem_similitudeCentralizer⟩ = (np, nm) :=
    Prod.ext (Subtype.ext (neg_one_of_restrict (he _).1))
      (Subtype.ext (neg_one_of_restrict (he _).2))
  let Φ : SpecialLinearGroup (Fin 2) K →*
      sesqUnitaryGroup (B.domRestrict₁₂ Vp Vp) × sesqUnitaryGroup (B.domRestrict₁₂ Vm Vm) :=
    MonoidHom.prod (ψp.codRestrict _ hψp) 1
  obtain ⟨hS, hSo⟩ := elementary_closure_odd hK 2
  refine ⟨SpecialLinearGroup (Fin 2) K, inferInstance, LinearGroups.elementarySet 2 K,
    (similitudeCentralizer B A).subtype.comp (e.symm.toMonoidHom.comp Φ), hS, hSo,
    fun g => (e.symm (Φ g)).2, slQuatI K, slQuatI_pow_four, fun h => ?_, fun h => ?_⟩
  · have h1 : e.symm (Φ (slQuatI K)) = 1 := Subtype.ext h
    have h2 : Φ (slQuatI K) = 1 := by rw [← e.apply_symm_apply (Φ _), h1, map_one]
    have h3 : ψp (slQuatI K) = 1 :=
      congrArg (fun z : sesqUnitaryGroup (B.domRestrict₁₂ Vp Vp) ×
        sesqUnitaryGroup (B.domRestrict₁₂ Vm Vm) =>
          ((z.1 : sesqUnitaryGroup _) : LinearMap.GeneralLinearGroup K Vp)) h2
    exact hψps 1 (by rw [h3, one_smul]; rfl)
  · have h1 : e.symm (Φ (slQuatI K)) = ⟨-1, neg_one_mem_similitudeCentralizer⟩ := Subtype.ext h
    have h2 : Φ (slQuatI K) = (np, nm) := by rw [← e.apply_symm_apply (Φ _), h1, hnn]
    have h3 := congrArg (fun z : sesqUnitaryGroup (B.domRestrict₁₂ Vp Vp) ×
        sesqUnitaryGroup (B.domRestrict₁₂ Vm Vm) =>
          ((z.2 : sesqUnitaryGroup _) : LinearMap.GeneralLinearGroup K Vm)) h2
    exact one_ne_neg_one_GL hK h3

theorem spWit_paired [Finite K] (hK : ringChar K ≠ 2) [FiniteDimensional K V]
    {Vp : Submodule K V} {r : ℕ} (hr : 3 ≤ r) (hdim : finrank K Vp = r)
    (e : similitudeCentralizer B A ≃* LinearMap.GeneralLinearGroup K Vp)
    (he : ∀ g : similitudeCentralizer B A,
      Vp.subtype ∘ₗ ((e g : LinearMap.GeneralLinearGroup K Vp) : Module.End K Vp) =
        ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) ∘ₗ Vp.subtype) :
    SpWit B A := by
  have hnn : e ⟨-1, neg_one_mem_similitudeCentralizer⟩ = -1 := neg_one_of_restrict (he _)
  obtain ⟨m, hm⟩ : ∃ m, r = 2 + m := ⟨r - 2, by omega⟩
  let c := Module.finBasisOfFinrankEq K Vp (hdim.trans hm)
  let Φ : SpecialLinearGroup (Fin 2) K →* LinearMap.GeneralLinearGroup K Vp :=
    (CLSFourGroupScalarSquare.basisGL c).comp
      ((LinearFlag.blockGL K 2 m).comp SpecialLinearGroup.toGL)
  have hΦs : ∀ a : K, ((Φ (slQuatI K) : LinearMap.GeneralLinearGroup K Vp) : Module.End K Vp) ≠
      a • 1 :=
    coe_basisGL_ne_smul c fun a h => LinearFlag.blockGL_ne_scalar_of_ne_one (k := 2) (m := m)
      (by omega) (LinearFlag.toGL_slQuatI_ne_one (K := K)) a
      (by rw [scalar_apply, ← smul_one_eq_diagonal]; exact h)
  obtain ⟨hS, hSo⟩ := elementary_closure_odd hK 2
  refine ⟨SpecialLinearGroup (Fin 2) K, inferInstance, LinearGroups.elementarySet 2 K,
    (similitudeCentralizer B A).subtype.comp (e.symm.toMonoidHom.comp Φ), hS, hSo,
    fun g => (e.symm (Φ g)).2, slQuatI K, slQuatI_pow_four, fun h => ?_, fun h => ?_⟩
  · have h1 : e.symm (Φ (slQuatI K)) = 1 := Subtype.ext h
    have h2 : Φ (slQuatI K) = 1 := by rw [← e.apply_symm_apply (Φ _), h1, map_one]
    exact ne_one_of_forall_ne_smul hΦs h2
  · have h1 : e.symm (Φ (slQuatI K)) = ⟨-1, neg_one_mem_similitudeCentralizer⟩ := Subtype.ext h
    have h2 : Φ (slQuatI K) = -1 := by rw [← e.apply_symm_apply (Φ _), h1, hnn]
    exact ne_neg_one_of_forall_ne_smul hΦs h2

theorem spWit_field_alt [Finite K] (hK : ringChar K ≠ 2) [FiniteDimensional K V] [Nontrivial V]
    {d : K} (hAA : (A : Module.End K V) * (A : Module.End K V) = d • 1)
    (hd : ∀ l : K, l ^ 2 ≠ d)
    (BE : LinearMap.BilinForm (scalarSquareField (A : Module.End K V)) V) (hBEa : BE.IsAlt)
    (hBEn : BE.Nondegenerate)
    (hiff : ∀ g : LinearMap.GeneralLinearGroup K V, g ∈ similitudeCentralizer B A ↔
      g ∈ Subgroup.centralizer {A} ∧
        ∀ v w, BE ((g : Module.End K V) v) ((g : Module.End K V) w) = BE v w) :
    SpWit B A := by
  let _ : Field (scalarSquareField (A : Module.End K V)) :=
    (isField_scalarSquareField hAA hd).toField
  have : FiniteDimensional (scalarSquareField (A : Module.End K V)) V :=
    Module.Finite.of_restrictScalars_finite K _ V
  have := finite_scalarSquareField (A := A)
  have hE2 := ringChar_scalarSquareField_ne_two hAA hd hK
  obtain ⟨ψE, hψE, -, hψEs⟩ := exists_sl2_sp BE hBEa hBEn
  have hmem : ∀ u ∈ sesqUnitaryGroup BE, restrictGL (K := K) u ∈ similitudeCentralizer B A :=
    fun u hu => (hiff _).2 ⟨restrictGL_mem_centralizer hAA hd u, fun v w => hu v w⟩
  have hs : ∀ a : K, ((restrictGL (K := K) (ψE (slQuatI _)) : LinearMap.GeneralLinearGroup K V) :
      Module.End K V) ≠ a • 1 := coe_restrictGL_ne_smul hψEs
  obtain ⟨hS, hSo⟩ := elementary_closure_odd hE2 2
  exact ⟨SpecialLinearGroup (Fin 2) (scalarSquareField (A : Module.End K V)), inferInstance,
    LinearGroups.elementarySet 2 _, restrictGL.comp ψE, hS, hSo, fun g => hmem _ (hψE g),
    slQuatI _, slQuatI_pow_four, ne_one_of_forall_ne_smul hs, ne_neg_one_of_forall_ne_smul hs⟩

theorem map_ne_smul_one {F E : Type*} [Field F] [Field E] (φ : F →+* E) {ι : Type*}
    [DecidableEq ι] {N : Matrix ι ι F} (hN : ∀ c : F, N ≠ c • 1) (a : E) :
    N.map φ ≠ a • 1 := by
  intro h
  by_cases hι : IsEmpty ι
  · exact hN 0 (Matrix.ext fun i => hι.elim i)
  · obtain ⟨i₀⟩ := not_isEmpty_iff.1 hι
    have hent : ∀ i j, φ (N i j) = if i = j then a else 0 := fun i j => by
      have := congrFun (congrFun h i) j
      rw [Matrix.map_apply] at this
      rw [this, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      split_ifs <;> simp
    refine hN (N i₀ i₀) (Matrix.ext fun i j => φ.injective ?_)
    rw [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, hent]
    split_ifs with hij
    · rw [mul_one, hent]
      simp
    · rw [mul_zero, map_zero]

theorem spWit_field_herm [Finite K] [FiniteDimensional K V] [Nontrivial V] {d : K}
    (hAA : (A : Module.End K V) * (A : Module.End K V) = d • 1) (hd : ∀ l : K, l ^ 2 ≠ d)
    (hK : ringChar K ≠ 2) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf1 : 1 ≤ f) (hcardK : Nat.card K = ℓ ^ f)
    (hcardE : Nat.card (scalarSquareField (A : Module.End K V)) = (ℓ ^ f) ^ 2)
    (hrank : 3 ≤ finrank (scalarSquareField (A : Module.End K V)) V)
    (bar : scalarSquareField (A : Module.End K V) →+* scalarSquareField (A : Module.End K V))
    (hbar : ∀ x, bar x = x ^ (ℓ ^ f))
    (hf : V →ₛₗ[bar] V →ₗ[scalarSquareField (A : Module.End K V)]
      scalarSquareField (A : Module.End K V))
    (hsymm : hf.IsSymm) (hsep : hf.SeparatingLeft)
    (hiff : ∀ g : LinearMap.GeneralLinearGroup K V, g ∈ similitudeCentralizer B A ↔
      g ∈ Subgroup.centralizer {A} ∧
        ∀ v w, hf ((g : Module.End K V) v) ((g : Module.End K V) w) = hf v w) :
    SpWit B A := by
  classical
  let _ : Field (scalarSquareField (A : Module.End K V)) :=
    (isField_scalarSquareField hAA hd).toField
  have : FiniteDimensional (scalarSquareField (A : Module.End K V)) V :=
    Module.Finite.of_restrictScalars_finite K _ V
  have hUF : UnitaryFieldData ℓ f (scalarSquareField (A : Module.End K V)) :=
    ⟨hℓ, hf1, by rw [hcardE, ← pow_mul, mul_comm]⟩
  have hbh : bar = hUF.bar := RingHom.ext fun x => by rw [hbar, hUF.bar_apply]
  subst hbh
  obtain ⟨ob, hob⟩ := hUF.exists_orthonormal_basis hsymm hsep
  obtain ⟨m, hm⟩ : ∃ m, finrank (scalarSquareField (A : Module.End K V)) V = 3 + m :=
    ⟨_, (Nat.add_sub_cancel' hrank).symm⟩
  let ob' := ob.reindex (finCongr hm)
  have hG : ∀ i j, hf (ob' i) (ob' j) =
      (1 : Matrix (Fin (3 + m)) (Fin (3 + m)) (scalarSquareField (A : Module.End K V))) i j :=
    fun i j => by
      rw [Basis.reindex_apply, Basis.reindex_apply, hob, Matrix.one_apply]
      simp
  obtain ⟨ζ, hζ, hζs⟩ := LinearFlag.exists_ternary_isometry_hom hK (fun _ => (1 : K))
    fun _ => one_ne_zero
  set φ := algebraMap K (scalarSquareField (A : Module.End K V)) with hφ
  have hfix : ∀ a : K, hUF.bar (φ a) = φ a := fun a => by
    rw [hUF.bar_apply, ← map_pow]
    congr 1
    have : Fintype K := Fintype.ofFinite K
    rw [← hcardK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  let Φ : SpecialLinearGroup (Fin 2) K →* LinearMap.GeneralLinearGroup K V :=
    restrictGL.comp ((CLSFourGroupScalarSquare.basisGL ob').comp
      ((GeneralLinearGroup.map φ).comp ((LinearFlag.blockGL K 3 m).comp ζ)))
  let N : SpecialLinearGroup (Fin 2) K → Matrix (Fin (3 + m)) (Fin (3 + m)) K :=
    fun X => ((LinearFlag.blockGL K 3 m (ζ X) : GL (Fin (3 + m)) K) :
      Matrix (Fin (3 + m)) (Fin (3 + m)) K)
  have hblock : ∀ X, (N X)ᵀ * N X = 1 := by
    intro X
    have h1 := hζ X
    rw [diagonal_one, Matrix.mul_one] at h1
    change ((LinearFlag.blockGL K 3 m (ζ X) : GL (Fin (3 + m)) K) :
      Matrix (Fin (3 + m)) (Fin (3 + m)) K)ᵀ *
        ((LinearFlag.blockGL K 3 m (ζ X) : GL (Fin (3 + m)) K) :
          Matrix (Fin (3 + m)) (Fin (3 + m)) K) = 1
    rw [LinearFlag.coe_blockGL_eq_diagBlock, LinearFlag.diagBlock_transpose,
      LinearFlag.diagBlock_mul, h1, transpose_one, Matrix.one_mul]
    simp [LinearFlag.diagBlock, fromBlocks_one]
  have hmem : ∀ X, Φ X ∈ similitudeCentralizer B A := fun X => by
    refine (hiff _).2 ⟨restrictGL_mem_centralizer hAA hd _, fun v w => ?_⟩
    change hf (Matrix.toLin ob' ob' ((N X).map φ) v) (Matrix.toLin ob' ob' ((N X).map φ) w) =
      hf v w
    refine toLin_preserves hf ob' 1 hG (fun i j => hfix _) ?_ v w
    show ((N X).map φ)ᵀ * 1 * (N X).map φ = 1
    rw [Matrix.mul_one, ← transpose_map, ← Matrix.map_mul, hblock X,
      Matrix.map_one _ (map_zero φ) (map_one φ)]
  have hs : ∀ a : K, ((Φ (slQuatI K) : LinearMap.GeneralLinearGroup K V) : Module.End K V) ≠
      a • 1 := by
    refine coe_restrictGL_ne_smul (coe_basisGL_ne_smul ob' fun a h => ?_)
    refine map_ne_smul_one φ (N := N (slQuatI K)) (fun c hc => ?_) a h
    exact LinearFlag.blockGL_ne_scalar_of_ne_scalar hζs c
      (by rw [scalar_apply, ← smul_one_eq_diagonal]; exact hc)
  obtain ⟨hS, hSo⟩ := elementary_closure_odd hK 2
  exact ⟨SpecialLinearGroup (Fin 2) K, inferInstance, LinearGroups.elementarySet 2 K, Φ, hS, hSo,
    hmem, slQuatI K, slQuatI_pow_four, ne_one_of_forall_ne_smul hs,
    ne_neg_one_of_forall_ne_smul hs⟩

end CFSG.ComponentClassification.HarrisLit.L33.OC
