module

public import CFSG.LocalAnalysis.SteinbergSFOddOrthogonalFixedRootExclusion
public import CFSG.LocalAnalysis.EvenBN.GMSK.CatOddLinear
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorOrthSplit

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.GMSK

open Subgroup Module QuadraticMap CFSG.Assembly.LowTwoRank CFSG.Blueprint OddClassicalRankOne
open CFSG.ComponentClassification CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
  CFSG.ComponentClassification.CatalogueBOrthogonalDescent
  CFSG.ComponentClassification.CatalogueBLinearTwoDescent
open CFSG.LocalAnalysis.ComponentInitial.OddOrthogonal (commutant mem_commutant)
open CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquare (orthogonalOmega)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.SymplecticFourStandard
open CFSG.LocalAnalysis.SymplecticFourStandard.OddOrthogonalRoot

namespace OddOrthogonalRankOne

theorem exists_fixed_root_lift_two {G : Type*} [Group G] [Finite G] (Z : Subgroup G) [Z.Normal]
    (hZ : Z ≤ center G) {K : Type*} [Field K] (φ : MulAut G) (hφZ : Z.map φ.toMonoidHom = Z)
    (hφφ : ∀ g, φ (φ g) = g)
    (h : FixedRootTwoConfig (CatalogueBFixedCentralQuotient.onQuotient Z φ hφZ) K) :
    ∃ Y : Subgroup G, CFSG.Assembly.IsComponentOf Y (fixedSubgroup φ) ∧
      (∃ (A : Subgroup Y) (_ : A.Normal), (∀ a ∈ A, (a : G) ∈ Z) ∧
        Nonempty (Y ⧸ A ≃* Matrix.SpecialLinearGroup (Fin 2) K)) ∧
      ∀ T : Subgroup G, (∀ z ∈ T, ∀ y ∈ Y, y * z = z * y) → (∀ z ∈ T, φ z = z) →
        4 ∣ (Z.subgroupOf T).index → False := by
  classical
  set β := CatalogueBFixedCentralQuotient.onQuotient Z φ hφZ with hβ
  obtain ⟨S, hSn, hSs, hSnab, ⟨eS⟩, hcard⟩ := h
  set X := S.map (fixedSubgroup β).subtype
  have hX : CFSG.Assembly.IsComponentOf X (fixedSubgroup β) :=
    isComponentOf_map_subtype S hSn hSs hSnab
  obtain ⟨Y, hY, ⟨σY, hσYs, -, hσY⟩, -⟩ := OddClassSelector.central_lift Z hZ φ hφZ hφφ hX
  refine ⟨Y, hY, ⟨σY.ker, inferInstance, fun a ha => ?_, ⟨?_⟩⟩, ?_⟩
  · have h1 : QuotientGroup.mk' Z (a : G) = 1 := by
      rw [← hσY a, ha]
      rfl
    exact (QuotientGroup.eq_one_iff _).mp h1
  · exact (QuotientGroup.quotientKerEquivOfSurjective σY hσYs).trans
      ((S.equivMapOfInjective _ (Subgroup.subtype_injective _)).symm.trans eS)
  · intro T hTY hTφ h4
    set π := QuotientGroup.mk' Z
    have hmem : ∀ z : G, (∀ y ∈ Y, y * z = z * y) → φ z = z →
        π z ∈ fixedSubgroup β ⊓ centralizer (X : Set (G ⧸ Z)) := by
      intro z hzY hzφ
      refine mem_inf.mpr ⟨?_, ?_⟩
      · change β (π z) = π z
        rw [hβ, CatalogueBFixedCentralQuotient.onQuotient_mk, hzφ]
      · rw [mem_centralizer_iff]
        intro s hs
        obtain ⟨y, hy⟩ := hσYs ⟨s, hs⟩
        have hs' : s = (σY y : G ⧸ Z) := congrArg Subtype.val hy.symm
        rw [hs', hσY, ← map_mul, ← map_mul, hzY y y.2]
    refine false_of_four_dvd (fun V hV hVp => hcard V (fun v hv => hV v hv) hVp)
      (W := T.map π) ?_ (by rw [card_map_mk'_eq_index]; exact h4)
    rintro _ ⟨z, hz, rfl⟩
    exact hmem z (hTY z hz) (hTφ z hz)

theorem card_center_SL2 {F : Type*} [Field F] [Finite F] (hF : ringChar F ≠ 2) :
    Nat.card (center (Matrix.SpecialLinearGroup (Fin 2) F)) = 2 := by
  rw [Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (0 : Fin 2)).toEquiv,
    Fintype.card_fin]
  have : CharP F (ringChar F) := ringChar.charP F
  exact (IsPrimitiveRoot.neg_one (ringChar F) hF).card_rootsOfUnity

theorem four_dvd_card_traceZeroSpecialImage {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 5) :
    4 ∣ Nat.card (LocalAnalysis.ComponentInitial.traceZeroSpecialImage F) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  set g := CatalogueBOrthogonal.traceZeroOrthogonalAction.comp
    (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 2) F →* GL (Fin 2) F)
    with hg
  have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = 120 := by
    rw [Matrix.card_SL_field, ← Nat.card_eq_fintype_card, hF]
    decide
  have hker : g.ker ≤ center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    intro A hA
    rw [MonoidHom.mem_ker, hg, MonoidHom.comp_apply,
      CatalogueBOrthogonal.traceZeroOrthogonalAction_eq_one_iff] at hA
    obtain ⟨c, hc⟩ := hA
    rw [Matrix.SpecialLinearGroup.mem_center_iff]
    refine ⟨c, ?_, congrArg Units.val hc⟩
    have hd := congrArg Matrix.det (congrArg Units.val hc)
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hd
    rw [Fintype.card_fin, hd]
    exact A.2
  have hchar : ringChar F ≠ 2 := by
    have : CharP F 5 := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      (k := 1) Nat.prime_five le_rfl (by rw [hF, pow_one])
    rw [ringChar.eq F 5]
    decide
  have hk := Subgroup.card_le_of_le hker
  rw [card_center_SL2 hchar] at hk
  have h1 := Subgroup.card_mul_index g.ker
  rw [Subgroup.index_ker, hSL] at h1
  have hpos : 0 < Nat.card g.ker := Nat.card_pos
  change 4 ∣ Nat.card g.range
  interval_cases hc : Nat.card g.ker <;> omega

section Linear

variable {F : Type} [Field F] [Finite F] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]

theorem split_factor_false_two (hodd : Odd (Nat.card F)) (hd : 7 ≤ finrank F V)
    {Q : QuadraticForm F V} {M N : Submodule F V} (hMN : IsCompl M N)
    (horth : ∀ m ∈ M, ∀ x ∈ N, polar Q m x = 0)
    (hMnd : (Q.comp M.subtype).polarBilin.Nondegenerate)
    (hNnd : (Q.comp N.subtype).polarBilin.Nondegenerate) (hN0 : N ≠ ⊥)
    (T : V ≃ₗ[F] V) (lM lN : F) (hTM : ∀ m ∈ M, T m = lM • m) (hTN : ∀ x ∈ N, T x = lN • x)
    {Y : Subgroup (V ≃ₗ[F] V)} (hYN : ∀ y ∈ Y, ∀ x ∈ N, y x = x)
    (hYM : ∀ y ∈ Y, ∀ m ∈ M, y m ∈ M)
    (ρ : Y →* TauCeti.QuadraticMap.orthogonalGroup (Q.comp M.subtype))
    (hρi : Function.Injective ρ) (hρc : CFSG.IsComponent ρ.range)
    (A : Subgroup Y) [A.Normal] (hA : ∀ a ∈ A, ∃ c : F, ∀ v, (a : V ≃ₗ[F] V) v = c • v)
    {K : Type*} [Field K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (eQ : Y ⧸ A ≃* Matrix.SpecialLinearGroup (Fin 2) K)
    (hsmall : ∀ H : Subgroup (V ≃ₗ[F] V), H ≤ orthogonalOmega Q →
      (∀ z ∈ H, ∀ y ∈ Y, y * z = z * y) → (∀ z ∈ H, ∀ x, z (T x) = T (z x)) →
      (∀ z ∈ H, ∀ c : F, (z : V →ₗ[F] V) = c • LinearMap.id → z = 1) →
      4 ∣ Nat.card H → False) : False := by
  classical
  have h2 : (2 : F) ≠ 0 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  have hdimV : finrank F M + finrank F N = finrank F V := Submodule.finrank_add_eq_of_isCompl hMN
  have hA1 : A = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall A).mpr fun a ha => ?_
    obtain ⟨c, hc⟩ := hA a ha
    obtain ⟨x, hxN, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN0
    have h1 : c • x = x := by rw [← hc, hYN _ a.2 x hxN]
    have hc1 : c = 1 := by
      have h3 : (c - 1) • x = 0 := by rw [sub_smul, one_smul, h1, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hx0)
    refine Subtype.ext (LinearEquiv.ext fun v => ?_)
    rw [hc, hc1, one_smul]
    rfl
  let ι : Y ≃* ρ.range := MonoidHom.ofInjective hρi
  obtain ⟨-, hn', ⟨eQ'⟩⟩ := nonempty_quotient_map ι A eQ
  have hbot : A.map ι.toMonoidHom = ⊥ := by rw [hA1, Subgroup.map_bot]
  obtain ⟨h5, hdimM⟩ := orth_component_quotient hodd hMnd (MulEquiv.refl _) hρc
    (A.map ι.toMonoidHom) (fun a ha => ⟨1, fun w => by
      rw [hbot, Subgroup.mem_bot] at ha
      rw [ha, one_smul]
      rfl⟩) hn hK eQ'
  have hM3 : finrank F M = 3 := by
    rcases hdimM with h3 | ⟨-, hc2⟩
    · exact h3
    · rw [hbot, Subgroup.card_bot] at hc2
      omega
  obtain ⟨U₀, U₁, hU, horthU, hU3, hU0nd⟩ := exists_nondegenerate_sub h2 (Q.comp N.subtype) hNnd
    (m := 3) (by omega)
  have hk3 : Nat.card F ≠ 3 := by omega
  obtain ⟨-, -, e₃, -, -, hc₃, -, -⟩ := LocalAnalysis.ComponentInitial.orthogonal_three_derived
    hodd hk3 ((Q.comp N.subtype).comp U₀.subtype) hU0nd hU3
  have horthNM : ∀ x ∈ N, ∀ m ∈ M, polar Q x m = 0 := fun x hx m hm => by
    rw [polar_comm]
    exact horth m hm x hx
  obtain ⟨hinj₁, hmem₁, -, -⟩ :=
    LocalAnalysis.ComponentInitial.orthogonal_complement_elementary_embedding (Q.comp N.subtype) hU
      horthU
  obtain ⟨hinj₂, hmem₂, -, -⟩ :=
    LocalAnalysis.ComponentInitial.orthogonal_complement_elementary_embedding Q hMN.symm horthNM
  set f : TauCeti.QuadraticMap.orthogonalGroup ((Q.comp N.subtype).comp U₀.subtype) →*
      TauCeti.QuadraticMap.orthogonalGroup Q :=
    MonoidHom.codRestrict ((LocalAnalysis.ComponentInitial.orthExtend hMN.symm).comp
      ((LocalAnalysis.ComponentInitial.orthExtend hU).comp
        (TauCeti.QuadraticMap.orthogonalGroup ((Q.comp N.subtype).comp U₀.subtype)).subtype))
      _ (fun g => hmem₂ _ (hmem₁ g g.2))
  have hfi : Function.Injective f := fun g h hgh =>
    Subtype.ext (hinj₁ (hinj₂ (congrArg Subtype.val hgh)))
  have hfM : ∀ g m, m ∈ M → ((f g : TauCeti.QuadraticMap.orthogonalGroup Q) : V ≃ₗ[F] V) m = m := by
    intro g m hm
    have h1 := LocalAnalysis.ComponentInitial.orthExtend_apply hMN.symm
      (LocalAnalysis.ComponentInitial.orthExtend hU g) 0 ⟨m, hm⟩
    simp only [Submodule.coe_zero, zero_add, map_zero] at h1
    exact h1
  have hfN : ∀ g x, x ∈ N → ((f g : TauCeti.QuadraticMap.orthogonalGroup Q) : V ≃ₗ[F] V) x ∈ N := by
    intro g x hx
    have h1 := LocalAnalysis.ComponentInitial.orthExtend_apply hMN.symm
      (LocalAnalysis.ComponentInitial.orthExtend hU g) ⟨x, hx⟩ 0
    simp only [Submodule.coe_zero, add_zero] at h1
    change (LocalAnalysis.ComponentInitial.orthExtend hMN.symm
      (LocalAnalysis.ComponentInitial.orthExtend hU g)) x ∈ N
    rw [h1]
    exact Submodule.coe_mem _
  have hΩ : ∀ t ∈ commutator (TauCeti.QuadraticMap.orthogonalGroup
      ((Q.comp N.subtype).comp U₀.subtype)),
      ((f t : TauCeti.QuadraticMap.orthogonalGroup Q) : V ≃ₗ[F] V) ∈ orthogonalOmega Q := by
    intro t ht
    have hle : (commutator (TauCeti.QuadraticMap.orthogonalGroup
        ((Q.comp N.subtype).comp U₀.subtype))).map f ≤
          commutator (TauCeti.QuadraticMap.orthogonalGroup Q) := by
      rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator]
      exact Subgroup.commutator_mono le_top le_top
    rw [orthogonalOmega, ← Subgroup.map_subtype_commutator]
    exact ⟨f t, hle ⟨t, ht, rfl⟩, rfl⟩
  have hM0 : M ≠ ⊥ := fun h => by
    rw [h, finrank_bot] at hM3
    omega
  have hns : ∀ t, t ≠ 1 → ∀ c : F,
      (((f t : TauCeti.QuadraticMap.orthogonalGroup Q) : V ≃ₗ[F] V) : V →ₗ[F] V) ≠
        c • LinearMap.id := by
    intro t ht c hc
    have hv : ∀ v, ((f t : TauCeti.QuadraticMap.orthogonalGroup Q) : V ≃ₗ[F] V) v = c • v :=
      fun v => LinearMap.congr_fun hc v
    obtain ⟨m, hmM, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hM0
    have hc1 : c = 1 := by
      have h3 : (c - 1) • m = 0 := by rw [sub_smul, one_smul, ← hv, hfM t m hmM, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hm0)
    apply ht
    apply hfi
    refine Subtype.ext (LinearEquiv.ext fun v => ?_)
    rw [hv, hc1, one_smul, map_one]
    rfl
  have hcomm := fun t => commute_of_isCompl hMN (hfM t) (hfN t)
  set fV := (TauCeti.QuadraticMap.orthogonalGroup Q).subtype.comp f with hfV
  have hfVi : Function.Injective fV := (Subgroup.subtype_injective _).comp hfi
  set H := (commutator (TauCeti.QuadraticMap.orthogonalGroup
    ((Q.comp N.subtype).comp U₀.subtype))).map fV
  have h4 : 4 ∣ Nat.card H := by
    rw [card_map_of_injective hfVi, hc₃, card_map_of_injective e₃.symm.injective]
    exact four_dvd_card_traceZeroSpecialImage h5
  refine hsmall H ?_ ?_ ?_ ?_ h4
  · rintro _ ⟨t, ht, rfl⟩
    exact hΩ t ht
  · rintro _ ⟨t, -, rfl⟩ y hy
    exact (hcomm t).1 y (hYN y hy) (hYM y hy)
  · rintro _ ⟨t, -, rfl⟩
    exact (hcomm t).2 T lM lN hTM hTN
  · rintro _ ⟨t, -, rfl⟩ c hc
    by_cases ht : t = 1
    · rw [ht, map_one]
    · exact absurd hc (hns t ht c)

theorem split_case_false_two {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hF : Nat.card F = ℓ ^ e) (hd : 7 ≤ finrank F V) {Q : QuadraticForm F V}
    (hQ : Q.polarBilin.Nondegenerate) (T : V ≃ₗ[F] V) (d μ : Fˣ)
    (hsquare : ∀ x, T (T x) = (d : F) • x)
    (hsim : ∀ x y, Q.polarBilin (T x) (T y) = (μ : F) * Q.polarBilin x y)
    (hnonscalar : ∀ c : F, T.toLinearMap ≠ c • (1 : Module.End F V)) (b : Fˣ)
    (hb : (d : F) = (b : F) ^ 2) (hμ : (μ : F) / (d : F) = 1)
    {Y : Subgroup (V ≃ₗ[F] V)}
    (hY : CFSG.Assembly.IsComponentOf Y (TauCeti.QuadraticMap.orthogonalGroup Q ⊓
      CatalogueBProjectiveInvolution.operatorCentralizer T.toLinearMap))
    (A : Subgroup Y) [A.Normal] (hA : ∀ a ∈ A, ∃ c : F, ∀ v, (a : V ≃ₗ[F] V) v = c • v)
    {K : Type*} [Field K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (eQ : Y ⧸ A ≃* Matrix.SpecialLinearGroup (Fin 2) K)
    (hsmall : ∀ H : Subgroup (V ≃ₗ[F] V), H ≤ orthogonalOmega Q →
      (∀ z ∈ H, ∀ y ∈ Y, y * z = z * y) → (∀ z ∈ H, ∀ x, z (T x) = T (z x)) →
      (∀ z ∈ H, ∀ c : F, (z : V →ₗ[F] V) = c • LinearMap.id → z = 1) →
      4 ∣ Nat.card H → False) : False := by
  classical
  have hodd : Odd (Nat.card F) := by rw [hF]; exact (hℓ.odd_of_ne_two hℓ2).pow
  obtain ⟨-, -, hsq, -⟩ :=
    CatalogueBOrthogonalScalarSquareStructure.scalar_square_centralizer_structure ℓ e hℓ hℓ2 he
      hF (by omega) Q hQ T d μ hsquare hsim hnonscalar
  obtain ⟨hc, hP0, hN0, hpos, -⟩ := hsq b hb
  obtain ⟨horth, hndP, hndN, E, hE1, hE2, -⟩ := hpos hμ
  have hb0 : (b : F) ≠ 0 := Units.ne_zero b
  have hTP : ∀ x ∈ positiveSquareKernel T b, T x = (b : F) • x := fun x hx =>
    LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquare.apply_of_mem_positiveSquareKernel
      hb0 hx
  have hTN : ∀ x ∈ negativeSquareKernel T b, T x = (-(b : F)) • x := fun x hx =>
    LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquare.apply_of_mem_negativeSquareKernel
      hb0 hx
  have hQP : (Q.comp (positiveSquareKernel T b).subtype).polarBilin.Nondegenerate := by
    rw [QuadraticMap.polarBilin_comp]
    exact hndP
  have hQN : (Q.comp (negativeSquareKernel T b).subtype).polarBilin.Nondegenerate := by
    rw [QuadraticMap.polarBilin_comp]
    exact hndN
  have horth' : ∀ m ∈ positiveSquareKernel T b, ∀ x ∈ negativeSquareKernel T b,
      polar Q m x = 0 := horth
  have horth'' : ∀ m ∈ negativeSquareKernel T b, ∀ x ∈ positiveSquareKernel T b,
      polar Q m x = 0 := fun m hm x hx => by
    rw [polar_comm]
    exact horth x hx m hm
  obtain ⟨Y₁, ι, hY₁, hι⟩ := exists_component_pullback
    (H := orthogonalOperatorCentralizer Q T.toLinearMap) (fun _ => Iff.rfl) hY
  have hval : ∀ y (hy : y ∈ Y), y = ((ι.symm ⟨y, hy⟩ : orthogonalOperatorCentralizer Q
      T.toLinearMap) : TauCeti.QuadraticMap.orthogonalGroup Q).val := fun y hy => by
    rw [← hι, MulEquiv.apply_symm_apply]
  rcases LocalAnalysis.ComponentInitial.CentralQuotientLift.fst_eq_or_snd_eq_of_isComponent_prod
      (LocalAnalysis.ComponentInitial.isComponent_map_of_isComponent E hY₁) with h2 | h1
  ·
    have h2' : ∀ x ∈ Y₁, (E x).2 = 1 := fun x hx => h2 _ (Subgroup.mem_map_of_mem _ hx)
    obtain ⟨ρ₁, hρ₁i, hρ₁c, -⟩ := OddClassSelector.restrict_component E hY₁ h2'
    refine split_factor_false_two hodd hd hc horth' hQP hQN hN0 T _ _ hTP hTN
      (fun y hy x hx => ?_) (fun y hy m hm => ?_) (ρ₁.comp ι.symm.toMonoidHom)
      (hρ₁i.comp ι.symm.injective) ?_ A hA hn hK eQ hsmall
    · have h3 := hE2 (ι.symm ⟨y, hy⟩) ⟨x, hx⟩
      rw [h2' _ (ι.symm ⟨y, hy⟩).2] at h3
      rw [hval y hy]
      exact h3.symm
    · have h3 := hE1 (ι.symm ⟨y, hy⟩) ⟨m, hm⟩
      rw [hval y hy, ← h3]
      exact Submodule.coe_mem _
    · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr ι.symm.surjective,
        ← MonoidHom.range_eq_map]
      exact hρ₁c
  ·
    have h1' : ∀ x ∈ Y₁, ((E.trans MulEquiv.prodComm) x).2 = 1 := fun x hx =>
      h1 _ (Subgroup.mem_map_of_mem _ hx)
    obtain ⟨ρ₁, hρ₁i, hρ₁c, -⟩ :=
      OddClassSelector.restrict_component (E.trans MulEquiv.prodComm) hY₁ h1'
    refine split_factor_false_two hodd hd hc.symm horth'' hQN hQP hP0 T _ _ hTN hTP
      (fun y hy x hx => ?_) (fun y hy m hm => ?_) (ρ₁.comp ι.symm.toMonoidHom)
      (hρ₁i.comp ι.symm.injective) ?_ A hA hn hK eQ hsmall
    · have h3 := hE1 (ι.symm ⟨y, hy⟩) ⟨x, hx⟩
      rw [show (E (ι.symm ⟨y, hy⟩)).1 = 1 from h1' _ (ι.symm ⟨y, hy⟩).2] at h3
      rw [hval y hy]
      exact h3.symm
    · have h3 := hE2 (ι.symm ⟨y, hy⟩) ⟨m, hm⟩
      rw [hval y hy, ← h3]
      exact Submodule.coe_mem _
    · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr ι.symm.surjective,
        ← MonoidHom.range_eq_map]
      exact hρ₁c

theorem similitude_case_false_two {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hF : Nat.card F = ℓ ^ e) (hd : 7 ≤ finrank F V) {Q : QuadraticForm F V}
    (hQ : Q.polarBilin.Nondegenerate) (T : V ≃ₗ[F] V) (d μ : Fˣ)
    (hsquare : ∀ x, T (T x) = (d : F) • x)
    (hsim : ∀ x y, Q.polarBilin (T x) (T y) = (μ : F) * Q.polarBilin x y)
    (hnonscalar : ∀ c : F, T.toLinearMap ≠ c • (1 : Module.End F V))
    {Y : Subgroup (V ≃ₗ[F] V)}
    (hY : CFSG.Assembly.IsComponentOf Y (TauCeti.QuadraticMap.orthogonalGroup Q ⊓
      CatalogueBProjectiveInvolution.operatorCentralizer T.toLinearMap))
    (A : Subgroup Y) [A.Normal] (hA : ∀ a ∈ A, ∃ c : F, ∀ v, (a : V ≃ₗ[F] V) v = c • v)
    {K : Type*} [Field K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (eQ : Y ⧸ A ≃* Matrix.SpecialLinearGroup (Fin 2) K)
    (hsmall : ∀ H : Subgroup (V ≃ₗ[F] V), H ≤ orthogonalOmega Q →
      (∀ z ∈ H, ∀ y ∈ Y, y * z = z * y) → (∀ z ∈ H, ∀ x, z (T x) = T (z x)) →
      (∀ z ∈ H, ∀ c : F, (z : V →ₗ[F] V) = c • LinearMap.id → z = 1) →
      4 ∣ Nat.card H → False) : False := by
  obtain ⟨hpm, -, -, -⟩ :=
    CatalogueBOrthogonalScalarSquareStructure.scalar_square_centralizer_structure ℓ e hℓ hℓ2 he
      hF (by omega) Q hQ T d μ hsquare hsim hnonscalar
  by_cases hsq : IsSquare (d : F)
  · obtain ⟨b0, hb0⟩ := hsq
    have hb00 : b0 ≠ 0 := by
      rintro rfl
      exact Units.ne_zero d (by rw [hb0, mul_zero])
    have hb : (d : F) = ((Units.mk0 b0 hb00 : Fˣ) : F) ^ 2 := by rw [Units.val_mk0, hb0, _root_.sq]
    rcases hpm with h1 | h1
    · exact split_case_false_two hℓ hℓ2 he hF hd hQ T d μ hsquare hsim hnonscalar _ hb h1 hY A hA
        hn hK eQ hsmall
    · exact paired_case_false hℓ hℓ2 he hF hd hQ T d μ hsquare hsim hnonscalar _ hb h1 hY A hA hn
        hK eQ
  · rcases hpm with h1 | h1
    · exact ext_case_false hℓ hℓ2 he hF hd hQ T d μ hsquare hsim hnonscalar hsq h1 hY A hA hn hK
        eQ
    · exact unitary_case_false hℓ hℓ2 he hF hd hQ T d μ hsquare hsim hnonscalar hsq h1 hY A hA hn
        hK eQ

end Linear

theorem coordinate_false_two {F : Type} [Field F] [Finite F] {ℓ e : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e) (hF : Nat.card F = ℓ ^ e) {d : ℕ} (hd : 7 ≤ d)
    {Q : QuadraticForm F (Fin d → F)} (hQ : Q.polarBilin.Nondegenerate) (g : similarityPairs Q)
    (hσ2 : g.val.right ^ 2 = 1) (c : Fˣ)
    (hc : g.val.left * CatalogueBHigherLinearField.glFieldAut (Fin d) F g.val.right g.val.left =
      Matrix.GeneralLinearGroup.scalar (Fin d) c)
    (hlin : g.val.right = 1 → ∀ a : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin d) a ≠ g.val.left)
    {K : Type*} [Field K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (h : FixedRootTwoConfig (matrixProjectiveConjugationHom Q g) K) : False := by
  classical
  have hdV : finrank F (Fin d → F) = d := Module.finrank_fin_fun F
  obtain ⟨Y, hY, ⟨A, _, hAZ, ⟨eQ⟩⟩, hsmall⟩ := exists_fixed_root_lift_two
    (matrixDerivedScalars Q) (matrixDerivedScalars_le_center Q) (matrixDerivedConjugation Q g)
    (matrixDerivedScalars_invariant Q g)
    (OddClassSelector.matrixDerivedConjugation_involutive Q g hσ2 ⟨c, hc⟩) h
  set J := OddClassSelector.derivedLinear Q
  have hJi : Function.Injective J := OddClassSelector.derivedLinear_injective Q
  set τ₀ := coordinateSemilinearMap g.val with hτ₀
  have hYl : CFSG.Assembly.IsComponentOf (Y.map J)
      (TauCeti.QuadraticMap.orthogonalGroup Q ⊓ commutant τ₀) := by
    have h1 := SymmetricLocal.isComponentOf_map_of_injective J hJi hY
    rw [OddClassSelector.map_derivedLinear_fixed] at h1
    have hle : orthogonalOmega Q ⊓ commutant τ₀ ≤
        TauCeti.QuadraticMap.orthogonalGroup Q ⊓ commutant τ₀ :=
      inf_le_inf_right _ (Subgroup.commutator_le_self _)
    have hnorm : ((orthogonalOmega Q ⊓ commutant τ₀).subgroupOf
        (TauCeti.QuadraticMap.orthogonalGroup Q ⊓ commutant τ₀)).Normal := by
      rw [normal_subgroupOf_iff hle]
      intro x k hx hk
      rw [Subgroup.mem_inf] at hx hk ⊢
      refine ⟨?_, mul_mem (mul_mem hk.2 hx.2) (inv_mem hk.2)⟩
      exact (mem_normalizer_iff.mp (Subgroup.normalizer_commutator_ge_left _ _ hk.1) x).mp hx.1
    exact OddClassSelector.isComponentOf_of_normal_le h1 hle hnorm
  have hscal : ∀ m : matrixDerived Q, m ∈ matrixDerivedScalars Q → ∃ c' : F,
      ((J m : (Fin d → F) ≃ₗ[F] (Fin d → F)) : (Fin d → F) →ₗ[F] (Fin d → F)) =
        c' • LinearMap.id := by
    intro m hm
    obtain ⟨c', hc'⟩ := (mem_matrixDerivedScalars_iff Q m).mp hm
    refine ⟨c', LinearMap.ext fun v => ?_⟩
    change matrixLinearEquiv m.val v = _
    rw [← hc']
    exact LocalAnalysis.ComponentInitial.OddOrthogonal.matrixLinearEquiv_scalar c' v
  set ι : Y ≃* Y.map J := Y.equivMapOfInjective J hJi
  obtain ⟨-, hn', ⟨eQl⟩⟩ := nonempty_quotient_map ι A eQ
  have hAl : ∀ a ∈ A.map ι.toMonoidHom, ∃ c' : F, ∀ v,
      (a : (Fin d → F) ≃ₗ[F] (Fin d → F)) v = c' • v := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨c', hc'⟩ := hscal _ (hAZ a ha)
    exact ⟨c', fun v => LinearMap.congr_fun hc' v⟩
  have hsmall' : ∀ H : Subgroup ((Fin d → F) ≃ₗ[F] (Fin d → F)), H ≤ orthogonalOmega Q →
      (∀ z ∈ H, ∀ y ∈ Y.map J, y * z = z * y) → H ≤ commutant τ₀ →
      (∀ z ∈ H, ∀ c' : F, (z : (Fin d → F) →ₗ[F] (Fin d → F)) = c' • LinearMap.id → z = 1) →
      4 ∣ Nat.card H → False := by
    intro H hHΩ hHY hHτ hHs h4
    have hHr : H ≤ J.range := by rw [OddClassSelector.range_derivedLinear]; exact hHΩ
    have hcard : Nat.card (H.comap J) = Nat.card H := by
      rw [← card_map_of_injective hJi, map_comap_eq_self hHr]
    have hZ0 : (matrixDerivedScalars Q).subgroupOf (H.comap J) = ⊥ := by
      refine (Subgroup.eq_bot_iff_forall _).mpr fun m hm => ?_
      obtain ⟨c', hc'⟩ := hscal _ (Subgroup.mem_subgroupOf.mp hm)
      have h1 := hHs (J m) m.2 c' hc'
      exact Subtype.ext (hJi (h1.trans (map_one J).symm))
    refine hsmall (H.comap J) (fun z hz y hy => hJi ?_)
      (fun z hz => (OddClassSelector.derivedConj_eq_iff Q g z).mpr (hHτ hz)) ?_
    · rw [map_mul, map_mul]
      exact hHY (J z) hz (J y) (mem_map_of_mem J hy)
    · rw [hZ0, Subgroup.index_bot, hcard]
      exact h4
  by_cases hσ1 : g.val.right = 1
  swap
  ·
    have hQτ := multiplier_spec Q g
    have hform : ∀ x y, Q.polarBilin (τ₀ x) (τ₀ y) =
        (multiplier Q g : F) * g.val.right (Q.polarBilin x y) := by
      intro x y
      rw [polarBilin_apply_apply, polarBilin_apply_apply, polar, polar,
        ← map_add (coordinateSemilinearMap g.val) x y, hQτ, hQτ, hQτ, map_sub, map_sub]
      ring
    have hsquare : ∀ x, τ₀ (τ₀ x) = (c : F) • x := fun x => by
      rw [hτ₀, ← coordinateSemilinearMap_mul, coordinateSemilinearMap_apply,
        coordinateSemilinearGroup_mul_matrix, hc, coordinateSemilinearGroup_mul_field, ← pow_two,
        hσ2]
      exact LocalAnalysis.ComponentInitial.OddOrthogonal.matrixLinearEquiv_scalar c x
    exact semilinear_case_false hℓ hℓ2 he hF (by omega) hQ g.val.right hσ2 hσ1 τ₀ (multiplier Q g) c
      (coordinateSemilinearMap_smul g.val) hform hsquare hYl _ hAl hn hK eQl
  set Aₗ := matrixLinearEquiv g.val.left with hAₗ
  have hτ : ∀ v, τ₀ v = Aₗ v := by
    intro v
    rw [hτ₀, coordinateSemilinearMap_apply, hσ1]
    rfl
  have hcomm : commutant τ₀ =
      CatalogueBProjectiveInvolution.operatorCentralizer Aₗ.toLinearMap := by
    ext u
    rw [mem_commutant]
    change _ ↔ ∀ x, u (Aₗ x) = Aₗ (u x)
    simp only [hτ]
  rw [hcomm] at hYl
  have hAA : g.val.left * g.val.left = Matrix.GeneralLinearGroup.scalar (Fin d) c := by
    rw [← hc, hσ1, map_one, MulAut.one_apply]
  have hsquare : ∀ x, Aₗ (Aₗ x) = (c : F) • x := by
    intro x
    rw [← LinearEquiv.mul_apply, hAₗ, ← matrixLinearEquiv_mul, hAA]
    exact LocalAnalysis.ComponentInitial.OddOrthogonal.matrixLinearEquiv_scalar c x
  have hQA : ∀ v, Q (Aₗ v) = (multiplier Q g : F) * Q v := by
    intro v
    have := multiplier_spec Q g v
    rw [← hτ₀, hτ v, hσ1] at this
    exact this
  have hsim : ∀ x y, Q.polarBilin (Aₗ x) (Aₗ y) = (multiplier Q g : F) * Q.polarBilin x y := by
    intro x y
    rw [polarBilin_apply_apply, polarBilin_apply_apply, polar, polar, ← map_add, hQA, hQA, hQA]
    ring
  have hnonscalar : ∀ c' : F, Aₗ.toLinearMap ≠ c' • (1 : Module.End F (Fin d → F)) := by
    intro c' hc'
    have hc0 : c' ≠ 0 := by
      rintro rfl
      have h0 := LinearMap.congr_fun hc' (Pi.single ⟨0, by omega⟩ 1)
      rw [zero_smul, LinearMap.zero_apply, LinearEquiv.coe_coe,
        LinearEquiv.map_eq_zero_iff] at h0
      simpa using congrFun h0 ⟨0, by omega⟩
    apply hlin hσ1 (Units.mk0 c' hc0)
    apply matrixLinearIso.injective
    refine LinearEquiv.ext fun v => ?_
    change matrixLinearEquiv (Matrix.GeneralLinearGroup.scalar (Fin d) (Units.mk0 c' hc0)) v =
      Aₗ v
    rw [LocalAnalysis.ComponentInitial.OddOrthogonal.matrixLinearEquiv_scalar]
    have := LinearMap.congr_fun hc' v
    rw [LinearEquiv.coe_coe] at this
    rw [this]
    rfl
  exact similitude_case_false_two hℓ hℓ2 he hF (by omega) hQ Aₗ c (multiplier Q g) hsquare hsim
    hnonscalar hYl _ hAl hn hK eQl fun H h₁ h₂ h₃ h₄ h₅ =>
      hsmall' H h₁ h₂ (fun z hz => mem_commutant.mpr fun x => by rw [hτ, hτ]; exact h₃ z hz x)
        h₄ h₅

theorem model_false_two {F : Type} [Field F] [Finite F] {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (he : 1 ≤ e) (hF : Nat.card F = ℓ ^ e) {d : ℕ} (hd : 7 ≤ d)
    {Q : QuadraticForm F (Fin d → F)} (hQ : Q.polarBilin.Nondegenerate)
    (hrep : CatalogueBOrthogonalInvolutionRepresentation.SemilinearRepresentation Q)
    {K : Type*} [Field K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (α : MulAut (matrixProjectiveDerived Q)) (hα : orderOf α = 2)
    (h : FixedRootTwoConfig α K) : False := by
  have hαα : α * α = 1 := by rw [← _root_.sq, ← hα, pow_orderOf_eq_one]
  have hα1 : α ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hα
    omega
  obtain ⟨β, g, hβ, hσ2, ⟨c, hc⟩, hlin, -⟩ := hrep.2 α hαα hα1
  refine coordinate_false_two hℓ hℓ2 he hF hd hQ g hσ2 c hc hlin hn hK
    (h.of_mulEquiv (β⁻¹ : MulAut _) fun x => ?_)
  rw [← hβ]
  change β⁻¹ (α x) = β⁻¹ (α (β (β⁻¹ x)))
  rw [MulAut.apply_inv_self]

end OddOrthogonalRankOne

open OddOrthogonalRankOne CatalogueBOrthogonalInvolutionRepresentation
  CatalogueBOrthogonalPointData in
theorem odd_orthogonal_fixed_root_rankOne_exclusion
    (K : Type*) [Field K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    {D : Type} [Group D] (α : MulAut D) (hα : orderOf α = 2)
    (S : Subgroup (α.toMonoidHom.eqLocus (MonoidHom.id D))) (hSn : S.Normal)
    (hSs : IsSimpleGroup S) (hSnab : ∃ a b : S, a * b ≠ b * a)
    (hSK : Nonempty (S ≃* Matrix.SpecialLinearGroup (Fin 2) K))
    (h2 : ∀ W : Subgroup D, W ≤ α.toMonoidHom.eqLocus (MonoidHom.id D) ⊓
      centralizer ((S.map (α.toMonoidHom.eqLocus (MonoidHom.id D)).subtype : Subgroup D) :
        Set D) → IsPGroup 2 W → Nat.card W ≤ 2)
    {t : StatedLieTag} (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus)
    (p f r : ℕ) (hp : p ≠ 2) : ¬ StatedClassicalModel D t r p f := by
  intro hL
  have hrep := odd_orthogonal_involution_semilinear_representation t ht hL
  have h0 : FixedRootTwoConfig α K := ⟨S, hSn, hSs, hSnab, hSK, h2⟩
  have finish : ∀ {F : Type} [Field F] [Finite F] {d : ℕ} (Q : QuadraticForm F (Fin d → F)),
      Nat.card F = p ^ f → 7 ≤ d → Q.polarBilin.Nondegenerate → SemilinearRepresentation Q →
      (D ≃* matrixProjectiveDerived Q) → False := by
    intro F _ _ d Q hF hd hQ hrepQ ψ
    exact model_false_two hL.1.1 hp hL.1.2.1 hF hd hQ hrepQ hn hK (MulAut.congr ψ α)
      (by rw [MulEquiv.orderOf_eq]; exact hα)
      (h0.of_mulEquiv ψ fun x => by
        change ψ (α x) = ψ (α (ψ.symm (ψ x)))
        rw [MulEquiv.symm_apply_apply])
  rcases ht with rfl | rfl | rfl
  · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hL.2
    obtain ⟨-, hQ, -⟩ := coordinate_model_witness_odd hL F hF e
    exact finish _ hF (by have := hL.1.2.2.1; omega) hQ (hrep F hF e)
      (coordinateOddWitnessEquiv F e)
  · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hL.2
    obtain ⟨-, hQ, -⟩ := coordinate_model_witness_plus hL F hF e
    exact finish _ hF (by have := hL.1.2.2; omega) hQ (hrep F hF e)
      (coordinatePlusWitnessEquiv F e)
  · obtain ⟨F, _, _, hF, b, c, hirr, ⟨e⟩⟩ := hL.2
    have hr : 1 ≤ r := by have := hL.1.2.2; omega
    obtain ⟨-, hQ, -⟩ := coordinate_model_witness_minus hL F hF b c hirr e
    exact finish _ hF (by have := hL.1.2.2; omega) hQ (hrep hr F hF b c hirr e)
      (coordinateMinusWitnessEquiv F hr b c e)

theorem fixedRootSelector_oddOrthogonal :
    FixedRootSelector fun D _ => ∃ (t : StatedLieTag) (r p f : ℕ),
      (t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) ∧ p ≠ 2 ∧
        StatedClassicalModel D t r p f := by
  intro D _ _ _ ⟨t, r, p, f, ht, hp, hM⟩ n hn K _ _ hK α hα S hSα hSn hSK hr
  obtain ⟨hSs, hSnab, hSK', -⟩ := subgroupOf_fixedRoot_data hn hK hSα hSK
  exact (odd_orthogonal_fixed_root_rankOne_exclusion K hn
    (by rw [Nat.card_eq_fintype_card, hK]) α hα _ hSn hSs hSnab hSK'
    (two_bound_of_fixedRootRankOne hSα hr) ht p f r hp hM).elim

theorem fixedRootSelector_oddOrthogonal_lieModel :
    FixedRootSelector fun D _ => ∃ (t : StatedLieTag) (r p f : ℕ),
      (t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) ∧ p ≠ 2 ∧ LieModel D t r p f :=
  fixedRootSelector_oddOrthogonal.mono fun _ _ _ _ ⟨t, r, p, f, ht, hp, h⟩ =>
    ⟨t, r, p, f, ht, hp, statedClassicalModel_of_lieModel (by
      rcases ht with rfl | rfl | rfl <;> decide) h⟩

end CFSG.LocalAnalysis.EvenBN.GMSK
