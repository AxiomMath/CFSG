module

public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTIUnitarySocleForms
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpCent
public import CFSG.LieType.Steinberg.CentralExt.SymplecticPerfect
public import CFSG.ClassicalInvolution.Orders.OrthogonalIndex
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinearBranches

public noncomputable section

namespace CFSG.SeitzReduction.RankOne.ClTwoPart

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem card_fixed_dvd_card_mul_onQuotient {X : Type*} [Group X] [Finite X] (Z : Subgroup X)
    [Z.Normal] (ψ : MulAut X) (hinv : Z.map ψ.toMonoidHom = Z) :
    Nat.card (fixedSubgroup ψ) ∣
      Nat.card Z * Nat.card (fixedSubgroup
        (CatalogueBFixedCentralQuotient.onQuotient Z ψ hinv)) := by
  let φ : fixedSubgroup ψ →*
      fixedSubgroup (CatalogueBFixedCentralQuotient.onQuotient Z ψ hinv) :=
    { toFun := fun x => ⟨QuotientGroup.mk' Z x, by
        change CatalogueBFixedCentralQuotient.onQuotient Z ψ hinv (QuotientGroup.mk' Z x) =
          QuotientGroup.mk' Z x
        rw [CatalogueBFixedCentralQuotient.onQuotient_mk]
        exact congrArg _ x.2⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp }
  have hkr := Subgroup.card_ker_mul_card_range φ
  let ι : φ.ker →* Z :=
    { toFun := fun x => ⟨((x : fixedSubgroup ψ) : X), by
        have h1 : φ x = 1 := x.2
        have h2 : QuotientGroup.mk' Z ((x : fixedSubgroup ψ) : X) = 1 :=
          congrArg Subtype.val h1
        exact (QuotientGroup.eq_one_iff _).mp h2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hι : Function.Injective ι := fun a b hab => by
    have h1 := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext h1)
  rw [← hkr]
  exact Nat.mul_dvd_mul (Subgroup.card_dvd_of_injective ι hι)
    (Subgroup.card_subgroup_dvd_card _)

theorem two_pow_dvd_of_two_pow_succ_dvd_two_mul {n m : ℕ} (h : 2 ^ (n + 1) ∣ 2 * m) :
    2 ^ n ∣ m := by
  rw [pow_succ, mul_comm] at h
  exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h

theorem dvd_two_of_pos_of_le_two {c : ℕ} (h0 : 0 < c) (h2 : c ≤ 2) : c ∣ 2 := by
  interval_cases c <;> norm_num

theorem eight_dvd_card_SL_two {k : Type} [Field k] [Finite k] (hq : Odd (Nat.card k)) :
    8 ∣ Nat.card (SpecialLinearGroup (Fin 2) k) := by
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
  exact (Nat.eight_dvd_sq_sub_one_of_odd hq).mul_left _

open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl in
theorem lam_injective {r : ℕ} {k : Type} [Field k] (i : Fin r) :
    Function.Injective (lam (r := r) (k := k) i) := by
  intro g h hgh
  have hm := congrArg (fun x : StatedSp r k => ((x : GL (Fin r ⊕ Fin r) k) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k)) hgh
  simp only [coe_lam] at hm
  have hne : (Sum.inl i : Fin r ⊕ Fin r) ≠ Sum.inr i := Sum.inl_ne_inr
  obtain ⟨a1, a2, a3, a4⟩ := pairMat_apply_pair hne (g : Matrix (Fin 2) (Fin 2) k)
  obtain ⟨b1, b2, b3, b4⟩ := pairMat_apply_pair hne (h : Matrix (Fin 2) (Fin 2) k)
  ext x y
  fin_cases x <;> fin_cases y
  · simpa [← a1, ← b1] using congrFun (congrFun hm (Sum.inl i)) (Sum.inl i)
  · simpa [← a2, ← b2] using congrFun (congrFun hm (Sum.inl i)) (Sum.inr i)
  · simpa [← a3, ← b3] using congrFun (congrFun hm (Sum.inr i)) (Sum.inl i)
  · simpa [← a4, ← b4] using congrFun (congrFun hm (Sum.inr i)) (Sum.inr i)

theorem eight_dvd_card_statedSp {r : ℕ} (hr : 1 ≤ r) {k : Type} [Field k] [Finite k]
    (hq : Odd (Nat.card k)) : 8 ∣ Nat.card (StatedSp r k) :=
  (eight_dvd_card_SL_two hq).trans
    (Subgroup.card_dvd_of_injective _ (lam_injective (r := r) (k := k) ⟨0, hr⟩))

theorem eight_dvd_card_isometryGroup {k W : Type} [Field k] [Finite k] [AddCommGroup W]
    [Module k W] [FiniteDimensional k W] (hq : Odd (Nat.card k)) (B : LinearMap.BilinForm k W)
    (hB : B.IsAlt) (hnd : B.Nondegenerate) (hW : 0 < Module.finrank k W) :
    8 ∣ Nat.card (CatalogueBAlternatingIsometry.isometryGroup B) := by
  obtain ⟨m, hdm, -⟩ := CatalogueBAlternatingIsometry.exists_isometryEquiv_symplectic B hB hnd
  obtain ⟨e⟩ := OutcomeLocal.nonempty_altIsometry_mulEquiv_statedSp B hB hnd hdm
  rw [Nat.card_congr e.toEquiv]
  exact eight_dvd_card_statedSp (by omega) hq

open CFSG.ComponentClassification.CatalogueBSymplecticB in
theorem sixtyFour_dvd_card_of_equiv_prod {k W₁ W₂ C : Type} [Field k] [Finite k] [Group C]
    [AddCommGroup W₁] [Module k W₁] [FiniteDimensional k W₁] [AddCommGroup W₂] [Module k W₂]
    [FiniteDimensional k W₂] (hq : Odd (Nat.card k)) {B₁ : LinearMap.BilinForm k W₁}
    {B₂ : LinearMap.BilinForm k W₂} (hB₁ : B₁.IsAlt) (hB₂ : B₂.IsAlt) (hnd₁ : B₁.Nondegenerate)
    (hnd₂ : B₂.Nondegenerate) (hW₁ : 0 < Module.finrank k W₁) (hW₂ : 0 < Module.finrank k W₂)
    (e : C ≃* LocalAnalysis.ComponentInitial.sesqUnitaryGroup B₁ ×
      LocalAnalysis.ComponentInitial.sesqUnitaryGroup B₂) : 64 ∣ Nat.card C := by
  rw [Nat.card_congr e.toEquiv, Nat.card_prod,
    Nat.card_congr (sesqUnitaryIsometryEquiv B₁).toEquiv,
    Nat.card_congr (sesqUnitaryIsometryEquiv B₂).toEquiv]
  exact Nat.mul_dvd_mul (eight_dvd_card_isometryGroup hq B₁ hB₁ hnd₁ hW₁)
    (eight_dvd_card_isometryGroup hq B₂ hB₂ hnd₂ hW₂)

open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher in
open CFSG.ComponentClassification.Burgoyne.Sp (spCent spCentEquiv) in
theorem two_pow_dvd_card_fixed_conjAut {r : ℕ} {k : Type} [Field k] [Finite k] (A : gsp r k)
    {n : ℕ} (h : 2 ^ (n + 1) ∣ Nat.card
      (LocalAnalysis.ComponentInitial.UnitaryHigher.similitudeCentralizer
      (CFSG.LocalAnalysis.ComponentInitial.pairedSympForm k r)
      (Matrix.GeneralLinearGroup.toLin (A : GL (Fin r ⊕ Fin r) k)))) :
    2 ^ n ∣ Nat.card (fixedSubgroup (conjAut r k A)) := by
  have hinv := map_eq_of_forall_mem (conjSp r k) (spScalars r k)
    (fun A _ hz => conjSp_mem_spScalars A hz) A
  have hfix := card_fixed_dvd_card_mul_onQuotient (spScalars r k) (conjSp r k A) hinv
  let Φ := (MulEquiv.subgroupCongr
    (show fixedSubgroup (conjSp r k A) = spCent r k A from rfl)).trans (spCentEquiv A)
  have hC := Nat.card_congr Φ.toEquiv
  have hZ := dvd_two_of_pos_of_le_two Nat.card_pos
    (LieType.Steinberg.card_statedScalars_subgroupOf_statedSp_le_two r k)
  exact two_pow_dvd_of_two_pow_succ_dvd_two_mul
    ((hC ▸ h).trans (hfix.trans (Nat.mul_dvd_mul_right hZ _)))

section Orthogonal

open Module QuadraticMap

@[expose] noncomputable def signChange (k : Type) [Field k] (n : ℕ) :
    (Fin n → ℤˣ) →* ((Fin n → k) ≃ₗ[k] (Fin n → k)) where
  toFun ε := LinearEquiv.piCongrRight fun i =>
    LinearEquiv.smulOfUnit (Units.map (Int.castRingHom k).toMonoidHom (ε i))
  map_one' := LinearEquiv.ext fun x => funext fun i => by
    change (Units.map (Int.castRingHom k).toMonoidHom (1 : ℤˣ)) • x i = x i
    rw [map_one, one_smul]
  map_mul' ε ε' := LinearEquiv.ext fun x => funext fun i => by
    change (Units.map (Int.castRingHom k).toMonoidHom (ε i * ε' i)) • x i =
      (Units.map (Int.castRingHom k).toMonoidHom (ε i)) •
        ((Units.map (Int.castRingHom k).toMonoidHom (ε' i)) • x i)
    rw [map_mul, mul_smul]

theorem signChange_apply {k : Type} [Field k] {n : ℕ} (ε : Fin n → ℤˣ) (x : Fin n → k) (i : Fin n) :
    signChange k n ε x i = ((ε i : ℤ) : k) * x i := rfl

theorem signChange_mem {k : Type} [Field k] {n : ℕ} (w : Fin n → k) (ε : Fin n → ℤˣ) :
    signChange k n ε ∈ TauCeti.QuadraticMap.orthogonalGroup (weightedSumSquares k w) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro x
  simp only [weightedSumSquares_apply, signChange_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : ((ε i : ℤ) : k) * ((ε i : ℤ) : k) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  linear_combination (w i * x i * x i) * h

theorem signChange_injective {k : Type} [Field k] {n : ℕ} (h2 : (2 : k) ≠ 0) :
    Function.Injective (signChange k n) := by
  intro ε ε' h
  funext i
  have h1 := congrArg (fun f : (Fin n → k) ≃ₗ[k] (Fin n → k) => f (Pi.single i 1) i) h
  simp only [signChange_apply, Pi.single_eq_same, mul_one] at h1
  rcases Int.units_eq_one_or (ε i) with h3 | h3 <;> rcases Int.units_eq_one_or (ε' i) with h4 | h4
  · rw [h3, h4]
  · exfalso; rw [h3, h4] at h1; norm_num at h1
    apply h2; linear_combination h1
  · exfalso; rw [h3, h4] at h1; norm_num at h1
    apply h2; linear_combination -h1
  · rw [h3, h4]

theorem det_neg_one_eq {k V : Type} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] :
    LinearEquiv.det (LinearEquiv.neg k : V ≃ₗ[k] V) = (-1) ^ finrank k V := by
  ext
  have h : ((LinearEquiv.neg k : V ≃ₗ[k] V) : V →ₗ[k] V) = (-1 : k) • LinearMap.id := by
    ext; simp
  rw [LinearEquiv.coe_det, h, LinearMap.det_smul, LinearMap.det_id, mul_one]
  simp

theorem two_pow_dvd_card_orthogonalGroup_weightedSumSquares {k : Type} [Field k] {n : ℕ}
    (h2 : (2 : k) ≠ 0) (w : Fin n → k) :
    2 ^ n ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup (weightedSumSquares k w)) := by
  let φ := (signChange k n).codRestrict _ (signChange_mem w)
  have hφ : Function.Injective φ := fun a b hab =>
    signChange_injective h2 (congrArg Subtype.val hab)
  have h := Subgroup.card_dvd_of_injective φ hφ
  rwa [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Nat.card_eq_fintype_card, Fintype.card_units_int] at h

theorem two_pow_finrank_dvd_card_orthogonalGroup {k W : Type} [Field k] [AddCommGroup W]
    [Module k W] [FiniteDimensional k W] (h2 : (2 : k) ≠ 0) (Q : QuadraticForm k W) :
    2 ^ finrank k W ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  let : Invertible (2 : k) := invertibleOfNonzero h2
  obtain ⟨w, ⟨e⟩⟩ := Q.equivalent_weightedSumSquares
  rw [Nat.card_congr (TauCeti.QuadraticMap.orthogonalGroupCongr e).toEquiv]
  exact two_pow_dvd_card_orthogonalGroup_weightedSumSquares h2 w

open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed in
theorem card_scalarSigns_le_two {k W : Type} [Field k] [AddCommGroup W] [Module k W]
    (Q : QuadraticForm k W) : Nat.card (scalarSigns Q) ≤ 2 := by
  classical
  have hsub : ((scalarSigns Q : Subgroup _) : Set (TauCeti.QuadraticMap.orthogonalGroup Q)) ⊆
      {1, QuadraticMap.negOrthogonal Q} := fun g hg => by
    rcases hg with hg | hg
    · exact Or.inl hg
    · exact Or.inr hg
  change Nat.card ((scalarSigns Q : Subgroup _) : Set (TauCeti.QuadraticMap.orthogonalGroup Q)) ≤ 2
  rw [Nat.card_coe_set_eq]
  calc Set.ncard ((scalarSigns Q : Subgroup _) : Set (TauCeti.QuadraticMap.orthogonalGroup Q))
      ≤ Set.ncard ({1, QuadraticMap.negOrthogonal Q} :
        Set (TauCeti.QuadraticMap.orthogonalGroup Q)) := Set.ncard_le_ncard hsub
    _ ≤ 2 := by
      refine (Set.ncard_insert_le _ _).trans ?_
      rw [Set.ncard_singleton]

open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed in
theorem negOrthogonal_not_mem_orthogonalDerived {k W : Type} [Field k] [AddCommGroup W]
    [Module k W] [FiniteDimensional k W] (h2 : (2 : k) ≠ 0) (Q : QuadraticForm k W)
    (hodd : Odd (finrank k W)) : QuadraticMap.negOrthogonal Q ∉ orthogonalDerived Q := by
  intro h
  have hk := Abelianization.commutator_subset_ker (QuadraticMap.orthogonalDet Q) h
  rw [MonoidHom.mem_ker, QuadraticMap.orthogonalDet_apply, QuadraticMap.coe_negOrthogonal,
    det_neg_one_eq, hodd.neg_one_pow] at hk
  have h1 := congrArg Units.val hk
  simp only [Units.val_neg, Units.val_one] at h1
  apply h2
  linear_combination -h1

open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed in
theorem card_scalarSigns_subgroupOf_orthogonalDerived_of_odd {k W : Type} [Field k]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W] (h2 : (2 : k) ≠ 0)
    (Q : QuadraticForm k W) (hodd : Odd (finrank k W)) :
    Nat.card ((scalarSigns Q).subgroupOf (orthogonalDerived Q)) = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun a b => ?_⟩, inferInstance⟩
  have key : ∀ x : (scalarSigns Q).subgroupOf (orthogonalDerived Q), x = 1 := by
    intro x
    have hx : ((x : orthogonalDerived Q) : TauCeti.QuadraticMap.orthogonalGroup Q) ∈
        scalarSigns Q := x.2
    rcases hx with hx | hx
    · exact Subtype.ext (Subtype.ext hx)
    · exact absurd (hx ▸ (x : orthogonalDerived Q).2)
        (negOrthogonal_not_mem_orthogonalDerived h2 Q hodd)
  rw [key a, key b]

theorem polar_map_isometryEquiv {K : Type} [Field K] {V₁ V₂ : Type*} [AddCommGroup V₁]
    [Module K V₁] [AddCommGroup V₂] [Module K V₂] {Q₁ : QuadraticForm K V₁}
    {Q₂ : QuadraticForm K V₂} (e : Q₁.IsometryEquiv Q₂) (x y : V₁) :
    polar Q₂ (e x) (e y) = polar Q₁ x y := by
  simp only [polar, ← map_add, e.map_app]

@[expose] def hypPairMap {K : Type} [Field K] {V₁ V₂ : Type*} [AddCommGroup V₁]
    [Module K V₁] [AddCommGroup V₂] [Module K V₂] {Q₁ : QuadraticForm K V₁}
    {Q₂ : QuadraticForm K V₂} (e : Q₁.IsometryEquiv Q₂)
    (P : ClassicalGroups.Orthogonal.HypPair Q₁) : ClassicalGroups.Orthogonal.HypPair Q₂ where
  e := e P.e
  f := e P.f
  Q_e := by rw [e.map_app]; exact P.Q_e
  Q_f := by rw [e.map_app]; exact P.Q_f
  polar_ef := by rw [polar_map_isometryEquiv]; exact P.polar_ef

theorem hypPairMap_orth {K : Type} [Field K] {V₁ V₂ : Type*} [AddCommGroup V₁]
    [Module K V₁] [AddCommGroup V₂] [Module K V₂] {Q₁ : QuadraticForm K V₁}
    {Q₂ : QuadraticForm K V₂} (e : Q₁.IsometryEquiv Q₂)
    {P P' : ClassicalGroups.Orthogonal.HypPair Q₁} (h : P.Orth P') :
    (hypPairMap e P).Orth (hypPairMap e P') :=
  ⟨(polar_map_isometryEquiv _ _ _).trans h.ee, (polar_map_isometryEquiv _ _ _).trans h.ef,
    (polar_map_isometryEquiv _ _ _).trans h.fe, (polar_map_isometryEquiv _ _ _).trans h.ff⟩

open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed in
theorem index_orthogonalDerived_eq_four {K V : Type} [Field K] [Finite K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (h2 : (2 : K) ≠ 0) {Q : QuadraticForm K V}
    (hQ : Q.polarBilin.Nondegenerate) {P₁ P₂ P₃ : ClassicalGroups.Orthogonal.HypPair Q}
    (h₁₂ : P₁.Orth P₂) (h₁₃ : P₁.Orth P₃) (h₂₃ : P₂.Orth P₃) :
    (orthogonalDerived Q).index = 4 := by
  let : Invertible (2 : K) := invertibleOfNonzero h2
  obtain ⟨hO, -⟩ := ClassicalInvolution.orthogonalGroup_index_four hQ h₁₂ h₁₃ h₂₃
  have hE : Nat.card (orthogonalDerived Q) =
      Nat.card (ClassicalGroups.Orthogonal.elementaryGroup Q) := by
    rw [← ClassicalGroups.Orthogonal.commutator_orthogonalGroup_eq_elementaryGroup_of_two_ne_zero
      h2 hQ h₁₂ h₁₃ h₂₃, ← Subgroup.map_subtype_commutator]
    exact (Subgroup.card_map_of_injective (Subgroup.subtype_injective _)).symm
  have hmul := (orthogonalDerived Q).card_mul_index
  rw [hE, hO] at hmul
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun g : V ≃ₗ[K] V => g.toEquiv)
      (fun g h hgh => LinearEquiv.ext fun x => by simpa using congrArg (fun e : V ≃ V => e x) hgh)
  have hpos : 0 < Nat.card (ClassicalGroups.Orthogonal.elementaryGroup Q) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos (hmul.trans (Nat.mul_comm _ _))

open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed in
theorem card_fixed_dvd_onNormalCentralQuotient {X : Type*} [Group X] [Finite X]
    (N Z : Subgroup X) [N.Normal] [Z.Normal] (ψ : MulAut X) (hN : N.map ψ.toMonoidHom = N)
    (hZ : Z.map ψ.toMonoidHom = Z) :
    Nat.card (fixedSubgroup ψ) ∣
      N.index * (Nat.card (Z.subgroupOf N) *
        Nat.card (fixedSubgroup
          (onNormalCentralQuotient N Z ψ hN hZ))) := by
  have h1 := Subgroup.card_mul_index
    (N.subgroupOf (fixedSubgroup ψ))
  have h2 : (N.subgroupOf
      (fixedSubgroup ψ)).index ∣ N.index :=
    Subgroup.relIndex_dvd_index_of_normal N _
  have h3 := Nat.card_congr (fixedNormalEquiv N ψ hN).toEquiv
  have h4 := card_fixed_dvd_card_mul_onQuotient
    (Z.subgroupOf N) (restrictAutomorphism N ψ hN) (restricted_central_invariant N Z ψ hN hZ)
  rw [← h1, ← h3, mul_comm]
  exact Nat.mul_dvd_mul h2 h4

open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed in
theorem two_pow_dvd_card_fixed_orthogonal_quotient {K V : Type} [Field K] [Finite K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hidx : (orthogonalDerived Q).index = 4) (ψ : MulAut (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hN : (orthogonalDerived Q).map ψ.toMonoidHom = orthogonalDerived Q)
    (hZ : (scalarSigns Q).map ψ.toMonoidHom = scalarSigns Q) {n : ℕ}
    (h : 2 ^ (n + 3) ∣ Nat.card (fixedSubgroup ψ)) :
    2 ^ n ∣ Nat.card (fixedSubgroup
      (onNormalCentralQuotient (orthogonalDerived Q) (scalarSigns Q) ψ hN hZ)) := by
  have h1 := card_fixed_dvd_onNormalCentralQuotient (orthogonalDerived Q) (scalarSigns Q) ψ hN hZ
  have hle : Nat.card ((scalarSigns Q).subgroupOf (orthogonalDerived Q)) ≤
      Nat.card (scalarSigns Q) :=
    Nat.card_le_card_of_injective (fun x => (⟨(x : orthogonalDerived Q).val, x.2⟩ : scalarSigns Q))
      (fun a b hab => by
        have h' := congrArg (fun x : scalarSigns Q =>
          (x : TauCeti.QuadraticMap.orthogonalGroup Q)) hab
        exact Subtype.ext (Subtype.ext h'))
  have hZ2 : Nat.card ((scalarSigns Q).subgroupOf (orthogonalDerived Q)) ∣ 2 :=
    dvd_two_of_pos_of_le_two Nat.card_pos (hle.trans (card_scalarSigns_le_two Q))
  rw [hidx] at h1
  have h2 := h.trans (h1.trans (Nat.mul_dvd_mul_left 4 (Nat.mul_dvd_mul_right hZ2 _)))
  rw [show 2 ^ (n + 3) = 8 * 2 ^ n by ring, show 4 * (2 * Nat.card (fixedSubgroup
      (onNormalCentralQuotient (orthogonalDerived Q) (scalarSigns Q) ψ hN hZ))) =
      8 * Nat.card (fixedSubgroup
        (onNormalCentralQuotient (orthogonalDerived Q) (scalarSigns Q) ψ hN hZ)) by ring] at h2
  exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h2

open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed in
theorem two_pow_dvd_card_fixed_orthogonal_quotient_of_odd {K V : Type} [Field K] [Finite K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (h2 : (2 : K) ≠ 0)
    {Q : QuadraticForm K V} (hodd : Odd (Module.finrank K V))
    (hidx : (orthogonalDerived Q).index = 4) (ψ : MulAut (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hN : (orthogonalDerived Q).map ψ.toMonoidHom = orthogonalDerived Q)
    (hZ : (scalarSigns Q).map ψ.toMonoidHom = scalarSigns Q) {n : ℕ}
    (h : 2 ^ (n + 2) ∣ Nat.card (fixedSubgroup ψ)) :
    2 ^ n ∣ Nat.card (fixedSubgroup
      (onNormalCentralQuotient (orthogonalDerived Q) (scalarSigns Q) ψ hN hZ)) := by
  have h1 := card_fixed_dvd_onNormalCentralQuotient (orthogonalDerived Q) (scalarSigns Q) ψ hN hZ
  rw [hidx, card_scalarSigns_subgroupOf_orthogonalDerived_of_odd h2 Q hodd, one_mul] at h1
  have h3 := h.trans h1
  rw [show 2 ^ (n + 2) = 4 * 2 ^ n by ring] at h3
  exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h3

end Orthogonal

end CFSG.SeitzReduction.RankOne.ClTwoPart
