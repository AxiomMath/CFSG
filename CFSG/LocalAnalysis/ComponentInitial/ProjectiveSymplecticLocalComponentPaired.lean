module

public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveSymplecticLocalComponentSplit
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveUnitaryLocalComponentPaired
public import CFSG.LocalAnalysis.ComponentInitial.LinearPairedSymplectic

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ProjectiveSymplectic

open Module Matrix CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
  {B : LinearMap.BilinForm K V}

theorem exists_bilin_eq_of_pairing [Finite K] [FiniteDimensional K V] {W₁ W₂ : Submodule K V}
    (hpair : ∀ w ∈ W₂, (∀ v ∈ W₁, B w v = 0) → w = 0) (hdim : finrank K W₂ = finrank K W₁)
    (φ : W₁ →ₗ[K] K) : ∃ w ∈ W₂, ∀ v : W₁, B w v = φ v := by
  have : Finite W₂ := Module.finite_of_finite K
  have : Finite (W₁ →ₗ[K] K) := Module.finite_of_finite K
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : W₂ → (W₁ →ₗ[K] K), Ψ = fun w : W₂ => (B (w : V)).comp W₁.subtype :=
    ⟨_, rfl⟩
  have hΨapp : ∀ (w : W₂) (v : W₁), Ψ w v = B (w : V) (v : V) := fun w v => by rw [hΨ]; rfl
  have hinj : Function.Injective Ψ := by
    intro w w' hww'
    have h1 : ∀ v ∈ W₁, B ((w : V) - w') v = 0 := fun v hv => by
      have := congrArg (fun φ : W₁ →ₗ[K] K => φ ⟨v, hv⟩) hww'
      simp only [hΨapp] at this
      rw [map_sub, LinearMap.sub_apply, this, sub_self]
    exact Subtype.ext (sub_eq_zero.mp (hpair _ (sub_mem w.2 w'.2) h1))
  have hcard : Nat.card W₂ = Nat.card (W₁ →ₗ[K] K) := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := W₂),
      Module.natCard_eq_pow_finrank (K := K) (V := W₁ →ₗ[K] K), Subspace.dual_finrank_eq,
      hdim]
  obtain ⟨w, hw⟩ := ((Nat.bijective_iff_injective_and_card Ψ).mpr ⟨hinj, hcard⟩).2 φ
  exact ⟨w, w.2, fun v => by rw [← hΨapp, hw]⟩

section Frame

variable {m : ℕ} {b d : Fin m → V}

theorem bilin_left_sum (hbb : ∀ i j, B (b i) (b j) = 0)
    (hbd : ∀ i j, B (b i) (d j) = if i = j then 1 else 0) (c : Fin m ⊕ Fin m → K) (i : Fin m) :
    B (b i) (∑ a, c a • Sum.elim b d a) = c (Sum.inr i) := by
  simp [map_sum, Fintype.sum_sum_type, hbb, hbd]

theorem bilin_right_sum (hdd : ∀ i j, B (d i) (d j) = 0)
    (hdb : ∀ i j, B (d i) (b j) = -(if i = j then 1 else 0)) (c : Fin m ⊕ Fin m → K)
    (i : Fin m) : B (d i) (∑ a, c a • Sum.elim b d a) = -c (Sum.inl i) := by
  simp [map_sum, Fintype.sum_sum_type, hdd, hdb]

theorem linearIndependent_sumElim' (hbb : ∀ i j, B (b i) (b j) = 0)
    (hdd : ∀ i j, B (d i) (d j) = 0) (hbd : ∀ i j, B (b i) (d j) = if i = j then 1 else 0)
    (hdb : ∀ i j, B (d i) (b j) = -(if i = j then 1 else 0)) :
    LinearIndependent K (Sum.elim b d) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc a
  rcases a with i | i
  · have h1 := bilin_right_sum hdd hdb c i
    rw [hc, map_zero] at h1
    exact neg_eq_zero.mp h1.symm
  · rw [← bilin_left_sum hbb hbd c i, hc, map_zero]

variable {bV : Basis (Fin m ⊕ Fin m) K V}

theorem repr_inl' (hdd : ∀ i j, B (d i) (d j) = 0)
    (hdb : ∀ i j, B (d i) (b j) = -(if i = j then 1 else 0)) (hbV : ⇑bV = Sum.elim b d) (v : V)
    (i : Fin m) : bV.repr v (Sum.inl i) = -B (d i) v := by
  have h1 := bilin_right_sum hdd hdb (bV.repr v) i
  rw [← hbV, bV.sum_repr] at h1
  rw [h1, neg_neg]

theorem repr_inr' (hbb : ∀ i j, B (b i) (b j) = 0)
    (hbd : ∀ i j, B (b i) (d j) = if i = j then 1 else 0) (hbV : ⇑bV = Sum.elim b d) (v : V)
    (i : Fin m) : bV.repr v (Sum.inr i) = B (b i) v := by
  have h1 := bilin_left_sum hbb hbd (bV.repr v) i
  rw [← hbV, bV.sum_repr] at h1
  exact h1.symm

theorem pairedSympForm_eq_bilin (hbb : ∀ i j, B (b i) (b j) = 0)
    (hdd : ∀ i j, B (d i) (d j) = 0) (hbd : ∀ i j, B (b i) (d j) = if i = j then 1 else 0)
    (hdb : ∀ i j, B (d i) (b j) = -(if i = j then 1 else 0)) (hbV : ⇑bV = Sum.elim b d)
    (u v : Fin m ⊕ Fin m → K) :
    pairedSympForm K m u v = B (bV.equivFun.symm u) (bV.equivFun.symm v) := by
  have key : ∀ (x : Fin m ⊕ Fin m → K) (w : V), B (∑ a, x a • Sum.elim b d a) w =
      ∑ i, (x (Sum.inl i) * B (b i) w + x (Sum.inr i) * B (d i) w) := by
    intro x w
    rw [map_sum, LinearMap.sum_apply, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply, Sum.elim_inl,
      Sum.elim_inr, smul_eq_mul, smul_eq_mul]
  rw [pairedSympForm_apply, Basis.equivFun_symm_apply, Basis.equivFun_symm_apply, hbV, key,
    dotProduct, dotProduct, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [bilin_left_sum hbb hbd, bilin_right_sum hdd hdb, Function.comp_apply, Function.comp_apply,
    Function.comp_apply, Function.comp_apply]
  ring

theorem frameMatrix_mem_pairedSymplecticGroup (hbb : ∀ i j, B (b i) (b j) = 0)
    (hdd : ∀ i j, B (d i) (d j) = 0) (hbd : ∀ i j, B (b i) (d j) = if i = j then 1 else 0)
    (hdb : ∀ i j, B (d i) (b j) = -(if i = j then 1 else 0)) (hbV : ⇑bV = Sum.elim b d)
    {g : LinearMap.GeneralLinearGroup K V} (hg : g ∈ sesqUnitaryGroup B) :
    frameMatrix bV g ∈ pairedSymplecticGroup K m := by
  rw [mem_pairedSymplecticGroup]
  intro u v
  rw [frameMatrix_coe, toMatrix_mulVec_eq, toMatrix_mulVec_eq,
    pairedSympForm_eq_bilin hbb hdd hbd hdb hbV, pairedSympForm_eq_bilin hbb hdd hbd hdb hbV,
    LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, hg]

end Frame

theorem transpose_mul_eq_one_of_fromBlocks {m : ℕ} {X Y : Matrix (Fin m) (Fin m) K}
    (hXY : ∀ u v, pairedSympForm K m (fromBlocks X 0 0 Y *ᵥ u) (fromBlocks X 0 0 Y *ᵥ v) =
      pairedSympForm K m u v) :
    Xᵀ * Y = 1 := by
  ext i j
  have h1 := hXY (Pi.single (Sum.inl i) 1) (Pi.single (Sum.inr j) 1)
  rw [pairedSympForm_fromBlocks] at h1
  simp [pairedSympForm_apply, dotProduct, Pi.single_apply, Matrix.mulVec] at h1
  rw [Matrix.one_apply]
  rw [h1]
  exact if_congr eq_comm rfl rfl

theorem paired_case {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) [FiniteDimensional K V] {r : ℕ} (hr : 1 ≤ r)
    (hdim : finrank K V = 2 * r) (hB : B.IsAlt) (hBnd : B.Nondegenerate)
    {T : sesqUnitaryGroup B} (hTns : ∀ c : K, spOp T ≠ c • 1)
    (hTT : spOp T * spOp T = (-1 : K) • 1) {l : K} (hl : l ^ 2 = -1)
    {L : Subgroup (Subgroup.centralizer {T})} (hL : CFSG.IsComponent L)
    {R : Subgroup (sesqUnitaryGroup B)}
    (hR : R ≤ Subgroup.centralizer ((L.map (Subgroup.centralizer {T}).subtype :
      Subgroup (sesqUnitaryGroup B)) : Set (sesqUnitaryGroup B)))
    (hRp : ⁅R, R⁆ = R) : R = ⊥ := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have hchar : CharP K ℓ := finite_field_prime_power_characteristic hℓ hf hK
  have hk : ringChar K ≠ 2 := by
    rw [ringChar.eq K ℓ]
    exact hℓ2
  obtain ⟨hε, hsq, -⟩ := odd_symplectic_scalar_square_centralizer_structure hℓ hℓ2 hf hK hr
    hdim hB hBnd (A := (T : LinearMap.GeneralLinearGroup K V)) hTns
    (neg_ne_zero.mpr one_ne_zero) hTT (μ := 1)
    (fun v w => by rw [one_mul]; exact mem_sesqUnitaryGroup.mp T.2 v w)
  obtain ⟨-, -, -, hneg⟩ := hsq l hl
  obtain ⟨hisoP, hisoM, hdimP, hdimM, -, hpairMP, e, he, -⟩ := hneg (by rw [div_neg, div_one])
  obtain ⟨b⟩ : Nonempty (Basis (Fin r) K (eigenPlus l (spOp T))) :=
    ⟨Module.finBasisOfFinrankEq K _ hdimP⟩
  obtain ⟨F, hF⟩ : ∃ F : Subgroup.centralizer {T} ≃* GL (Fin r) K,
      F = (centralizerSimEquiv T).trans
        (e.trans (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv)) := ⟨_, rfl⟩
  have hFapp : ∀ (x : Subgroup.centralizer {T}) (i j : Fin r),
      ((F x : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) i j =
        b.repr (((e (centralizerSimEquiv T x) :
          LinearMap.GeneralLinearGroup K (eigenPlus l (spOp T))) :
            Module.End K (eigenPlus l (spOp T))) (b j)) i := by
    intro x i j
    rw [hF]
    exact LinearMap.toMatrixAlgEquiv_apply b _ i j
  have hL' : CFSG.IsComponent (L.map F.toMonoidHom) := isComponent_map_of_isComponent F hL
  have : Group.IsPerfect (L.map F.toMonoidHom) := hL'.1.1
  have : Nontrivial (L.map F.toMonoidHom) := CFSG.LocalCores.isQuasisimple_nontrivial hL'.1
  obtain ⟨hm2, hSL⟩ : 2 ≤ r ∧
      L.map F.toMonoidHom = CatalogueBGeneralLinear.specialLinearRange r K := by
    by_cases hs : r = 1 ∨ r = 2 ∧ (Nat.card K = 2 ∨ Nat.card K = 3)
    · exfalso
      have : Group.IsSolvable (GL (Fin r) K) :=
        CatalogueBGeneralLinear.generalLinear_small_solvable r K hs
      exact Group.IsPerfect.not_isSolvable (L.map F.toMonoidHom) inferInstance
    · obtain ⟨hm2, h22, h23⟩ := CatalogueBGeneralLinear.retained_parameters r K hr hs
      exact ⟨hm2, CatalogueBGeneralLinear.perfect_subnormal_eq_specialLinearRange r K hm2 h22
        h23 _ hL'.2⟩
  have hpair : ∀ w ∈ eigenMinus l (spOp T),
      (∀ v ∈ eigenPlus l (spOp T), B w v = 0) → w = 0 := fun w hw h0 =>
    hpairMP w hw fun v hv => by rw [← hB.neg_eq w v, h0 v hv, neg_zero]
  have hex : ∀ j : Fin r, ∃ w ∈ eigenMinus l (spOp T),
      ∀ v : eigenPlus l (spOp T), B w v = (-b.coord j) v := fun j =>
    exists_bilin_eq_of_pairing hpair (hdimM.trans hdimP.symm) (-b.coord j)
  choose d hdM hdB using hex
  have hbb : ∀ i j, B (b i : V) (b j : V) = 0 := fun i j => hisoP _ (b i).2 _ (b j).2
  have hdd : ∀ i j, B (d i) (d j) = 0 := fun i j => hisoM _ (hdM i) _ (hdM j)
  have hdb : ∀ i j, B (d i) (b j : V) = -(if i = j then 1 else 0) := fun i j => by
    rw [hdB i (b j), LinearMap.neg_apply, Basis.coord_apply, Basis.repr_self,
      Finsupp.single_apply]
    exact congrArg Neg.neg (if_congr eq_comm rfl rfl)
  have hbd : ∀ i j, B (b i : V) (d j) = if i = j then 1 else 0 := fun i j => by
    rw [← hB.neg_eq, hdb j i, neg_neg]
    exact if_congr eq_comm rfl rfl
  obtain ⟨bV, hbV⟩ : ∃ bV : Basis (Fin r ⊕ Fin r) K V,
      ⇑bV = Sum.elim (fun i => (b i : V)) d :=
    ⟨basisOfLinearIndependentOfCardEqFinrank' _
      (linearIndependent_sumElim' (b := fun i => (b i : V)) hbb hdd hbd hdb)
      (by rw [Fintype.card_sum, Fintype.card_fin, hdim]; ring),
      coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _⟩
  have hψS : ∀ g : sesqUnitaryGroup B,
      frameMatrix bV (g : LinearMap.GeneralLinearGroup K V) ∈ pairedSymplecticGroup K r :=
    fun g => frameMatrix_mem_pairedSymplecticGroup (b := fun i => (b i : V)) hbb hdd hbd hdb hbV
      g.2
  have hcover : ∀ M : SpecialLinearGroup (Fin r) K, ∃ x ∈ L,
      frameMatrix bV ((x : sesqUnitaryGroup B) : LinearMap.GeneralLinearGroup K V) =
        pairedSLHom (RingHom.id K) r M := by
    intro M
    have hM : SpecialLinearGroup.toGL M ∈ L.map F.toMonoidHom := by
      rw [hSL]
      exact ⟨M, rfl⟩
    obtain ⟨x, hx, hxM⟩ := hM
    have hxM' : F x = SpecialLinearGroup.toGL M := hxM
    refine ⟨x, hx, ?_⟩
    obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K,
        P = ((frameMatrix bV ((x : sesqUnitaryGroup B) : LinearMap.GeneralLinearGroup K V) :
          GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := ⟨_, rfl⟩
    have hPe : ∀ a c, P a c = bV.repr (spOp (x : sesqUnitaryGroup B) (bV c)) a :=
      fun a c => by rw [hP, frameMatrix_coe, LinearMap.toMatrix_apply]
    have h11 : P.toBlocks₁₁ = (M : Matrix (Fin r) (Fin r) K) := by
      ext i j
      change P (Sum.inl i) (Sum.inl j) = _
      rw [hPe, hbV, Sum.elim_inl, repr_inl' (b := fun i => (b i : V)) hdd hdb hbV]
      have h2 : ((((e (centralizerSimEquiv T x) :
          LinearMap.GeneralLinearGroup K (eigenPlus l (spOp T))) :
            Module.End K (eigenPlus l (spOp T))) (b j) : eigenPlus l (spOp T)) : V) =
          spOp (x : sesqUnitaryGroup B) (b j) :=
        LinearMap.congr_fun (he (centralizerSimEquiv T x)) (b j)
      rw [← h2, hdB, LinearMap.neg_apply, Basis.coord_apply, neg_neg, ← hFapp, hxM']
      rfl
    have h12 : P.toBlocks₁₂ = 0 := by
      ext i j
      change P (Sum.inl i) (Sum.inr j) = 0
      rw [hPe, hbV, Sum.elim_inr, repr_inl' (b := fun i => (b i : V)) hdd hdb hbV, neg_eq_zero]
      exact hisoM _ (hdM i) _ (mapsTo_eigenMinus_of_mem l (centralizerSimEquiv T x).2 (hdM j))
    have h21 : P.toBlocks₂₁ = 0 := by
      ext i j
      change P (Sum.inr i) (Sum.inl j) = 0
      rw [hPe, hbV, Sum.elim_inl, repr_inr' (b := fun i => (b i : V)) hbb hbd hbV]
      exact hisoP _ (b i).2 _ (mapsTo_eigenPlus_of_mem l (centralizerSimEquiv T x).2 (b j).2)
    have hblocks : fromBlocks (M : Matrix (Fin r) (Fin r) K) 0 0 P.toBlocks₂₂ = P := by
      calc fromBlocks (M : Matrix (Fin r) (Fin r) K) 0 0 P.toBlocks₂₂ =
          fromBlocks P.toBlocks₁₁ P.toBlocks₁₂ P.toBlocks₂₁ P.toBlocks₂₂ := by
            rw [h11, h12, h21]
        _ = P := fromBlocks_toBlocks P
    have hPS : ∀ u v, pairedSympForm K r
        (fromBlocks (M : Matrix (Fin r) (Fin r) K) 0 0 P.toBlocks₂₂ *ᵥ u)
        (fromBlocks (M : Matrix (Fin r) (Fin r) K) 0 0 P.toBlocks₂₂ *ᵥ v) =
          pairedSympForm K r u v := by
      rw [hblocks, hP]
      exact mem_pairedSymplecticGroup.mp (hψS x)
    have hSLS := pairedSLHom_range_le_pairedSymplecticGroup (k := K) (m := r) ⟨M, rfl⟩
    rw [mem_pairedSymplecticGroup, pairedSLHom_id_coe] at hSLS
    have h22 : P.toBlocks₂₂ =
        (((M⁻¹ : SpecialLinearGroup (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ) :=
      (Matrix.inv_eq_right_inv (transpose_mul_eq_one_of_fromBlocks hPS)).symm.trans
        (Matrix.inv_eq_right_inv (transpose_mul_eq_one_of_fromBlocks hSLS))
    apply Units.ext
    rw [← hP, ← hblocks, h22, pairedSLHom_id_coe]
  obtain ⟨-, hsolv, -⟩ := paired_symplectic_special_linear_centralizer_solvable hk hm2
  have hRcent : ∀ r' ∈ R, (⟨frameMatrix bV (r' : LinearMap.GeneralLinearGroup K V), hψS r'⟩ :
      pairedSymplecticGroup K r) ∈ Subgroup.centralizer
        (((pairedSLHom (RingHom.id K) r).range.subgroupOf (pairedSymplecticGroup K r)) :
          Set (pairedSymplecticGroup K r)) := by
    intro r' hr'
    rw [Subgroup.mem_centralizer_iff]
    rintro ⟨y, hyS⟩ hy
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hy
    obtain ⟨M, rfl⟩ := hy
    obtain ⟨x, hx, hxM⟩ := hcover M
    have hxr := Subgroup.mem_centralizer_iff.mp (hR hr') _ (Subgroup.mem_map_of_mem _ hx)
    apply Subtype.ext
    change pairedSLHom (RingHom.id K) r M * frameMatrix bV (r' : LinearMap.GeneralLinearGroup K V) =
      frameMatrix bV (r' : LinearMap.GeneralLinearGroup K V) * pairedSLHom (RingHom.id K) r M
    rw [← hxM, ← map_mul, ← map_mul]
    exact congrArg (fun z : sesqUnitaryGroup B => frameMatrix bV
      (z : LinearMap.GeneralLinearGroup K V)) hxr
  let ι : R →* Subgroup.centralizer
      (((pairedSLHom (RingHom.id K) r).range.subgroupOf (pairedSymplecticGroup K r)) :
        Set (pairedSymplecticGroup K r)) :=
    { toFun := fun r' => ⟨_, hRcent r' r'.2⟩
      map_one' := Subtype.ext (Subtype.ext (map_one (frameMatrix bV)))
      map_mul' := fun r₁ r₂ => Subtype.ext (Subtype.ext (map_mul (frameMatrix bV) _ _)) }
  have hι : Function.Injective ι := fun r₁ r₂ h12 =>
    Subtype.ext (Subtype.ext ((frameMatrix bV).injective
      (congrArg Subtype.val (congrArg Subtype.val h12))))
  have : Group.IsSolvable R := Group.isSolvable_of_isSolvable_injective hι
  by_contra hne
  have : Nontrivial R := (Subgroup.nontrivial_iff_ne_bot R).mpr hne
  have : Group.IsPerfect R := Subgroup.isPerfect_iff.mpr hRp
  exact Group.IsPerfect.not_isSolvable R inferInstance

end CFSG.LocalAnalysis.ComponentInitial.ProjectiveSymplectic
