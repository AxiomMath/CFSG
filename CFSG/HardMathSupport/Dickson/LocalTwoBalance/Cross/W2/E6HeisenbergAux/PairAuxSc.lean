module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeToralityProof

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis.PairAux

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.CentralExt.MinusculeClosed
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartOne.KE
open CFSG.LieType.Steinberg.Minuscule.MinData (toWeight reflectWeight)

attribute [local instance] CFSG.HardMathSupport.Timmesfeld.CrossChar.e6ScLiftNeZeroRank


theorem e6WtEval_zsmul {K : Type} [Field K] (u : Fin Tag.E6.rank → Kˣ) (c : ℤ)
    (μ : Fin Tag.E6.rank → ℤ) : e6WtEval u (c • μ) = e6WtEval u μ ^ c := by
  rw [e6WtEval, e6WtEval, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, ← zpow_mul, mul_comm]

theorem e6WtEval_single {K : Type} [Field K] (u : Fin Tag.E6.rank → Kˣ) (i : Fin Tag.E6.rank) :
    e6WtEval u (Pi.single i 1) = u i := by
  rw [e6WtEval, Finset.prod_eq_single i (fun l _ hl => by rw [Pi.single_eq_of_ne hl, zpow_zero])
    (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same, zpow_one]

@[expose] def e6WtCoeff : Fin Tag.E6.rank → ℤ := ![1, 0, 2, 0, 1, 2]

@[expose] def e6WtRoot : Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ :=
  ![![0, 0, 0, 0, 0, 0], ![1, 2, 2, 3, 2, 1], ![-1, 0, 0, 0, 0, 0], ![2, 3, 4, 6, 4, 2],
    ![0, 1, 1, 2, 2, 1], ![-2, -1, -2, -2, -1, 0]]

theorem single_eq_e6WtCoeff : ∀ i : Fin Tag.E6.rank,
    (Pi.single i 1 : Fin Tag.E6.rank → ℤ) =
      e6WtCoeff i • Pi.single 0 1 + toWeight (τ := Tag.E6) (e6WtRoot i) := by
  decide +kernel

theorem eq_of_e6RootParams_eq_of_wtEval {K : Type} [Field K] {u v : Fin Tag.E6.rank → Kˣ}
    (hc : e6RootParams v = e6RootParams u)
    (h0 : e6WtEval v (Pi.single 0 1) = e6WtEval u (Pi.single 0 1)) : v = u := by
  funext i
  rw [← e6WtEval_single v i, ← e6WtEval_single u i, single_eq_e6WtCoeff i, e6WtEval_add,
    e6WtEval_add, e6WtEval_zsmul, e6WtEval_zsmul, h0, e6WtEval_toWeight, e6WtEval_toWeight, hc]

theorem rootChar_e6Shift_inv_eq_one {K : Type} [Field K] {a : Fin Tag.E6.rank → Kˣ}
    {w : WeylGroup Tag.E6} (hw : w ∈ rootCharStabilizer a) (h1 : rootChar a (e6Shift w) = 1) :
    rootChar a (e6Shift w⁻¹) = 1 := by
  have hcoc := e6Shift_mul w⁻¹ w
  rw [inv_mul_cancel, e6Shift_one] at hcoc
  have e1 : rootChar a (w⁻¹ • e6Shift w) = 1 := by
    have h := hw (w⁻¹ • e6Shift w)
    rw [smul_inv_smul] at h
    rw [← h, h1]
  have e2 := rootChar_add a (w⁻¹ • e6Shift w) (e6Shift w⁻¹)
  rw [← hcoc, rootChar_zero, e1, one_mul] at e2
  exact e2.symm

theorem e6Sc_commute_of_shift_eq_one {k : Type} [Field k] [Finite k]
    {x y : e6Data_valid.minGroup k} {a b : Fin Tag.E6.rank → kˣ} {w : WeylGroup Tag.E6}
    (hx : ((e6Isogeny k x : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) = rootDiagUnit Tag.E6 a)
    (hy : ((e6Isogeny k y : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) =
      rootDiagUnit Tag.E6 b * canonicalRep (coxeterSystem Tag.E6) k w)
    {u u' : Fin Tag.E6.rank → kˣ} (hu : e6RootParams u = a) (hu' : e6RootParams u' = b)
    (hw : w ∈ rootCharStabilizer a) (h1 : rootChar a (e6Shift w) = 1) :
    x * y = y * x := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem Tag.E6).exists_isReduced w
  obtain ⟨T, hT⟩ : ∃ T, T = minTorus e6Data_valid k u := ⟨_, rfl⟩
  obtain ⟨T', hT'⟩ : ∃ T', T' = minTorus e6Data_valid k u' := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N, N = e6NWord k ω := ⟨_, rfl⟩
  have hker : ∀ g g' : e6Data_valid.minGroup k,
      ((e6Isogeny k g : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) =
        ((e6Isogeny k g' : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) →
      g'⁻¹ * g ∈ Subgroup.center (e6Data_valid.minGroup k) := by
    intro g g' hgg'
    refine ker_e6IsogenyT_le_center k ?_
    rw [MonoidHom.mem_ker]
    change e6Isogeny k (g'⁻¹ * g) = 1
    rw [map_mul, map_inv, inv_mul_eq_one]
    exact Subtype.ext hgg'.symm
  have hπT : ((e6Isogeny k T : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) =
      rootDiagUnit Tag.E6 a := by
    rw [hT, e6Isogeny_minTorus, hu]
  have hπN : ((e6Isogeny k N : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) =
      canonicalRep (coxeterSystem Tag.E6) k ((coxeterSystem Tag.E6).wordProd ω) := by
    rw [hN, e6Isogeny_nWord_eq_canonicalRep hω]
  have hxT : T⁻¹ * x ∈ Subgroup.center (e6Data_valid.minGroup k) := hker x T (by rw [hx, hπT])
  have hyS : (T' * N)⁻¹ * y ∈ Subgroup.center (e6Data_valid.minGroup k) :=
    hker y (T' * N) (by rw [hy, map_mul, Subgroup.coe_mul, hπN, hT', e6Isogeny_minTorus, hu'])
  have hfix : ω.foldr e6StarS u = u := by
    refine eq_of_e6RootParams_eq_of_wtEval ?_ ?_
    · apply CFSG.LieType.Chevalley.rootDiagUnit_injective (K := k)
      rw [hu, ← e6Isogeny_minTorus (ω.foldr e6StarS u), ← nWord_conj_minTorus k ω u, ← hN, ← hT]
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hπN, hπT]
      have h := (conj_canonicalRep_eq_iff a ((coxeterSystem Tag.E6).wordProd ω)).2 hw
      rw [mul_inv_eq_iff_eq_mul] at h ⊢
      exact h.symm
    · rw [e6WtEval_foldr]
      have e := toWeight_e6Shift_inv ω
      rw [eq_sub_iff_add_eq] at e
      rw [← e, e6WtEval_add, e6WtEval_toWeight, hu, rootChar_e6Shift_inv_eq_one hw h1, one_mul]
  have hNT : N * T = T * N := by
    have h2 : N * T * N⁻¹ = T := by rw [hN, hT, nWord_conj_minTorus, hfix]
    calc N * T = N * T * N⁻¹ * N := by group
      _ = T * N := by rw [h2]
  have hTT' : T * T' = T' * T := by rw [hT, hT', ← map_mul, ← map_mul, mul_comm]
  have hTS : T * (T' * N) = (T' * N) * T := by
    calc T * (T' * N) = T' * (T * N) := by rw [← mul_assoc, hTT', mul_assoc]
      _ = T' * (N * T) := by rw [hNT]
      _ = (T' * N) * T := by group
  obtain ⟨z₁, hz₁⟩ : ∃ z, z = T⁻¹ * x := ⟨_, rfl⟩
  obtain ⟨z₂, hz₂⟩ : ∃ z, z = (T' * N)⁻¹ * y := ⟨_, rfl⟩
  rw [← hz₁] at hxT
  rw [← hz₂] at hyS
  have hz1 := Subgroup.mem_center_iff.1 hxT
  have hz2 := Subgroup.mem_center_iff.1 hyS
  have ex : x = T * z₁ := by rw [hz₁]; group
  have ey : y = (T' * N) * z₂ := by rw [hz₂]; group
  rw [ex, ey]
  calc T * z₁ * (T' * N * z₂) = T * ((T' * N) * z₁) * z₂ := by rw [hz1 (T' * N)]; group
    _ = (T * (T' * N)) * (z₁ * z₂) := by group
    _ = ((T' * N) * T) * (z₁ * z₂) := by rw [hTS]
    _ = ((T' * N) * T) * (z₂ * z₁) := by rw [hz1 z₂]
    _ = (T' * N) * (T * z₂) * z₁ := by group
    _ = T' * N * z₂ * (T * z₁) := by rw [hz2 T]; group

theorem minEndBC_injective {d : ℕ} {k k' : Type*} [Field k] [Field k'] (ι : k →+* k') :
    Function.Injective (minEndBC (d := d) ι) := by
  intro A B h
  refine minEnd_ext fun b => Finsupp.ext fun c => ?_
  have h1 := congrArg (fun f : Module.End k' (Fin d →₀ k') => f (Finsupp.single b 1) c) h
  simp only [minEndBC_single, Finsupp.mapRange_apply] at h1
  exact ι.injective h1

theorem minBC_injective {τ : Tag} {D : MinData τ} (hV : D.Valid) {k k' : Type*} [Field k]
    [Field k'] (ι : k →+* k') : Function.Injective (minBC hV ι) := by
  intro g h e
  apply Subtype.ext
  apply Units.ext
  apply minEndBC_injective ι
  exact congrArg (fun x : hV.minGroup k' => ((x : (Module.End k' (Fin D.d →₀ k'))ˣ) :
    Module.End k' (Fin D.d →₀ k'))) e

theorem commute_of_rootChar_e6Shift_eq_one {K : Type} [Field K] [Finite K] {K₁ : Type}
    [Field K₁] [Finite K₁] (ι : K₁ →+* AlgebraicClosure K) {s t : e6Data_valid.minGroup K₁}
    {c : ModGL Tag.E6 (AlgebraicClosure K)} (hc : c ∈ adjointGroup Tag.E6 (AlgebraicClosure K))
    {a b : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ} {w : WeylGroup Tag.E6}
    (ha : c * e6ScToBar K₁ ι s * c⁻¹ = rootDiagUnit Tag.E6 a)
    (hb : c * e6ScToBar K₁ ι t * c⁻¹ =
      rootDiagUnit Tag.E6 b * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) w)
    (hw : w ∈ rootCharStabilizer a) (h1 : rootChar a (e6Shift w) = 1) :
    s * t = t * s := by
  classical
  obtain ⟨u, hu⟩ := exists_e6RootParams_eq a
  obtain ⟨u', hu'⟩ := exists_e6RootParams_eq b
  obtain ⟨Ec, hEc⟩ := exists_finset_descent hc
  obtain ⟨Ev, hEv⟩ : ∃ Ev : Finset (AlgebraicClosure K), ∀ i,
      (u i : AlgebraicClosure K) ∈ Ev ∧ (u' i : AlgebraicClosure K) ∈ Ev ∧
        (a i : AlgebraicClosure K) ∈ Ev ∧ (b i : AlgebraicClosure K) ∈ Ev :=
    ⟨(Finset.univ.image fun i => ((u i : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)) ∪
      (Finset.univ.image fun i => ((u' i : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)) ∪
      (Finset.univ.image fun i => ((a i : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)) ∪
      (Finset.univ.image fun i => ((b i : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)),
      fun i => by simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
        exists_apply_eq_apply, or_true, true_or, and_self]⟩
  obtain ⟨K₃, hK₃, hEK₃, -⟩ := exists_finite_subfield_of_finset (K := K)
    (Ec ∪ Ev ∪ (Set.finite_range ι).toFinset)
  have hmem : ∀ x ∈ Ec ∪ Ev ∪ (Set.finite_range ι).toFinset, x ∈ K₃ :=
    fun x hx => hEK₃ (Finset.mem_coe.2 hx)
  have hcK : (Ec : Set (AlgebraicClosure K)) ⊆ K₃ := fun x hx =>
    hmem x (Finset.mem_union_left _ (Finset.mem_union_left _ hx))
  have hvK : ∀ x ∈ Ev, x ∈ K₃ := fun x hx =>
    hmem x (Finset.mem_union_left _ (Finset.mem_union_right _ hx))
  have hιK : ∀ x, ι x ∈ K₃ := fun x => hmem _ (Finset.mem_union_right _
    ((Set.finite_range ι).mem_toFinset.2 ⟨x, rfl⟩))
  obtain ⟨u₃, hu₃⟩ := exists_units_descent K₃ u fun i => hvK _ (hEv i).1
  obtain ⟨u'₃, hu'₃⟩ := exists_units_descent K₃ u' fun i => hvK _ (hEv i).2.1
  obtain ⟨a₃, ha₃⟩ := exists_units_descent K₃ a fun i => hvK _ (hEv i).2.2.1
  obtain ⟨b₃, hb₃⟩ := exists_units_descent K₃ b fun i => hvK _ (hEv i).2.2.2
  have : Finite K₃ := hK₃
  obtain ⟨ι₃, hιι⟩ : ∃ ι₃ : K₁ →+* K₃, K₃.subtype.comp ι₃ = ι :=
    ⟨ι.codRestrict K₃ hιK, RingHom.ext fun x => rfl⟩
  obtain ⟨c₃, hc₃C, hc₃⟩ := hEc K₃ hcK
  obtain ⟨bc, hbc⟩ : ∃ f : ModGL Tag.E6 K₃ →* ModGL Tag.E6 (AlgebraicClosure K),
      f = baseChangeGL K₃.subtype := ⟨_, rfl⟩
  have hbcinj : Function.Injective bc := hbc ▸ baseChangeGL_injective K₃.subtype
  have hc₃' : bc c₃ = c := by rw [hbc]; exact hc₃
  have hpar : ∀ (v : Fin Tag.E6.rank → K₃ˣ) (v' : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ),
      (fun i => Units.map K₃.subtype.toMonoidHom (v i)) = v' → ∀ j,
      Units.map K₃.subtype.toMonoidHom (e6RootParams v j) = e6RootParams v' j := by
    intro v v' hv j
    rw [← hv]
    simp only [e6RootParams, map_prod, map_zpow]
  have hu₃a : e6RootParams u₃ = a₃ := by
    funext j
    apply units_map_subtype_injective K₃
    rw [hpar u₃ u hu₃ j, hu, ← congrFun ha₃ j]
  have hu'₃b : e6RootParams u'₃ = b₃ := by
    funext j
    apply units_map_subtype_injective K₃
    rw [hpar u'₃ u' hu'₃ j, hu', ← congrFun hb₃ j]
  have hda : bc (rootDiagUnit Tag.E6 a₃) = rootDiagUnit Tag.E6 a := by
    rw [hbc, baseChangeGL_rootDiagUnit, ha₃]
  have hdb : bc (rootDiagUnit Tag.E6 b₃) = rootDiagUnit Tag.E6 b := by
    rw [hbc, baseChangeGL_rootDiagUnit, hb₃]
  have hdw : bc (canonicalRep (coxeterSystem Tag.E6) K₃ w) =
      canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) w := by
    rw [hbc, baseChangeGL_canonicalRep]
  obtain ⟨cS, hcS⟩ := e6Isogeny_surjective K₃ ⟨c₃, hc₃C⟩
  obtain ⟨π₃, hπ₃⟩ : ∃ π : e6Data_valid.minGroup K₃ →* ModGL Tag.E6 K₃,
      π = (adjointGroup Tag.E6 K₃).subtype.comp (e6Isogeny K₃) := ⟨_, rfl⟩
  have hπc : π₃ cS = c₃ := by rw [hπ₃, MonoidHom.comp_apply, hcS]; rfl
  have hbcπ : ∀ g : e6Data_valid.minGroup K₁,
      bc (π₃ (minBC e6Data_valid ι₃ g)) = e6ScToBar K₁ ι g := by
    intro g
    rw [hπ₃, MonoidHom.comp_apply, Subgroup.coe_subtype, e6Isogeny_minBC, hbc,
      baseChangeGL_baseChangeGL, hιι]
    rfl
  obtain ⟨xS, hxS⟩ : ∃ x, x = cS * minBC e6Data_valid ι₃ s * cS⁻¹ := ⟨_, rfl⟩
  obtain ⟨yS, hyS⟩ : ∃ y, y = cS * minBC e6Data_valid ι₃ t * cS⁻¹ := ⟨_, rfl⟩
  have hxSπ : π₃ xS = rootDiagUnit Tag.E6 a₃ := by
    apply hbcinj
    rw [hda, ← ha, hxS]
    simp only [map_mul, map_inv, hbcπ, hπc, hc₃']
  have hySπ : π₃ yS = rootDiagUnit Tag.E6 b₃ * canonicalRep (coxeterSystem Tag.E6) K₃ w := by
    apply hbcinj
    rw [map_mul bc, hdb, hdw, ← hb, hyS]
    simp only [map_mul, map_inv, hbcπ, hπc, hc₃']
  have hw₃ : w ∈ rootCharStabilizer a₃ := by
    intro v
    apply units_map_subtype_injective K₃
    have e1 := rootChar_map_tuple K₃.subtype a₃ (w • v)
    have e2 := rootChar_map_tuple K₃.subtype a₃ v
    rw [ha₃] at e1 e2
    rw [← e1, ← e2]
    exact hw v
  have h1₃ : rootChar a₃ (e6Shift w) = 1 := by
    apply units_map_subtype_injective K₃
    have e3 := rootChar_map_tuple K₃.subtype a₃ (e6Shift w)
    rw [ha₃, h1] at e3
    rw [← e3, map_one]
  have hx' : ((e6Isogeny K₃ xS : adjointGroup Tag.E6 K₃) : ModGL Tag.E6 K₃) =
      rootDiagUnit Tag.E6 a₃ := by
    rw [← hxSπ, hπ₃]
    rfl
  have hy' : ((e6Isogeny K₃ yS : adjointGroup Tag.E6 K₃) : ModGL Tag.E6 K₃) =
      rootDiagUnit Tag.E6 b₃ * canonicalRep (coxeterSystem Tag.E6) K₃ w := by
    rw [← hySπ, hπ₃]
    rfl
  have hcomm := e6Sc_commute_of_shift_eq_one hx' hy' hu₃a hu'₃b hw₃ h1₃
  have h2 : cS * (minBC e6Data_valid ι₃ s * minBC e6Data_valid ι₃ t) * cS⁻¹ =
      cS * (minBC e6Data_valid ι₃ t * minBC e6Data_valid ι₃ s) * cS⁻¹ := by
    calc cS * (minBC e6Data_valid ι₃ s * minBC e6Data_valid ι₃ t) * cS⁻¹ = xS * yS := by
          rw [hxS, hyS]; group
      _ = yS * xS := hcomm
      _ = cS * (minBC e6Data_valid ι₃ t * minBC e6Data_valid ι₃ s) * cS⁻¹ := by
          rw [hxS, hyS]; group
  have h3 := mul_left_cancel (mul_right_cancel h2)
  apply minBC_injective e6Data_valid ι₃
  rw [map_mul, map_mul, h3]

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis.PairAux
