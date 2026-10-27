module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.D4TrialityAux.Regular
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27D4AmbientFixed
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.D4TrialityAux.Basic
public import CFSG.HardMathSupport.Lang.D4Three.NormalForm
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.Lattice.SteinbergBIListMatrix

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Chevalley.FieldGraphFieldPointwise
  CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E6Descent
  CFSG.LocalAnalysis.ComponentInitial

section Faithful


variable {K : Type} [Field K]

abbrev d4n0 : Fin Tag.D4.rank := ⟨0, by decide⟩
abbrev d4n1 : Fin Tag.D4.rank := ⟨1, by decide⟩
abbrev d4n2 : Fin Tag.D4.rank := ⟨2, by decide⟩
abbrev d4n3 : Fin Tag.D4.rank := ⟨3, by decide⟩

theorem d4Graph_zero_f : d4Graph K 0 = 1 :=
  MulEquiv.ext fun h => Subtype.ext (by
    rw [coe_d4Graph, pow_zero, one_mul, inv_one, mul_one]; rfl)

theorem d4Rho_n0 : d4Rho d4n0 = d4n1 := by decide
theorem d4Rho_n1 : d4Rho d4n1 = d4n3 := by decide
theorem d4Rho_n3 : d4Rho d4n3 = d4n0 := by decide
theorem d4Rho_n2 : d4Rho d4n2 = d4n2 := by decide

abbrev x4 (j : ℤ) (T : K ≃+* K) : MulAut (adjointGroup Tag.D4 K) :=
  twistedEntrywiseAut TwistTag.D4 j T

theorem x4_eq (ε : ℕ) (T : K ≃+* K) :
    x4 (ε : ℤ) T = exactNormalAut Tag.D4 K 1 T 0 * d4Graph K ε := by
  refine MulEquiv.ext fun u => Subtype.ext ?_
  have hP : Units.map (entrywiseHom (τ := Tag.D4) T.toRingHom) (d4P K ^ ε) = d4P K ^ ε := by
    rw [map_pow]
    exact congrArg (· ^ ε) (units_map_entrywiseHom_diagramMap (t := TwistTag.D4) T.toRingHom)
  have h1 : (Subtype.val (x4 (ε : ℤ) T u) : ModGL Tag.D4 K) =
      d4P K ^ ε * Units.map (entrywiseHom T.toRingHom) (u : ModGL Tag.D4 K) * (d4P K ^ ε)⁻¹ := by
    have h := coe_twistedEntrywiseAut TwistTag.D4 (ε : ℤ) T u
    rw [zpow_natCast] at h
    exact h
  rw [h1, MulAut.mul_apply, coe_exactNormalAut, exactQ_zero, coe_d4Graph, rootDiagUnit_one]
  simp only [map_mul, map_inv, hP, mul_one, inv_one, one_mul]

theorem x4_one_adjX (T : K ≃+* K) (i : Fin Tag.D4.rank) (c : K) :
    x4 1 T (adjX Tag.D4 K i c) = adjX Tag.D4 K (d4Rho i) (T c) := by
  rw [show (1 : ℤ) = ((1 : ℕ) : ℤ) from rfl, x4_eq, MulAut.mul_apply,
    d4Graph_adjX, exactNormalAut_adjX]
  simp [exactPerm_zero]

theorem x4_mem (ε : ℕ) (T : K ≃+* K) : x4 (ε : ℤ) T ∈ unipotentPairAut Tag.D4 K := by
  rw [x4_eq]
  exact mul_mem (exactNormalAut_mem _ _ _) (d4Graph_mem ε)

theorem x4_one_mem (T : K ≃+* K) : x4 1 T ∈ unipotentPairAut Tag.D4 K := by
  simpa using x4_mem 1 T

theorem simplePermHom_x4_one (T : K ≃+* K) :
    simplePermHom Tag.D4 K ⟨x4 1 T, x4_one_mem T⟩ = d4Rho :=
  perm_map_simple_unique (α := x4 1 T)
    (fun i => (simplePerm_spec (τ := Tag.D4) (K := K) ⟨x4 1 T, x4_one_mem T⟩ i).1)
    (fun i => map_simplePosSubgroup_of_adjX (f := T) T.surjective (fun c => x4_one_adjX T i c))

theorem perm_commute_d4Rho (π : Equiv.Perm (Fin Tag.D4.rank)) (h : π * d4Rho = d4Rho * π) :
    π = 1 ∨ π = d4Rho ∨ π = d4Rho ^ 2 := by
  have key : ∀ π : Equiv.Perm (Fin 4),
      π * (Equiv.swap 0 1 * Equiv.swap 1 3) = (Equiv.swap 0 1 * Equiv.swap 1 3) * π →
      π = 1 ∨ π = (Equiv.swap 0 1 * Equiv.swap 1 3) ∨
        π = (Equiv.swap 0 1 * Equiv.swap 1 3) ^ 2 := by
    decide +kernel
  exact key π h

theorem orderOf_d4Rho : orderOf d4Rho = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (by decide) (by decide)

theorem orderOf_d4Rho_sq : orderOf (d4Rho ^ 2) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (by decide) (by decide)

@[expose] def u₀ (K : Type) [Field K] : adjointGroup Tag.D4 K :=
  adjX Tag.D4 K d4n2 1 * (adjX Tag.D4 K d4n0 1 * adjX Tag.D4 K d4n1 1 * adjX Tag.D4 K d4n3 1)

@[expose] def orbSum (T : K ≃+* K) (c : K) : adjointGroup Tag.D4 K :=
  adjX Tag.D4 K d4n0 c * adjX Tag.D4 K d4n1 (T c) * adjX Tag.D4 K d4n3 (T (T c))

theorem u₀_eq_orbSum (T : K ≃+* K) : u₀ K = adjX Tag.D4 K d4n2 1 * orbSum T 1 := by
  simp [u₀, orbSum]

theorem adjX_comm_01 (c d : K) : adjX Tag.D4 K d4n0 c * adjX Tag.D4 K d4n1 d =
    adjX Tag.D4 K d4n1 d * adjX Tag.D4 K d4n0 c := by
  have h : Tag.D4.cartan d4n0 d4n1 ≠ -1 := by decide
  exact ((simplePos_commute_iff_D4 (K := K) (i := d4n0) (j := d4n1) (by decide)).2 h _ ⟨c, rfl⟩ _
    ⟨d, rfl⟩).eq

theorem adjX_comm_03 (c d : K) : adjX Tag.D4 K d4n0 c * adjX Tag.D4 K d4n3 d =
    adjX Tag.D4 K d4n3 d * adjX Tag.D4 K d4n0 c := by
  have h : Tag.D4.cartan d4n0 d4n3 ≠ -1 := by decide
  exact ((simplePos_commute_iff_D4 (K := K) (i := d4n0) (j := d4n3) (by decide)).2 h _ ⟨c, rfl⟩ _
    ⟨d, rfl⟩).eq

theorem x4_one_orbSum (T : K ≃+* K) (hT3 : ∀ c, T (T (T c)) = c) (c : K) :
    x4 1 T (orbSum T c) = orbSum T c := by
  unfold orbSum
  rw [map_mul, map_mul, x4_one_adjX, x4_one_adjX, x4_one_adjX, d4Rho_n0, d4Rho_n1, d4Rho_n3,
    hT3]
  have hab := adjX_comm_01 (K := K) c (T c)
  have hac := adjX_comm_03 (K := K) c (T (T c))
  calc _ = adjX Tag.D4 K d4n1 (T c) * (adjX Tag.D4 K d4n3 (T (T c)) * adjX Tag.D4 K d4n0 c) :=
        mul_assoc _ _ _
    _ = adjX Tag.D4 K d4n1 (T c) * (adjX Tag.D4 K d4n0 c * adjX Tag.D4 K d4n3 (T (T c))) := by
        rw [hac]
    _ = (adjX Tag.D4 K d4n1 (T c) * adjX Tag.D4 K d4n0 c) * adjX Tag.D4 K d4n3 (T (T c)) :=
        (mul_assoc _ _ _).symm
    _ = _ := by rw [hab]

theorem x4_one_u₀ (T : K ≃+* K) (hT3 : ∀ c, T (T (T c)) = c) : x4 1 T (u₀ K) = u₀ K := by
  rw [u₀_eq_orbSum T, map_mul, x4_one_orbSum T hT3, x4_one_adjX, d4Rho_n2, map_one]

@[expose] def repW (K : Type) [Field K] (w : WeylGroup Tag.D4) : adjointGroup Tag.D4 K :=
  ⟨canonicalRep (coxeterSystem Tag.D4) K w,
    canonicalRep_mem_adjointGroup (coxeterSystem Tag.D4) K w⟩

theorem x4_one_repW (T : K ≃+* K) {w₀ : WeylGroup Tag.D4}
    (hw₀ : ∀ w, (coxeterSystem Tag.D4).length w ≤ (coxeterSystem Tag.D4).length w₀) :
    x4 1 T (repW K w₀) = repW K w₀ := by
  have hw : w₀ ∈ relWeylTwist TwistTag.D4 := mem_relWeylTwist_of_forall_length_le hw₀
  have hmem := graphFixedRootGroup_le TwistTag.D4 K T.toRingHom
    (canonicalRep_mem_graphFixedRootGroup (K := K) (σ := T.toRingHom) hw)
  rw [mem_twistedFixedGroup_iff_twistHom] at hmem
  exact Subtype.ext ((coe_twistedEntrywiseAut_one TwistTag.D4 T (repW K w₀)).trans hmem.2)

theorem d4_cases (j : Fin Tag.D4.rank) : j = d4n0 ∨ j = d4n1 ∨ j = d4n2 ∨ j = d4n3 := by
  revert j; decide

theorem list4_sum (j : Fin Tag.D4.rank) (f : Fin Tag.D4.rank → K) :
    ([d4n2, d4n0, d4n1, d4n3].map fun i => if i = j then f i else 0).sum = f j := by
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rcases d4_cases j with rfl | rfl | rfl | rfl
  · rw [if_neg (by decide), if_pos rfl, if_neg (by decide), if_neg (by decide)]; simp
  · rw [if_neg (by decide), if_neg (by decide), if_pos rfl, if_neg (by decide)]; simp
  · rw [if_pos rfl, if_neg (by decide), if_neg (by decide), if_neg (by decide)]; simp
  · rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]; simp

section Coordinates

variable [Finite K]

theorem coe_u₀ : ((u₀ K : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) =
    ([d4n2, d4n0, d4n1, d4n3].map fun i => xUnit Tag.D4 K i 1).prod := by
  show xUnit Tag.D4 K d4n2 1 * (xUnit Tag.D4 K d4n0 1 * xUnit Tag.D4 K d4n1 1 *
    xUnit Tag.D4 K d4n3 1) = _
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [mul_assoc]

theorem u₀_mem_posUnipotent :
    ((u₀ K : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) ∈ posUnipotent Tag.D4 K := by
  rw [coe_u₀]
  refine list_prod_mem fun x hx => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  exact xUnit_mem_posUnipotent i 1

theorem rootCoord_u₀ (j : Fin Tag.D4.rank) :
    rootCoord (single_pos j) ((u₀ K : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) = 1 := by
  rw [coe_u₀, rootCoord_single_list_prod]
  exact list4_sum j (fun _ => 1)

theorem coe_exactNormalAut_u₀ (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) :
    ((exactNormalAut Tag.D4 K a σ 0 (u₀ K) : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) =
      ([d4n2, d4n0, d4n1, d4n3].map fun i => xUnit Tag.D4 K i ((a i : K) * σ 1)).prod := by
  have h : u₀ K = ([d4n2, d4n0, d4n1, d4n3].map fun i => adjX Tag.D4 K i 1).prod := by
    simp [u₀, mul_assoc]
  rw [h, map_list_prod, List.map_map, Subgroup.val_list_prod, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun i _ => ?_)
  simp only [Function.comp_apply, exactNormalAut_adjX, exactPerm_zero, Equiv.Perm.one_apply]
  rfl

theorem eq_one_of_exactNormalAut_zero_fix_u₀ {a : Fin Tag.D4.rank → Kˣ} {σ : K ≃+* K}
    (h : exactNormalAut Tag.D4 K a σ 0 (u₀ K) = u₀ K) : a = 1 := by
  funext j
  have h1 : rootCoord (single_pos j)
      ((exactNormalAut Tag.D4 K a σ 0 (u₀ K) : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) =
        rootCoord (single_pos j) ((u₀ K : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) := by
    rw [h]
  rw [coe_exactNormalAut_u₀, rootCoord_u₀, rootCoord_single_list_prod] at h1
  simp only [map_one, mul_one] at h1
  have h2 : (a j : K) = 1 := by
    have := list4_sum j (fun i => (a i : K))
    exact this.symm.trans h1
  exact Units.ext h2

theorem rootCoord_xUnit_mul3 (j p q r : Fin Tag.D4.rank) (s t u : K) :
    rootCoord (single_pos j) (xUnit Tag.D4 K p s * xUnit Tag.D4 K q t * xUnit Tag.D4 K r u) =
      ((if p = j then s else 0) + (if q = j then t else 0)) + (if r = j then u else 0) := by
  have hpq : xUnit Tag.D4 K p s * xUnit Tag.D4 K q t ∈ posUnipotent Tag.D4 K :=
    mul_mem (xUnit_mem_posUnipotent p s) (xUnit_mem_posUnipotent q t)
  rw [rootCoord_mul _ (mem_heightSeries_single hpq j)
    (mem_heightSeries_single (xUnit_mem_posUnipotent r u) j), rootCoord_single_xUnit_mul_xUnit,
    rootCoord_single_xUnit]

theorem rootCoord_orbSum_zero (T : K ≃+* K) (c : K) :
    rootCoord (single_pos d4n0) ((orbSum T c : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) = c := by
  change rootCoord (single_pos d4n0) (xUnit Tag.D4 K d4n0 c * xUnit Tag.D4 K d4n1 (T c) *
    xUnit Tag.D4 K d4n3 (T (T c))) = c
  rw [rootCoord_xUnit_mul3, if_pos rfl, if_neg (by decide), if_neg (by decide)]
  simp

theorem rootCoord_exactNormalAut_orbSum_zero (a : Fin Tag.D4.rank → Kˣ) (σ T : K ≃+* K) (c : K) :
    rootCoord (single_pos d4n0)
      ((exactNormalAut Tag.D4 K a σ 0 (orbSum T c) : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) =
        (a d4n0 : K) * σ c := by
  unfold orbSum
  rw [map_mul, map_mul, exactNormalAut_adjX, exactNormalAut_adjX, exactNormalAut_adjX]
  change rootCoord (single_pos d4n0) (xUnit Tag.D4 K _ _ * xUnit Tag.D4 K _ _ *
    xUnit Tag.D4 K _ _) = _
  rw [rootCoord_xUnit_mul3]
  simp only [exactPerm_zero, Equiv.Perm.one_apply, if_true]
  rw [if_neg (by decide), if_neg (by decide)]
  simp

end Coordinates

section Main

variable [Finite K]

theorem faithfulAt_x4_one (T : K ≃+* K) (hT3 : ∀ c, T (T (T c)) = c) :
    FaithfulAt 3 (x4 1 T) := by
  classical
  intro φ hcop hcomm hfix
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem Tag.D4).length
  have hu₀F : u₀ K ∈ fixSub (x4 1 T) := mem_fixSub.2 (x4_one_u₀ T hT3)
  have hvF : repW K w₀ * u₀ K * (repW K w₀)⁻¹ ∈ fixSub (x4 1 T) := by
    rw [mem_fixSub, map_mul, map_mul, map_inv, x4_one_repW T hw₀, x4_one_u₀ T hT3]
  have hφA : φ ∈ unipotentPairAut Tag.D4 K :=
    mem_unipotentPairAut_of_fix_regular hw₀ (n₀ := repW K w₀) (u := u₀ K) rfl
      u₀_mem_posUnipotent (fun j => by rw [rootCoord_u₀]; exact one_ne_zero)
      (hfix _ hu₀F) (hfix _ hvF)
  set a : unipotentPairAut Tag.D4 K := ⟨φ, hφA⟩ with ha
  set b : unipotentPairAut Tag.D4 K := ⟨x4 1 T, x4_one_mem T⟩ with hb
  have hab : a * b = b * a := Subtype.ext hcomm
  have hπcomm : simplePermHom Tag.D4 K a * d4Rho = d4Rho * simplePermHom Tag.D4 K a := by
    rw [← simplePermHom_x4_one T, ← map_mul, ← map_mul, hab]
  have hπ1 : simplePermHom Tag.D4 K a = 1 := by
    have hdvd : orderOf (simplePermHom Tag.D4 K a) ∣ orderOf φ := by
      have := orderOf_map_dvd (simplePermHom Tag.D4 K) a
      rwa [ha, Subgroup.orderOf_mk] at this
    rcases perm_commute_d4Rho _ hπcomm with h | h | h
    · exact h
    · exfalso
      rw [h, orderOf_d4Rho] at hdvd
      exact absurd (Nat.Coprime.eq_one_of_dvd hcop hdvd) (by norm_num)
    · exfalso
      rw [h, orderOf_d4Rho_sq] at hdvd
      exact absurd (Nat.Coprime.eq_one_of_dvd hcop hdvd) (by norm_num)
  have hε : ∀ i, (simplePosSubgroup Tag.D4 K i).map φ.toMonoidHom =
        simplePosSubgroup Tag.D4 K ((d4Rho ^ 0) i) ∧
      (simpleNegSubgroup Tag.D4 K i).map φ.toMonoidHom =
        simpleNegSubgroup Tag.D4 K ((d4Rho ^ 0) i) := by
    intro i
    have h := simplePerm_spec a i
    have h1 : simplePerm Tag.D4 K a = 1 := hπ1
    rw [h1] at h
    simpa using h
  obtain ⟨a', σ', hφ⟩ := exists_normalAut_mul_graph hε
  rw [d4Graph_zero_f, mul_one] at hφ
  have ha' : a' = 1 := by
    refine eq_one_of_exactNormalAut_zero_fix_u₀ (σ := σ') ?_
    rw [← hφ]
    exact hfix _ hu₀F
  have hσ' : σ' = 1 := by
    refine RingEquiv.ext fun c => ?_
    have h1 := hfix (orbSum T c) (mem_fixSub.2 (x4_one_orbSum T hT3 c))
    rw [hφ] at h1
    have h2 := congrArg (fun g : adjointGroup Tag.D4 K =>
      rootCoord (single_pos d4n0) (g : ModGL Tag.D4 K)) h1
    simp only [rootCoord_exactNormalAut_orbSum_zero, rootCoord_orbSum_zero, ha',
      Pi.one_apply, Units.val_one, one_mul] at h2
    exact h2
  rw [hφ, ha', hσ', exactNormalAut_one_one_zero]

theorem faithfulAt_entrywise (T : K ≃+* K) (hT3 : T ^ 3 = 1) :
    FaithfulAt 3 (entrywiseAdjointAut Tag.D4 T) := by
  classical
  intro φ hcop hcomm hfix
  have hxX : ∀ (i : Fin Tag.D4.rank) (c : K), entrywiseAdjointAut Tag.D4 T (adjX Tag.D4 K i c) =
      adjX Tag.D4 K i (T c) := fun i c => entrywiseAdjointAut_adjX T i c
  have hX1 : ∀ i : Fin Tag.D4.rank, adjX Tag.D4 K i 1 ∈ fixSub (entrywiseAdjointAut Tag.D4 T) :=
    fun i => mem_fixSub.2 (by rw [hxX, map_one])
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem Tag.D4).length
  have hu₀F : u₀ K ∈ fixSub (entrywiseAdjointAut Tag.D4 T) := by
    refine mem_fixSub.2 ?_
    simp only [u₀, map_mul, hxX, map_one]
  have hrepF : entrywiseAdjointAut Tag.D4 T (repW K w₀) = repW K w₀ := by
    have h1 := fixedFieldImage_le (canonicalRep_mem_fixedFieldImage T w₀)
    exact Subtype.ext h1.2
  have hvF : repW K w₀ * u₀ K * (repW K w₀)⁻¹ ∈ fixSub (entrywiseAdjointAut Tag.D4 T) := by
    rw [mem_fixSub, map_mul, map_mul, map_inv, hrepF, mem_fixSub.1 hu₀F]
  have hφA : φ ∈ unipotentPairAut Tag.D4 K :=
    mem_unipotentPairAut_of_fix_regular hw₀ (n₀ := repW K w₀) (u := u₀ K) rfl
      u₀_mem_posUnipotent (fun j => by rw [rootCoord_u₀]; exact one_ne_zero)
      (hfix _ hu₀F) (hfix _ hvF)
  set a : unipotentPairAut Tag.D4 K := ⟨φ, hφA⟩ with ha
  have hπ1 : simplePerm Tag.D4 K a = 1 := by
    refine Equiv.ext fun i => ?_
    have hfx := hfix _ (hX1 i)
    have hmem : φ (adjX Tag.D4 K i 1) ∈ simplePosSubgroup Tag.D4 K (simplePerm Tag.D4 K a i) := by
      rw [← (simplePerm_spec a i).1]
      exact Subgroup.mem_map_of_mem _ ⟨1, rfl⟩
    rw [hfx] at hmem
    obtain ⟨c, hc⟩ := hmem
    have h1 := rootCoord_ite_eq_of_adjX_eq (Subtype.ext hc.symm : adjX Tag.D4 K _ c = adjX Tag.D4 K i 1) i
    by_contra hne
    have hne' : simplePerm Tag.D4 K a i ≠ i := hne
    rw [if_neg hne', if_pos rfl] at h1
    exact one_ne_zero h1.symm
  have hε : ∀ i, (simplePosSubgroup Tag.D4 K i).map φ.toMonoidHom =
        simplePosSubgroup Tag.D4 K ((d4Rho ^ 0) i) ∧
      (simpleNegSubgroup Tag.D4 K i).map φ.toMonoidHom =
        simpleNegSubgroup Tag.D4 K ((d4Rho ^ 0) i) := by
    intro i
    have h := simplePerm_spec a i
    rw [hπ1] at h
    simpa using h
  obtain ⟨a', σ', hφ⟩ := exists_normalAut_mul_graph hε
  rw [d4Graph_zero_f, mul_one] at hφ
  have ha' : a' = 1 := by
    refine eq_one_of_exactNormalAut_zero_fix_u₀ (σ := σ') ?_
    rw [← hφ]
    exact hfix _ hu₀F
  have hσfix : ∀ c, T c = c → σ' c = c := by
    intro c hc
    have hF : adjX Tag.D4 K d4n0 c ∈ fixSub (entrywiseAdjointAut Tag.D4 T) :=
      mem_fixSub.2 (by rw [hxX, hc])
    have h1 := hfix _ hF
    rw [hφ, ha', exactNormalAut_adjX, exactPerm_zero, Equiv.Perm.one_apply] at h1
    have h2 := adjX_injective d4n0 h1
    simpa using h2
  have hmem : σ' ∈ Subgroup.zpowers T := CFSG.ComponentClassification.UnbalancedCatalog.mem_zpowers_of_fixed hσfix
  have hσ3 : σ' ^ 3 = 1 := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hmem
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hT3, one_zpow]
  have hφ3 : φ ^ 3 = 1 := by
    rw [hφ, ha', exactNormalAut_one_zero_eq, ← entrywiseAdjointAut_pow, hσ3,
      entrywiseAdjointAut_one]
  have hdvd : orderOf φ ∣ 3 := orderOf_dvd_of_pow_eq_one hφ3
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hcop.symm hdvd)

end Main

section Invariance

variable {G : Type*} [Group G] {p : ℕ}

theorem FaithfulAt.inv {x : MulAut G} (h : FaithfulAt p x) : FaithfulAt p x⁻¹ := by
  intro g hg hgx hfix
  rw [fixSub_inv_eq] at hfix
  refine h g hg ?_ hfix
  calc g * x = x * (x⁻¹ * g) * x := by group
    _ = x * (g * x⁻¹) * x := by rw [← hgx]
    _ = x * g := by group

end Invariance

section Std

variable [Finite K]

theorem x4_mod_three (T : K ≃+* K) (j : ℤ) : x4 j T = x4 (j % 3) T := by
  have h := twistedEntrywiseAut_add_mul_order TwistTag.D4 (j % 3) (j / 3) T
  have hj : (j % 3 + j / 3 * ((TwistTag.D4.order : ℕ) : ℤ)) = j := by
    have h3 : ((TwistTag.D4.order : ℕ) : ℤ) = 3 := rfl
    rw [h3]; omega
  rw [hj] at h
  exact h

theorem x4_two (T : K ≃+* K) : x4 2 T = (x4 1 T⁻¹)⁻¹ := by
  have h := twistedEntrywiseAut_add_mul_order TwistTag.D4 (-1) 1 T
  rw [show (-1 : ℤ) + 1 * ((TwistTag.D4.order : ℕ) : ℤ) = 2 by decide] at h
  have h2 := twistedEntrywiseAut_inv TwistTag.D4 1 T⁻¹
  rw [inv_inv] at h2
  exact h.trans h2.symm

theorem ringEquiv_cube_inv {T : K ≃+* K} (h : ∀ c, T (T (T c)) = c) :
    ∀ c, T⁻¹ (T⁻¹ (T⁻¹ c)) = c := by
  have hinv : ∀ y, T⁻¹ y = T (T y) := fun y => by
    have : (T⁻¹) y = T.symm y := rfl
    rw [this, RingEquiv.symm_apply_eq]
    exact (h y).symm
  intro c
  simp only [hinv, h]

theorem faithfulAt_x4 (T : K ≃+* K) (hT3 : ∀ c, T (T (T c)) = c) (j : ℤ)
    (hj : j % 3 = 1 ∨ j % 3 = 2) : FaithfulAt 3 (x4 j T) := by
  rw [x4_mod_three]
  rcases hj with h | h
  · rw [h]
    exact faithfulAt_x4_one T hT3
  · rw [h, x4_two]
    exact (faithfulAt_x4_one T⁻¹ (ringEquiv_cube_inv hT3)).inv

end Std

end Faithful

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
