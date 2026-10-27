module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriD4Outer
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CatTw
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.D4Residual
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.OrthD4
import CFSG.RankThree.Chevalley.SteinbergCBTrialityTransposition
import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27D4AmbientForm

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec8
  CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof

set_option linter.unusedSectionVars false


theorem isEmpty_alt6_of_lieModel_n {G : Type} [Group G] {t : StatedLieTag} {n p f : ℕ}
    (h : LieModel G t n p f) (hlarge : 4 ≤ lieSylowExponent t n * f) :
    IsEmpty (G ≃* alternatingGroup (Fin 6)) := by
  refine ⟨fun e => ?_⟩
  obtain ⟨-, -, hfac⟩ := lieOrderFormulasInput G t n p f h.admissible h
  have hp : p.Prime := h.admissible.1
  have hcard : Nat.card G = 360 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    decide
  rw [hcard] at hfac
  have hdvd : p ^ ((360 : ℕ).factorization p) ∣ 360 := Nat.ordProj_dvd 360 p
  rw [hfac] at hdvd
  exact not_pow_four_dvd_360 hp ((pow_dvd_pow p hlarge).trans hdvd)

section D4Cat

open TauCeti CFSG.Assembly.LowTwoRank CFSG.Yardstones.Md0ec50421ce4
  CFSG.Adapters.RankTwoModelTransports

private theorem nonempty_ringEquiv_fixedField' {K : Type} [Field K] [Fintype K]
    (d : ValidLieTypeIndex)
    (hK : Fintype.card K = d.fieldOrder) : Nonempty (K ≃+* ↥d.fixedField) := by
  haveI : Finite d.fixedField := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField d
  let _ : Fintype d.fixedField := Fintype.ofFinite _
  have hcard : Fintype.card K = Fintype.card d.fixedField := by
    rw [← Nat.card_eq_fintype_card (α := d.fixedField), ValidLieTypeIndex.card_fixedField]
    exact hK
  exact ⟨FiniteField.ringEquivOfCardEq hcard⟩

private theorem isChevSimple_statedProj_plus' {K : Type} [Field K] [Fintype K] (n : ℕ)
    (hn : 4 ≤ n) :
    IsChevSimple (ringChar K) (StatedProj (StatedOmega (StatedQuadPlus n K))) := by
  obtain ⟨f, hp, hcard⟩ := FiniteField.card K (ringChar K)
  let q : PrimePower := ⟨ringChar K, f, hp, f.pos⟩
  have hv : (LieTypeIndex.D n q).Valid := by
    rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨hn, not_false⟩
  obtain ⟨φ⟩ := nonempty_ringEquiv_fixedField' (K := K) ⟨.D n q, hv⟩ (by
    simp [ValidLieTypeIndex.fieldOrder, q, hcard])
  exact Or.inl ⟨.lie ⟨.D n q, hv⟩, LieTypeIndex.characteristic_D n q,
    ⟨(statedProjCongr (glCongr φ) (CFSG.ClassicalInvolution.Upgrade.map_statedOmega φ
      (CFSG.ClassicalInvolution.Upgrade.statedQuadPlus_comp φ)) (glCongr_statedScalars φ)).trans
      (CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid n q hv).symm⟩⟩

theorem isChevSimple_adjointGroup_D4 {K : Type} [Field K] [Finite K] :
    IsChevSimple (ringChar K) ↥(adjointGroup Tag.D4 K) ∧
      IsEmpty (↥(adjointGroup Tag.D4 K) ≃* alternatingGroup (Fin 6)) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨e⟩ := CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_statedProj_equiv_adjointGroup K
  refine ⟨isChevSimple_congr e (isChevSimple_statedProj_plus' (K := K) 4 le_rfl), ?_⟩
  obtain ⟨f, hp, hcard⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  have hmod : StatedClassicalModel ↥(adjointGroup Tag.D4 K) .POmegaPlus 4 (ringChar K) f :=
    ⟨⟨hp, f.pos, le_rfl⟩, K, inferInstance, inferInstance, hK, ⟨e.symm⟩⟩
  exact isEmpty_alt6_of_lieModel_n (t := .POmegaPlus) (n := 4) (p := ringChar K) (f := f)
    (Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], hmod⟩)
    (by simp [lieSylowExponent]; have := f.pos; omega)

end D4Cat

section Twisted

open CFSG.HardMathSupport.Lang.E6Descent CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.RecipeExcLang CFSG.RankThree.Chevalley CFSG.HardMathSupport.Lang.D4Three

variable {K : Type} [Field K] [Finite K]

theorem exists_fixSubgroup_twistedOne_equiv {ℓ e : ℕ} [Fact ℓ.Prime] [CharP K ℓ] (he : 1 ≤ e)
    (hK : Nat.card K = ℓ ^ (e * 3)) (σ : K ≃+* K) (r : ℕ) (hr : r = 1 ∨ r = 2)
    (hσ : ∀ c, σ c = c ^ ((ℓ ^ e) ^ r)) :
    IsSimpleGroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ∧
      (∃ x y : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom), x * y ≠ y * x) ∧
      Nonempty (↥(fixSubgroup (twistedEntrywiseAut TwistTag.D4 1 σ)) ≃*
        ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
  classical
  haveI : CharP (AlgebraicClosure K) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective ℓ
  obtain ⟨-, -, hfixeq, hsimple, hnc⟩ :=
    triality_both_field_orientations_simple_full_ambient_fixed_group ℓ e Fact.out he K
      (by rw [hK, pow_mul]) (AlgebraicClosure K) r hr σ.toRingHom hσ
      (iterateFrobenius (AlgebraicClosure K) ℓ e) (fun c => by simp [iterateFrobenius_def])
  exact ⟨hsimple, hnc, ⟨(fixedSubgroupTwistedEntrywiseAutOneEquiv TwistTag.D4 σ).trans
    (MulEquiv.subgroupCongr hfixeq)⟩⟩

theorem compsFine_of_equiv_cat_trialityD4 {ℓ : ℕ} {C X : Type} [Group C] [Group X] [Finite X]
    [IsSimpleGroup X] (hnc : ∃ x y : X, x * y ≠ y * x) (q : TauCeti.PrimePower) (hq : q.p = ℓ)
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid)
    (eC : (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group ≃* X) (eF : C ≃* X) :
    CompsFine ℓ C := by
  haveI : Finite C := Finite.of_equiv X eF.symm.toEquiv
  haveI : IsSimpleGroup C := (MulEquiv.isSimpleGroup_congr eF).2 inferInstance
  have hnc' : ∃ x y : C, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hnc
    exact ⟨eF.symm x, eF.symm y, fun h => hxy (by simpa using congrArg eF h)⟩
  have hchev := isChevSimple_of_lie (q := ℓ) ⟨.trialityD4 q, hv⟩
    (by rw [TauCeti.LieTypeIndex.characteristic_trialityD4]; exact hq) (eF.trans eC.symm)
  exact compsFine_of_simple hnc' hchev
    ⟨fun f => (isEmpty_cat_alt6 ⟨.trialityD4 q, hv⟩ (Or.inl rfl)).false
      ((eC.trans eF.symm).trans f)⟩

theorem compsFine_fixSubgroup_twistedEntrywiseAut_D4 {ℓ e : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (he : 1 ≤ e) (hK : Nat.card K = ℓ ^ (e * 3)) (T : K ≃+* K) (hT : ∀ c, T c = c ^ (ℓ ^ e))
    (j : ℤ) (hj : j % 3 = 1 ∨ j % 3 = 2) :
    CompsFine ℓ ↥(fixSubgroup (twistedEntrywiseAut TwistTag.D4 j T)) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  let q : TauCeti.PrimePower := ⟨ℓ, e, hℓ, he⟩
  have hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid := TauCeti.LieTypeIndex.valid_trialityD4 q
  have hKq : Nat.card K = q.card ^ 3 := by
    rw [hK, TauCeti.PrimePower.card_def, ← pow_mul]
  have hTq : ∀ c, T c = c ^ q.card := fun c => by rw [hT, TauCeti.PrimePower.card_def]
  obtain ⟨eC⟩ := catEquiv_trialityD4_of_field q hv K hKq T hTq
  have : Fintype K := Fintype.ofFinite K
  have hq3 : ∀ c : K, c ^ ((ℓ ^ e) ^ 3) = c := fun c => by
    rw [← pow_mul, ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hT3 : T ^ 3 = 1 := by
    refine RingEquiv.ext fun c => ?_
    change T (T (T c)) = c
    rw [hT, hT, hT, ← pow_mul, ← pow_mul, show ℓ ^ e * (ℓ ^ e * ℓ ^ e) = (ℓ ^ e) ^ 3 by ring, hq3]
  have hinv : ∀ c, T⁻¹ c = c ^ ((ℓ ^ e) ^ 2) := by
    have h1 : T⁻¹ = T ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hT3)
    intro c
    rw [h1, pow_two]
    change T (T c) = _
    rw [hT, hT, ← pow_mul, sq]
  have hper : twistedEntrywiseAut TwistTag.D4 j T = twistedEntrywiseAut TwistTag.D4 (j % 3) T := by
    have h := twistedEntrywiseAut_add_mul_order TwistTag.D4 (j % 3) (j / 3) T
    rw [show j % 3 + j / 3 * ((TwistTag.D4.order : ℕ) : ℤ) = j by
      change j % 3 + j / 3 * 3 = j
      omega] at h
    exact h
  rw [hper]
  rcases hj with h | h
  · rw [h]
    obtain ⟨hs, hnc, ⟨eF⟩⟩ := exists_fixSubgroup_twistedOne_equiv he hK T 1 (Or.inl rfl)
      (fun c => by rw [hT, pow_one])
    haveI := hs
    exact compsFine_of_equiv_cat_trialityD4 hnc q rfl hv eC eF
  · rw [h]
    have hfix := fixedSubgroup_twistedEntrywiseAut_D4_two T
    obtain ⟨hs, hnc, ⟨eF⟩⟩ := exists_fixSubgroup_twistedOne_equiv he hK T⁻¹ 2 (Or.inr rfl) hinv
    haveI := hs
    let eT : ↥(graphFixedRootGroup TwistTag.D4 K T.toRingHom) ≃*
        ↥(graphFixedRootGroup TwistTag.D4 K T⁻¹.toRingHom) :=
      (Subgroup.equivMapOfInjective _ (trialityTranspositionAut K).toMonoidHom
        (trialityTranspositionAut K).injective).trans
        (MulEquiv.subgroupCongr (map_trialityTranspositionAut_graphFixedRootGroup T))
    refine CompsFine.of_mulEquiv (MulEquiv.subgroupCongr hfix) ?_
    exact compsFine_of_equiv_cat_trialityD4 hnc q rfl hv (eC.trans eT) eF

theorem exists_frobenius_data_D4 (σ : K ≃+* K) (hσ : σ ≠ 1) (hσ3 : σ ^ 3 = 1) :
    ∃ (ℓ e : ℕ) (T : K ≃+* K), ℓ.Prime ∧ CharP K ℓ ∧ 1 ≤ e ∧ Nat.card K = ℓ ^ (e * 3) ∧
      (∀ c, T c = c ^ (ℓ ^ e)) ∧ (σ = T ∨ σ = T⁻¹) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hpr, hn⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hpr⟩
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ
  obtain ⟨e, T, he, hef, hT, hσT⟩ :=
    exists_frobenius_eq_or_inv_of_orderOf_three hpr n.pos K hK σ hord
  exact ⟨ringChar K, e, T, hpr, ringChar.charP K, he, by rw [hef, hK], hT, hσT⟩

theorem compsFine_of_lang_D4 {ℓ e : ℕ} [Fact ℓ.Prime] [CharP K ℓ] (he : 1 ≤ e)
    (hK : Nat.card K = ℓ ^ (e * 3)) (T : K ≃+* K) (hT : ∀ c, T c = c ^ (ℓ ^ e))
    (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K)
    (hσT : σ = T ∨ σ = T⁻¹) (ε : ℕ)
    (hP : ∀ j : ℤ, (j = (ε : ℤ) ∨ j = -(ε : ℤ)) →
      CompsFine ℓ ↥(fixSubgroup (twistedEntrywiseAut TwistTag.D4 j T)))
    (hα : (MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε)) ^ 3 = 1) :
    CompsFine ℓ ↥(fixSubgroup (MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε))) := by
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ ℓ ^ 2 := Nat.pow_le_pow_left (Fact.out : ℓ.Prime).two_le 2
      _ ≤ ℓ ^ (e * 3) := Nat.pow_le_pow_right (Fact.out : ℓ.Prime).pos (by omega)
  set α := MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε) with hαdef
  rcases hσT with hσT | hσT
  · subst hσT
    obtain ⟨ψ, hψ⟩ := exists_conj_eq_twistedEntrywiseAut_of_normalForm K hK hK4 he rfl σ hT α hα
      g a ε hαdef
    have h := hP _ (Or.inl rfl)
    rw [← hψ] at h
    exact h.of_mulEquiv (fixSubgroupConjEquiv ψ α)
  · subst hσT
    obtain ⟨ψ, hψ⟩ := exists_conj_inv_eq_twistedEntrywiseAut_of_normalForm K hK hK4 he rfl T T⁻¹
      hT (mul_inv_cancel T) α hα g a ε hαdef
    have h := hP _ (Or.inr rfl)
    rw [← hψ] at h
    exact (h.of_mulEquiv (fixSubgroupConjEquiv ψ α⁻¹)).of_mulEquiv
      (MulEquiv.subgroupCongr (LieSemisimple.fixSubgroup_inv_eq α).symm)

end Twisted

section FieldType

open CFSG.Yardstones.Md0ec50421ce4

variable {K : Type} [Field K] [Finite K]

theorem compsFine_fixSubgroup_entrywiseAdjointAut {q : ℕ} (τ : Tag) (σ : K ≃+* K)
    (hs : IsSimpleGroup (adjointGroup τ (fixSubfield σ)))
    (hnc : ∃ x y : adjointGroup τ (fixSubfield σ), x * y ≠ y * x)
    (hchev : IsChevSimple q ↥(adjointGroup τ (fixSubfield σ)))
    (hA6 : IsEmpty (↥(adjointGroup τ (fixSubfield σ)) ≃* alternatingGroup (Fin 6))) :
    CompsFine q ↥(fixSubgroup (entrywiseAdjointAut τ σ)) := by
  classical
  haveI : Finite (ModGL τ K) := finite_modGL
  haveI : Finite (fixSubfield σ) := Subtype.finite
  haveI : Finite (ModGL τ (fixSubfield σ)) := finite_modGL
  haveI : Finite ↥(adjointGroup τ (fixSubfield σ)) := Subtype.finite
  haveI : Finite ↥(adjointGroup τ K) := Subtype.finite
  obtain ⟨ι, hι, hJC, hnorm, hsol⟩ := ExcCopy.exists_fixed_structure τ σ
  haveI := hs
  let J : Subgroup ↥(fixSubgroup (entrywiseAdjointAut τ σ)) :=
    ι.range.subgroupOf (fixSubgroup (entrywiseAdjointAut τ σ))
  haveI : J.Normal := hnorm
  let e : adjointGroup τ (fixSubfield σ) ≃* ι.range := MonoidHom.ofInjective hι
  let eJ : ↥J ≃* adjointGroup τ (fixSubfield σ) :=
    (Subgroup.subgroupOfEquivOfLe hJC).trans e.symm
  have hZ : Subgroup.center ↥(adjointGroup τ (fixSubfield σ)) = ⊥ := b3Lie_center_eq_bot hnc
  refine compsFine_of_normal_quasisimple J
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv eJ.symm
      (LieSemisimple.isQuasisimple_of_isSimpleGroup hs hnc)) hsol
    ⟨_, inferInstance, inferInstance, lieFactorData_of_simple hnc hchev, eJ.symm.toMonoidHom,
      eJ.symm.surjective, ?_⟩ ?_
  · intro x hx
    rw [MonoidHom.mem_ker] at hx
    have : x = 1 := eJ.symm.injective (by rw [map_one]; exact hx)
    rw [this]
    exact one_mem _
  · exact isEmpty_quotient_center_alt6_of_equiv eJ (isEmpty_quotient_center_alt6 hZ hA6)

end FieldType

section Assembly

open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E6Descent

private theorem d4Graph_zero_D4 {K : Type} [Field K] [Finite K] : d4Graph K 0 = 1 :=
  MulEquiv.ext fun h => Subtype.ext (by
    rw [coe_d4Graph, pow_zero, one_mul, inv_one, mul_one]; rfl)

theorem compsFine_d4_graph_type (hodd : TrialityOddA2Comps) {ℓ f : ℕ} [Fact ℓ.Prime]
    (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f) {F : Type} [Field F] [Finite F] [CharP F ℓ]
    (hF : Nat.card F = ℓ ^ f) (g : adjointGroup Tag.D4 F) (a : Fin Tag.D4.rank → Fˣ)
    (σ : F ≃+* F) (hσ3 : σ ^ 3 = 1) {ε : ℕ} (hε : ε = 1 ∨ ε = 2)
    (hα : (MulAut.conj g * (exactNormalAut Tag.D4 F a σ 0 * d4Graph F ε)) ^ 3 = 1) :
    CompsFine ℓ ↥(fixSubgroup (MulAut.conj g * (exactNormalAut Tag.D4 F a σ 0 * d4Graph F ε))) := by
  classical
  by_cases hσ1 : σ = 1
  · subst hσ1
    obtain ⟨K₃, _, _, Fr, hK₃, hFr, φ, hφ3, hφout, ⟨e⟩⟩ :=
      D4Dual.exists_dual_fixEquiv hf F hF _ hα g a hε rfl
    exact (compsFine_triality_outer hodd hℓ3 hf hK₃ Fr hFr φ hφ3 hφout).of_mulEquiv e
  · obtain ⟨ℓ', e, T, hℓ', hchar', he, hK, hT, hσT⟩ := exists_frobenius_data_D4 σ hσ1 hσ3
    obtain rfl : ℓ' = ℓ := CharP.eq F hchar' ‹CharP F ℓ›
    refine compsFine_of_lang_D4 he hK T hT g a σ hσT ε (fun j hj => ?_) hα
    refine compsFine_fixSubgroup_twistedEntrywiseAut_D4 he hK T hT j ?_
    rcases hε with rfl | rfl <;> rcases hj with rfl | rfl <;> omega

theorem compsFine_d4_outer (hodd : TrialityOddA2Comps) {ℓ f : ℕ} [Fact ℓ.Prime] (hℓ3 : ℓ ≠ 3)
    (hf : 1 ≤ f) {F : Type} [Field F] [Finite F] (hF : Nat.card F = ℓ ^ f)
    (α : MulAut ↥(adjointGroup Tag.D4 F)) (hα : α ^ 3 = 1)
    (hout : ∀ h : adjointGroup Tag.D4 F, MulAut.conj h ≠ α) :
    CompsFine ℓ ↥(fixSubgroup α) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have hchF : CharP F ℓ := by
    have : Fintype F := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hF])
  have hchar : ringChar F ≠ 3 := by rw [ringChar.eq F ℓ]; exact hℓ3
  obtain ⟨g, a, σ, ε, hε, hσ3, hαeq⟩ := exists_cube_normal_form_sigma α hα
  interval_cases ε
  · have hα' : α = MulAut.conj g * exactNormalAut Tag.D4 F a σ 0 := by
      rw [hαeq, d4Graph_zero_D4, mul_one]
    by_cases hσ1 : σ = 1
    · exfalso
      subst hσ1
      rw [hα'] at hα
      obtain ⟨h, hh⟩ := d4_inner_of_diag hchar g a hα
      exact hout h (by rw [hα', hh])
    · rw [hα'] at hα
      obtain ⟨ψ, hψ⟩ := ExcCopy.exists_conj_eq_entrywiseAdjointAut .D4 Nat.prime_three g a σ hσ1
        hσ3 hα
      haveI : Finite (fixSubfield σ) := Subtype.finite
      obtain ⟨hChev, hA6⟩ := isChevSimple_adjointGroup_D4 (K := fixSubfield σ)
      have hring : ringChar (fixSubfield σ) = ℓ :=
        ringChar_subfield (ringChar.eq F ℓ) (fixSubfield σ)
      rw [hring] at hChev
      have hperf := ExcCopy.isPerfect_adjointGroup .D4 (fixSubfield σ) (fun h => absurd h (by decide))
      obtain ⟨hs, hnc⟩ := ExcCopy.isSimpleGroup_adjointGroup_of_perfect .D4 (fixSubfield σ) hperf
      have hcf := compsFine_fixSubgroup_entrywiseAdjointAut .D4 σ hs hnc hChev hA6
      rw [← hψ] at hcf
      rw [hα']
      exact hcf.of_mulEquiv (fixSubgroupConjEquiv ψ _)
  · rw [hαeq]
    exact compsFine_d4_graph_type hodd hℓ3 hf hF g a σ hσ3 (Or.inl rfl) (hαeq ▸ hα)
  · rw [hαeq]
    exact compsFine_d4_graph_type hodd hℓ3 hf hF g a σ hσ3 (Or.inr rfl) (hαeq ▸ hα)

@[expose] def D4Char3Outer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] {f : ℕ}, StatedClassicalModel G .POmegaPlus 4 3 f →
    ∀ β : MulAut G, β ^ 3 = 1 → (∀ a : G, MulAut.conj a ≠ β) →
      LieCompExport 3 β ∨ NoThreeComponents β

theorem d4OuterExport_of (hodd : TrialityOddA2Comps) (hchar3 : D4Char3Outer) : D4OuterExport := by
  intro G _ _ ℓ f hG β hβ hout
  by_cases hℓ3 : ℓ = 3
  · subst hℓ3
    exact hchar3 G hG β hβ hout
  left
  have hG' := hG
  obtain ⟨⟨hℓ, hf, -⟩, F, _, _, hF, ⟨eG⟩⟩ := hG'
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨eC⟩ := CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_statedProj_equiv_adjointGroup F
  let e₂ : G ≃* ↥(adjointGroup Tag.D4 F) := eG.trans eC
  refine lieCompExport_of_compsFine (perfectInLayer_omega_D4_three hG hℓ3 β hβ) ?_
  have hα : MulAut.congr e₂ β ^ 3 = 1 := by rw [← map_pow, hβ, map_one]
  have hout' : ∀ h : adjointGroup Tag.D4 F, MulAut.conj h ≠ MulAut.congr e₂ β := fun h hh => by
    apply hout (e₂.symm h)
    have hc : MulAut.congr e₂.symm (MulAut.conj h) = MulAut.conj (e₂.symm h) := by
      ext y
      simp [MulAut.congr_apply, MulAut.conj_apply]
    rw [← hc, hh]
    ext y
    simp [MulAut.congr_apply]
  exact (compsFine_d4_outer hodd hℓ3 hf hF (MulAut.congr e₂ β) hα hout').of_mulEquiv
    (fixSubgroupCongrEquiv e₂ β)

end Assembly

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
