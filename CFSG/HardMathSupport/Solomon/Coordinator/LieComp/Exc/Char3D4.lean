module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Char3TriD4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.D4Outer
import CFSG.HardMathSupport.Lang.D4Three.DiagSquare
import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27D4AmbientForm
import CFSG.RankThree.Chevalley.SteinbergCBTrialityTransposition

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec8
  CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof

set_option linter.unusedSectionVars false


section Diag

open CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E6Descent
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.RecipeExcLang

variable {K : Type} [Field K] [Finite K]

private theorem coe_conj_mul_exactNormalAut_one' (g : adjointGroup Tag.D4 K)
    (a : Fin Tag.D4.rank → Kˣ) (h : adjointGroup Tag.D4 K) :
    ((MulAut.conj g * exactNormalAut Tag.D4 K a 1 0) h : ModGL Tag.D4 K) =
      ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a) * (h : ModGL Tag.D4 K) *
        ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a)⁻¹ := by
  have h1 : Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) (h : ModGL Tag.D4 K) = h := by
    have e1 : (1 : K ≃+* K).toRingHom = RingHom.id K := RingHom.ext fun _ => rfl
    rw [e1]
    exact Units.ext (entrywise_id (R := K) _)
  rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
    coe_exactNormalAut, exactQ_zero, h1]
  group

theorem d4_inner_of_diag_char_free (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ)
    (hα : (MulAut.conj g * exactNormalAut Tag.D4 K a 1 0) ^ 3 = 1) :
    ∃ h : adjointGroup Tag.D4 K, MulAut.conj g * exactNormalAut Tag.D4 K a 1 0 = MulAut.conj h := by
  set α := MulAut.conj g * exactNormalAut Tag.D4 K a 1 0 with hαdef
  have hγ : (g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a ∈ inndiagGroup Tag.D4 K :=
    mul_mem (adjointGroup_le_inndiagGroup g.2) (rootDiagUnit_mem_inndiagGroup a)
  have hsq := sq_mem_adjointGroup_of_mem_inndiagGroup hγ
  have hα2 : α ^ 2 = MulAut.conj ⟨_, hsq⟩ := by
    refine MulEquiv.ext fun h => Subtype.ext ?_
    rw [pow_two, MulAut.mul_apply, hαdef, coe_conj_mul_exactNormalAut_one',
      coe_conj_mul_exactNormalAut_one', MulAut.conj_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, pow_two]
    group
  have hinv : α = (α ^ 2)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ' α 2]
    exact hα
  exact ⟨_, by rw [hinv, hα2, ← map_inv]⟩

end Diag

section FieldType

variable {K : Type} [Field K] [Finite K]

theorem char3Good_fixSubgroup_entrywiseAdjointAut_D4 (hK3 : ringChar K = 3) (σ : K ≃+* K) :
    Char3Good ↥(fixSubgroup (entrywiseAdjointAut Tag.D4 σ)) := by
  classical
  haveI : Finite (ModGL Tag.D4 K) := finite_modGL
  haveI : Finite (fixSubfield σ) := Subtype.finite
  haveI : Finite (ModGL Tag.D4 (fixSubfield σ)) := finite_modGL
  haveI : Finite ↥(adjointGroup Tag.D4 (fixSubfield σ)) := Subtype.finite
  haveI : Finite ↥(adjointGroup Tag.D4 K) := Subtype.finite
  obtain ⟨hChev, hA6⟩ := isChevSimple_adjointGroup_D4 (K := fixSubfield σ)
  rw [ringChar_subfield hK3 (fixSubfield σ)] at hChev
  have hperf := ExcCopy.isPerfect_adjointGroup .D4 (fixSubfield σ) (fun h => absurd h (by decide))
  obtain ⟨hs, hnc⟩ := ExcCopy.isSimpleGroup_adjointGroup_of_perfect .D4 (fixSubfield σ) hperf
  obtain ⟨ι, hι, hJC, hnorm, hsol⟩ := ExcCopy.exists_fixed_structure Tag.D4 σ
  let J : Subgroup ↥(fixSubgroup (entrywiseAdjointAut Tag.D4 σ)) :=
    ι.range.subgroupOf (fixSubgroup (entrywiseAdjointAut Tag.D4 σ))
  haveI : J.Normal := hnorm
  let e : adjointGroup Tag.D4 (fixSubfield σ) ≃* ι.range := MonoidHom.ofInjective hι
  let eJ : ↥J ≃* adjointGroup Tag.D4 (fixSubfield σ) :=
    (Subgroup.subgroupOfEquivOfLe hJC).trans e.symm
  left
  refine ⟨J, inferInstance, eJ.isSimpleGroup_congr.2 hs, ?_, isChevSimple_congr eJ.symm hChev,
    ⟨fun f => hA6.false (eJ.symm.trans f)⟩, hsol⟩
  obtain ⟨x, y, hxy⟩ := hnc
  exact ⟨eJ.symm x, eJ.symm y, fun h => hxy (by simpa using congrArg eJ h)⟩

end FieldType

section Twisted

open CFSG.HardMathSupport.Lang.E6Descent CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.RecipeExcLang CFSG.RankThree.Chevalley CFSG.HardMathSupport.Lang.D4Three

variable {K : Type} [Field K] [Finite K]

theorem char3Good_of_equiv_cat_trialityD4 {C X : Type} [Group C] [Group X] [Finite X]
    [IsSimpleGroup X] (hnc : ∃ x y : X, x * y ≠ y * x) (q : TauCeti.PrimePower) (hq : q.p = 3)
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid)
    (eC : (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group ≃* X) (eF : C ≃* X) :
    Char3Good C := by
  haveI : Finite C := Finite.of_equiv X eF.symm.toEquiv
  haveI : IsSimpleGroup C := (MulEquiv.isSimpleGroup_congr eF).2 inferInstance
  have hnc' : ∃ x y : C, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hnc
    exact ⟨eF.symm x, eF.symm y, fun h => hxy (by simpa using congrArg eF h)⟩
  have hchev := isChevSimple_of_lie (q := 3) ⟨.trialityD4 q, hv⟩
    (by rw [TauCeti.LieTypeIndex.characteristic_trialityD4]; exact hq) (eF.trans eC.symm)
  exact Char3Good.of_simple hnc' hchev
    ⟨fun f => (isEmpty_cat_alt6 ⟨.trialityD4 q, hv⟩ (Or.inl rfl)).false
      ((eC.trans eF.symm).trans f)⟩

theorem char3Good_fixSubgroup_twistedEntrywiseAut_D4 [CharP K 3] {e : ℕ} (he : 1 ≤ e)
    (hK : Nat.card K = 3 ^ (e * 3)) (T : K ≃+* K) (hT : ∀ c, T c = c ^ (3 ^ e))
    (j : ℤ) (hj : j % 3 = 1 ∨ j % 3 = 2) :
    Char3Good ↥(fixSubgroup (twistedEntrywiseAut TwistTag.D4 j T)) := by
  classical
  let q : TauCeti.PrimePower := ⟨3, e, Nat.prime_three, he⟩
  have hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid := TauCeti.LieTypeIndex.valid_trialityD4 q
  have hKq : Nat.card K = q.card ^ 3 := by
    rw [hK, TauCeti.PrimePower.card_def, ← pow_mul]
  have hTq : ∀ c, T c = c ^ q.card := fun c => by rw [hT, TauCeti.PrimePower.card_def]
  obtain ⟨eC⟩ := catEquiv_trialityD4_of_field q hv K hKq T hTq
  have : Fintype K := Fintype.ofFinite K
  have hq3 : ∀ c : K, c ^ ((3 ^ e) ^ 3) = c := fun c => by
    rw [← pow_mul, ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hT3 : T ^ 3 = 1 := by
    refine RingEquiv.ext fun c => ?_
    change T (T (T c)) = c
    rw [hT, hT, hT, ← pow_mul, ← pow_mul, show 3 ^ e * (3 ^ e * 3 ^ e) = (3 ^ e) ^ 3 by ring, hq3]
  have hinv : ∀ c, T⁻¹ c = c ^ ((3 ^ e) ^ 2) := by
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
    exact char3Good_of_equiv_cat_trialityD4 hnc q rfl hv eC eF
  · rw [h]
    have hfix := fixedSubgroup_twistedEntrywiseAut_D4_two T
    obtain ⟨hs, hnc, ⟨eF⟩⟩ := exists_fixSubgroup_twistedOne_equiv he hK T⁻¹ 2 (Or.inr rfl) hinv
    haveI := hs
    let eT : ↥(graphFixedRootGroup TwistTag.D4 K T.toRingHom) ≃*
        ↥(graphFixedRootGroup TwistTag.D4 K T⁻¹.toRingHom) :=
      (Subgroup.equivMapOfInjective _ (trialityTranspositionAut K).toMonoidHom
        (trialityTranspositionAut K).injective).trans
        (MulEquiv.subgroupCongr (map_trialityTranspositionAut_graphFixedRootGroup T))
    refine Char3Good.of_mulEquiv (MulEquiv.subgroupCongr hfix) ?_
    exact char3Good_of_equiv_cat_trialityD4 hnc q rfl hv (eC.trans eT) eF

theorem char3Good_of_lang_D4 [CharP K 3] {e : ℕ} (he : 1 ≤ e)
    (hK : Nat.card K = 3 ^ (e * 3)) (T : K ≃+* K) (hT : ∀ c, T c = c ^ (3 ^ e))
    (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K)
    (hσT : σ = T ∨ σ = T⁻¹) (ε : ℕ)
    (hP : ∀ j : ℤ, (j = (ε : ℤ) ∨ j = -(ε : ℤ)) →
      Char3Good ↥(fixSubgroup (twistedEntrywiseAut TwistTag.D4 j T)))
    (hα : (MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε)) ^ 3 = 1) :
    Char3Good ↥(fixSubgroup (MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε))) := by
  haveI : Finite (ModGL Tag.D4 K) := finite_modGL
  haveI : Finite ↥(adjointGroup Tag.D4 K) := Subtype.finite
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 3 ^ 2 := Nat.pow_le_pow_left (by norm_num) 2
      _ ≤ 3 ^ (e * 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  set α := MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε) with hαdef
  rcases hσT with hσT | hσT
  · subst hσT
    obtain ⟨ψ, hψ⟩ := exists_conj_eq_twistedEntrywiseAut_of_normalForm K hK hK4 he rfl σ hT α hα
      g a ε hαdef
    have h := hP _ (Or.inl rfl)
    rw [← hψ] at h
    exact Char3Good.of_conj_aut ψ α h
  · subst hσT
    obtain ⟨ψ, hψ⟩ := exists_conj_inv_eq_twistedEntrywiseAut_of_normalForm K hK hK4 he rfl T T⁻¹
      hT (mul_inv_cancel T) α hα g a ε hαdef
    have h := hP _ (Or.inr rfl)
    rw [← hψ] at h
    exact Char3Good.of_inv α (Char3Good.of_conj_aut ψ α⁻¹ h)

end Twisted

section Assembly

open CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E6Descent

private theorem d4Graph_zero_D4' {K : Type} [Field K] [Finite K] : d4Graph K 0 = 1 :=
  MulEquiv.ext fun h => Subtype.ext (by
    rw [coe_d4Graph, pow_zero, one_mul, inv_one, mul_one]; rfl)

theorem char3Good_d4_graph_type {f : ℕ} (hf : 1 ≤ f) {F : Type} [Field F] [Finite F] [CharP F 3]
    (hF : Nat.card F = 3 ^ f) (g : adjointGroup Tag.D4 F) (a : Fin Tag.D4.rank → Fˣ)
    (σ : F ≃+* F) (hσ3 : σ ^ 3 = 1) {ε : ℕ} (hε : ε = 1 ∨ ε = 2)
    (hα : (MulAut.conj g * (exactNormalAut Tag.D4 F a σ 0 * d4Graph F ε)) ^ 3 = 1) :
    Char3Good ↥(fixSubgroup (MulAut.conj g * (exactNormalAut Tag.D4 F a σ 0 * d4Graph F ε))) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hσ1 : σ = 1
  · subst hσ1
    obtain ⟨K₃, _, _, Fr, hK₃, hFr, φ, hφ3, hφout, ⟨e⟩⟩ :=
      D4Dual.exists_dual_fixEquiv hf F hF _ hα g a hε rfl
    haveI : CharP K₃ 3 :=
      CFSG.HardMathSupport.Dickson.DefCharOuter.Export.exc_charP_three_of_card K₃ hK₃
    exact (char3Good_fixSubgroup_trialityD4 hf hK₃ Fr hFr φ hφ3 hφout).of_mulEquiv e
  · obtain ⟨ℓ', e, T, hℓ', hchar', he, hK, hT, hσT⟩ := exists_frobenius_data_D4 σ hσ1 hσ3
    obtain rfl : ℓ' = 3 := CharP.eq F hchar' ‹CharP F 3›
    haveI : Finite ↥(adjointGroup Tag.D4 F) := by
      haveI : Finite (ModGL Tag.D4 F) := finite_modGL
      infer_instance
    refine char3Good_of_lang_D4 he hK T hT g a σ hσT ε (fun j hj => ?_) hα
    refine char3Good_fixSubgroup_twistedEntrywiseAut_D4 he hK T hT j ?_
    rcases hε with rfl | rfl <;> rcases hj with rfl | rfl <;> omega

theorem char3Good_d4_outer {f : ℕ} (hf : 1 ≤ f) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 3 ^ f) (α : MulAut ↥(adjointGroup Tag.D4 F)) (hα : α ^ 3 = 1)
    (hout : ∀ h : adjointGroup Tag.D4 F, MulAut.conj h ≠ α) :
    Char3Good ↥(fixSubgroup α) := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  have hchF : CharP F 3 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hF])
  have hchar : ringChar F = 3 := ringChar.eq F 3
  haveI : Finite (ModGL Tag.D4 F) := finite_modGL
  haveI : Finite ↥(adjointGroup Tag.D4 F) := Subtype.finite
  obtain ⟨g, a, σ, ε, hε, hσ3, hαeq⟩ := exists_cube_normal_form_sigma α hα
  interval_cases ε
  · have hα' : α = MulAut.conj g * exactNormalAut Tag.D4 F a σ 0 := by
      rw [hαeq, d4Graph_zero_D4', mul_one]
    by_cases hσ1 : σ = 1
    · exfalso
      subst hσ1
      rw [hα'] at hα
      obtain ⟨h, hh⟩ := d4_inner_of_diag_char_free g a hα
      exact hout h (by rw [hα', hh])
    · rw [hα'] at hα
      obtain ⟨ψ, hψ⟩ := ExcCopy.exists_conj_eq_entrywiseAdjointAut .D4 Nat.prime_three g a σ hσ1
        hσ3 hα
      have hc := char3Good_fixSubgroup_entrywiseAdjointAut_D4 hchar σ
      rw [← hψ] at hc
      rw [hα']
      exact Char3Good.of_conj_aut ψ _ hc
  · rw [hαeq]
    exact char3Good_d4_graph_type hf hF g a σ hσ3 (Or.inl rfl) (hαeq ▸ hα)
  · rw [hαeq]
    exact char3Good_d4_graph_type hf hF g a σ hσ3 (Or.inr rfl) (hαeq ▸ hα)

theorem d4Char3Outer_holds : D4Char3Outer := by
  intro G _ _ f hG β hβ hout
  classical
  have hG' := hG
  obtain ⟨⟨hℓ, hf, -⟩, F, _, _, hF, ⟨eG⟩⟩ := hG'
  haveI : Fact (Nat.Prime 3) := ⟨hℓ⟩
  obtain ⟨eC⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_statedProj_equiv_adjointGroup F
  let e₂ : G ≃* ↥(adjointGroup Tag.D4 F) := eG.trans eC
  refine lieCompExport_or_noThreeComponents_of_char3Good β
    (Char3Good.of_mulEquiv (fixSubgroupCongrEquiv e₂ β) ?_)
  have hα : MulAut.congr e₂ β ^ 3 = 1 := by rw [← map_pow, hβ, map_one]
  have hout' : ∀ h : adjointGroup Tag.D4 F, MulAut.conj h ≠ MulAut.congr e₂ β := fun h hh => by
    apply hout (e₂.symm h)
    have hc : MulAut.congr e₂.symm (MulAut.conj h) = MulAut.conj (e₂.symm h) := by
      ext y
      simp [MulAut.congr_apply, MulAut.conj_apply]
    rw [← hc, hh]
    ext y
    simp [MulAut.congr_apply]
  exact char3Good_d4_outer hf hF (MulAut.congr e₂ β) hα hout'

end Assembly

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
