module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H1429SubTri

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.H1429Sub

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Dickson.DefCharOuter.Export
open CFSG.HardMathSupport.Dickson.DefCharOuter.Export.SporthD4
open CFSG.HardMathSupport.Dickson.I271 (coprime_ker_mulEquiv pSimpleEquiv)
open scoped commutatorElement

@[expose] def NoU42Sub {T : Type} [Group T] (C : Subgroup T) : Prop :=
  ∀ I : Subgroup T, GLAPComponent 3 C I → Nat.card (PSimple 3 I) ≠ 25920

theorem NoU42Sub.of_map_injective {S T : Type} [Group S] [Finite S] [Group T] (f : S →* T)
    (hf : Function.Injective f) {C : Subgroup S} (h : NoU42Sub (C.map f)) : NoU42Sub C := by
  intro I hI hc
  have hker : Nat.Coprime 3 (Nat.card ↥(C ⊓ f.ker)) := by
    rw [(MonoidHom.ker_eq_bot_iff f).2 hf, inf_bot_eq, Subgroup.card_bot]
    exact Nat.coprime_one_right 3
  have hI' := glaPComponent_map Nat.prime_three f hker hI
  exact h _ hI' ((Nat.card_congr (pSimpleEquiv 3 (I.equivMapOfInjective f hf)).toEquiv).symm.trans hc)

theorem NoU42Sub.map_injective {S T : Type} [Group S] [Finite S] [Group T] (f : S →* T)
    (hf : Function.Injective f) {C : Subgroup S} (h : NoU42Sub C) : NoU42Sub (C.map f) := by
  have hker : Nat.Coprime 3 (Nat.card ↥(C ⊓ f.ker)) := by
    rw [(MonoidHom.ker_eq_bot_iff f).2 hf, inf_bot_eq, Subgroup.card_bot]
    exact Nat.coprime_one_right 3
  intro I' hI' hc
  obtain ⟨I, hI, rfl⟩ := exists_glaPComponent_map_eq Nat.prime_three f hker hI'
  exact h I hI ((Nat.card_congr (pSimpleEquiv 3 (I.equivMapOfInjective f hf)).toEquiv).trans hc)

theorem NoU42At.of_pow {T : Type} [Group T] {β : MulAut T} (r : ℕ) (h : NoU42At (β ^ r))
    (hfix : fixSubgroup (β ^ r) = fixSubgroup β) : NoU42At β := by
  intro I hI
  exact h I (by rwa [hfix])

set_option linter.unusedSectionVars false

section Field

variable {K : Type} [Field K] [Finite K]

open CFSG.Assembly.LowTwoRank in
theorem noU42At_entrywise_D4 [CharP K 3] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 3 ^ f)
    (T : K ≃+* K) (hT3 : T ^ 3 = 1) (hT1 : T ≠ 1) :
    NoU42At (entrywiseAdjointAut Tag.D4 T) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hM : ringChar K ≠ 2 := by rw [ringChar.eq K 3]; norm_num
  set β := entrywiseAdjointAut Tag.D4 T with hβ
  have hk2 : ringChar (fixSubfield T) ≠ 2 := by
    intro h
    have h0 : ((2 : ℕ) : fixSubfield T) = 0 := by
      rw [← h]
      exact ringChar.Nat.cast_ringChar
    apply Ring.two_ne_zero hM
    have := congrArg (fixSubfield T).subtype h0
    rw [map_natCast, map_zero] at this
    exact_mod_cast this
  obtain ⟨hs, hnc, -⟩ := odd_pinned_Chevalley_p_components Tag.D4 (fixSubfield T) hk2
  obtain ⟨-, -, -, hJΓ, -, hnormal, -, hder⟩ :=
    Chevalley_coordinate_field_fixed_structure Tag.D4 K hM T
  have hJA : fixedFieldImage Tag.D4 T ≤ adjointGroup Tag.D4 K := hJΓ.trans inf_le_left
  have hΓ : ∀ n : ↥(fixSubgroup β), ((n : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) ∈
      entrywiseFixedGroup Tag.D4 T := fun n =>
    ⟨(n : ↥(adjointGroup Tag.D4 K)).2, by
      have h1 : β n = n := n.2
      have := congrArg Subtype.val h1
      rwa [coe_entrywiseAdjointAut] at this⟩
  set J : Subgroup ↥(adjointGroup Tag.D4 K) :=
    (fixedFieldImage Tag.D4 T).subgroupOf (adjointGroup Tag.D4 K) with hJ
  have hmemJ : ∀ x : ↥(adjointGroup Tag.D4 K), x ∈ J ↔ (x : ModGL Tag.D4 K) ∈
      fixedFieldImage Tag.D4 T := fun x => Iff.rfl
  have hJC : J ≤ fixSubgroup β := fun x hx => by
    rw [mem_fixSubgroup]
    refine Subtype.ext ?_
    rw [coe_entrywiseAdjointAut]
    exact (hJΓ ((hmemJ x).1 hx)).2
  haveI hJn : (J.subgroupOf (fixSubgroup β)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf, hmemJ] at hn ⊢
    have h1 := hnormal.conj_mem ⟨((n : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K), hΓ n⟩
      (Subgroup.mem_subgroupOf.2 hn) ⟨((g : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K), hΓ g⟩
    simpa using Subgroup.mem_subgroupOf.1 h1
  let eJ : ↥J ≃* adjointGroup Tag.D4 (fixSubfield T) :=
    (Subgroup.subgroupOfEquivOfLe hJA).trans (fixedFieldImageEquiv T).symm
  haveI := hs
  haveI hJs : IsSimpleGroup ↥J := eJ.isSimpleGroup
  have hncJ : ∃ x y : ↥J, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hnc
    exact ⟨eJ.symm x, eJ.symm y, fun h => hxy (by simpa using congrArg eJ h)⟩
  have hsol : Group.IsSolvable (↥(fixSubgroup β) ⧸ J.subgroupOf (fixSubgroup β)) := by
    refine Group.isSolvable_of_comm fun a b => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have h1 : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by simp [commutatorElement_def, mul_assoc]
    rw [h1, Subgroup.mem_subgroupOf, hmemJ]
    have h2 : (((⁅y⁻¹, x⁻¹⁆ : ↥(fixSubgroup β)) : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) =
        ⁅(((y⁻¹ : ↥(fixSubgroup β)) : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K),
          (((x⁻¹ : ↥(fixSubgroup β)) : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K)⁆ := by
      simp [commutatorElement_def]
    rw [h2, ← hder]
    exact Subgroup.commutator_mem_commutator (hΓ _) (hΓ _)
  have hordT : orderOf T = 3 := orderOf_eq_prime hT3 hT1
  obtain ⟨hdvd3, hkcard⟩ :=
    CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield Nat.prime_three hf hK T
  rw [hordT] at hdvd3 hkcard
  have hfp : 1 ≤ f / 3 := Nat.div_pos (Nat.le_of_dvd hf hdvd3) (by norm_num)
  obtain ⟨Φ⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_statedProj_equiv_adjointGroup
      (fixSubfield T)
  have hmodelJ : StatedClassicalModel ↥J .POmegaPlus 4 3 (f / 3) :=
    ⟨⟨Nat.prime_three, hfp, le_rfl⟩, ↥(fixSubfield T), inferInstance, inferInstance, hkcard,
      ⟨eJ.trans Φ.symm⟩⟩
  have ht : (StatedLieTag.POmegaPlus = .PSp ∧ 2 ≤ 4) ∨
      (StatedLieTag.POmegaPlus = .POmegaOdd ∧ 3 ≤ 4) ∨
      (StatedLieTag.POmegaPlus = .POmegaPlus ∧ 4 ≤ 4) ∨
      (StatedLieTag.POmegaPlus = .POmegaMinus ∧ 4 ≤ 4) := Or.inr (Or.inr (Or.inl ⟨rfl, le_rfl⟩))
  have hdvdJ : 3 ∣ Nat.card ↥J := Sporth.dvd_card hmodelJ ht
  intro I hI hc
  obtain ⟨e⟩ := exists_equiv_of_conj (MulEquiv.refl _) (β := β) (a := β) rfl hJC hsol hJs hncJ
    hdvdJ hI
  have hmodelI : StatedClassicalModel (PSimple 3 I) .POmegaPlus 4 3 (f / 3) :=
    CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm hmodelJ
  obtain ⟨ht', -, -⟩ := finish_classical_card hmodelI hc
  exact absurd ht' (by decide)

end Field

section GraphField

variable {K : Type} [Field K] [Finite K]

open CFSG.EvenSmallLie.CatalogOrders CFSG.Assembly.LowTwoRank in
theorem noU42At_alphaOne [CharP K 3] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 3 ^ f)
    (σ : K ≃+* K) (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1) : NoU42At (alphaOne σ) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hM : ringChar K ≠ 2 := by rw [ringChar.eq K 3]; norm_num
  have hσσσ : ∀ c, σ (σ (σ c)) = c := fun c => by
    have h := congrArg (fun g : K ≃+* K => g c) hσ3
    simpa [pow_succ] using h
  obtain ⟨hs, hnc, -⟩ := odd_diagram_field_fixed_p_components TwistTag.D4 K hM σ
  obtain ⟨hnormal, -, hcomm, -, -⟩ := fixed_root_generated_normal_subgroup TwistTag.D4 K σ
  have hC0Γ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≤
      twistedFixedGroup TwistTag.D4 K σ.toRingHom := graphFixedRootGroup_le _ _ _
  have hΓA : twistedFixedGroup TwistTag.D4 K σ.toRingHom ≤ adjointGroup Tag.D4 K :=
    twistedFixedGroup_le_adjointGroup _ _ _
  have hC0A : graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≤ adjointGroup Tag.D4 K :=
    hC0Γ.trans hΓA
  have hfix : fixSubgroup (alphaOne σ) =
      (twistedFixedGroup TwistTag.D4 K σ.toRingHom).subgroupOf (adjointGroup Tag.D4 K) := by
    rw [← twistedEntrywiseAut_one_eq]
    exact CFSG.HardMathSupport.Lang.E6Descent.fixedSubgroup_twistedEntrywiseAut_one TwistTag.D4 σ
  have hnormal' := (Subgroup.normal_subgroupOf_iff hC0Γ).1 hnormal
  set J : Subgroup ↥(adjointGroup Tag.D4 K) :=
    (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subgroupOf (adjointGroup Tag.D4 K) with hJdef
  set N : Subgroup ↥(adjointGroup Tag.D4 K) :=
    (twistedFixedGroup TwistTag.D4 K σ.toRingHom).subgroupOf (adjointGroup Tag.D4 K) with hNdef
  have hJN : J ≤ N := fun x hx => hC0Γ hx
  have hJn : (J.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff hJN).2 fun h k hh hk => hnormal' _ _ hh hk
  let eJ : ↥J ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    Subgroup.subgroupOfEquivOfLe hC0A
  haveI := hs
  haveI hJs : IsSimpleGroup ↥J := eJ.isSimpleGroup
  have hncJ : ∃ x y : ↥J, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hnc
    refine ⟨eJ.symm x, eJ.symm y, fun h => hxy ?_⟩
    have h' := congrArg eJ h
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h'
  have hmemJ : ∀ x : ↥(adjointGroup Tag.D4 K), x ∈ J ↔ (x : ModGL Tag.D4 K) ∈
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom := fun x => Iff.rfl
  have hΓmem : ∀ n : ↥N, ((n : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) ∈
      twistedFixedGroup TwistTag.D4 K σ.toRingHom := fun n => n.2
  have hsol : Group.IsSolvable (↥N ⧸ J.subgroupOf N) := by
    refine Group.isSolvable_of_comm fun a b => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have h1 : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by simp [commutatorElement_def, mul_assoc]
    rw [h1, Subgroup.mem_subgroupOf, hmemJ]
    have h2 : (((⁅y⁻¹, x⁻¹⁆ : ↥N) : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) =
        ⁅(((y⁻¹ : ↥N) : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K),
          (((x⁻¹ : ↥N) : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K)⁆ := by
      simp [commutatorElement_def]
    rw [h2]
    exact hcomm (Subgroup.commutator_mem_commutator (hΓmem _) (hΓmem _))
  obtain ⟨d, T, hd0, hdf, hT, -, hσT⟩ :=
    CFSG.HardMathSupport.Lang.E6Descent.exists_frobenius_of_cube Nat.prime_three hf K hK σ hσ3 hσ1
  have hk3 : Nat.card K = (3 ^ d) ^ 3 := by rw [hK, ← hdf, pow_mul]
  have hσ₀ : (∀ c, σ c = c ^ 3 ^ d) ∨ ∀ c, σ c = c ^ (3 ^ d) ^ 2 := by
    rcases hσT with h | h
    · exact Or.inl fun c => by rw [h]; exact hT c
    · refine Or.inr fun c => ?_
      rw [h, pow_two, RingAut.mul_apply, hT, hT, ← pow_mul, sq]
  have hLM := CFSG.ComponentClassification.CatLeafProof.lieModel_graphFixedRootGroup_trialityD4_odd
    Nat.prime_three (by norm_num) hd0 hk3 σ hσ₀
  have hCEM := CFSG.Blueprint.LieModel.chevalleyExceptionalModel hLM (by decide)
  obtain ⟨-, hdvd0, -⟩ := excModel_facts (t := .trialityD4) (by decide) (by norm_num) hCEM
  have hdvdJ : 3 ∣ Nat.card ↥J := by rw [Nat.card_congr eJ.toEquiv]; exact hdvd0
  intro I hI hc
  rw [hfix] at hI
  have hIJ := eq_of_component hJN hsol hJs hI
  rw [hIJ] at hc
  have hcard : Nat.card (PSimple 3 J) =
      Nat.card (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    Nat.card_congr ((pSimple_equiv_self hJs hncJ hdvdJ).trans eJ).toEquiv
  have hc' : Nat.card (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = 25920 := hcard.symm.trans hc
  have hord := card_eq_lieOrd_of_exceptional hCEM
  have hpow := pow_lieExp_dvd (t := .trialityD4) (n := 0) (by simp [lieMin]) (3 ^ d)
  rw [← hord, hc'] at hpow
  have h12 : 3 ^ 12 ∣ 25920 := by
    refine (pow_dvd_pow_of_dvd (dvd_pow_self 3 (Nat.pos_iff_ne_zero.1 hd0)) 12).trans ?_
    simpa [lieExp] using hpow
  norm_num at h12

end GraphField

section Graph

open CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E6Descent
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4Aux
  CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3

theorem noU42At_d4_graphOne {K : Type} [Field K] [Finite K] [CharP K 3]
    (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ)
    (α : MulAut (adjointGroup Tag.D4 K))
    (hαdef : α = MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K 1))
    (hα3 : α ^ 3 = 1) : NoU42At α := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨f, hf, hKf⟩ : ∃ f : ℕ, 1 ≤ f ∧ Nat.card K = 3 ^ f := by
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 3
    exact ⟨n, n.pos, by rw [Nat.card_eq_fintype_card, hn]⟩
  obtain ⟨K₃, hF₃, hFin₃, hAlg, Fr, hK₃, hFr, ψ, φ, -, hφ3, hφo, -, hfix1, hfix2, -, -⟩ :=
    dual_data_one (ℓ := 3) hf K hKf α hα3 g a hαdef
  have hchar : CharP K₃ 3 :=
    charP_of_injective_algebraMap (algebraMap K K₃).injective 3
  haveI : Finite (graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) :=
    finite_graphFixedRootGroup_D4 Fr
  have hφfix : NoU42At φ := noU42At_trialityD4_three hf hK₃ Fr hFr φ hφ3 hφo
  have hinjA : Function.Injective (baseChangeAdj (algebraMap K K₃)) := fun u u' h =>
    Subtype.ext (baseChangeGL_injective _ (congrArg Subtype.val h))
  let ι' : adjointGroup Tag.D4 K →* adjointGroup Tag.D4 K₃ :=
    (ψ : adjointGroup Tag.D4 K₃ ≃* adjointGroup Tag.D4 K₃).toMonoidHom.comp
      (baseChangeAdj (algebraMap K K₃))
  have hι' : Function.Injective ι' := ψ.injective.comp hinjA
  have hmap : (fixSubgroup α).map ι' =
      (fixSubgroup φ).map (graphFixedInclusion K₃ Fr) := by
    ext z
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨y, hy1, hy2⟩ := hfix1 ⟨u, hu⟩
      exact ⟨y, hy2, hy1⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨u, hu⟩ := hfix2 y hy
      exact ⟨u.1, u.2, hu.symm⟩
  haveI : Finite (adjointGroup Tag.D4 K) := by
    haveI : Finite (ModGL Tag.D4 K) := finite_modGL
    infer_instance
  refine NoU42Sub.of_map_injective ι' hι' ?_
  rw [hmap]
  exact NoU42Sub.map_injective (graphFixedInclusion K₃ Fr)
    (graphFixedInclusion_injective' K₃ Fr) hφfix

theorem noU42At_d4_graph {K : Type} [Field K] [Finite K] [CharP K 3] (g : adjointGroup Tag.D4 K)
    (a : Fin Tag.D4.rank → Kˣ) (ε : ℕ) (hε0 : 0 < ε) (hε3 : ε < 3)
    (α : MulAut (adjointGroup Tag.D4 K))
    (hα : α = MulAut.conj g * (exactNormalAut Tag.D4 K a (RingEquiv.refl K) 0 * d4Graph K ε))
    (hα3 : α ^ 3 = 1) : NoU42At α := by
  have hrefl : (RingEquiv.refl K) = (1 : K ≃+* K) := rfl
  rw [hrefl] at hα
  interval_cases ε
  · exact noU42At_d4_graphOne g a α hα hα3
  · obtain ⟨g', a', hinv⟩ := GraphCorrespondence.inv_normalForm g a
    rw [← hα] at hinv
    exact NoU42At.of_inv (noU42At_d4_graphOne g' a' α⁻¹ hinv (by rw [inv_pow, hα3, inv_one]))

end Graph

end CFSG.LocalAnalysis.GLTheoremA.H1429Sub

end
