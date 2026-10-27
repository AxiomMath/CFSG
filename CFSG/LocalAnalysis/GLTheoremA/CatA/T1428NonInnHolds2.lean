module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.D4Outer
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27D4AmbientForm
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GTriLab

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T1428NonInn

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E6Descent
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartTwo
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.Assembly.RankThreeEven (projImage)
open scoped commutatorElement

@[expose] def NonInnCore (H : Type) [Group H] : Prop :=
  Group.IsSolvable H ∨
    ∃ (N : Subgroup H) (_ : N.Normal), IsSimpleGroup ↥N ∧ Group.IsSolvable (H ⧸ N)

theorem NonInnCore.of_mulEquiv {H H' : Type} [Group H] [Group H'] (h : NonInnCore H')
    (e : H ≃* H') : NonInnCore H := by
  rcases h with hsol | ⟨N, hN, hs, hsol⟩
  · haveI := hsol
    exact Or.inl (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)
  · right
    have hmap : (N.comap e.toMonoidHom).map e.toMonoidHom = N :=
      Subgroup.map_comap_eq_self_of_surjective e.surjective N
    haveI := hN
    haveI : (N.comap e.toMonoidHom).Normal := hN.comap _
    haveI := hs
    haveI := hsol
    refine ⟨N.comap e.toMonoidHom, inferInstance, ?_, ?_⟩
    · exact (((N.comap e.toMonoidHom).equivMapOfInjective e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr hmap)).isSimpleGroup
    · exact Group.isSolvable_of_isSolvable_injective
        (f := (QuotientGroup.congr (N.comap e.toMonoidHom) N e hmap).toMonoidHom)
        (QuotientGroup.congr (N.comap e.toMonoidHom) N e hmap).injective

theorem nonInnCore_of_isSolvable {H : Type} [Group H] [Group.IsSolvable H] : NonInnCore H :=
  Or.inl inferInstance

theorem nonInnCore_of_normal_simple {H : Type} [Group H] (N : Subgroup H) [N.Normal]
    (hs : IsSimpleGroup ↥N) (hsol : Group.IsSolvable (H ⧸ N)) : NonInnCore H :=
  Or.inr ⟨N, inferInstance, hs, hsol⟩

theorem nonInnCore_of_simple {H : Type} [Group H] [IsSimpleGroup H] : NonInnCore H := by
  haveI : Subsingleton (H ⧸ (⊤ : Subgroup H)) := QuotientGroup.subsingleton_quotient_top
  exact nonInnCore_of_normal_simple ⊤ (Subgroup.topEquiv.isSimpleGroup_congr.2 inferInstance)
    inferInstance

theorem nonInnCore_of_commutator {H : Type} [Group H] (hs : IsSimpleGroup ↥(commutator H)) :
    NonInnCore H := by
  refine nonInnCore_of_normal_simple (commutator H) hs (Group.isSolvable_of_comm fun a b => ?_)
  induction a using QuotientGroup.induction_on with | H x => ?_
  induction b using QuotientGroup.induction_on with | H y => ?_
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  have hxy : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by
    rw [commutatorElement_def]
    group
  rw [hxy, commutator_def]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

private theorem eq_bot_of_perfect_of_isSolvable' {H : Type} [Group H] [Group.IsSolvable H]
    {P : Subgroup H} (hP : ⁅P, P⁆ = P) : P = ⊥ := by
  have hle : ∀ n, P ≤ derivedSeries H n := by
    intro n
    induction n with
    | zero => exact le_top
    | succ n ih =>
      rw [derivedSeries_succ, ← hP]
      exact Subgroup.commutator_mono ih ih
  obtain ⟨n, hn⟩ := (inferInstance : Group.IsSolvable H).solvable
  exact le_bot_iff.mp (hn ▸ hle n)

theorem not_glaPComponent_of_isSolvable {T : Type} [Group T] [Finite T] {C J : Subgroup T}
    (hsol : Group.IsSolvable ↥C) {p : ℕ} (hJ : GLAPComponent p C J) : False := by
  have hJC : J ≤ C := hJ.1
  have hJ0 : ⁅J.subgroupOf C, J.subgroupOf C⁆ = J.subgroupOf C := by
    apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hJC]
    exact CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ
  haveI := hsol
  have hbot := eq_bot_of_perfect_of_isSolvable' hJ0
  apply CFSG.LocalAnalysis.GLTheoremA.glaPComponent_ne_bot' hJ
  rw [← Subgroup.map_subgroupOf_eq_of_le hJC, hbot, Subgroup.map_bot]

theorem NonInnCore.pComponent_eq {T : Type} [Group T] [Finite T] {C : Subgroup T}
    (h : NonInnCore ↥C) {p : ℕ} {J₁ J₂ : Subgroup T} (h₁ : GLAPComponent p C J₁)
    (h₂ : GLAPComponent p C J₂) : J₁ = J₂ := by
  rcases h with hsol | ⟨N, hN, hs, hsol⟩
  · exact (not_glaPComponent_of_isSolvable hsol h₁).elim
  · haveI := hN
    haveI := hs
    have hN'C : N.map C.subtype ≤ C := Subgroup.map_subtype_le N
    have hN'eq : (N.map C.subtype).subgroupOf C = N :=
      Subgroup.comap_map_eq_self_of_injective C.subtype_injective N
    haveI : ((N.map C.subtype).subgroupOf C).Normal := by
      rw [hN'eq]
      exact hN
    have hsol' : Group.IsSolvable (↥C ⧸ (N.map C.subtype).subgroupOf C) := by
      haveI := hsol
      exact Group.isSolvable_of_isSolvable_injective
        (f := (QuotientGroup.quotientMulEquivOfEq hN'eq).toMonoidHom)
        (QuotientGroup.quotientMulEquivOfEq hN'eq).injective
    have hs' : IsSimpleGroup ↥(N.map C.subtype) :=
      (N.equivMapOfInjective C.subtype C.subtype_injective).symm.isSimpleGroup
    rw [Y10GFldOrth.FOB.eq_of_component hN'C hsol' hs' h₁,
      Y10GFldOrth.FOB.eq_of_component hN'C hsol' hs' h₂]

section Models

set_option linter.unusedSectionVars false


theorem nonInnCore_G2 {f : ℕ} (hf : 1 ≤ f) {F₀ : Type} [Field F₀] [Finite F₀]
    (hF₀ : Nat.card F₀ = 2 ^ f) : NonInnCore ↥(adjointGroup Tag.G2 F₀) := by
  by_cases hf2 : 2 ≤ f
  · obtain ⟨hG, -⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GTri.tri_g2_simple hf2 hF₀
    haveI := hG
    exact nonInnCore_of_simple
  · have hk : Nat.card F₀ = 2 := by
      rw [hF₀, show f = 1 by omega, pow_one]
    obtain ⟨-, -, hs⟩ := CFSG.LieType.Catalog.lieModel_finite_simple _ _ _ _ _
      (CFSG.Quasithin.EmptyFaithfulMultiple.g2TwoDerivedUnitaryTransport_holds F₀ hk)
    have hDM : (commutator ↥(adjointGroup Tag.G2 F₀)).map (adjointGroup Tag.G2 F₀).subtype =
        ⁅adjointGroup Tag.G2 F₀, adjointGroup Tag.G2 F₀⁆ := by
      rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    let eD : ↥(commutator ↥(adjointGroup Tag.G2 F₀)) ≃*
        ↥⁅adjointGroup Tag.G2 F₀, adjointGroup Tag.G2 F₀⁆ :=
      ((commutator ↥(adjointGroup Tag.G2 F₀)).equivMapOfInjective _
        (adjointGroup Tag.G2 F₀).subtype_injective).trans (MulEquiv.subgroupCongr hDM)
    haveI := hs
    exact nonInnCore_of_commutator eD.isSimpleGroup

theorem nonInnCore_PGL {π : Bool} {f : ℕ} {F : Type} [Field F] (hF : Sec4.PiField π 2 f F)
    (hπ2 : π = true → 2 < 2 ^ f) : NonInnCore ↥(projImage (Sec4.glPi π 3 (2 ^ f) F)) := by
  have := hF.finite
  by_cases hq2 : 2 < 2 ^ f
  · have hπ : π = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f F := fun h => by
      subst h
      exact hF.unitary
    have hSP : projImage (Sec4.slPi π 3 (2 ^ f) F) ≤ projImage (Sec4.glPi π 3 (2 ^ f) F) :=
      Subgroup.map_mono (Sec4.slPi_le_glPi hπ)
    haveI : IsSimpleGroup (projImage (Sec4.slPi π 3 (2 ^ f) F)) :=
      Sec8.Item8KFacts2Proof.isSimpleGroup_projImage_slPi hF hq2
    have hcomm := Sec13.commutator_projImage_glPi hF hq2
    let eP : ↥(commutator ↥(projImage (Sec4.glPi π 3 (2 ^ f) F))) ≃*
        ↥(projImage (Sec4.slPi π 3 (2 ^ f) F)) :=
      (MulEquiv.subgroupCongr hcomm).trans (Subgroup.subgroupOfEquivOfLe hSP)
    exact nonInnCore_of_commutator eP.isSimpleGroup
  · have h2 : 2 ^ f = 2 := by
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hF.one_le
      omega
    cases π
    · haveI := Sec13.isSolvable_projImage_glPi_two hF h2
      exact nonInnCore_of_isSolvable
    · exact absurd (hπ2 rfl) hq2

end Models

section Triality

set_option linter.unusedSectionVars false


theorem nonInnCore_triality_outer {f : ℕ} (hf : 1 ≤ f) {K₃ : Type} [Field K₃] [Finite K₃]
    (hK₃ : Nat.card K₃ = (2 ^ f) ^ 3) (Fr : K₃ ≃+* K₃) (hFr : ∀ c, Fr c = c ^ (2 ^ f))
    (φ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)) (hφ3 : φ ^ 3 = 1)
    (hφ : φ ∉ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) →*
      MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)).range) :
    NonInnCore ↥(fixSubgroup φ) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hF : Nat.card (fixSubfield Fr) = 2 ^ f :=
    CFSG.GH74.GLS.Stage4.Hex.card_fixedField_of_cube Fr.toRingHom hq hK₃ hFr
  haveI : Finite (fixSubfield Fr) := Subtype.finite
  have hG2 : ↥(fixSubgroup (fieldActor (t := TwistTag.D4) Fr Fr)) ≃*
      ↥(adjointGroup Tag.G2 (fixSubfield Fr)) :=
    (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_fixSubgroup_fieldActor_equiv_G2
      (ℓ := 2) (by norm_num) hf (Or.inl rfl) hK₃ Fr hFr).some
  have hcG2 : NonInnCore ↥(fixSubgroup (fieldActor (t := TwistTag.D4) Fr Fr)) :=
    (nonInnCore_G2 hf hF).of_mulEquiv hG2
  rcases Sec8.Item8KFacts2Proof.isStdGraphFieldConj_or_nonempty_autFix_equiv hf hK₃ hFr hφ3 hφ with
    ⟨β, hβ | hβ⟩ | ⟨e₂⟩
  · rw [hβ]
    exact hcG2.of_mulEquiv
      (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroupConjEquiv β _).symm
  · rw [hβ]
    exact (hcG2.of_mulEquiv (MulEquiv.subgroupCongr
      (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.fixSubgroup_inv_eq _))).of_mulEquiv
      (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroupConjEquiv β _).symm
  · have hfixφ : fixSubgroup φ = Sec4.autFix φ := Subgroup.ext fun _ => Iff.rfl
    let ef : ↥(fixSubgroup φ) ≃* ↥(Sec4.autFix φ) := MulEquiv.subgroupCongr hfixφ
    rcases Nat.even_or_odd f with hfe | hfo
    · obtain ⟨F, _, _, hF', ⟨e₃⟩⟩ := Sec8.kF82D4SecondCentY0Even_holds f hfe hf K₃ Fr hK₃ hFr
      have hf2 : 2 ≤ f := by
        obtain ⟨k, hk⟩ := hfe
        omega
      have h2 : 2 < 2 ^ f :=
        lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf2)
      exact (nonInnCore_PGL (π := true) ⟨Nat.prime_two, hf, hF'⟩ fun _ => h2).of_mulEquiv
        (ef.trans (e₂.some.trans e₃))
    · obtain ⟨F, _, _, hF', ⟨e₃⟩⟩ := Sec8.kF82D4SecondCentY0_holds f hfo K₃ Fr hK₃ hFr
      exact (nonInnCore_PGL (π := false) ⟨Nat.prime_two, hf, hF'⟩
        fun h => absurd h (by decide)).of_mulEquiv (ef.trans (e₂.some.trans e₃))

end Triality

section D4

set_option linter.unusedSectionVars false


variable {K : Type} [Field K] [Finite K]

private theorem t1428NonInn_d4Graph_zero : d4Graph K 0 = 1 :=
  MulEquiv.ext fun h => Subtype.ext (by
    rw [coe_d4Graph, pow_zero, one_mul, inv_one, mul_one]; rfl)

theorem nonInnCore_entrywise_D4 (σ : K ≃+* K) :
    NonInnCore ↥(fixSubgroup (entrywiseAdjointAut Tag.D4 σ)) := by
  classical
  haveI : Finite (fixSubfield σ) := Subtype.finite
  obtain ⟨ι, hι, hJC, hnorm, hsol⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ExcCopy.exists_fixed_structure .D4 σ
  have hperf := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ExcCopy.isPerfect_adjointGroup .D4
    (fixSubfield σ) (fun h => absurd h (by decide))
  obtain ⟨hs, -⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ExcCopy.isSimpleGroup_adjointGroup_of_perfect
      .D4 (fixSubfield σ) hperf
  haveI := hs
  haveI := hnorm
  let e : adjointGroup Tag.D4 (fixSubfield σ) ≃* ι.range := MonoidHom.ofInjective hι
  exact nonInnCore_of_normal_simple _ ((Subgroup.subgroupOfEquivOfLe hJC).trans e.symm).isSimpleGroup
    hsol

theorem nonInnCore_twisted_D4 {ℓ e : ℕ} [Fact ℓ.Prime] [CharP K ℓ] (he : 1 ≤ e)
    (hK : Nat.card K = ℓ ^ (e * 3)) (T : K ≃+* K) (hT : ∀ c, T c = c ^ (ℓ ^ e)) (j : ℤ)
    (hj : j % 3 = 1 ∨ j % 3 = 2) :
    NonInnCore ↥(fixSubgroup (twistedEntrywiseAut TwistTag.D4 j T)) := by
  classical
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
    obtain ⟨hs, -, ⟨eF⟩⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_fixSubgroup_twistedOne_equiv he hK T 1
        (Or.inl rfl) (fun c => by rw [hT, pow_one])
    haveI := hs
    exact NonInnCore.of_mulEquiv nonInnCore_of_simple eF
  · rw [h]
    have hfix := fixedSubgroup_twistedEntrywiseAut_D4_two T
    obtain ⟨hs, -, ⟨eF⟩⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_fixSubgroup_twistedOne_equiv he hK T⁻¹ 2
        (Or.inr rfl) hinv
    haveI := hs
    exact (NonInnCore.of_mulEquiv nonInnCore_of_simple eF).of_mulEquiv (MulEquiv.subgroupCongr hfix)

theorem nonInnCore_of_lang_D4 {ℓ e : ℕ} [Fact ℓ.Prime] [CharP K ℓ] (he : 1 ≤ e)
    (hK : Nat.card K = ℓ ^ (e * 3)) (T : K ≃+* K) (hT : ∀ c, T c = c ^ (ℓ ^ e))
    (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K)
    (hσT : σ = T ∨ σ = T⁻¹) (ε : ℕ)
    (hP : ∀ j : ℤ, (j = (ε : ℤ) ∨ j = -(ε : ℤ)) →
      NonInnCore ↥(fixSubgroup (twistedEntrywiseAut TwistTag.D4 j T)))
    (hα : (MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε)) ^ 3 = 1) :
    NonInnCore ↥(fixSubgroup (MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε))) := by
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
    exact h.of_mulEquiv (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroupConjEquiv ψ α)
  · subst hσT
    obtain ⟨ψ, hψ⟩ := exists_conj_inv_eq_twistedEntrywiseAut_of_normalForm K hK hK4 he rfl T T⁻¹
      hT (mul_inv_cancel T) α hα g a ε hαdef
    have h := hP _ (Or.inr rfl)
    rw [← hψ] at h
    exact (h.of_mulEquiv
      (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroupConjEquiv ψ α⁻¹)).of_mulEquiv
      (MulEquiv.subgroupCongr
        (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.fixSubgroup_inv_eq α).symm)

theorem nonInnCore_d4_graph_type {f : ℕ} (hf : 1 ≤ f) [CharP K 2] (hKf : Nat.card K = 2 ^ f)
    (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) (hσ3 : σ ^ 3 = 1)
    {ε : ℕ} (hε : ε = 1 ∨ ε = 2)
    (hα : (MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε)) ^ 3 = 1) :
    NonInnCore ↥(fixSubgroup (MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε))) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hσ1 : σ = 1
  · subst hσ1
    obtain ⟨K₃, _, _, Fr, hK₃, hFr, φ, hφ3, hφout, ⟨e⟩⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual.exists_dual_fixEquiv hf K hKf _
        hα g a hε rfl
    exact (nonInnCore_triality_outer hf hK₃ Fr hFr φ hφ3 hφout).of_mulEquiv e
  · obtain ⟨ℓ', e, T, hℓ', hchar', he, hK, hT, hσT⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_frobenius_data_D4 σ hσ1 hσ3
    obtain rfl : ℓ' = 2 := CharP.eq K hchar' ‹CharP K 2›
    refine nonInnCore_of_lang_D4 he hK T hT g a σ hσT ε (fun j hj => ?_) hα
    refine nonInnCore_twisted_D4 he hK T hT j ?_
    rcases hε with rfl | rfl <;> rcases hj with rfl | rfl <;> omega

theorem nonInnCore_d4 [CharP K 2] (α : MulAut ↥(adjointGroup Tag.D4 K)) (hα : α ^ 3 = 1)
    (hout : ∀ h : ↥(adjointGroup Tag.D4 K), MulAut.conj h ≠ α) : NonInnCore ↥(fixSubgroup α) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  have hKn : Nat.card K = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have hchar : ringChar K ≠ 3 := by
    rw [ringChar.eq K 2]
    norm_num
  obtain ⟨g, a, σ, ε, hε, hσ3, hαeq⟩ := exists_cube_normal_form_sigma α hα
  interval_cases ε
  · have hα' : α = MulAut.conj g * exactNormalAut Tag.D4 K a σ 0 := by
      rw [hαeq, t1428NonInn_d4Graph_zero, mul_one]
    by_cases hσ1 : σ = 1
    · exfalso
      subst hσ1
      rw [hα'] at hα
      obtain ⟨h, hh⟩ :=
        CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.d4_inner_of_diag hchar g a hα
      exact hout h (by rw [hα', hh])
    · rw [hα'] at hα
      obtain ⟨ψ, hψ⟩ :=
        CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ExcCopy.exists_conj_eq_entrywiseAdjointAut
          .D4 Nat.prime_three g a σ hσ1 hσ3 hα
      have hc := nonInnCore_entrywise_D4 σ
      rw [← hψ] at hc
      rw [hα']
      exact hc.of_mulEquiv
        (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroupConjEquiv ψ _)
  · rw [hαeq]
    exact nonInnCore_d4_graph_type n.pos hKn g a σ hσ3 (Or.inl rfl) (hαeq ▸ hα)
  · rw [hαeq]
    exact nonInnCore_d4_graph_type n.pos hKn g a σ hσ3 (Or.inr rfl) (hαeq ▸ hα)

end D4

end CFSG.LocalAnalysis.GLTheoremA.T1428NonInn

end
