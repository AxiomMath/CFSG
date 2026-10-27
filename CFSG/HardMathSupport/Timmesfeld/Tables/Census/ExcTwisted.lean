module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.SL2Witness
public import CFSG.RankThree.PartTwo.Census.Exceptional.TwistedE6
public import CFSG.Adapters.TauCetiExceptional.EvenAll
public import CFSG.RankThree.Chevalley.SteinbergCFTrialityCommutingSL2
public import CFSG.LargeExtraspecial.DWRtTwisted
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.GraphTwisted
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.AmbientGroup
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Classification

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.Census

open CFSG.RankThree.PartTwo.Census.Exceptional CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.TauCetiBridge TauCeti

theorem nonempty_derivedCentralQuotient_equiv' {G : Type} [Group G] (H C : Subgroup G)
    (h : ⁅H, H⁆ = C) (hZ : Subgroup.center C = ⊥) :
    Nonempty (CFSG.Blueprint.DerivedCentralQuotient H ≃* C) := by
  subst h
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot⟩

theorem exists_injective_sl2_trialityD4
    (q : PrimePower) (hv : (LieTypeIndex.trialityD4 q).Valid) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : Nat.card F = q.card)
      (φ : SL2 F →* ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩), Function.Injective φ := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨K, _, _, hK, hKchar⟩ : ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = (q.p ^ q.exponent) ^ TwistTag.D4.order ∧ CharP K q.p :=
    ⟨GaloisField q.p (q.exponent * TwistTag.D4.order), inferInstance, inferInstance, by
      rw [GaloisField.card _ _ (Nat.mul_pos q.exponent_pos TwistTag.D4.order_pos).ne', pow_mul],
      inferInstance⟩
  obtain ⟨σ, hσ'', hord, -, -, k, hk, hkcard, -⟩ :=
    finite_graph_field_parameter_fields TwistTag.D4 q.prime_p q.exponent_pos K hK
  have hσo : σ ^ 3 = 1 := by
    rw [show 3 = TwistTag.D4.order from rfl, ← hord]
    exact pow_orderOf_eq_one σ
  have hσ' : ∀ x, σ.toRingHom x = x ^ q.card := fun x => by
    rw [TauCeti.PrimePower.card_def]
    exact hσ'' x
  obtain ⟨φ⟩ := Even.chevalleyBridgesAll.trialityD4 q hv K
    (by rw [TauCeti.PrimePower.card_def]; exact hK) σ.toRingHom hσ'
  have hperf := finite_fixed_root_group_perfect TwistTag.D4 q.prime_p q.exponent_pos K hK
    σ.toRingHom hσ''
  have hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  obtain ⟨ψ⟩ := nonempty_derivedCentralQuotient_equiv' _ _ hperf.2.2.1 hZ
  let e : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ≃*
      ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩ := ψ.symm.trans φ
  obtain ⟨ι, η, hι, hη, -⟩ :=
    CFSG.RankThree.Chevalley.triality_D4_commuting_faithful_extension_and_fixed_SL2 K σ hσo
  refine ⟨fixSubfield σ, inferInstance, inferInstance, ?_,
    e.toMonoidHom.comp η, e.injective.comp hη⟩
  rw [TauCeti.PrimePower.card_def, ← hkcard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun c => by
    have h1 : c ∈ fixSubfield σ ↔ σ c = c := by
      simp [fixSubfield, RingHom.mem_eqLocusField]
    rw [h1, hσ'']
    exact (Set.ext_iff.1 hk c).symm)

theorem ringChar_ne_two_of_card {F : Type} [Field F] [Finite F] {p e : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (he : e ≠ 0) (hF : Nat.card F = p ^ e) : ringChar F ≠ 2 := by
  intro h
  have : Fintype F := Fintype.ofFinite F
  have h1 := (FiniteField.even_card_iff_char_two (F := F)).1 h
  rw [← Nat.card_eq_fintype_card, hF] at h1
  have := (Nat.even_pow.1 (Nat.even_iff.2 h1)).1
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1
    (even_iff_two_dvd.1 this)).symm

theorem threeTwoWitness_trialityD4
    {X : Type} [Group X] [Finite X] {q : PrimePower} {hv : (LieTypeIndex.trialityD4 q).Valid}
    (e : X ≃* ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩) (h : q.p ≠ 2 ∨ Even q.exponent) :
    ThreeTwoWitness X := by
  obtain ⟨F, _, _, hF, φ, hφ⟩ := exists_injective_sl2_trialityD4 q hv
  rw [TauCeti.PrimePower.card_def] at hF
  have hψ : Function.Injective (e.symm.toMonoidHom.comp φ) := e.symm.injective.comp hφ
  by_cases hp2 : q.p = 2
  · have hq : Even q.exponent := h.resolve_left (not_not.2 hp2)
    rw [hp2] at hF
    exact threeTwoWitness_of_injective_sl2_even hF hq _ hψ
  · exact threeTwoWitness_of_injective_sl2_odd
      (ringChar_ne_two_of_card q.prime_p hp2 q.exponent_pos.ne' hF) _ hψ

theorem exists_injective_sl2_twistedE6
    (q : PrimePower) (hv : (LieTypeIndex.twistedE6 q).Valid) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : Nat.card F = q.card)
      (φ : SL2 F →* ValidLieTypeIndex.Group ⟨.twistedE6 q, hv⟩), Function.Injective φ := by
  let d : TypeTwistedE6LieIndex :=
    ⟨⟨.twistedE6 q, hv⟩, (LieTypeIndex.isTypeTwistedE6_iff _).2 trivial⟩
  have hfin : Finite d.1.fixedField := Nat.finite_of_card_ne_zero (by
    rw [ValidLieTypeIndex.card_fixedField]
    have h : (d.1 : ValidLieTypeIndex).fieldOrder = q.card := LieTypeIndex.fieldOrder_twistedE6 q
    rw [h, TauCeti.PrimePower.card_def]
    exact (pow_pos q.prime_p.pos _).ne')
  have : Fintype d.1.fixedField := Fintype.ofFinite _
  have hC := commutator_fixedGroup_quadField d
  have hj : ∀ x, quadFrob d (quadIncl d x) = quadIncl d x := quadFrob_quadIncl d
  have hinj : Function.Injective
      ((toQuot (te6Embed d) hC).comp (te6SL2 (quadFrob d) (quadIncl d) hj 0)) :=
    toQuot_comp_injective (te6Embed_injective d) hC _ fun A hA =>
      te6SL2_central (quadFrob d) (quadIncl d) hj 0 hA
  refine ⟨d.1.fixedField, inferInstance, inferInstance, ?_,
    (toQuot (te6Embed d) hC).comp (te6SL2 (quadFrob d) (quadIncl d) hj 0), hinj⟩
  rw [ValidLieTypeIndex.card_fixedField]
  exact LieTypeIndex.fieldOrder_twistedE6 q

theorem threeTwoWitness_twistedE6_odd
    {X : Type} [Group X] {q : PrimePower} {hv : (LieTypeIndex.twistedE6 q).Valid}
    (e : X ≃* ValidLieTypeIndex.Group ⟨.twistedE6 q, hv⟩) (hp : q.p ≠ 2) : ThreeTwoWitness X := by
  obtain ⟨F, _, _, hF, φ, hφ⟩ := exists_injective_sl2_twistedE6 q hv
  rw [TauCeti.PrimePower.card_def] at hF
  exact threeTwoWitness_of_injective_sl2_odd
    (ringChar_ne_two_of_card q.prime_p hp q.exponent_pos.ne' hF) (e.symm.toMonoidHom.comp φ)
    (e.symm.injective.comp hφ)

theorem threeTwoWitness_graphFixedRootGroup_char2
    {t : TwistTag} {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)
    (a : Fin t.foldedTag.rank) (hb : ∃ b : Fin t.foldedTag.rank, b ≠ a) :
    ThreeTwoWitness ↥(graphFixedRootGroup t K σ.toRingHom) := by
  have hfin : Finite (ModGL t.tag K) := finite_modGL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C := graphFixedRootGroup t K σ.toRingHom
  let J : Set (Fin t.foldedTag.rank) := {a}
  have hJ : J ≠ Set.univ := by
    obtain ⟨b, hb⟩ := hb
    intro h
    have : b ∈ J := h ▸ Set.mem_univ b
    exact hb (Set.mem_singleton_iff.1 this)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hpg, hne⟩ :=
    diagram_fixed_parabolic_root_radical_Levi_factors t K σ {a}
  have hQC : graphFixedParabolicRadical t K σ.toRingHom J ≤ C :=
    (graphFixedParabolicRadical_le_graphFixedPosUnipotent J).trans
      (graphFixedPosUnipotent_le_graphFixedRootGroup t K σ.toRingHom)
  have hRinj : Function.Injective (orbitRankOneHom t K σ.toRingHom a) :=
    LargeExtraspecial.DW.injective_of_ker_scalar _ fun g hg =>
      eq_smul_one_of_mem_ker_orbitRankOneHom hg
  have hRC : ∀ g, orbitRankOneHom t K σ.toRingHom a g ∈ C := fun g =>
    LargeExtraspecial.DW.orbitRankOneHom_range_le_graphFixedRootGroup σ.toRingHom a ⟨g, rfl⟩
  have hRM : ∀ g, orbitRankOneHom t K σ.toRingHom a g ∈ parabolicLevi t.tag K (t.orbitUnion {a}) :=
    fun g => LargeExtraspecial.DW.orbitRankOneHom_range_le_parabolicLevi σ.toRingHom a ⟨g, rfl⟩
  let g0 : ↥C := ⟨orbitRankOneHom t K σ.toRingHom a cThree, hRC _⟩
  let Q : Subgroup ↥C := (graphFixedParabolicRadical t K σ.toRingHom J).subgroupOf C
  refine ThreeTwoWitness.mk' (P := Q) ?_ ?_ (x := g0) ?_ ?_
  ·
    obtain ⟨q, hq1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 (hne hJ)
    intro hbot
    have hmem : (⟨(q : ModGL t.tag K), hQC q.2⟩ : ↥C) ∈ Q := q.2
    rw [hbot, Subgroup.mem_bot] at hmem
    have h1 : (q : ModGL t.tag K) = 1 := congrArg (fun x : ↥C => (x : ModGL t.tag K)) hmem
    exact hq1 (Subtype.ext h1)
  ·
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).1 (hpg 2)
    refine (IsPGroup.iff_card (p := 2)).2 ⟨n, ?_⟩
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQC).toEquiv]
    exact hn
  · refine orderOf_eq_prime ?_ ?_
    · refine Subtype.ext ?_
      show (orbitRankOneHom t K σ.toRingHom a cThree) ^ 3 = 1
      rw [← map_pow, cThree_pow_three, map_one]
    · intro h
      have h1 : orbitRankOneHom t K σ.toRingHom a cThree = 1 := congrArg Subtype.val h
      rw [← map_one (orbitRankOneHom t K σ.toRingHom a)] at h1
      have hc1 := hRinj h1
      exact cThree_mul_u_ne (K := orbitField t K σ.toRingHom a) (by rw [hc1, one_mul, mul_one])
  · refine mem_normalizer_of_conj_le fun y hy => ?_
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    obtain ⟨hyQ, hyΓ⟩ := Subgroup.mem_inf.1 hy
    have hxP : orbitRankOneHom t K σ.toRingHom a cThree ∈
        parabolicSubgroup t.tag K (t.orbitUnion {a}) :=
      parabolicLevi_le_parabolicSubgroup _ (hRM _)
    have hxΓ : orbitRankOneHom t K σ.toRingHom a cThree ∈ twistedFixedGroup t K σ.toRingHom :=
      graphFixedRootGroup_le t K σ.toRingHom (hRC _)
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.1 (parabolicSubgroup_le_normalizer_parabolicRadical _ hxP)
        (y : ModGL t.tag K)).1 hyQ
    · exact mul_mem (mul_mem hxΓ hyΓ) (inv_mem hxΓ)

theorem threeTwoWitness_trialityD4_char2
    {X : Type} [Group X] {q : PrimePower} {hv : (LieTypeIndex.trialityD4 q).Valid}
    (e : X ≃* ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩) (hp : q.p = 2) : ThreeTwoWitness X := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨K, _, _, hK, hKchar⟩ : ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = (q.p ^ q.exponent) ^ TwistTag.D4.order ∧ CharP K q.p :=
    ⟨GaloisField q.p (q.exponent * TwistTag.D4.order), inferInstance, inferInstance, by
      rw [GaloisField.card _ _ (Nat.mul_pos q.exponent_pos TwistTag.D4.order_pos).ne', pow_mul],
      inferInstance⟩
  have hK2 : CharP K 2 := hp ▸ hKchar
  obtain ⟨σ, hσ'', hord, -⟩ :=
    finite_graph_field_parameter_fields TwistTag.D4 q.prime_p q.exponent_pos K hK
  have hσ' : ∀ x, σ.toRingHom x = x ^ q.card := fun x => by
    rw [TauCeti.PrimePower.card_def]
    exact hσ'' x
  obtain ⟨φ⟩ := Even.chevalleyBridgesAll.trialityD4 q hv K
    (by rw [TauCeti.PrimePower.card_def]; exact hK) σ.toRingHom hσ'
  have hperf := finite_fixed_root_group_perfect TwistTag.D4 q.prime_p q.exponent_pos K hK
    σ.toRingHom hσ''
  have hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  obtain ⟨ψ⟩ := nonempty_derivedCentralQuotient_equiv' _ _ hperf.2.2.1 hZ
  let e' : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ≃*
      ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩ := ψ.symm.trans φ
  have hC := threeTwoWitness_graphFixedRootGroup_char2 (t := TwistTag.D4) σ
    (⟨0, by decide⟩ : Fin TwistTag.D4.foldedTag.rank) ⟨⟨1, by decide⟩, by simp [Fin.ext_iff]⟩
  exact hC.of_mulEquiv (e'.trans e.symm)

end CFSG.HardMathSupport.Timmesfeld.Tables.Census
