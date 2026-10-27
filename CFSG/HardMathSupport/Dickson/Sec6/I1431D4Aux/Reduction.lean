module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431D4Aux.Residual
public import CFSG.HardMathSupport.Dickson.Sec6.I1431D4Aux.RootSL2.Main
public import CFSG.HardMathSupport.Dickson.Sec6.I1431D4Aux.FieldPart.NormalForm
public import CFSG.HardMathSupport.Dickson.Sec6.I1431D4Aux.Char3
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Aux.Cube
public import CFSG.HardMathSupport.Solomon.Coordinator.L2FldFixed
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.D4Aux.Model
public import CFSG.RankThree.Chevalley.SteinbergCBTrialityQuadraticDescent

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.CaseThreeNs
  CFSG.RankThree.PartTwo.KFacts CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootChar rootDiagUnit)
open CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E6Descent
open scoped MatrixGroups commutatorElement

@[expose] def D4RootSL2 : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 3 →
    ∀ (g : adjointGroup Tag.D4 K) (J : Subgroup (adjointGroup Tag.D4 K)) (q : ℕ),
      orderOf g = 3 →
      GLAPComponent 3 (Subgroup.centralizer ({g} : Set (adjointGroup Tag.D4 K))) J →
      IsTypeL2 q (barOf 3 J) → (∃ q0 : ℕ, 4 ≤ q0 ∧ q = q0 ^ 3) →
        ∃ (c : adjointGroup Tag.D4 K) (i : Fin Tag.D4.rank),
          J = (simplePosSubgroup Tag.D4 K i ⊔ simpleNegSubgroup Tag.D4 K i).map
            (MulAut.conj c).toMonoidHom

section Generic

theorem exists_not_mem_zpowers {P : Type} [Group P] [Finite P] {A : Subgroup (MulAut P)}
    {ψ : MulAut P} (hψ3 : ψ ^ 3 = 1) (hψ1 : ψ ≠ 1) (hcard : Nat.card A = 9) :
    ∃ η ∈ A, η ∉ Subgroup.zpowers ψ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hcon
  push Not at hcon
  have hle : A ≤ Subgroup.zpowers ψ := hcon
  have h1 := Subgroup.card_le_of_le hle
  have h2 : orderOf ψ = 3 := orderOf_eq_prime hψ3 hψ1
  rw [Nat.card_zpowers, h2, hcard] at h1
  omega

theorem pow_three_apply {P : Type} [Group P] {η : MulAut P} (h : η ^ 3 = 1) :
    ∀ x, η (η (η x)) = x := fun x => by
  have h1 := congrArg (fun f : MulAut P => f x) h
  simpa [pow_succ] using h1

theorem map_eq_of_mem_stabAut {P : Type} [Group P] {J : Subgroup P} {η : MulAut P}
    (h : η ∈ stabAut J) : J.map η.toMonoidHom = J := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (h z).2 hz
  · intro hy
    exact ⟨η⁻¹ y, (h (η⁻¹ y)).1 (by simpa using hy), by simp⟩

theorem false_of_inner_on_fieldBar {P : Type} [Group P] [Finite P] {X J : Subgroup P} {η : MulAut P}
    (hstab : η ∈ stabAut J) (hη3 : η ^ 3 = 1)
    (hfld : IsFieldAutPSLn 2 (inducedBarHom J ⟨η, hstab⟩)) (hnt : ¬ TrivBar J η)
    (hw : ∃ w ∈ J, ∀ y ∈ J, η y = w * y * w⁻¹) {q : ℕ} (hcomp : GLAPComponent 3 X J)
    (hq : IsTypeL2 q (barOf 3 J)) (hq3 : ¬ 3 ∣ q) (hq8 : q ≠ 8) : False := by
  obtain ⟨w, hw, hwy⟩ := hw
  have hQ : CFSG.Open.IsQuasisimple (barOf 3 J) :=
    isQuasisimple_barOf_of_glaPComponent Nat.prime_three hcomp
  have hα3 : inducedBarHom J ⟨η, hstab⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨η, hstab⟩ : ↥(stabAut J)) ^ 3 = 1 := Subtype.ext hη3
    rw [this, map_one]
  have hα1 : inducedBarHom J ⟨η, hstab⟩ ≠ 1 := fun h => hnt ⟨hstab, h⟩
  refine not_isInnerAut_descend_of_fieldAut CFSG.HardMathSupport.Solomon.Proving.l2OrderUnique_holds
    CFSG.HardMathSupport.Solomon.Coordinator.l2FieldFixed_holds hQ hα3 hα1 hfld hq hq3 hq8 ?_
  have hαeq : inducedBarHom J ⟨η, hstab⟩ =
      MulAut.conj (QuotientGroup.mk (⟨w, hw⟩ : ↥J) : barOf 3 J) := by
    ext z
    induction z using QuotientGroup.induction_on with
    | H j =>
      rw [inducedBarHom_mk]
      simp only [MulAut.conj_apply]
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      simp [restrictAut_coe, hwy j.1 j.2]
  rw [hαeq, CFSG.RankThree.PartTwo.KFacts.centerDescend_conj]
  exact isInnerAut_conj _

end Generic

section Reduction


variable {K : Type} [Field K] [Finite K]

theorem rankOneRep_range_eq (i : Fin Tag.D4.rank) :
    (rankOneRep Tag.D4 K i).range = simplePosSubgroup Tag.D4 K i ⊔ simpleNegSubgroup Tag.D4 K i := by
  have hrange : (rankOneRep Tag.D4 K i).range = Subgroup.closure
      ((rankOneRep Tag.D4 K i) '' (Set.range (sl2Upper K) ∪ Set.range (sl2Lower K))) := by
    rw [MonoidHom.range_eq_map, ← sl2_closure_upper_lower,
      MonoidHom.map_closure]
  apply le_antisymm
  · rw [hrange, Subgroup.closure_le]
    rintro _ ⟨_, (⟨c, rfl⟩ | ⟨c, rfl⟩), rfl⟩
    · exact Subgroup.mem_sup_left ⟨c, by rw [rankOneRep_upper]; rfl⟩
    · exact Subgroup.mem_sup_right ⟨c, by rw [rankOneRep_lower]; rfl⟩
  · refine sup_le ?_ ?_
    · rintro _ ⟨c, hc⟩
      refine ⟨sl2Upper K c, ?_⟩
      rw [rankOneRep_upper]
      exact Subtype.ext hc.symm
    · rintro _ ⟨c, hc⟩
      refine ⟨sl2Lower K c, ?_⟩
      rw [rankOneRep_lower]
      exact Subtype.ext hc.symm

theorem exists_linear_conj (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (ε : ℕ) :
    ∃ Φ : ModGL Tag.D4 K, ∀ x : adjointGroup Tag.D4 K,
      (((MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K ε)) x :
        adjointGroup Tag.D4 K) : ModGL Tag.D4 K) = Φ * (x : ModGL Tag.D4 K) * Φ⁻¹ := by
  refine ⟨(g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a * d4P K ^ ε,
    fun x => ?_⟩
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_exactNormalAut,
    coe_d4Graph, exactQ_D4]
  have h1 : (RingEquiv.toRingHom (1 : K ≃+* K)) = RingHom.id K := rfl
  rw [h1, CFSG.RankThree.Chevalley.units_map_entrywiseHom_ringHom_id]
  group

theorem normalizer_inner_conj {i : Fin Tag.D4.rank} {c : adjointGroup Tag.D4 K}
    {Φ : ModGL Tag.D4 K} {η : MulAut (adjointGroup Tag.D4 K)}
    (hΦ : ∀ x : adjointGroup Tag.D4 K,
      ((η x : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) = Φ * (x : ModGL Tag.D4 K) * Φ⁻¹)
    (hη3 : ∀ x, η (η (η x)) = x)
    (hηJ : ((simplePosSubgroup Tag.D4 K i ⊔ simpleNegSubgroup Tag.D4 K i).map
      (MulAut.conj c).toMonoidHom).map η.toMonoidHom =
        (simplePosSubgroup Tag.D4 K i ⊔ simpleNegSubgroup Tag.D4 K i).map
          (MulAut.conj c).toMonoidHom) :
    ∃ w ∈ (simplePosSubgroup Tag.D4 K i ⊔ simpleNegSubgroup Tag.D4 K i).map
        (MulAut.conj c).toMonoidHom,
      ∀ y ∈ (simplePosSubgroup Tag.D4 K i ⊔ simpleNegSubgroup Tag.D4 K i).map
        (MulAut.conj c).toMonoidHom, η y = w * y * w⁻¹ := by
  set J0 := simplePosSubgroup Tag.D4 K i ⊔ simpleNegSubgroup Tag.D4 K i with hJ0
  set η' : MulAut (adjointGroup Tag.D4 K) := MulAut.conj c⁻¹ * η * MulAut.conj c with hη'
  have hη'x : ∀ x, η' x = c⁻¹ * η (c * x * c⁻¹) * c := by
    intro x
    simp [hη', MulAut.mul_apply, MulAut.conj_apply]
  have hηx : ∀ x, η (c * x * c⁻¹) = c * η' x * c⁻¹ := by
    intro x
    rw [hη'x]
    group
  have hΦ' : ∀ x : adjointGroup Tag.D4 K, ((η' x : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) =
      ((c : ModGL Tag.D4 K)⁻¹ * Φ * c) * (x : ModGL Tag.D4 K) *
        ((c : ModGL Tag.D4 K)⁻¹ * Φ * c)⁻¹ := by
    intro x
    rw [hη'x]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hΦ]
    group
  have hη'3 : ∀ x, η' (η' (η' x)) = x := by
    intro x
    simp only [hη'x]
    have h1 : ∀ y, c * (c⁻¹ * y * c) * c⁻¹ = y := fun y => by group
    rw [h1, h1]
    simp only [hη3]
    group
  have hJ' : (rankOneRep Tag.D4 K i).range.map η'.toMonoidHom = (rankOneRep Tag.D4 K i).range := by
    rw [rankOneRep_range_eq, ← hJ0]
    rw [hη', map_mulAut_mul, map_mulAut_mul, hηJ, ← map_mulAut_mul, ← map_mul, inv_mul_cancel,
      map_one, map_mulAut_one]
  obtain ⟨w, hw, hwy⟩ := RootSL2.normalizer_inner hΦ' hη'3 hJ'
  rw [rankOneRep_range_eq, ← hJ0] at hw hwy
  refine ⟨c * w * c⁻¹, ⟨w, hw, by simp [MulAut.conj_apply]⟩, ?_⟩
  rintro _ ⟨y0, hy0, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [hηx, hwy y0 hy0]
  group

theorem commutator_adjointD4_eq_top : commutator (adjointGroup Tag.D4 K) = ⊤ := by
  obtain ⟨hs, a, b, hab⟩ := CFSG.HardMathSupport.Dickson.Sec6.I923.D4Aux.isSimple_adjointD4 K
  haveI := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator (adjointGroup Tag.D4 K)) with h | h
  · exfalso
    have : ⁅a, b⁆ ∈ commutator (adjointGroup Tag.D4 K) := Subgroup.commutator_mem_commutator
      (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact hab this
  · exact h

theorem pow_three_eq_one_of_conj {g : adjointGroup Tag.D4 K} (h : (MulAut.conj g) ^ 3 = 1) :
    g ^ 3 = 1 := by
  have h1 : MulAut.conj (g ^ 3) = 1 := by rw [map_pow]; exact h
  have hc : g ^ 3 ∈ Subgroup.center (adjointGroup Tag.D4 K) := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h2 := congrArg (fun φ : MulAut (adjointGroup Tag.D4 K) => φ y) h1
    simp only [MulAut.conj_apply, MulAut.one_apply] at h2
    exact (mul_inv_eq_iff_eq_mul.1 h2).symm
  rw [center_adjointGroup_eq_bot, Subgroup.mem_bot] at hc
  exact hc

theorem d4NoCfg_of_rootSL2 (hR : D4RootSL2) : D4NoCfg := by
  intro K _ _ hchar A ψ J q cfg hq hψ hA
  haveI := CFSG.HardMathSupport.Dickson.Sec6.I923.D4Aux.finite_adjointD4 K
  obtain ⟨g, rfl⟩ := hψ
  have hψ3 : (MulAut.conj g) ^ 3 = 1 := cfg.elemAbelian.2 _ cfg.mem
  have hg3 : g ^ 3 = 1 := pow_three_eq_one_of_conj hψ3
  have hg1 : g ≠ 1 := by
    rintro rfl
    exact cfg.ne_one (map_one _)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf g = 3 := orderOf_eq_prime hg3 hg1
  have hcomp : GLAPComponent 3 (Subgroup.centralizer ({g} : Set (adjointGroup Tag.D4 K))) J := by
    have := cfg.comp
    rwa [d4_fixSub_conj_eq_centralizer] at this
  obtain ⟨c, i, hJ⟩ := hR K hchar g J q hord hcomp cfg.typeL2 hq
  obtain ⟨η, hηA, hηnot⟩ := exists_not_mem_zpowers hψ3 cfg.ne_one cfg.card
  have hη3 : η ^ 3 = 1 := cfg.elemAbelian.2 η hηA
  have hηc : η ∈ commutator (MulAut (adjointGroup Tag.D4 K)) := by
    have := hA η hηA
    rwa [innAutDerived_eq_commutator_of_perfect commutator_adjointD4_eq_top] at this
  obtain ⟨g', a, ε, -, hηeq⟩ := FieldPart.exists_algebraic_of_mem_commutator hηc hη3
  obtain ⟨Φ, hΦ⟩ := exists_linear_conj g' a ε
  rw [← hηeq] at hΦ
  obtain ⟨⟨hstab, hfld⟩, hnt⟩ := cfg.field η hηA hηnot
  have hηJ : J.map η.toMonoidHom = J := map_eq_of_mem_stabAut hstab
  subst hJ
  obtain ⟨w, hw, hwy⟩ := normalizer_inner_conj hΦ (pow_three_apply hη3) hηJ
  exact false_of_inner_on_fieldBar hstab hη3 hfld hnt ⟨w, hw, hwy⟩ cfg.comp cfg.typeL2
    cfg.not_dvd cfg.ne_eight

end Reduction

end CFSG.HardMathSupport.Dickson.Sec6.I1431
