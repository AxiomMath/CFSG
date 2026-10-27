module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs295d2
public import Certificates.Certificate2012
import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutU42Aut
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87U4SvNine
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.Transfer
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.EvenClass
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.ClassOdd.Glue
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.ClassOdd.Shintani
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.ClassOdd.ThreeD4
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.ClassOdd.G2Class
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHighD4Three
import CFSG.RankThree.Chevalley.SteinbergCFOddG2QPlusTorus
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenWeyl
import CFSG.RankThree.Chevalley.SteinbergBIRootSL2Tools
import CFSG.RankThree.Chevalley.SteinbergBID4TrialityConjugacy
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTorus
import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.SporthD4Stab
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LinearUnitaryComps
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.SympAut
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Derivation
import CFSG.GH74.GLS.Stage2.Local.Prop27Cfg
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L4SvEngLift
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SurvU4Core
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87U4SvDefs
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87U4SvEngLift

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs295e

section U42

open CFSG.ComponentClassification.CatFactsSmall.PSp43

theorem p_exponent_of_card_two {q : TauCeti.PrimePower} (hq : q.card = 2) :
    q.p = 2 ∧ q.exponent = 1 :=
  Inputs295d.p_eq_two_of_card_two hq

theorem lieModel_psu42_of_equiv {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA 3 q).Valid) (hq : q.card = 2) {K : Type} [Group K]
    (e : K ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group) :
    CFSG.Blueprint.LieModel K .PSU 4 2 1 := by
  obtain ⟨hp, hf⟩ := p_exponent_of_card_two hq
  have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv e
  rw [hp, hf] at h
  exact Or.inl ⟨by decide, h⟩

theorem exists_orderOf_nine_of_lieModel_psu42 {K : Type} [Group K]
    (h : CFSG.Blueprint.LieModel K .PSU 4 2 1) : ∃ g : K, orderOf g = 9 := by
  obtain ⟨φ⟩ :=
    equiv_of_lieModel (CFSG.GH74.Exceptional.lieModel_PSp_two_three_of_lieModel_PSU_four_two h)
  obtain ⟨-, -, h3⟩ := x45_facts
  have h9 : orderOf (x45 * y45) = 9 := by
    have := (CFSG.GH74.KGroups.pairInvB_iff ws45 (by simp [ws45]) x45 y45).1 h3
      ([false, true], 9) (by simp [ws45])
    simpa [CFSG.GH74.KGroups.evalW] using this
  have hx : x45 ∈ QP45.originalSubgroup := by
    rw [QP45_closure]
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  have hy : y45 ∈ QP45.originalSubgroup := by
    rw [QP45_closure]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  refine ⟨φ.symm ⟨x45 * y45, mul_mem hx hy⟩, ?_⟩
  rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, h9]

theorem factorization_three_51840 : (51840 : ℕ).factorization 3 = 4 := by
  have e : (51840 : ℕ) = 3 ^ 4 * 640 := by norm_num
  rw [e, Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, Nat.prime_three.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 640)]
  simp

theorem pRank_mulAut_le_three_u42 {K : Type} [Group K] [Finite K]
    (h : CFSG.Blueprint.LieModel K .PSU 4 2 1) (hnab : ∃ a b : K, a * b ≠ b * a)
    [IsSimpleGroup K] : CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut K)) ≤ 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hAut, -⟩ := CFSG.EvenSporadicStandard.M22Std.card_mulAut_of_lieModel_psu42 h
  obtain ⟨g, hg⟩ := exists_orderOf_nine_of_lieModel_psu42 h
  have hZ : Subgroup.center K = ⊥ := GL83.I713.center_eq_bot_of_simple hnab
  have hinj : Function.Injective (MulAut.conj : K →* MulAut K) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hxZ : x ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro y
      have := congrArg (fun φ : MulAut K => φ y) hx
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc y * x = x * y * x⁻¹ * x := by rw [this]
        _ = x * y := by group
    rw [hZ] at hxZ
    exact hxZ
  have hg' : orderOf (MulAut.conj g) = 9 := by rw [orderOf_injective _ hinj, hg]
  haveI : Finite (MulAut K) := Nat.finite_of_card_ne_zero (by rw [hAut]; norm_num)
  refine CFSG.SectionRank.pRank_le (p := 3) (by norm_num) fun E _ hE => ?_
  have hEp : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨k, hk⟩ := hEp.exists_card_eq
  rw [hk]
  have hdvd : 3 ^ k ∣ 51840 := by
    rw [← hk, ← hAut]
    exact Subgroup.card_subgroup_dvd_card E
  have hk4 : k ≤ 4 := by
    by_contra hlt
    have h5 : 3 ^ 5 ∣ 51840 := (pow_dvd_pow 3 (by omega : 5 ≤ k)).trans hdvd
    norm_num at h5
  by_contra hlt
  have hk4' : k = 4 := by
    by_contra hne
    exact hlt (Nat.pow_le_pow_right (by norm_num) (by omega))
  obtain ⟨x, hxE, hx3⟩ := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.exists_pow_three_ne_one_of_card_81
    (G := MulAut K) (by rw [hAut]; exact factorization_three_51840) hg' (X := E)
    (by rw [hk, hk4']; norm_num)
  exact hx3 (hE.2 x hxE)

theorem at_twistedA_three_two {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA 3 q).Valid) (hq : q.card = 2) :
    Inputs295c.Outer295At ⟨.twistedA 3 q, hv⟩ ∧ Inputs295c.Inner295At ⟨.twistedA 3 q, hv⟩ :=
  Inputs295c.at_of_pRank_mulAut_le fun K _ _ hs hnab ⟨e⟩ =>
    haveI := hs
    pRank_mulAut_le_three_u42 (lieModel_psu42_of_equiv hv hq e) hnab

end U42

section Generic

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartOne.CTP (fixedSubgroup mem_fixedSubgroup fixedSubgroup_conj)
open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure (isPSolvable_of_le)
open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal
  (isPSolvable_of_mulEquiv)

variable {K : Type} [Field K] [Finite K]

theorem uSL_one_ne_one : CFSG.LieType.Chevalley.uSL (1 : K) ≠ 1 := by
  intro h
  have h1 := congrArg (fun A : SL2 K => (A : Matrix (Fin 2) (Fin 2) K) 0 1) h
  simp [CFSG.LieType.Chevalley.uSL] at h1

theorem not_isPSolvable_of_sl2_le {G : Type} [Group G] [Finite G] (hK4 : 4 ≤ Nat.card K)
    (f : SL2 K →* G) (hf : ∃ A, f A ≠ 1) {H : Subgroup G} (hle : f.range ≤ H) :
    ¬ CFSG.HallHigman.IsPSolvable 3 ↥H := fun hs =>
  Inputs295c.not_isPSolvable_range_of_quasisimple
    (CFSG.SeitzReduction.LinearPilot.isQuasisimple_specialLinearGroup_of_le le_rfl (Or.inr hK4))
    (Inputs295c.three_dvd_card_sl (F := K) (m := 2) le_rfl) f hf (isPSolvable_of_le hs hle)

theorem not_isPSolvable_of_conj {G : Type} [Group G] [Finite G] (ψ α : MulAut G)
    (h : ¬ CFSG.HallHigman.IsPSolvable 3 ↥(fixedSubgroup (ψ * α * ψ⁻¹))) :
    ¬ CFSG.HallHigman.IsPSolvable 3 ↥(fixedSubgroup α) := fun hs => h (by
  rw [fixedSubgroup_conj]
  exact isPSolvable_of_mulEquiv ((fixedSubgroup α).equivMapOfInjective _ ψ.injective) hs)

theorem five_le_ringChar (h2 : ringChar K ≠ 2) (h3 : ringChar K ≠ 3) : 5 ≤ ringChar K := by
  have : Fintype K := Fintype.ofFinite K
  have hp : (ringChar K).Prime := CharP.char_is_prime K (ringChar K)
  have h2' := hp.two_le
  have h4 : ringChar K ≠ 4 := fun h => by rw [h] at hp; norm_num at hp
  omega

theorem not_isMulCommutative_of_simple {G : Type} [Group G] (hs : IsSimpleGroup G)
    (h9 : 9 ∣ Nat.card G) : ¬ IsMulCommutative G := by
  intro hc
  letI : CommGroup G := { (inferInstance : Group G) with mul_comm := hc.is_comm.comm }
  have hp : (Nat.card G).Prime := IsSimpleGroup.prime_card
  rcases hp.eq_one_or_self_of_dvd 9 h9 with h | h
  · norm_num at h
  · rw [← h] at hp
    norm_num at hp

theorem map_uSL (τ : K →+* K) (c : K) :
    Matrix.SpecialLinearGroup.map τ (CFSG.LieType.Chevalley.uSL c) =
      CFSG.LieType.Chevalley.uSL (τ c) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CFSG.LieType.Chevalley.uSL, RingHom.mapMatrix_apply]

theorem map_vSL (τ : K →+* K) (c : K) :
    Matrix.SpecialLinearGroup.map τ (CFSG.LieType.Chevalley.vSL c) =
      CFSG.LieType.Chevalley.vSL (τ c) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CFSG.LieType.Chevalley.vSL, RingHom.mapMatrix_apply]

end Generic

section D4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Lang.D4Three
  CFSG.LieType.SeitzGeneration.ExcWideThree
  CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph
open CFSG.RankThree.PartOne.CTP (fixedSubgroup mem_fixedSubgroup fixedSubgroup_conj)
open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure (isPSolvable_of_le)
open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal
  (isPSolvable_of_mulEquiv)


variable {K : Type} [Field K] [Finite K]

theorem sl2At_injective (i : Fin Tag.D4.rank) : Function.Injective (sl2At K i) := by
  intro A B h
  apply CFSG.RankThree.Chevalley.rootSL2_injective_of_field (τ := Tag.D4) (K := K)
    (Pi.single i 1)
  rw [CFSG.RankThree.Chevalley.rootSL2_single_apply, CFSG.RankThree.Chevalley.rootSL2_single_apply]
  exact congrArg Subtype.val h

theorem not_isPSolvable_fixedSubgroup_d4Graph (hK4 : 4 ≤ Nat.card K) {ε : ℕ}
    (hε : ε = 1 ∨ ε = 2) : ¬ CFSG.HallHigman.IsPSolvable 3 ↥(fixedSubgroup (d4Graph K ε)) := by
  have : Finite (ModGL Tag.D4 K) := finite_modGL
  have : Finite ↥(adjointGroup Tag.D4 K) := Subtype.finite
  refine not_isPSolvable_of_sl2_le hK4 (sl2At K ⟨2, by decide⟩)
    ⟨_, fun h => uSL_one_ne_one (sl2At_injective _ (h.trans (map_one _).symm))⟩ ?_
  rintro _ ⟨A, rfl⟩
  rw [mem_fixedSubgroup, d4Graph_sl2At]
  rcases hε with rfl | rfl
  · rfl
  · rfl

theorem not_isPSolvable_fixedSubgroup_gammaP (hK4 : 4 ≤ Nat.card K) (B : SL2 K) :
    ¬ CFSG.HallHigman.IsPSolvable 3 ↥(fixedSubgroup (gammaP K B)) := by
  have : Finite (ModGL Tag.D4 K) := finite_modGL
  have : Finite ↥(adjointGroup Tag.D4 K) := Subtype.finite
  have hK3 : 3 ≤ Nat.card K := by omega
  set E := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.fixSubgroupEquivG2 K hK3
    with hE
  let ρv : SL2 K →* ↥(adjointGroup Tag.G2 K) :=
    (CFSG.LieType.Chevalley.rootSL2 Tag.G2 K
      CFSG.ComponentClassification.UnbalancedCatalog.g2v).codRestrict
      _ (fun A => (CFSG.LieType.Chevalley.exceptional_Lang_root_rank_one_data Tag.G2 K
        CFSG.ComponentClassification.UnbalancedCatalog.g2v).2.2.2.2.1 A)
  have hρv : Function.Injective ρv := fun A A' h =>
    CFSG.RankThree.Chevalley.rootSL2_injective_of_field _ (congrArg Subtype.val h)
  let f : SL2 K →* ↥(adjointGroup Tag.D4 K) :=
    (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (d4Graph K 1)).subtype.comp
      (E.symm.toMonoidHom.comp ρv)
  have hf : Function.Injective f :=
    (Subgroup.subtype_injective _).comp (E.symm.injective.comp hρv)
  refine not_isPSolvable_of_sl2_le hK4 f
    ⟨_, fun h => uSL_one_ne_one (hf (h.trans (map_one f).symm))⟩ ?_
  rintro _ ⟨A, rfl⟩
  rw [mem_fixedSubgroup]
  have h1 : d4Graph K 1 (f A) = f A := (E.symm (ρv A)).2
  have hc : E (sl2TwoFix B) * ρv A = ρv A * E (sl2TwoFix B) := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, fixSubgroupEquivG2_sl2Two hK3 B]
    have hsa := CFSG.RankThree.Chevalley.rootSL2_single_apply (Ω := K) Tag.G2 ⟨0, by decide⟩ B
    rw [← hsa]
    have hga : (Pi.single (⟨0, by decide⟩ : Fin Tag.G2.rank) (1 : ℤ)) =
        CFSG.ComponentClassification.UnbalancedCatalog.g2a :=
      CFSG.ComponentClassification.UnbalancedCatalog.g2a_eq_single.symm
    rw [hga]
    exact (CFSG.RankThree.Chevalley.rootSL2_g2v_mul_rootSL2_g2a A B).symm
  have hc' : sl2TwoFix B * E.symm (ρv A) = E.symm (ρv A) * sl2TwoFix B := by
    apply E.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hc
  have hc'' : sl2At K ⟨2, by decide⟩ B * f A = f A * sl2At K ⟨2, by decide⟩ B :=
    congrArg Subtype.val hc'
  change sl2At K ⟨2, by decide⟩ B * d4Graph K 1 (f A) * (sl2At K ⟨2, by decide⟩ B)⁻¹ = f A
  rw [h1, hc'', mul_inv_cancel_right]

theorem not_isPSolvable_fixedSubgroup_graphType (hK3 : ringChar K ≠ 3) (hK4 : 4 ≤ Nat.card K)
    {α : MulAut ↥(adjointGroup Tag.D4 K)} (hα3 : α ^ 3 = 1)
    (hT : D4ElemType α fun ε σ => ε ≠ 0 ∧ σ = 1) :
    ¬ CFSG.HallHigman.IsPSolvable 3 ↥(fixedSubgroup α) := by
  have : Finite (ModGL Tag.D4 K) := finite_modGL
  have : Finite ↥(adjointGroup Tag.D4 K) := Subtype.finite
  have hcls : IsG2Type α ∨ IsA2Type α := by
    by_cases h2 : ringChar K = 2
    · exact isG2Type_or_isA2Type_of_charTwo K h2 α hα3 hT
    · exact ClassOdd.d4GraphClassOdd_of (ClassOdd.graphShintaniNF_of ClassOdd.threeD4FixedNF_holds)
        ClassOdd.g2ThreeClass_holds K (five_le_ringChar h2 hK3) α hα3 hT
  rcases hcls with ⟨ψ, h | h⟩ | ⟨ψ, B, -, -, h | h⟩
  · exact not_isPSolvable_of_conj ψ α (h ▸ not_isPSolvable_fixedSubgroup_d4Graph hK4 (Or.inl rfl))
  · exact not_isPSolvable_of_conj ψ α (h ▸ not_isPSolvable_fixedSubgroup_d4Graph hK4 (Or.inr rfl))
  · exact not_isPSolvable_of_conj ψ α (h ▸ not_isPSolvable_fixedSubgroup_gammaP hK4 B)
  · refine not_isPSolvable_of_conj ψ α ?_
    rw [h, fixedSubgroup_inv]
    exact not_isPSolvable_fixedSubgroup_gammaP hK4 B

theorem not_isPSolvable_fixedSubgroup_field (hK3 : ringChar K ≠ 3)
    {α : MulAut ↥(adjointGroup Tag.D4 K)} (hα3 : α ^ 3 = 1) (g : adjointGroup Tag.D4 K)
    (a : Fin Tag.D4.rank → Kˣ) {σ : K ≃+* K} (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1)
    (hα : α = MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K 0)) :
    ¬ CFSG.HallHigman.IsPSolvable 3 ↥(fixedSubgroup α) := by
  classical
  have : Finite (ModGL Tag.D4 K) := finite_modGL
  have : Finite ↥(adjointGroup Tag.D4 K) := Subtype.finite
  rw [CFSG.HardMathSupport.Lang.E6Descent.d4Graph_zero, mul_one] at hα
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  have : CharP K (ringChar K) := ringChar.charP K
  obtain ⟨e, T, he0, hef, hT, hT3, hσT⟩ :=
    CFSG.HardMathSupport.Lang.E6Descent.exists_frobenius_of_cube hℓ n.pos K hK σ hσ3 hσ1
  have hT1 : T ≠ 1 := by
    rintro rfl
    rcases hσT with h | h
    · exact hσ1 h
    · exact hσ1 (by rw [h, one_pow])
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK, ← hef]
    calc 4 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (e * 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ ringChar K ^ (e * 3) := Nat.pow_le_pow_left hℓ.two_le _
  obtain ⟨ψ, -, hF⟩ := exists_conj_fixedSubgroup_D4_field hK hK4 he0 hef T σ hT hT3 hσT
    (AlgebraicClosure K) g a α hα hα3
  refine not_isPSolvable_of_conj ψ α ?_
  rw [hF]
  have hq0 : Nat.card (fixSubfield T) = ringChar K ^ e := card_fixSubfield_eq_pow hK hef T hT3 hT1
  obtain ⟨φ₀⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh3.nonempty_subfieldGroup_equiv_d4 hℓ
      he0 T hT3 hq0
  have hs : IsSimpleGroup ↥(CFSG.LieType.SeitzGeneration.ExcOuterLeOne.subfieldGroup Tag.D4 T) :=
    (CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_of_statedClassicalModel_POmegaPlus _ 4 _ _
      (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD 4 _ _ φ₀)).2
  have : Finite (fixSubfield T) := Subtype.finite
  have h27 :
      27 ∣ Nat.card ↥(CFSG.LieType.SeitzGeneration.ExcOuterLeOne.subfieldGroup Tag.D4 T) := by
    rw [Nat.card_congr (fixedD4Equiv T hT3).toEquiv]
    exact CFSG.HardMathSupport.Lang.E6Descent.twentySeven_dvd_card_adjointGroup_D4 _
  exact CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.not_isPSolvable_three_of_simple hs
    (not_isMulCommutative_of_simple hs (dvd_trans (by norm_num) h27)) (dvd_trans (by norm_num) h27)

theorem d4Twist_one_sl2At (τ : K ≃+* K) (i : Fin Tag.D4.rank) (A : SL2 K) :
    d4Twist 1 τ (sl2At K i A) =
      sl2At K (d4Rho i) (Matrix.SpecialLinearGroup.map (τ : K →+* K) A) := by
  have h : (d4Twist 1 τ).toMonoidHom.comp (sl2At K i) =
      (sl2At K (d4Rho i)).comp (Matrix.SpecialLinearGroup.map (τ : K →+* K)) := by
    refine sl2_hom_ext (fun c => ?_) fun c => ?_
    · simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, sl2At_uSL]
      rw [d4Twist_one_adjX, map_uSL, sl2At_uSL]
      rfl
    · simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, sl2At_vSL]
      rw [map_vSL, sl2At_vSL]
      exact CFSG.HardMathSupport.Dickson.DefCharOuter.Export.SporthD4.twistedEntrywiseAut_one_adjY'
        τ i c
  exact DFunLike.congr_fun h A

theorem not_isPSolvable_fixedSubgroup_d4Twist (hK4 : 4 ≤ Nat.card K) (τ : K ≃+* K)
    (hτ3 : τ ^ 3 = 1) : ¬ CFSG.HallHigman.IsPSolvable 3 ↥(fixedSubgroup (d4Twist 1 τ)) := by
  have : Finite (ModGL Tag.D4 K) := finite_modGL
  have : Finite ↥(adjointGroup Tag.D4 K) := Subtype.finite
  have hK3 : 3 ≤ Nat.card K := by omega
  set m : SL2 K →* SL2 K := Matrix.SpecialLinearGroup.map (τ : K →+* K) with hm
  have hτx : ∀ x : K, τ (τ (τ x)) = x := fun x => by
    have h := congrArg (fun φ : K ≃+* K => φ x) hτ3
    simpa [pow_succ] using h
  have hm3 : ∀ A : SL2 K, m (m (m A)) = A := fun A => by
    ext i j
    simp [hm, hτx]
  set i0 : Fin Tag.D4.rank := ⟨0, by decide⟩
  set i1 : Fin Tag.D4.rank := ⟨1, by decide⟩
  set i3 : Fin Tag.D4.rank := ⟨3, by decide⟩
  have c01 : ∀ X Y : SL2 K, Commute (sl2At K i0 X) (sl2At K i1 Y) := fun X Y =>
    sl2At_commute (by decide) (by decide) (by decide) X Y
  have c03 : ∀ X Y : SL2 K, Commute (sl2At K i0 X) (sl2At K i3 Y) := fun X Y =>
    sl2At_commute (by decide) (by decide) (by decide) X Y
  have c13 : ∀ X Y : SL2 K, Commute (sl2At K i1 X) (sl2At K i3 Y) := fun X Y =>
    sl2At_commute (by decide) (by decide) (by decide) X Y
  let f : SL2 K →* ↥(adjointGroup Tag.D4 K) := MonoidHom.mk'
    (fun A => sl2At K i0 A * sl2At K i1 (m A) * sl2At K i3 (m (m A))) (fun A B => by
      simp only [map_mul]
      set a0 := sl2At K i0 A
      set a1 := sl2At K i1 (m A)
      set a3 := sl2At K i3 (m (m A))
      set b0 := sl2At K i0 B
      set b1 := sl2At K i1 (m B)
      set b3 := sl2At K i3 (m (m B))
      have h01 : Commute a1 b0 := (c01 B (m A)).symm
      have h03 : Commute a3 b0 := (c03 B (m (m A))).symm
      have h13 : Commute a3 b1 := (c13 (m B) (m (m A))).symm
      calc a0 * b0 * (a1 * b1) * (a3 * b3) = a0 * (b0 * a1) * b1 * a3 * b3 := by group
        _ = a0 * (a1 * b0) * b1 * a3 * b3 := by rw [h01.eq]
        _ = a0 * a1 * b0 * (b1 * a3) * b3 := by group
        _ = a0 * a1 * b0 * (a3 * b1) * b3 := by rw [h13.eq]
        _ = a0 * a1 * (b0 * a3) * b1 * b3 := by group
        _ = a0 * a1 * (a3 * b0) * b1 * b3 := by rw [h03.eq]
        _ = a0 * a1 * a3 * (b0 * b1 * b3) := by group)
  have hfA : ∀ A, f A = sl2At K i0 A * sl2At K i1 (m A) * sl2At K i3 (m (m A)) := fun A => rfl
  have hf1 : f (CFSG.LieType.Chevalley.uSL 1) ≠ 1 := by
    have hmu : m (CFSG.LieType.Chevalley.uSL 1) = CFSG.LieType.Chevalley.uSL 1 := by
      rw [hm, map_uSL, map_one]
    rw [hfA, hmu, hmu]
    intro h1
    have h2 : sl2ShortFix (CFSG.LieType.Chevalley.uSL (1 : K)) = 1 := Subtype.ext h1
    have h3 := fixSubgroupEquivG2_sl2Short hK3 (CFSG.LieType.Chevalley.uSL (1 : K))
    rw [h2, map_one] at h3
    apply uSL_one_ne_one (K := K)
    apply CFSG.RankThree.Chevalley.rootSL2_injective_of_field (τ := Tag.G2) (K := K)
      (Pi.single ⟨1, by decide⟩ 1)
    rw [CFSG.RankThree.Chevalley.rootSL2_single_apply,
      CFSG.RankThree.Chevalley.rootSL2_single_apply, ← h3, map_one]
    rfl
  refine not_isPSolvable_of_sl2_le hK4 f ⟨_, hf1⟩ ?_
  rintro _ ⟨A, rfl⟩
  rw [mem_fixedSubgroup, hfA, map_mul, map_mul, d4Twist_one_sl2At, d4Twist_one_sl2At,
    d4Twist_one_sl2At]
  have e0 : d4Rho i0 = i1 := by decide
  have e1 : d4Rho i1 = i3 := by decide
  have e3 : d4Rho i3 = i0 := by decide
  rw [e0, e1, e3, ← hm, hm3, mul_assoc, ← (c03 A (m (m A))).eq, ← mul_assoc,
    ← (c01 A (m A)).eq]

theorem not_isPSolvable_fixedSubgroup_graphField (hK3 : ringChar K ≠ 3)
    {β : MulAut ↥(adjointGroup Tag.D4 K)} (hβ3 : β ^ 3 = 1) (g : adjointGroup Tag.D4 K)
    (a : Fin Tag.D4.rank → Kˣ) {σ : K ≃+* K} {ε : ℕ} (hεlt : ε < 3) (hε0 : ε ≠ 0)
    (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1)
    (hβ : β = MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε)) :
    ¬ CFSG.HallHigman.IsPSolvable 3 ↥(fixedSubgroup β) := by
  classical
  have : Finite (ModGL Tag.D4 K) := finite_modGL
  have : Finite ↥(adjointGroup Tag.D4 K) := Subtype.finite
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  have : CharP K (ringChar K) := ringChar.charP K
  obtain ⟨e, T, he0, hef, hT, hT3, hσT⟩ :=
    CFSG.HardMathSupport.Lang.E6Descent.exists_frobenius_of_cube hℓ n.pos K hK σ hσ3 hσ1
  have hT1 : T ≠ 1 := by
    rintro rfl
    rcases hσT with h | h
    · exact hσ1 h
    · exact hσ1 (by rw [h, one_pow])
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK, ← hef]
    calc 4 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (e * 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ ringChar K ^ (e * 3) := Nat.pow_le_pow_left hℓ.two_le _
  have hσ' : σ = T ∨ σ = T⁻¹ := by
    rcases hσT with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans (inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hT3)).symm)
  have hε12 : ε = 1 ∨ ε = 2 := by omega
  obtain ⟨ψ, hF⟩ := exists_conj_fixedSubgroup_D4_graphField hK hK4 he0 hef T σ hT hT3 hT1 hσ'
    hε12 g a β hβ3 hβ
  refine not_isPSolvable_of_conj ψ β ?_
  rw [hF]
  have hτ3 : d4GfTwist T σ ε ^ 3 = 1 := by
    rcases d4GfTwist_eq_or T σ ε with h | h <;> rw [h]
    · exact hT3
    · rw [inv_pow, hT3, inv_one]
  exact not_isPSolvable_fixedSubgroup_d4Twist hK4 _ hτ3

theorem not_isPSolvable_fixedSubgroup_D4 (hK3 : ringChar K ≠ 3) (hK4 : 4 ≤ Nat.card K)
    (α : MulAut ↥(adjointGroup Tag.D4 K)) (hα3 : α ^ 3 = 1)
    (hα : α ∉ (MulAut.conj : ↥(adjointGroup Tag.D4 K) →* MulAut ↥(adjointGroup Tag.D4 K)).range) :
    ¬ CFSG.HallHigman.IsPSolvable 3 ↥(fixedSubgroup α) := by
  obtain ⟨g, a, σ, ε, hε, hαeq, hσ3, hcase⟩ :=
    CFSG.HardMathSupport.Lang.E6Descent.outer_cube_normal_form_cases α hα3 hα
  rcases hcase with ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩
  · subst h0
    exact not_isPSolvable_fixedSubgroup_field hK3 hα3 g a hσ3 h1 hαeq
  · exact not_isPSolvable_fixedSubgroup_graphField hK3 hα3 g a hε h0 hσ3 h1 hαeq
  · exact not_isPSolvable_fixedSubgroup_graphType hK3 hK4 hα3 ⟨g, a, σ, ε, hε, hσ3, ⟨h0, h1⟩, hαeq⟩

theorem outer295At_D4 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.D 4 q).Valid)
    (hp3 : q.p ≠ 3) (hq2 : q.card ≠ 2) : Inputs295c.Outer295At ⟨.D 4 q, hv⟩ := by
  intro S _ _ _ _ ⟨e⟩ _ _ _ α hα hout
  obtain ⟨K, _, _, hK, hKchar, ⟨φ⟩⟩ := exists_catEquiv_D4 q hv
  let θ : S ≃* ↥(adjointGroup Tag.D4 K) := e.trans φ
  have hK3 : ringChar K ≠ 3 := by rw [ringChar.eq K q.p]; exact hp3
  have hK4 : 4 ≤ Nat.card K := by rw [hK]; exact Inputs295c.four_le_card_of hp3 hq2
  have h := not_isPSolvable_fixedSubgroup_D4 hK3 hK4 _ (Inputs295d.congr_pow_three_eq_one θ hα)
    (Inputs295d.congr_not_mem_range_conj θ hout)
  refine Or.inr (Or.inr fun hs => h ?_)
  have hfix : fixedSubgroup (MulAut.congr θ α) =
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α).map θ.toMonoidHom :=
    Inputs295c.fixSubgroup_congr θ α
  rw [hfix]
  exact isPSolvable_of_mulEquiv
    ((CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α).equivMapOfInjective _ θ.injective) hs

end D4

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs295e
