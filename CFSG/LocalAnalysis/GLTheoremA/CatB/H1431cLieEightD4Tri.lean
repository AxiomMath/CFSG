module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieEightOrth
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitzBal2
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerCriterion

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (LieOrderBridge)
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns (eq_of_isSubnormal_of_quasisimple)
open scoped commutatorElement

local notation "fixSub" => CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup

theorem lieSEightD4_center_eq_bot {G : Type*} [Group G] (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) : Subgroup.center G = ⊥ := by
  refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G)).resolve_right fun h => ?_
  obtain ⟨a, b, hab⟩ := hnab
  exact hab (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a)

theorem lieSEightD4_isQuasisimple {G : Type*} [Group G] (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) : CFSG.Open.IsQuasisimple G := by
  have hZ := lieSEightD4_center_eq_bot hs hnab
  refine ⟨?_, (MulEquiv.isSimpleGroup_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans
    QuotientGroup.quotientBot)).2 hs⟩
  refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G)).resolve_left fun h => ?_
  obtain ⟨a, b, hab⟩ := hnab
  have hm : ⁅a, b⁆ ∈ commutator G :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
  rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hm
  exact hab hm

theorem lieSEightD4_noSp_of_normal_simple (hLO : LieOrderBridge) {P : Type} [Group P] [Finite P]
    (D J : Subgroup P) (hJD : J ≤ D) [(J.subgroupOf D).Normal]
    (hsol : Group.IsSolvable (↥D ⧸ J.subgroupOf D)) (hs : IsSimpleGroup ↥J)
    (hnab : ∃ a b : ↥J, a * b ≠ b * a) (hN : Nat.card ↥J ≠ 1056706560) :
    ¬ ∃ A : Subgroup P, GLAPComponent 3 D A ∧ catalogIs (PSimple 3 A) S8.L84.isSp48 := by
  rintro ⟨A, hA, hT⟩
  have hq : CFSG.Open.IsQuasisimple ↥J := lieSEightD4_isQuasisimple hs hnab
  have hAJ : A ≤ J :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfect_le_of_solvable_quotient hJD hsol
      hA.1 (glaPComponent_perfect hA)
  have hsn : IsSubnormal A J := isSubnormal_of_le_of_le hA.2.1 hAJ hJD
  have hAeq : A = J :=
    eq_of_isSubnormal_of_quasisimple hq hsn (glaPComponent_perfect hA)
      (CFSG.HardMathSupport.Solomon.LocalBalance.glaPComponent_ne_bot hA)
  subst hAeq
  have hc := lieSEight_card_quot_center hLO hA hq hT
  have hZ := lieSEightD4_center_eq_bot hs hnab
  rw [Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans
    QuotientGroup.quotientBot).toEquiv] at hc
  exact hN hc

theorem lieSEightD4_noSp_of_equiv (hLO : LieOrderBridge) {P : Type} [Group P] [Finite P]
    (D : Subgroup P) {H : Type} [Group H] (e : ↥D ≃* H) (M : Subgroup H) [hM : M.Normal]
    (hsol : Group.IsSolvable (H ⧸ M)) (hs : IsSimpleGroup ↥M)
    (hnab : ∃ a b : ↥M, a * b ≠ b * a) (hN : Nat.card ↥M ≠ 1056706560) :
    ¬ ∃ A : Subgroup P, GLAPComponent 3 D A ∧ catalogIs (PSimple 3 A) S8.L84.isSp48 := by
  let J₀ : Subgroup ↥D := M.map e.symm.toMonoidHom
  let J : Subgroup P := J₀.map D.subtype
  have hJD : J ≤ D := Subgroup.map_subtype_le J₀
  have hJ₀ : J.subgroupOf D = J₀ := Subgroup.comap_map_eq_self_of_injective D.subtype_injective J₀
  haveI hJ₀n : J₀.Normal := Subgroup.Normal.map hM e.symm.toMonoidHom e.symm.surjective
  haveI : (J.subgroupOf D).Normal := by rw [hJ₀]; exact hJ₀n
  let eq : H ⧸ M ≃* ↥D ⧸ J.subgroupOf D := QuotientGroup.congr M (J.subgroupOf D) e.symm hJ₀.symm
  have hsol' : Group.IsSolvable (↥D ⧸ J.subgroupOf D) :=
    Group.isSolvable_of_surjective (f := eq.toMonoidHom) eq.surjective
  let eJ : ↥M ≃* ↥J :=
    (Subgroup.equivMapOfInjective M e.symm.toMonoidHom e.symm.injective).trans
      (Subgroup.equivMapOfInjective J₀ D.subtype D.subtype_injective)
  have hsJ : IsSimpleGroup ↥J := (MulEquiv.isSimpleGroup_congr eJ).1 hs
  have hnabJ : ∃ a b : ↥J, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨eJ a, eJ b, fun h => hab (eJ.injective (by rw [map_mul, map_mul]; exact h))⟩
  have hNJ : Nat.card ↥J ≠ 1056706560 := by
    rw [← Nat.card_congr eJ.toEquiv]
    exact hN
  exact lieSEightD4_noSp_of_normal_simple hLO D J hJD hsol' hsJ hnabJ hNJ

@[expose] def LieSEightD4Fix (Γ : Type) [Group Γ] : Prop :=
  ∃ (H : Type) (_ : Group H) (_ : Γ ≃* H) (M : Subgroup H) (_ : M.Normal),
    Group.IsSolvable (H ⧸ M) ∧ IsSimpleGroup ↥M ∧ (∃ a b : ↥M, a * b ≠ b * a) ∧
      Nat.card ↥M ≠ 1056706560

theorem lieSEightD4Fix_of_equiv {Γ Γ' : Type} [Group Γ] [Group Γ'] (e : Γ ≃* Γ')
    (h : LieSEightD4Fix Γ') : LieSEightD4Fix Γ := by
  obtain ⟨H, _, e', M, hM, hsol, hs, hnab, hN⟩ := h
  exact ⟨H, inferInstance, e.trans e', M, hM, hsol, hs, hnab, hN⟩

theorem lieSEightD4Fix_of_simple {Γ H : Type} [Group Γ] [Group H] (e : Γ ≃* H)
    (hs : IsSimpleGroup H) (hnab : ∃ a b : H, a * b ≠ b * a) (hN : Nat.card H ≠ 1056706560) :
    LieSEightD4Fix Γ := by
  refine ⟨H, inferInstance, e, ⊤, inferInstance, ?_, ?_, ?_, ?_⟩
  · haveI : Subsingleton (H ⧸ (⊤ : Subgroup H)) := QuotientGroup.subsingleton_quotient_top
    exact Group.isSolvable_of_comm fun a b => Subsingleton.elim _ _
  · exact (MulEquiv.isSimpleGroup_congr (Subgroup.topEquiv (G := H))).2 hs
  · obtain ⟨a, b, hab⟩ := hnab
    exact ⟨Subgroup.topEquiv.symm a, Subgroup.topEquiv.symm b, fun h => hab (by
      have := congrArg (Subgroup.topEquiv (G := H)) h
      simpa using this)⟩
  · rw [Subgroup.card_top]
    exact hN

theorem lieSEightD4_noSp_of_fix (hLO : LieOrderBridge) {P : Type} [Group P] [Finite P]
    (D : Subgroup P) (h : LieSEightD4Fix ↥D) :
    ¬ ∃ A : Subgroup P, GLAPComponent 3 D A ∧ catalogIs (PSimple 3 A) S8.L84.isSp48 := by
  obtain ⟨H, _, e, M, hM, hsol, hs, hnab, hN⟩ := h
  exact lieSEightD4_noSp_of_equiv hLO D e M hsol hs hnab hN

section D4Cases

set_option linter.unusedSectionVars false



open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourInAux
open CFSG.HardMathSupport.Lang.D4Three (d4Graph)
open CFSG.RankThree.PartOne.CTP (fixedSubgroup mem_fixedSubgroup)

theorem lieSEightD4Fix_field {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ 3)
    {σ : K ≃+* K} (hσ : σ ≠ 1) :
    LieSEightD4Fix ↥(fixedSubgroup (entrywiseAdjointAut Tag.D4 σ)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by norm_num) hK
  have hchar : ringChar K = 2 := ringChar.eq K 2
  obtain ⟨hdvd, hcardfix⟩ := CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield
    Nat.prime_two (f := 3) (by norm_num) hK σ
  have hord : orderOf σ = 3 :=
    ((Nat.dvd_prime Nat.prime_three).1 hdvd).resolve_left fun h => hσ (orderOf_eq_one_iff.1 h)
  have h2 : Nat.card ↥(fixSubfield σ) = 2 := by
    rw [hcardfix, hord]
    norm_num
  have hΓJ := entrywiseFixedGroup_eq_fixedFieldImage_of_ringChar_two (τ := Tag.D4)
    (Or.inr (Or.inr (Or.inl rfl))) hchar σ
  have E4 := CFSG.LieType.SeitzGeneration.ExcOuterLeOne.fixedEquivOfEq (τ := Tag.D4) σ hΓJ
  have hm : CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥(adjointGroup Tag.D4 (fixSubfield σ))
      .POmegaPlus 4 2 1 :=
    ⟨⟨Nat.prime_two, by norm_num, le_rfl⟩, fixSubfield σ, inferInstance, inferInstance,
      by rw [h2]; norm_num,
      ⟨(CFSG.HardMathSupport.Dickson.Bal207.D4Graph.isoAdj (fixSubfield σ)).symm⟩⟩
  have hcard := (CFSG.Timmesfeld.card_statedClassicalModel_two hm).2.2.2.1 rfl
  refine lieSEightD4Fix_of_simple E4 (isSimpleGroup_adjointGroup_D4 _)
    (opposite_simple_root_noncommutativity Tag.D4 (fixSubfield σ)).2.2.1 ?_
  rw [hcard]
  simp only [ordD]
  decide

theorem lieSEightD4Fix_graphField {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ 3)
    {α : MulAut ↥(adjointGroup Tag.D4 K)} (hα3 : α ^ 3 = 1) {g : ↥(adjointGroup Tag.D4 K)}
    {a : Fin Tag.D4.rank → Kˣ} {σ : K ≃+* K} {ε : ℕ} (hε : ε = 1 ∨ ε = 2) (hσ3 : σ ^ 3 = 1)
    (hσ1 : σ ≠ 1)
    (hαeq : α = MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε)) :
    LieSEightD4Fix ↥(fixedSubgroup α) := by
  classical
  obtain ⟨T, hT, hT3, hT1, hσT⟩ := OuterFourSeitz.exists_frobenius_eight hK hσ3 hσ1
  obtain ⟨ψ, hFψ⟩ := OuterFourSeitz.graphField_conj_fixed hK hT hT3 hT1 hσT hε hα3 hαeq
  obtain ⟨e₀⟩ := OuterFourSeitz.nonempty_fixed_d4Twist_equiv_cat' hK T hT
    (CFSG.LieType.SeitzGeneration.ExcWideThree.d4GfTwist_eq_or T σ ε)
  have E3 : ↥(fixedSubgroup α) ≃* ↥(fixedSubgroup (ψ * α * ψ⁻¹)) :=
    (Subgroup.equivMapOfInjective _ ψ.toMonoidHom ψ.injective).trans
      (MulEquiv.subgroupCongr (D4FixedAux.fixed_map_conj ψ α))
  let Ffix : ↥(fixedSubgroup α) ≃*
      (TauCeti.CFSGIndex.lie OuterFourSeitz.trialityTwoIndex).Group :=
    E3.trans ((MulEquiv.subgroupCongr hFψ).trans e₀)
  have hmodel := CFSG.LieType.SeitzGeneration.chevalleyModel_cat_trialityD4
    OuterFourSeitz.valid_trialityD4_two
  have hsC : IsSimpleGroup (TauCeti.CFSGIndex.lie OuterFourSeitz.trialityTwoIndex).Group :=
    (CFSG.LieType.Simplicity.fam_3d4_simplicity _ _ _ hmodel).2
  have hcardC : Nat.card (TauCeti.CFSGIndex.lie OuterFourSeitz.trialityTwoIndex).Group =
      ordTrialityD4 2 := CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hmodel
  haveI : Finite (TauCeti.CFSGIndex.lie OuterFourSeitz.trialityTwoIndex).Group :=
    Nat.finite_of_card_ne_zero (by rw [hcardC]; decide)
  obtain ⟨u, v, huv⟩ : ∃ u v : (TauCeti.CFSGIndex.lie OuterFourSeitz.trialityTwoIndex).Group,
      u * v ≠ v * u :=
    OuterFourSeitz.exists_noncomm_of_four_dvd (by rw [hcardC]; decide)
  refine lieSEightD4Fix_of_simple Ffix hsC ⟨u, v, huv⟩ ?_
  rw [hcardC]
  simp only [ordTrialityD4]
  decide

theorem lieSEightD4Fix_graph {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ 3)
    {α : MulAut ↥(adjointGroup Tag.D4 K)} (hα3 : α ^ 3 = 1)
    (hA : CFSG.LieType.SeitzGeneration.ExcWideThree.D4ElemType α fun ε σ => ε ≠ 0 ∧ σ = 1) :
    LieSEightD4Fix ↥(fixedSubgroup α) := by
  classical
  rcases OuterFourSeitz2.graphFix_cases hK hα3 hA with ⟨F', _, _, hF', ⟨Fg⟩⟩ | hPGU
  · obtain ⟨hs, -, -, hcard⟩ := OuterFourSeitz2.g2Props hF' Fg
    haveI := hs
    haveI : Finite ↥(fixedSubgroup α) :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; simp only [ordG2]; decide)
    exact lieSEightD4Fix_of_simple (MulEquiv.refl _) hs
      (OuterFourSeitz.exists_noncomm_of_four_dvd (by rw [hcard]; simp only [ordG2]; decide))
      (by rw [hcard]; simp only [ordG2]; decide)
  · obtain ⟨M, hM⟩ := OuterFourSeitz2.pguData_of_isoPGUThree hPGU
    haveI := hM.normal
    haveI := hM.simple
    have hsol : Group.IsSolvable (↥(fixedSubgroup α) ⧸ M) := by
      refine Group.isSolvable_of_comm fun a b => ?_
      induction a using QuotientGroup.induction_on with
      | H x =>
        induction b using QuotientGroup.induction_on with
        | H y =>
          rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
          simpa [mul_assoc] using hM.comm y⁻¹ x⁻¹
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hc := CFSG.RankThree.PartTwo.KFacts.KS14.card_projSU_three_mul_gcd 2 3 (by norm_num)
    have hMcard : Nat.card ↥M = 5515776 := by
      rw [Nat.card_congr hM.model.some.toEquiv]
      norm_num at hc
      omega
    haveI : Finite ↥M := Nat.finite_of_card_ne_zero (by rw [hMcard]; norm_num)
    exact ⟨↥(fixedSubgroup α), inferInstance, MulEquiv.refl _, M, hM.normal, hsol, hM.simple,
      OuterFourSeitz.exists_noncomm_of_four_dvd (by rw [hMcard]; norm_num),
      by rw [hMcard]; norm_num⟩

theorem lieSEightD4Tri_holds (hLO : LieOrderBridge) : LieSEightD4Tri := by
  rintro S _ _ hM β - hβ3 hnin ⟨J, hJ, hT⟩
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := hM
  obtain ⟨e'⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_statedProj_equiv_adjointGroup K
  let θ : S ≃* adjointGroup Tag.D4 K := e.trans e'
  have hα3 : MulAut.congr θ β ^ 3 = 1 := by rw [← map_pow, hβ3, map_one]
  have hfx : ∀ {G : Type} [Group G] (δ : MulAut G), fixSub δ = fixedSubgroup δ := fun δ =>
    Subgroup.ext fun _ => Iff.rfl
  have eD : ↥(fixSub β) ≃* ↥(fixedSubgroup (MulAut.congr θ β)) :=
    (MulEquiv.subgroupCongr (hfx β)).trans
      ((Subgroup.equivMapOfInjective _ θ.toMonoidHom θ.injective).trans
        (MulEquiv.subgroupCongr (D4FixedAux.fixed_map_congr θ β)))
  have hfix : LieSEightD4Fix ↥(fixedSubgroup (MulAut.congr θ β)) := by
    rcases d4_cube_trichotomy_model hK (MulAut.congr θ β) hα3 with ⟨g, hg⟩ | ⟨σ, ψ, hσ, hψ⟩ |
      ⟨g, a, σ, ε, hε, hαeq⟩
    · exact absurd (congr_eq_conj_imp θ β g hg.symm).symm (hnin _)
    · have E3 : ↥(fixedSubgroup (MulAut.congr θ β)) ≃*
          ↥(fixedSubgroup (entrywiseAdjointAut Tag.D4 σ)) :=
        ((Subgroup.equivMapOfInjective _ ψ.toMonoidHom ψ.injective).trans
          (MulEquiv.subgroupCongr (D4FixedAux.fixed_map_conj ψ (MulAut.congr θ β)))).trans
          (MulEquiv.subgroupCongr (by rw [hψ]))
      exact lieSEightD4Fix_of_equiv E3 (lieSEightD4Fix_field hK hσ)
    · have hσ3 : σ ^ 3 = 1 :=
        CFSG.HardMathSupport.Lang.E6Descent.cube_normal_form_sigma_cube (hαeq ▸ hα3)
      by_cases hσ1 : σ = 1
      · subst hσ1
        exact lieSEightD4Fix_graph hK hα3
          ⟨g, a, 1, ε, by omega, by simp, ⟨by omega, rfl⟩, hαeq⟩
      · exact lieSEightD4Fix_graphField hK hα3 hε hσ3 hσ1 hαeq
  exact lieSEightD4_noSp_of_fix hLO (fixSub β) (lieSEightD4Fix_of_equiv eD hfix) ⟨J, hJ, hT⟩

end D4Cases

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
