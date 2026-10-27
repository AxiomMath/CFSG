module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerLift
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.Shared
public import CFSG.RankThree.PartTwo.Census.Classical.EvenPrimes
public import CFSG.RankThree.Chevalley.OddRankOneExceptionalModel
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.ExcOrder
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2TwAModel
public import CFSG.LocalAnalysis.StandardType.GGTableBExcRank
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Basic
public import CFSG.LocalAnalysis.StandardType.GGTableBF4Rank
public import CFSG.HardMathSupport.Lang.E6Descent.RankE6
public import CFSG.RankThree.PartTwo.Census.Exceptional.E6Two
public import CFSG.RankThree.PartOne.Census3.Interface
public import CFSG.RankThree.OddKernel.ThreeComplementQuotient
public import CFSG.RankThree.PartOne.KE.A1Weyl
public import CFSG.LieType.Chevalley.GraphFixedHighestRoot
public import CFSG.LieType.Chevalley.PerfectSimpleRoot
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis.E7Arith
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.E8Arith
public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87MultMilestone
public import CFSG.LieType.SeitzGeneration.ExcPlaneModel
public import CFSG.Adapters.TauCetiExceptional.EvenAll
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.ChevIndep
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.GenPeriodic
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.OuterTwist
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.LieType.SeitzGeneration.ExcPlaneFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011LabUniq
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.Milestones.CL_LIT_SQTK_simple_list
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.Quasithin.Background.B5Statement
public import CFSG.Quasithin.EmptyFaithful.S146zYFacts
public import CFSG.Quasithin.EmptyFaithful.S146zYRes
public import CFSG.Quasithin.H13.NQCoreP134Main
public import CFSG.Quasithin.Vol2.Ch1Sec3E9Inputs
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A1Untwisted
public import Certificates.Certificate8026Base

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.StandardType
open CFSG.LieType.Chevalley CFSG.Timmesfeld.ExceptionalOrders

theorem exists_elemAbelian_le_normalizer_rootSubgroup
    {τ : Tag} {F : Type} [Field F] [Finite F]
    {p : ℕ} [CharP F 2]
    {V : Subgroup (adjointGroup τ F)}
    (hV : V ≤ (torusGroup τ F).subgroupOf (adjointGroup τ F))
    (hVp : ∀ g ∈ V, g ^ p = 1)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    ∃ (E X : Subgroup (adjointGroup τ F)),
      X ≠ ⊥ ∧ IsPGroup 2 X ∧ IsElemAbelian p E ∧ Nat.card E = Nat.card V ∧
        E ≤ Subgroup.normalizer (X : Set (adjointGroup τ F)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨V, (rootSubgroup τ F α).subgroupOf (adjointGroup τ F), ?_, ?_, ?_, rfl, ?_⟩
  · rw [← Subgroup.one_lt_card_iff_ne_bot]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (rootSubgroup_le_adjointGroup α)).toEquiv,
      card_rootSubgroup]
    exact Finite.one_lt_card
  · have hroot2 : IsPGroup 2 (rootSubgroup τ F α) := by
      refine IsPGroup.iff_orderOf.2 fun g => ?_
      by_cases hg : (g : (Module.End F (RootModule τ F))ˣ) = 1
      · refine ⟨0, ?_⟩
        rw [pow_zero]
        have hg1 : g = 1 := Subtype.ext hg
        rw [hg1]
        simp
      · refine ⟨1, ?_⟩
        rw [pow_one, (Subgroup.orderOf_coe g).symm]
        exact orderOf_eq_of_mem_rootSubgroup g.2 hg
    exact hroot2.of_equiv
      (Subgroup.subgroupOfEquivOfLe (rootSubgroup_le_adjointGroup α)).symm
  · refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => hVp x hx⟩
    apply Subtype.ext
    apply Subtype.ext
    have ha := Subgroup.mem_subgroupOf.mp (hV a.2)
    have hb := Subgroup.mem_subgroupOf.mp (hV b.2)
    simpa [Subgroup.coe_mul] using CFSG.RankThree.PartOne.KE.torusGroup_comm ha hb
  · intro v hv
    rw [Subgroup.mem_normalizer_iff'']
    intro h
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    have hvN : (v : ModGL τ F) ∈
        Subgroup.normalizer (rootSubgroup τ F α : Set (ModGL τ F)) :=
      torusGroup_le_normalizer_rootSubgroup hα (Subgroup.mem_subgroupOf.mp (hV hv))
    rw [Subgroup.mem_normalizer_iff''] at hvN
    have hcoe : ((v⁻¹ * h * v : adjointGroup τ F) : ModGL τ F) =
        (v : ModGL τ F)⁻¹ * (h : ModGL τ F) * (v : ModGL τ F) := rfl
    rw [hcoe]
    exact hvN (h : ModGL τ F)

theorem le_evenRank_adjointGroup_of_torusSubgroup
    {τ : Tag} {F : Type} [Field F] [Finite F]
    {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) [CharP F 2]
    {V : Subgroup (adjointGroup τ F)}
    (hV : V ≤ (torusGroup τ F).subgroupOf (adjointGroup τ F))
    (hVp : ∀ g ∈ V, g ^ p = 1)
    (hcard : Nat.card V = p ^ m)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    m ≤ evenRank (adjointGroup τ F) := by
  obtain ⟨E, X, hX, hX2, hE, hEcard, hXE⟩ :=
    exists_elemAbelian_le_normalizer_rootSubgroup hV hVp hα
  exact le_evenRank_of_normalizer hp hp2 hX hX2 hE (hEcard.trans hcard) hXE

theorem le_evenRank_adjointGroup_of_torusPow
    {τ : Tag} {F : Type} [Field F] [Finite F]
    {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) [CharP F 2]
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hcard : Nat.card (TableBExc.torusPow τ F p) = p ^ m) :
    m ≤ evenRank (adjointGroup τ F) := by
  have hV : TableBExc.torusPow τ F p ≤
      (torusGroup τ F).subgroupOf (adjointGroup τ F) :=
    fun g hg => Subgroup.mem_subgroupOf.mpr ((TableBExc.mem_torusPow.mp hg).1)
  have hVp : ∀ g ∈ TableBExc.torusPow τ F p, g ^ p = 1 :=
    fun g hg => (TableBExc.mem_torusPow.mp hg).2
  exact le_evenRank_adjointGroup_of_torusSubgroup hp hp2 hV hVp hcard hα

section E6Torus


theorem exists_elemAbelian_243_le_torusGroup_E6 {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4) :
    ∃ E : Subgroup (adjointGroup .E6 K), IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 5 ∧
      E ≤ (torusGroup .E6 K).subgroupOf (adjointGroup .E6 K) := by
  have h3 : 3 ∣ Nat.card K - 1 := by
    simpa [hK] using (show 3 ∣ (4 - 1) by norm_num)
  have hle : torusGroup .E6 K ≤ adjointGroup .E6 K :=
    (Subgroup.closure_le _).2 (by
      rintro _ ⟨⟨i, t⟩, rfl⟩
      exact torusElt_mem_adjointGroup i t)
  let Θ : (Fin Tag.E6.rank → Kˣ) →* adjointGroup .E6 K :=
    (Subgroup.inclusion hle).comp (torusCoordHom .E6 K)
  have hker : Θ.ker = (zpowMatrix (G := Kˣ) Tag.E6.cartan).ker := by
    ext t
    constructor
    · intro h
      exact (torusCoordHom_eq_one_iff t).mp
        ((Subgroup.inclusion_injective hle) (by simpa [Θ] using h))
    · intro h
      have h' : torusCoordHom .E6 K t = 1 := (torusCoordHom_eq_one_iff t).mpr h
      simpa [Θ] using congrArg (Subgroup.inclusion hle) h'
  obtain ⟨T₀, hT₀, hT₀c⟩ :=
    CFSG.HardMathSupport.Lang.E6Descent.exists_torsion_three_pi (K := K) h3
  let T : Subgroup (Fin Tag.E6.rank → Kˣ) := T₀
  have hT : ∀ x ∈ T, x ^ 3 = 1 := hT₀
  have hTc : Nat.card ↥T = 3 ^ 6 := hT₀c
  let f : ↥T →* adjointGroup .E6 K :=
    { toFun := fun x => Θ (x : Fin Tag.E6.rank → Kˣ)
      map_one' := map_one Θ
      map_mul' := fun x y =>
        map_mul Θ (x : Fin Tag.E6.rank → Kˣ) (y : Fin Tag.E6.rank → Kˣ) }
  have hfker_le : Nat.card f.ker ≤ 3 := by
    refine (Nat.card_le_card_of_injective ?_ ?_).trans
      (hker ▸ CFSG.HardMathSupport.Lang.E6Descent.card_ker_zpowMatrix_cartan_E6_le)
    · intro x
      exact ⟨(x.1 : Fin Tag.E6.rank → Kˣ), by
        have hx := x.2
        rw [MonoidHom.mem_ker] at hx ⊢
        simpa [f] using hx⟩
    · intro x y hxy
      apply Subtype.ext
      simpa using congrArg (fun z : Θ.ker => (z : Fin Tag.E6.rank → Kˣ)) hxy
  have hcard : Nat.card ↥T = Nat.card f.range * Nat.card f.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  have hcont : f.range ≤ (torusGroup .E6 K).subgroupOf (adjointGroup .E6 K) := by
    rintro y ⟨x, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr (by simpa [f, Θ] using
      (torusCoordHom .E6 K (x.1 : Fin Tag.E6.rank → Kˣ)).2)
  have hE : IsElemAbelian 3 f.range := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨x, hx⟩ := a.2
      obtain ⟨y, hy⟩ := b.2
      apply Subtype.ext
      change (a : adjointGroup .E6 K) * b = (b : adjointGroup .E6 K) * a
      rw [← hx, ← hy]
      change f x * f y = f y * f x
      rw [← map_mul, ← map_mul, mul_comm]
    · rintro _ ⟨x, rfl⟩
      have hx3 : x ^ 3 = 1 := Subtype.ext (hT x x.2)
      rw [← map_pow, hx3, map_one]
  have htorus : Nat.card (torusGroup .E6 K) = 3 ^ 5 := by
    have h := card_torusGroup_E6 (K := K)
    rw [hK] at h
    norm_num at h
    omega
  have htorusSub : Nat.card ((torusGroup .E6 K).subgroupOf (adjointGroup .E6 K)) = 3 ^ 5 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, htorus]
  have hcard_le : Nat.card f.range ≤ 3 ^ 5 :=
    (Subgroup.card_le_of_le hcont).trans_eq htorusSub
  have hcard_ge : 3 ^ 5 ≤ Nat.card f.range := by
    have h : Nat.card ↥T ≤ Nat.card f.range * 3 := by
      calc Nat.card ↥T = Nat.card f.range * Nat.card f.ker := hcard
        _ ≤ Nat.card f.range * 3 := Nat.mul_le_mul_left _ hfker_le
    rw [hTc] at h
    norm_num at h ⊢
    omega
  exact ⟨f.range, hE, hcard_le.antisymm hcard_ge, hcont⟩

end E6Torus

open CFSG.Blueprint.Multiplier

theorem not_dvd_card_center_of_markedModel_E6 {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hQ : CFSG.IsQuasisimple K) (hM : MarkedModel lab (K ⧸ Subgroup.center K))
    (htag : lab.tag = .E6) {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) :
    ¬ p ∣ Nat.card (Subgroup.center K) := by
  obtain ⟨t, r, n⟩ := lab
  simp only at htag hM
  subst htag
  obtain ⟨-, ⟨eM⟩⟩ := CFSG.Milestones.cl_lit_griess_schur_multipliers_all_native_models
    (K ⧸ Subgroup.center K) (markTag ⟨.E6, r, n⟩) (markRank ⟨.E6, r, n⟩)
    (markChar ⟨.E6, r, n⟩) (markDeg ⟨.E6, r, n⟩) hM
  have hg : genericOrders (markTag ⟨.E6, r, n⟩) (markRank ⟨.E6, r, n⟩)
      (markChar ⟨.E6, r, n⟩) (markDeg ⟨.E6, r, n⟩) = (Nat.gcd 3 (2 ^ n - 1), 1) := rfl
  have he : exceptionalOrders (markTag ⟨.E6, r, n⟩) (markRank ⟨.E6, r, n⟩)
      (markChar ⟨.E6, r, n⟩) (markDeg ⟨.E6, r, n⟩) = (1, 1) := rfl
  have hcard : Nat.card (griessHopfMultiplier (K ⧸ Subgroup.center K)) =
      Nat.gcd 3 (2 ^ n - 1) := by
    rw [Nat.card_congr eM.toEquiv,
      CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_generic_exceptional', hg, he]
    norm_num
  haveI : Finite (griessHopfMultiplier (K ⧸ Subgroup.center K)) :=
    Nat.finite_of_card_ne_zero
      (by rw [hcard]; exact (Nat.gcd_pos_of_pos_left _ (by norm_num)).ne')
  have hdvd := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_center_dvd_hopf hQ
    (MulEquiv.refl (K ⧸ Subgroup.center K))
  rw [hcard] at hdvd
  intro h
  have h3 : p ∣ 3 := (h.trans hdvd).trans (Nat.gcd_dvd_left _ _)
  exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3)

private theorem not_dvd_card_center_F4 {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hQ : CFSG.IsQuasisimple K) (hM : MarkedModel lab (K ⧸ Subgroup.center K))
    (htag : lab.tag = .F4) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ∣ Nat.card (Subgroup.center K) := by
  obtain ⟨t, r, n⟩ := lab
  simp only at htag hM
  subst htag
  obtain ⟨-, ⟨eM⟩⟩ := CFSG.Milestones.cl_lit_griess_schur_multipliers_all_native_models
    (K ⧸ Subgroup.center K) (markTag ⟨.F4, r, n⟩) (markRank ⟨.F4, r, n⟩)
    (markChar ⟨.F4, r, n⟩) (markDeg ⟨.F4, r, n⟩) hM
  have hg : genericOrders (markTag ⟨.F4, r, n⟩) (markRank ⟨.F4, r, n⟩)
      (markChar ⟨.F4, r, n⟩) (markDeg ⟨.F4, r, n⟩) = (1, 1) := rfl
  have he : exceptionalOrders (markTag ⟨.F4, r, n⟩) (markRank ⟨.F4, r, n⟩)
      (markChar ⟨.F4, r, n⟩) (markDeg ⟨.F4, r, n⟩) = (if n = 1 then 2 else 1, 1) := by
    by_cases hn : n = 1
    · subst hn
      simp [exceptionalOrders, markTag, markRank, markChar, markDeg]
    · simp [exceptionalOrders, markTag, markRank, markChar, markDeg, hn]
  have hcard : Nat.card (griessHopfMultiplier (K ⧸ Subgroup.center K)) =
      (if n = 1 then 2 else 1) := by
    rw [Nat.card_congr eM.toEquiv,
      CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_generic_exceptional', hg, he]
    by_cases hn : n = 1 <;> simp [hn]
  haveI : Finite (griessHopfMultiplier (K ⧸ Subgroup.center K)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; by_cases hn : n = 1 <;> simp [hn])
  have hdvd := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_center_dvd_hopf hQ
    (MulEquiv.refl (K ⧸ Subgroup.center K))
  rw [hcard] at hdvd
  intro h
  by_cases hn : n = 1
  · have hp2dvd : p ∣ 2 := by simpa [hn] using h.trans hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hp2dvd)
  · have hp1 : p ∣ 1 := by simpa [hn] using h.trans hdvd
    exact hp.one_lt.ne' (Nat.dvd_one.1 hp1)

private theorem center_eq_bot_of_E6_one {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hQ : CFSG.IsQuasisimple K) (hM : MarkedModel lab (K ⧸ Subgroup.center K))
    (htag : lab.tag = .E6) (hn : lab.n = 1) :
    Subgroup.center K = ⊥ := by
  obtain ⟨t, r, n⟩ := lab
  simp only at htag hM hn
  subst htag
  subst hn
  obtain ⟨-, ⟨eM⟩⟩ := CFSG.Milestones.cl_lit_griess_schur_multipliers_all_native_models
    (K ⧸ Subgroup.center K) (markTag ⟨.E6, r, 1⟩) (markRank ⟨.E6, r, 1⟩)
    (markChar ⟨.E6, r, 1⟩) (markDeg ⟨.E6, r, 1⟩) hM
  have hg : genericOrders (markTag ⟨.E6, r, 1⟩) (markRank ⟨.E6, r, 1⟩)
      (markChar ⟨.E6, r, 1⟩) (markDeg ⟨.E6, r, 1⟩) = (Nat.gcd 3 (2 ^ 1 - 1), 1) := rfl
  have he : exceptionalOrders (markTag ⟨.E6, r, 1⟩) (markRank ⟨.E6, r, 1⟩)
      (markChar ⟨.E6, r, 1⟩) (markDeg ⟨.E6, r, 1⟩) = (1, 1) := rfl
  have hcard : Nat.card (griessHopfMultiplier (K ⧸ Subgroup.center K)) = 1 := by
    rw [Nat.card_congr eM.toEquiv,
      CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_generic_exceptional', hg, he]
    norm_num
  haveI : Finite (griessHopfMultiplier (K ⧸ Subgroup.center K)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hdvd := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_center_dvd_hopf hQ
    (MulEquiv.refl (K ⧸ Subgroup.center K))
  rw [hcard, Nat.dvd_one] at hdvd
  exact Subgroup.card_eq_one.mp hdvd

theorem rk2_low_f4 (K : Type) [Group K] [Finite K] (lab : GLALabel)
    (hK : Rk2IsLabel K lab) (htag : lab.tag = .F4) (hn : 2 ≤ lab.n) :
    4 ≤ evenRank K := by
  obtain ⟨t, r, n⟩ := lab
  simp only at htag
  subst htag
  obtain ⟨hQ, hl, hM⟩ := rk2_model_of_isLabel hK
  have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .F4 0 2 n :=
    lieModel_of_markedModel_F4 rfl hM
  obtain ⟨-, F, hFld, hFin, hFcard, ⟨φ⟩⟩ :=
    hM'.chevalleyExceptionalModel (by decide : StatedLieTag.F4 ∈ chevalleyExceptionalTags)
  letI : Field F := hFld
  letI : Finite F := hFin
  have hn1 : 1 ≤ n := hl.1
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hn1 hFcard
  obtain ⟨p, hp, hp2, hpd⟩ := CFSG.RankThree.Chevalley.exists_odd_prime_dvd_two_pow_sub_one hn
  have hpq : p ∣ Nat.card F - 1 := by rw [hFcard]; exact hpd
  have hcard : Nat.card (TableBF4.torusPow F p) = p ^ 4 :=
    TableBF4.card_torusPow hp hpq
  have hV : TableBF4.torusPow F p ≤
      (torusGroup .F4 F).subgroupOf (adjointGroup .F4 F) :=
    fun g hg => Subgroup.mem_subgroupOf.mpr ((TableBF4.mem_torusPow.mp hg).1)
  have hVp : ∀ g ∈ TableBF4.torusPow F p, g ^ p = 1 :=
    fun g hg => (TableBF4.mem_torusPow.mp hg).2
  obtain ⟨E, X, hX, hX2, hE, hEcard, hXE⟩ :=
    exists_elemAbelian_le_normalizer_rootSubgroup (p := p) hV hVp
      (isRoot_single .F4 0)
  have hEcard' : Nat.card E = p ^ 4 := hEcard.trans hcard
  let θ : K ⧸ Subgroup.center K ≃* adjointGroup .F4 F :=
    φ.trans (CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.adjointQuotientEquiv .F4 F)
  have hQ' : CFSG.IsQuasisimple K :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff K).2.2.1.2 hQ
  have hZ : ¬ p ∣ Nat.card (Subgroup.center K) :=
    not_dvd_card_center_F4 hQ' hM rfl hp hp2
  exact le_evenRank_of_center_quotient θ hp hp2 hZ hX hX2 hE hEcard' hXE

theorem rk2_low_e7 (K : Type) [Group K] [Finite K] (lab : GLALabel)
    (hK : Rk2IsLabel K lab) (htag : lab.tag = .E7) (hn : 2 ≤ lab.n) :
    7 ≤ evenRank K := by
  obtain ⟨t, r, n⟩ := lab
  simp only at htag
  subst htag
  obtain ⟨hQ, hl, hM⟩ := rk2_model_of_isLabel hK
  have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .E7 0 2 n :=
    lieModel_of_markedModel_E7 rfl hM
  obtain ⟨-, F, hFld, hFin, hFcard, ⟨φ⟩⟩ :=
    hM'.chevalleyExceptionalModel (by decide : StatedLieTag.E7 ∈ chevalleyExceptionalTags)
  letI : Field F := hFld
  letI : Finite F := hFin
  have hn1 : 1 ≤ n := hl.1
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hn1 hFcard
  obtain ⟨p, hp, hp2, hpd⟩ := CFSG.RankThree.Chevalley.exists_odd_prime_dvd_two_pow_sub_one hn
  have hpq : p ∣ Nat.card F - 1 := by rw [hFcard]; exact hpd
  have hcard : Nat.card (TableBExc.torusPow .E7 F p) = p ^ 7 :=
    TableBExc.card_torusPow_E7 hp hpq
  have hV : TableBExc.torusPow .E7 F p ≤
      (torusGroup .E7 F).subgroupOf (adjointGroup .E7 F) :=
    fun g hg => Subgroup.mem_subgroupOf.mpr ((TableBExc.mem_torusPow.mp hg).1)
  have hVp : ∀ g ∈ TableBExc.torusPow .E7 F p, g ^ p = 1 :=
    fun g hg => (TableBExc.mem_torusPow.mp hg).2
  obtain ⟨E, X, hX, hX2, hE, hEcard, hXE⟩ :=
    exists_elemAbelian_le_normalizer_rootSubgroup (p := p) hV hVp
      (isRoot_single .E7 0)
  have hEcard' : Nat.card E = p ^ 7 := hEcard.trans hcard
  let θ : K ⧸ Subgroup.center K ≃* adjointGroup .E7 F :=
    φ.trans (CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.adjointQuotientEquiv .E7 F)
  have hQ' : CFSG.IsQuasisimple K :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff K).2.2.1.2 hQ
  have hz : Subgroup.center K = ⊥ :=
    CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis.center_eq_bot_of_E7
      hQ' hl.1 hFcard φ
  have hZ : ¬ p ∣ Nat.card (Subgroup.center K) := by
    rw [hz, Subgroup.card_bot]
    exact fun h => hp.ne_one (Nat.dvd_one.1 h)
  exact le_evenRank_of_center_quotient θ hp hp2 hZ hX hX2 hE hEcard' hXE

theorem rk2_low_e8 (K : Type) [Group K] [Finite K] (lab : GLALabel)
    (hK : Rk2IsLabel K lab) (htag : lab.tag = .E8) (hn : 2 ≤ lab.n) :
    8 ≤ evenRank K := by
  obtain ⟨t, r, n⟩ := lab
  simp only at htag
  subst htag
  obtain ⟨hQ, hl, hM⟩ := rk2_model_of_isLabel hK
  have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .E8 0 2 n :=
    lieModel_of_markedModel_E8 rfl hM
  obtain ⟨-, F, hFld, hFin, hFcard, ⟨φ⟩⟩ :=
    hM'.chevalleyExceptionalModel (by decide : StatedLieTag.E8 ∈ chevalleyExceptionalTags)
  letI : Field F := hFld
  letI : Finite F := hFin
  have hn1 : 1 ≤ n := hl.1
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hn1 hFcard
  obtain ⟨p, hp, hp2, hpd⟩ := CFSG.RankThree.Chevalley.exists_odd_prime_dvd_two_pow_sub_one hn
  have hpq : p ∣ Nat.card F - 1 := by rw [hFcard]; exact hpd
  have hcard : Nat.card (TableBExc.torusPow .E8 F p) = p ^ 8 :=
    TableBExc.card_torusPow_E8 hp hpq
  have hV : TableBExc.torusPow .E8 F p ≤
      (torusGroup .E8 F).subgroupOf (adjointGroup .E8 F) :=
    fun g hg => Subgroup.mem_subgroupOf.mpr ((TableBExc.mem_torusPow.mp hg).1)
  have hVp : ∀ g ∈ TableBExc.torusPow .E8 F p, g ^ p = 1 :=
    fun g hg => (TableBExc.mem_torusPow.mp hg).2
  obtain ⟨E, X, hX, hX2, hE, hEcard, hXE⟩ :=
    exists_elemAbelian_le_normalizer_rootSubgroup (p := p) hV hVp
      (isRoot_single .E8 0)
  have hEcard' : Nat.card E = p ^ 8 := hEcard.trans hcard
  let θ : K ⧸ Subgroup.center K ≃* adjointGroup .E8 F :=
    φ.trans (CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.adjointQuotientEquiv .E8 F)
  have hQ' : CFSG.IsQuasisimple K :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff K).2.2.1.2 hQ
  have hz : Subgroup.center K = ⊥ :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.center_eq_bot_of_E8
      hQ' hl.1 hFcard φ
  have hZ : ¬ p ∣ Nat.card (Subgroup.center K) := by
    rw [hz, Subgroup.card_bot]
    exact fun h => hp.ne_one (Nat.dvd_one.1 h)
  exact le_evenRank_of_center_quotient θ hp hp2 hZ hX hX2 hE hEcard' hXE

theorem rk2_low_e6_of_three_le (K : Type) [Group K] [Finite K] (lab : GLALabel)
    (hK : Rk2IsLabel K lab) (htag : lab.tag = .E6) (hn : 3 ≤ lab.n) :
    6 ≤ evenRank K := by
  obtain ⟨t, r, n⟩ := lab
  simp only at htag
  subst htag
  obtain ⟨hQ, hl, hM⟩ := rk2_model_of_isLabel hK
  have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .E6 0 2 n :=
    lieModel_of_markedModel_E6 rfl hM
  obtain ⟨-, F, hFld, hFin, hFcard, ⟨φ⟩⟩ :=
    hM'.chevalleyExceptionalModel (by decide : StatedLieTag.E6 ∈ chevalleyExceptionalTags)
  letI : Field F := hFld
  letI : Finite F := hFin
  have hn1 : 1 ≤ n := hl.1
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hn1 hFcard
  obtain ⟨p, hp, hp5, hpd⟩ := CFSG.RankThree.PartTwo.Census.exists_prime_five_le_dvd_two_pow_sub_one hn
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have hpq : p ∣ Nat.card F - 1 := by rw [hFcard]; exact hpd
  have hcard : Nat.card (TableBExc.torusPow .E6 F p) = p ^ 6 :=
    TableBExc.card_torusPow_E6 hp hp3 hpq
  have hV : TableBExc.torusPow .E6 F p ≤
      (torusGroup .E6 F).subgroupOf (adjointGroup .E6 F) :=
    fun g hg => Subgroup.mem_subgroupOf.mpr ((TableBExc.mem_torusPow.mp hg).1)
  have hVp : ∀ g ∈ TableBExc.torusPow .E6 F p, g ^ p = 1 :=
    fun g hg => (TableBExc.mem_torusPow.mp hg).2
  obtain ⟨E, X, hX, hX2, hE, hEcard, hXE⟩ :=
    exists_elemAbelian_le_normalizer_rootSubgroup (p := p) hV hVp
      (isRoot_single .E6 0)
  have hEcard' : Nat.card E = p ^ 6 := hEcard.trans hcard
  let θ : K ⧸ Subgroup.center K ≃* adjointGroup .E6 F :=
    φ.trans (CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.adjointQuotientEquiv .E6 F)
  have hQ' : CFSG.IsQuasisimple K :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff K).2.2.1.2 hQ
  have hZ : ¬ p ∣ Nat.card (Subgroup.center K) :=
    not_dvd_card_center_of_markedModel_E6 hQ' hM rfl hp hp3
  exact le_evenRank_of_center_quotient θ hp hp2 hZ hX hX2 hE hEcard' hXE

theorem rk2_low_e6_one (K : Type) [Group K] [Finite K] (lab : GLALabel)
    (hK : Rk2IsLabel K lab) (htag : lab.tag = .E6) (hn : lab.n = 1) :
    4 ≤ evenRank K := by
  obtain ⟨t, r, n⟩ := lab
  simp only at htag hn
  subst htag
  subst hn
  obtain ⟨hQ, hl, hM⟩ := rk2_model_of_isLabel hK
  have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .E6 0 2 1 :=
    lieModel_of_markedModel_E6 rfl hM
  obtain ⟨-, F, hFld, hFin, hFcard, ⟨φ⟩⟩ :=
    hM'.chevalleyExceptionalModel (by decide : StatedLieTag.E6 ∈ chevalleyExceptionalTags)
  letI : Field F := hFld
  letI : Finite F := hFin
  have hQ' : CFSG.IsQuasisimple K :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff K).2.2.1.2 hQ
  have hz : Subgroup.center K = ⊥ := center_eq_bot_of_E6_one hQ' hM rfl rfl
  let eK : K ≃* adjointGroup .E6 F :=
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.trans
      (φ.trans (CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.adjointQuotientEquiv .E6 F))
  let q : TauCeti.PrimePower := ⟨2, 1, Nat.prime_two, by norm_num⟩
  have hv : (TauCeti.LieTypeIndex.E6 q).Valid := by simp
  obtain ⟨K', hK'fld, hK'fin, hK'card, hK'char, ⟨eCat⟩⟩ :=
    CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
      (CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6) q hv
  letI : Field K' := hK'fld
  letI : Finite K' := hK'fin
  have hcardFK : Nat.card F = Nat.card K' := by
    simp [hFcard, hK'card, TauCeti.PrimePower.card_def, q]
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fintype K' := Fintype.ofFinite K'
  let eField : F ≃+* K' := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hcardFK)
  let eAdj : adjointGroup .E6 F ≃* adjointGroup .E6 K' :=
    CFSG.TauCetiBridge.adjointGroupCongr (τ := Tag.E6) eField
  let e : K ≃* CFSG.LieType.SeitzGeneration.Cat
      ⟨TauCeti.LieTypeIndex.E6 q, hv⟩ := eK.trans (eAdj.trans eCat.symm)
  haveI : Finite (CFSG.LieType.SeitzGeneration.Cat
      ⟨TauCeti.LieTypeIndex.E6 q, hv⟩) := Finite.of_equiv K e.toEquiv
  have h4 : 4 ≤ CFSG.twoLocalOddRank (CFSG.LieType.SeitzGeneration.Cat
      ⟨TauCeti.LieTypeIndex.E6 q, hv⟩) :=
    CFSG.RankThree.PartTwo.Census.Exceptional.four_le_twoLocalOddRank_E6 q hv
  have h4K : 4 ≤ CFSG.twoLocalOddRank K := by
    rw [CFSG.RankThree.PartOne.Census3.twoLocalOddRank_eq_of_mulEquiv e]
    exact h4
  have heq : evenRank K = CFSG.twoLocalOddRank K := by
    have h : evenRank K = CFSG.Assembly.evenRank K := rfl
    rw [h, CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank]
  rw [heq]
  exact h4K

theorem rk2_low_e6_two_of_center_eq_bot (K : Type) [Group K] [Finite K] (lab : GLALabel)
    (hK : Rk2IsLabel K lab) (htag : lab.tag = .E6) (hn : lab.n = 2)
    (hc : Subgroup.center K = ⊥) :
    5 ≤ evenRank K := by
  obtain ⟨t, r, n⟩ := lab
  simp only at htag hn
  subst htag
  subst hn
  obtain ⟨hQ, hl, hM⟩ := rk2_model_of_isLabel hK
  have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .E6 0 2 2 :=
    lieModel_of_markedModel_E6 rfl hM
  obtain ⟨-, F, hFld, hFin, hFcard, ⟨φ⟩⟩ :=
    hM'.chevalleyExceptionalModel (by decide : StatedLieTag.E6 ∈ chevalleyExceptionalTags)
  letI : Field F := hFld
  letI : Finite F := hFin
  have hcardF : Nat.card F = 4 := by
    rw [hFcard]
    norm_num
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by norm_num) (k := 2) (by rw [hcardF]; norm_num)
  obtain ⟨E, hE, hEcard, hEle⟩ := exists_elemAbelian_243_le_torusGroup_E6 hcardF
  obtain ⟨E', X, hX, hX2, hE', hE'card, hXE⟩ :=
    exists_elemAbelian_le_normalizer_rootSubgroup (p := 3) hEle hE.2
      (isRoot_single .E6 0)
  have hE'card' : Nat.card E' = 3 ^ 5 := hE'card.trans hEcard
  let θ : K ⧸ Subgroup.center K ≃* adjointGroup .E6 F :=
    φ.trans (CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.adjointQuotientEquiv .E6 F)
  have hZ : ¬ 3 ∣ Nat.card (Subgroup.center K) := by
    rw [hc, Subgroup.card_bot]
    exact fun h => (by norm_num : ¬ 3 ∣ 1) h
  exact le_evenRank_of_center_quotient θ Nat.prime_three (by norm_num) hZ hX hX2 hE'
    hE'card' hXE

theorem rk2_low_e6_two (K : Type) [Group K] [Finite K] (lab : GLALabel)
    (hK : Rk2IsLabel K lab) (htag : lab.tag = .E6)
    (h : 3 ≤ lab.n ∨ (lab.n = 2 ∧ Subgroup.center K = ⊥)) :
    5 ≤ evenRank K := by
  rcases h with h3 | ⟨h2, hc⟩
  · exact (rk2_low_e6_of_three_le K lab hK htag h3).trans' (by norm_num)
  · exact rk2_low_e6_two_of_center_eq_bot K lab hK htag h2 hc

end CFSG.LocalAnalysis.GLTheoremA
