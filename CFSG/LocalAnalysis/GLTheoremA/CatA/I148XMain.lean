module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I148XRes
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuousTriality
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I148XOdd
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIAut2
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma102

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Blueprint.Chevalley (TwistTag)
open CFSG.LieType.Chevalley (graphFixedRootGroup)

theorem barAut_comp_conjQ {G : Type} [Group G] [Finite G] {L : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G)) (z : PQuot 3 L) :
    CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 L ⟨x, hx⟩ (lemma102_conjQ 3 hx z) = z := by
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective z
  rw [lemma102_conjQ_mk, CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk]
  congr 1
  apply Subtype.ext
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe, lemma102_conjHomL_val]
  group

theorem lemma102_fixSub_eq_centralizer {G : Type} [Group G] [Finite G] {L : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G)) {c : PQuot 3 L}
    (hc : MulAut.conj c = CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 L ⟨x, hx⟩) :
    lemma102_fixSub 3 hx = Subgroup.centralizer ({c} : Set (PQuot 3 L)) := by
  have key : ∀ z : PQuot 3 L, lemma102_conjQ 3 hx z = c⁻¹ * z * c := by
    intro z
    have h1 := barAut_comp_conjQ hx z
    rw [← hc, MulAut.conj_apply] at h1
    calc lemma102_conjQ 3 hx z = c⁻¹ * (c * lemma102_conjQ 3 hx z * c⁻¹) * c := by group
      _ = c⁻¹ * z * c := by rw [h1]
  ext z
  rw [Subgroup.mem_centralizer_singleton_iff]
  show lemma102_conjQ 3 hx z = z ↔ _
  rw [key z]
  constructor
  · intro h
    calc z * c = c * (c⁻¹ * z * c) := by group
      _ = c * z := by rw [h]
  · intro h
    calc c⁻¹ * z * c = c⁻¹ * (z * c) := by group
      _ = c⁻¹ * (c * z) := by rw [h]
      _ = z := by group

theorem i148At_of_td4InnThreeCentLe (G : Type) [Group G] [Finite G]
    (hres : ∀ f : ℕ, 1 ≤ f → TD4InnThreeCentLe f) : I148At G := by
  intro X L x hL hTD4 hx3 hA hnc
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hxN : x ∈ Subgroup.normalizer (L : Set G) := hA.1 (Subgroup.mem_zpowers x)
  have hInn : InducesInnerMod 3 L x := by
    by_contra h
    exact (MI.td4_nonInnDiag_holds hp3 hL hTD4 ⟨hxN, h⟩).2 hA
  have hBin : CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 L ⟨x, hxN⟩ ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (PQuot 3 L) :=
    (inducesInnerMod_iff_barAut_mem_inner hxN).1 hInn
  have hB1 : CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 L ⟨x, hxN⟩ ≠ 1 := fun h =>
    hnc ((chev_barAut_eq_one_iff_centMod (p := 3) hxN).1 h)
  obtain ⟨q, hv, ⟨eS⟩⟩ := td4_index hTD4
  have hq2 : q.p = 2 := td4_two_of_centQ (centQIndexCases_of_marking hA.2) hv eS
  obtain ⟨-, hfac⟩ := td4_order hv eS
  rw [hq2] at hfac
  have hQ : CFSG.Open.IsQuasisimple (PQuot 3 L) := isQuasisimple_pQuot_of_glaPComponent hp3 hL
  have hm : CFSG.Models.LieModel (PQuot 3 L ⧸ Subgroup.center (PQuot 3 L)) .trialityD4 0 q.p q.exponent :=
    CFSG.Models.lieModel_of_namesTag ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨_, hv⟩ ⟨rfl, rfl⟩ eS
  have hGA : CFSG.Open.GriessAllModelsStatement :=
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  have hdvd := card_center_dvd_of_table hGA hQ hm (a := 1) (b := 1) (c := 1) (d := 1) rfl rfl
    (by norm_num)
  have hc1 : Nat.card (Subgroup.center (PQuot 3 L)) = 1 := Nat.dvd_one.1 (by simpa using hdvd)
  have hcenter : Subgroup.center (PQuot 3 L) = ⊥ := Subgroup.eq_bot_of_card_eq _ hc1
  have eQS : PQuot 3 L ≃* PSimple 3 L :=
    ((QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot).symm
  have hcard2 : card2 3 L = 2 ^ (12 * q.exponent) := by
    unfold card2 twoPart
    rw [Nat.card_congr eQS.toEquiv, hfac]
  obtain ⟨K, _, _, σ, hK, hσ, -, ⟨eC⟩⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
  have hK' : Nat.card K = (2 ^ q.exponent) ^ 3 := by rw [hK, hq2]
  have hσ' : ∀ c, σ c = c ^ 2 ^ q.exponent := fun c => by rw [hσ c, hq2]
  obtain ⟨eQC, -⟩ : ∃ e : PQuot 3 L ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom, True :=
    ⟨eQS.trans (eS.trans eC), trivial⟩
  obtain ⟨c, hc⟩ := hBin
  have hB3 : (CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 L ⟨x, hxN⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have h3x : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ 3 = 1 := Subtype.ext hx3
    rw [h3x, map_one]
  have hc3 : c ^ 3 = 1 := by
    have h3 : MulAut.conj (c ^ 3) = 1 := by
      rw [map_pow, hc, hB3]
    have hmem : c ^ 3 ∈ Subgroup.center (PQuot 3 L) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg := congrArg (fun φ : MulAut (PQuot 3 L) => φ g) h3
      simp only [MulAut.conj_apply, MulAut.one_apply] at hg
      exact (mul_inv_eq_iff_eq_mul.1 hg).symm
    rw [hcenter] at hmem
    exact Subgroup.mem_bot.1 hmem
  have hc1' : c ≠ 1 := by
    intro h
    apply hB1
    rw [← hc, h, map_one]
  have hfix := lemma102_fixSub_eq_centralizer hxN hc
  have hcent : centCard2 3 L x = twoPart (Nat.card (Subgroup.centralizer ({c} : Set (PQuot 3 L)))) := by
    rw [lemma102_centCard2_eq_fixSub 3 hxN, hfix]
  have hcentC : Nat.card (Subgroup.centralizer ({c} : Set (PQuot 3 L))) =
      Nat.card (Subgroup.centralizer ({eQC c} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) := by
    apply Nat.card_congr
    refine Equiv.subtypeEquiv eQC.toEquiv (fun g => ?_)
    show g ∈ Subgroup.centralizer ({c} : Set (PQuot 3 L)) ↔
      eQC g ∈ Subgroup.centralizer ({eQC c} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      eQC.injective.eq_iff]
  have hz3 : eQC c ^ 3 = 1 := by
    rw [← map_pow, hc3, map_one]
  have hz1 : eQC c ≠ 1 := by
    intro h
    apply hc1'
    exact eQC.injective (by rw [h, map_one])
  have hres' := hres q.exponent q.exponent_pos K σ hK' hσ' (eQC c) hz3 hz1
  rw [hcent, hcentC, hcard2]
  calc _ ≤ ((2 ^ q.exponent) ^ 6) ^ 2 := Nat.pow_le_pow_left hres' 2
    _ = 2 ^ (12 * q.exponent) := by ring

end CFSG.LocalAnalysis.GLTheoremA

end
