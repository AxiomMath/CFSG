module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S262GF2Red
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCoreS

import CFSG.LocalAnalysis.GLTheoremA.CatA.S262OmM8Lin
import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.BlockB.OuterThree.LieTwo
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusCentOrthModel
import CFSG.LocalAnalysis.GLTheoremA.CatA.HDescCTwo
import CFSG.Adapters.LieModelSimple
import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec4.KAPIHypB
public import CFSG.HardMathSupport.Solomon.Coordinator.B3LieRes
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusCentLift
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerNonsolv3
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedBlocks
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge
import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbTwDChar
import CFSG.LocalAnalysis.GLTheoremA.CatA.HDescLift

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S262

open Module QuadraticMap CFSG.Open CFSG.Yardstones.Md0ec50421ce4 TauCeti
open CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.LocalAnalysis.GLTheoremA.HDesc
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeOrth
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.AGLEmbedding.ToralCensus (PerfectThreeIn)

theorem exists_twistedD_four_of_gf2OmMinus8 (d : ValidLieTypeIndex) (h : gf2OmMinus8 d.1) :
    ∃ (q : PrimePower) (hv : (LieTypeIndex.twistedD 4 q).Valid),
      d.1 = .twistedD 4 q ∧ q.card = 2 := by
  obtain ⟨e, hv⟩ := d
  cases e with
  | twistedD r q =>
    by_cases hr : r = 4
    · subst hr
      exact ⟨q, hv, rfl, by simpa [gf2OmMinus8] using h⟩
    · exfalso
      simp [gf2OmMinus8, hr] at h
  | A r q => simp [gf2OmMinus8] at h
  | twistedA r q => simp [gf2OmMinus8] at h
  | B r q => simp [gf2OmMinus8] at h
  | C r q => simp [gf2OmMinus8] at h
  | D r q => simp [gf2OmMinus8] at h
  | E6 q => simp [gf2OmMinus8] at h
  | E7 q => simp [gf2OmMinus8] at h
  | E8 q => simp [gf2OmMinus8] at h
  | F4 q => simp [gf2OmMinus8] at h
  | G2 q => simp [gf2OmMinus8] at h
  | twistedE6 q => simp [gf2OmMinus8] at h
  | trialityD4 q => simp [gf2OmMinus8] at h
  | suzuki m => simp [gf2OmMinus8] at h
  | reeG2 m => simp [gf2OmMinus8] at h
  | reeF4 m => simp [gf2OmMinus8] at h
  | tits => simp [gf2OmMinus8] at h

theorem e9GoodOn_gf2OmMinus8 (hPL : KD264PL 3) : E9GoodOn gf2OmMinus8 := by
  classical
  intro d hfin hQ A hA h9
  obtain ⟨q, hv, hd, hq⟩ := exists_twistedD_four_of_gf2OmMinus8 d hQ
  let d' : ValidLieTypeIndex := ⟨.twistedD 4 q, hv⟩
  have hdd : d = d' := Subtype.ext hd
  subst hdd
  let T := (TauCeti.CFSGIndex.lie d').Group
  obtain ⟨hp2, hexp⟩ :=
    CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.primePower_card_two' hq
  have hmodel : StatedClassicalModel T .POmegaMinus 4 2 1 := by
    have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even 4 q hv hp2
      (MulEquiv.refl T)
    rwa [hp2, hexp] at h
  haveI : IsSimpleGroup T := CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hmodel
  obtain ⟨-, K, hfieldK, hfiniteK, hcardK, b, c, hbc, ⟨eK⟩⟩ := hmodel
  letI : Field K := hfieldK
  letI : Finite K := hfiniteK
  haveI : Fintype K := Fintype.ofFinite K
  have hK2 : Nat.card K = 2 := by simpa using hcardK
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1) (by
    rw [← Nat.card_eq_fintype_card]; exact hK2)
  let V := Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K
  let Q : QuadraticForm K V := CFSG.LieType.Universal.Spin.quadMinus 4 K b c
  have hQnd : (polarBilin Q).Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite 4 K hbc
  let eΩ : StatedProj (StatedOmega (StatedQuadMinus 4 K b c)) ≃*
      ↥(CFSG.RankThree.Classical2.orthDerived Q) :=
    CFSG.AGLEmbedding.ToralCensus.statedProjOmegaEquivDerivedCharTwo
      (CFSG.LieType.Universal.Spin.coe_quadMinus 4 K b c) hQnd
  let e : T ≃* ↥(CFSG.RankThree.Classical2.orthDerived Q) := eK.trans eΩ
  have hdim : Module.finrank K V = 8 := by
    rw [Module.finrank_fintype_fun_eq_card]
    norm_num [Fintype.card_sum]
  have hS : (∑ v : V, chi (Q v)) = -16 := by
    have hsum : (∑ v : V, chi (Q v)) =
        ∑ v : V, chi (StatedQuadMinus 4 K b c v) := by
      refine Finset.sum_congr rfl fun v _ => ?_
      show chi (CFSG.LieType.Universal.Spin.quadMinus 4 K b c v) = _
      rw [CFSG.LieType.Universal.Spin.coe_quadMinus]
    rw [hsum]
    simpa using CFSG.HardMathSupport.Curtis.UnitaryLevi.charSum_statedQuadMinus hK2 (n := 4)
      (by norm_num) hbc
  have hInn : AutThreePowInner T :=
    CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.OuterThree.autThreePowInner_typeTwistedD_two
      hv hq (MulEquiv.refl T)
  have hAinn : A ≤ (MulAut.conj : T →* MulAut T).range := by
    intro a ha
    obtain ⟨s, hs⟩ := hInn a 1 (by
      intro x
      have h3 : a ^ 3 = 1 := hA.2 a ha
      show a^[3 ^ 1] x = x
      rw [show 3 ^ 1 = 3 from rfl]
      calc a^[3] x = (a ^ 3) x := rfl
        _ = x := by rw [h3]; rfl)
    exact ⟨s, by ext x; rw [MulAut.conj_apply]; exact (hs x).symm⟩
  have hnonab : ∃ u v : T, u * v ≠ v * u := by
    by_contra hcon
    push Not at hcon
    have hrange : (MulAut.conj : T →* MulAut T).range = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨g, rfl⟩
      ext x
      simp only [MulAut.conj_apply, MulAut.one_apply]
      rw [hcon g x]
      group
    have hbot : A = ⊥ := le_bot_iff.mp (hAinn.trans (le_of_eq hrange))
    have hcard : Nat.card ↥A = 1 := by rw [hbot]; simp
    omega
  have hconj_inj : Function.Injective (MulAut.conj : T →* MulAut T) :=
    CFSG.SignalizerFunctorTheorem.McBride.Near.KAPI.conj_injective_of_isSimpleGroup hnonab
  let F : Subgroup T := A.comap (MulAut.conj : T →* MulAut T)
  have hFcard : Nat.card ↥F = Nat.card ↥A := by
    have hmap : F.map (MulAut.conj : T →* MulAut T) = A := Subgroup.map_comap_eq_self hAinn
    have h := Nat.card_congr (Subgroup.equivMapOfInjective F _ hconj_inj).toEquiv
    rwa [hmap] at h
  have hF : IsElemAbelian 3 F := hA.comap hconj_inj
  obtain ⟨B, hBF, hB9⟩ : ∃ B : Subgroup T, B ≤ F ∧ Nat.card B = 9 := by
    have h9F : 9 ≤ Nat.card ↥F := by rw [hFcard]; exact h9
    obtain ⟨K', hK'⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card (n := 2)
      Nat.prime_three hF.isPGroup (by norm_num; exact h9F)
    refine ⟨K'.map F.subtype, Subgroup.map_subtype_le K', ?_⟩
    rw [← Nat.card_congr (Subgroup.equivMapOfInjective K' _ F.subtype_injective).toEquiv, hK']
    norm_num
  have hB : IsElemAbelian 3 B := hF.mono hBF
  let BΩ : Subgroup ↥(CFSG.RankThree.Classical2.orthDerived Q) := B.map e.toMonoidHom
  have hBΩ : IsElemAbelian 3 BΩ := hB.map e.toMonoidHom
  have hBΩ9 : Nat.card ↥BΩ = 9 := by
    rw [show BΩ = B.map e.toMonoidHom from rfl,
      ← Nat.card_congr (Subgroup.equivMapOfInjective B _ e.injective).toEquiv, hB9]
  let A' : Subgroup (V ≃ₗ[K] V) := BΩ.map (CFSG.RankThree.Classical2.orthDerived Q).subtype
  have hA'Ω : A' ≤ CFSG.RankThree.Classical2.orthDerived Q := Subgroup.map_subtype_le BΩ
  have hA'e : IsElemAbelian 3 A' := hBΩ.map (CFSG.RankThree.Classical2.orthDerived Q).subtype
  have hA'9 : Nat.card ↥A' = 9 := by
    rw [show A' = BΩ.map (CFSG.RankThree.Classical2.orthDerived Q).subtype from rfl,
      ← Nat.card_congr (Subgroup.equivMapOfInjective BΩ _
        (CFSG.RankThree.Classical2.orthDerived Q).subtype_injective).toEquiv, hBΩ9]
  obtain ⟨a, haA', ha1, hP⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.S262.OmM8.exists_perfectThreeIn_orthDerived
      hK2 hQnd hdim hS hA'Ω hA'e hA'9
  obtain ⟨b, hbBΩ, hba⟩ := Subgroup.mem_map.mp haA'
  obtain ⟨g, hgB, hgb⟩ := Subgroup.mem_map.mp hbBΩ
  subst hgb
  subst hba
  obtain ⟨P, hPle, hPperf, y, hyP, hy3, hy1⟩ := hP
  let P' : Subgroup T := P.map e.symm.toMonoidHom
  have hP'perf : ⁅P', P'⁆ = P' := by
    rw [show P' = P.map e.symm.toMonoidHom from rfl, ← Subgroup.map_commutator, hPperf]
  have hP'fix : P' ≤ fixSubgroup (MulAut.conj g) := by
    rw [CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_fixSubgroup_conj]
    intro z hz
    obtain ⟨y', hy'P, rfl⟩ := Subgroup.mem_map.mp hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hy'C : (y' : V ≃ₗ[K] V) ∈
        isometryCentralizer Q ((e g : ↥(CFSG.RankThree.Classical2.orthDerived Q)) : V ≃ₗ[K] V) := by
      have h := hPle hy'P
      rwa [Subgroup.mem_subgroupOf] at h
    have hcommV : (y' : V ≃ₗ[K] V) *
        ((e g : ↥(CFSG.RankThree.Classical2.orthDerived Q)) : V ≃ₗ[K] V) =
        ((e g : ↥(CFSG.RankThree.Classical2.orthDerived Q)) : V ≃ₗ[K] V) * (y' : V ≃ₗ[K] V) :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hy'C).2
    have hcommΩ : y' * e g = e g * y' := Subtype.ext hcommV
    have hcongr := congrArg e.symm hcommΩ
    simpa using hcongr
  have h3P : 3 ∣ Nat.card ↥P := by
    haveI : Fintype ↥P := Fintype.ofFinite _
    have hyord : orderOf y = 3 := orderOf_eq_prime hy3 hy1
    have h := orderOf_dvd_card (x := (⟨y, hyP⟩ : ↥P))
    have hord : orderOf (⟨y, hyP⟩ : ↥P) = orderOf y :=
      (Subgroup.orderOf_coe (⟨y, hyP⟩ : ↥P)).symm
    rw [hord, hyord] at h
    rwa [Nat.card_eq_fintype_card]
  have hP'3 : 3 ∣ Nat.card ↥P' := by
    have hcard : Nat.card ↥P' = Nat.card ↥P :=
      (Nat.card_congr (Subgroup.equivMapOfInjective P _ e.symm.injective).toEquiv).symm
    rw [hcard]; exact h3P
  have hg3 : g ^ 3 = 1 := hF.2 g (hBF hgB)
  have hconj3 : (MulAut.conj g) ^ 3 = 1 := by
    rw [← map_pow, hg3, map_one]
  have hg1 : g ≠ 1 := by
    intro h1
    exact ha1 (by rw [h1, map_one]; rfl)
  have hconj1 : MulAut.conj g ≠ 1 := by
    intro h1
    exact hg1 (hconj_inj (by rw [h1, map_one]))
  have hchar : (3 : ℕ) ≠ d'.1.characteristic := by
    rw [show d'.1 = .twistedD 4 q from rfl, LieTypeIndex.characteristic_twistedD, hp2]
    norm_num
  obtain ⟨J, hJ, hJp⟩ := hPL d' hchar (MulAut.conj g) hconj3 hconj1 P' hP'fix hP'perf hP'3
  refine ⟨MulAut.conj g, ?_, hconj1, layer_ne_bot_of_component d' Nat.prime_three hJ hJp⟩
  rw [← Subgroup.map_comap_eq_self hAinn]
  exact Subgroup.mem_map.mpr ⟨g, hBF hgB, rfl⟩

end CFSG.LocalAnalysis.GLTheoremA.S262

end
