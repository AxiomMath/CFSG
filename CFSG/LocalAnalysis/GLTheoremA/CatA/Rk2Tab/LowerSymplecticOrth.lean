module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerLift
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylMatrices
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagData
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.SignalizerFunctorTheorem.NonLocal.SpSiegel
public import CFSG.LieType.Steinberg.CentralExt.GriessClassical
public import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194OmegaTorus
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87MultMilestone
public import CFSG.RankThree.PartOne.KF.ClsSpWit
public import CFSG.RankThree.PartOne.KF.ClsBasic
public import CFSG.RankThree.PartOne.S11c.EvenOrthogonal
public import CFSG.LocalAnalysis.SectionRank.QTK.EvenMinus8
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.CoverUnique
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitCoverTorus
public import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194Mult
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitCoverTorus
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitUnipotent
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitSylow
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Orthogonal
public import CFSG.ClassicalGroups.Orthogonal.Simple
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Certificates.Kernel.Spor.ONKSound
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDispatch
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Cover
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.PCompBasics
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.RankThree.CentralCover.SymplecticFourGroupWitness
public import CFSG.RankThree.CentralExtension.InvariantComplement
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.Classical2.OrthogonalDefiningPrimeRank
public import CFSG.RankThree.PartOne.KC.UnitaryDefining
public import CFSG.RankThree.PartOne.S11c.OddClassicalPlane
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194Core
public import CFSG.RankThree.PartTwo.Sec19.Item194Used
public import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG CFSG.Open CFSG.StandardType CFSG.Assembly CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.SignalizerFunctorTheorem.NonLocal CFSG.Blueprint.Multiplier
open CFSG.Assembly.RankThreeEven (localRank)
open _root_.CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.OmegaEven
open CFSG.LieType.Universal.Spin CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

theorem quasisimple_markedModel_of_isLabel {K : Type} [Group K] {lab : GLALabel}
    (hK : Rk2IsLabel K lab) :
    CFSG.IsQuasisimple K ∧ LargeEvenInLambda2 lab ∧
      CFSG.StandardType.MarkedModel lab (K ⧸ Subgroup.center K) := by
  change CFSG.Assembly.LargeEvenMarking K (fun lab' _ _ _ _ _ => lab' = lab) at hK
  obtain ⟨hL, lab', hlab', hraw⟩ := hK
  have hna : ∀ (R : Type) [Group R] (I F : Set (MulAut R)),
      IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        (∃ θ : K ⧸ Subgroup.center K ≃* R, lab' = lab) → ∃ a b : R, a * b ≠ b * a :=
    fun R _ I F h => h.2.1
  have hraw' := CFSG.StandardType.Canonical.largeEvenRawDatum_markedModel hlab' hna hraw
  obtain ⟨R, hgroup, I, F, ⟨⟨hs, ⟨a, b, hab⟩, θ, hlab'⟩, hM⟩⟩ :=
    CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw'
  letI : Group R := hgroup
  subst hlab'
  exact ⟨⟨⟨hL⟩, (θ.isSimpleGroup_congr).2 hs,
      ⟨θ.symm a, θ.symm b, fun h => hab (θ.symm.injective (by simpa [map_mul] using h))⟩⟩,
    hlab', CFSG.StandardType.MarkedModel.of_mulEquiv θ.symm hM⟩

theorem spSiegel_ne_bot {F : Type} [Field F] [Finite F] [CharP F 2] {ℓ : ℕ}
    (hℓ : 1 ≤ ℓ) : spSiegel ℓ F ≠ ⊥ := by
  rw [← Subgroup.one_lt_card_iff_ne_bot, card_spSiegel]
  haveI : Fintype F := Fintype.ofFinite F
  have h2 : 2 ≤ Nat.card F := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hpos : 0 < Nat.card F := Nat.card_pos
  have hm : 1 ≤ ℓ * (ℓ + 1) / 2 :=
    Nat.div_pos (by
      calc 2 = 1 * 2 := by norm_num
        _ ≤ ℓ * (ℓ + 1) := Nat.mul_le_mul hℓ (by omega)) (by norm_num)
  calc 1 < Nat.card F ^ 1 := by simpa using lt_of_lt_of_le (by norm_num : 1 < 2) h2
    _ ≤ Nat.card F ^ (ℓ * (ℓ + 1) / 2) := Nat.pow_le_pow_right hpos hm

theorem isPGroup_spSiegel {F : Type} [Field F] [Finite F] [CharP F 2] (ℓ : ℕ) :
    IsPGroup 2 (spSiegel ℓ F) := by
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨k, -, hk⟩ := FiniteField.card F 2
  refine IsPGroup.of_card (n := k * (ℓ * (ℓ + 1) / 2)) ?_
  rw [card_spSiegel, Nat.card_eq_fintype_card, hk, ← pow_mul]

theorem exists_isElemAbelian_torus_statedSp {F : Type} [Field F] [Finite F] [CharP F 2]
    {ℓ r : ℕ} (hℓ : 1 ≤ ℓ) (hr : r.Prime) (hr2 : r ≠ 2) (hdvd : r ∣ Nat.card F - 1) :
    ∃ E : Subgroup (StatedSp ℓ F), IsElemAbelian r E ∧ Nat.card E = r ^ ℓ ∧
      E ≤ Subgroup.normalizer (spSiegel ℓ F : Set (StatedSp ℓ F)) := by
  classical
  have hdvd' : r ∣ Nat.card Fˣ := by rwa [Nat.card_units]
  set μ := rootsOfUnity r F with hμ
  let incl : (Fin ℓ → μ) →* (Fin ℓ → Fˣ) := μ.subtype.compLeft (Fin ℓ)
  let φ : (Fin ℓ → μ) →* StatedSp ℓ F := torusHom.comp incl
  have hφ : Function.Injective φ := by
    intro a b hab
    have h1 : incl a = incl b := torusHom_injective hab
    funext i
    exact Subtype.ext (congrFun h1 i)
  have hμcard : Nat.card μ = r :=
    _root_.CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.OmegaEven.card_rootsOfUnity_of_dvd' hr hdvd'
  refine ⟨φ.range, ?_, ?_, ?_⟩
  · have htop : IsElemAbelian r (⊤ : Subgroup (Fin ℓ → μ)) := by
      refine ⟨⟨⟨fun a b => Subtype.ext (funext fun i => mul_comm _ _)⟩⟩, fun x _ => ?_⟩
      funext i
      exact Subtype.ext (by
        simpa using congrArg Subtype.val
          (_root_.CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.OmegaEven.rootsOfUnity_pow_eq_one'
            (x i) : (x i) ^ r = 1))
    have h := CFSG.SectionRank.isElemAbelian_map htop φ
    simpa [MonoidHom.range_eq_map] using h
  · rw [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv, Nat.card_fun, hμcard, Nat.card_fin]
  · rintro _ ⟨a, rfl⟩
    rw [Subgroup.mem_set_normalizer_iff]
    intro h
    constructor
    · intro hh
      have hga : φ a = leviSp (TauCeti.diagGL (incl a)) := rfl
      rw [hga]
      exact leviSp_conj_mem (TauCeti.diagGL (incl a)) hh
    · intro hh
      have h2 := leviSp_conj_mem (A := (TauCeti.diagGL (incl a))⁻¹)
        (e := leviSp (TauCeti.diagGL (incl a)) * h * (leviSp (TauCeti.diagGL (incl a)))⁻¹) hh
      rw [map_inv, inv_inv] at h2
      have heq : h = (leviSp (TauCeti.diagGL (incl a)))⁻¹ *
          (leviSp (TauCeti.diagGL (incl a)) * h * (leviSp (TauCeti.diagGL (incl a)))⁻¹) *
            leviSp (TauCeti.diagGL (incl a)) := by group
      rw [heq]
      exact h2

theorem card_griess_psp_dvd_four {X : Type} [Group X] {ℓ n : ℕ}
    (h : StatedClassicalModel X .PSp ℓ 2 n) (hn : 2 ≤ n) :
    Nat.card (CFSG.Open.griessHopfMultiplier X) ∣ 4 := by
  have hq : 5 ≤ 2 ^ n ∨ 2 ^ n = 4 ∨ (2 ^ n = 2 ∧ 4 ≤ ℓ) ∨ (2 ^ n = 3 ∧ 3 ≤ ℓ) := by
    rcases Nat.lt_or_ge n 3 with h3 | h3
    · have hn2 : n = 2 := by omega
      subst hn2
      exact Or.inr (Or.inl (by norm_num))
    · exact Or.inl (by
        calc 5 ≤ 2 ^ 3 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h3)
  obtain ⟨-, ⟨e⟩⟩ := CFSG.LieType.Steinberg.CentralExt.GriessClassical.psp_row h hq
  rw [Nat.card_congr e.toEquiv,
    _root_.CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_generic_exceptional']
  have hg : genericOrders .PSp ℓ 2 n = (Nat.gcd 2 (2 ^ n - 1), 1) := by simp [genericOrders]
  have he : exceptionalOrders .PSp ℓ 2 n = (1, 1) ∨
      exceptionalOrders .PSp ℓ 2 n = (2, 1) := by
    by_cases h3 : ℓ = 3 ∧ n = 1
    · right
      obtain ⟨rfl, rfl⟩ := h3
      decide
    · left
      by_cases h1 : ℓ = 3
      · subst h1
        have hn : n ≠ 1 := fun hn => h3 ⟨rfl, hn⟩
        simp [exceptionalOrders, hn]
      · simp [exceptionalOrders, h1]
  rcases he with he | he <;> rw [hg, he]
  · simpa using (Nat.mul_dvd_mul_right (Nat.gcd_dvd_left 2 (2 ^ n - 1)) 1).trans
      (by norm_num : 2 * 1 ∣ 4)
  · simpa using (Nat.mul_dvd_mul (Nat.gcd_dvd_left 2 (2 ^ n - 1)) (dvd_refl 2)).trans
      (by norm_num : 2 * 2 ∣ 4)


private theorem le_evenRank_statedSp_of_markedModel {K F : Type} [Group K] [Finite K]
    [Field F] [Finite F] [CharP F 2] {ℓ n r : ℕ} (hcard : Nat.card F = 2 ^ n)
    (hQ : CFSG.IsQuasisimple K)
    (θ : K ⧸ Subgroup.center K ≃* StatedProj (StatedSp ℓ F))
    (hrZ : ¬ r ∣ Nat.card (Subgroup.center K))
    (hr : r.Prime) (hr2 : r ≠ 2) (hdvd : r ∣ Nat.card F - 1) (hℓ : 1 ≤ ℓ) :
    ℓ ≤ evenRank K := by
  have hbot : (StatedScalars (Fin ℓ ⊕ Fin ℓ) F).subgroupOf (StatedSp ℓ F) = ⊥ :=
    CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot
  let φ : StatedProj (StatedSp ℓ F) ≃* StatedSp ℓ F :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans (QuotientGroup.quotientBot)
  obtain ⟨E, hE, hEcard, hEnorm⟩ := exists_isElemAbelian_torus_statedSp (F := F) hℓ hr hr2 hdvd
  exact le_evenRank_of_center_quotient (θ.trans φ) hr hr2 hrZ
    (spSiegel_ne_bot hℓ) (isPGroup_spSiegel ℓ) hE hEcard hEnorm

private theorem rk2_low_bc_ge_aux {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hK : Rk2IsLabel K lab) (htag : lab.tag = .B ∨ lab.tag = .C) (hn : 2 ≤ lab.n) :
    lab.rank ≤ evenRank K := by
  obtain ⟨hQ, hlab, hM⟩ := quasisimple_markedModel_of_isLabel hK
  have ht : markTag lab = .PSp := by
    rcases htag with hB | hC
    · simp [CFSG.StandardType.markTag, hB]
    · simp [CFSG.StandardType.markTag, hC]
  have hrk : markRank lab = lab.rank := by
    rcases htag with hB | hC
    · simp [CFSG.StandardType.markRank, hB]
    · simp [CFSG.StandardType.markRank, hC]
  have hch : markChar lab = 2 := by
    rcases htag with hB | hC
    · simp [CFSG.StandardType.markChar, hB]
    · simp [CFSG.StandardType.markChar, hC]
  have hdg : markDeg lab = lab.n := by
    rcases htag with hB | hC
    · simp [CFSG.StandardType.markDeg, hB]
    · simp [CFSG.StandardType.markDeg, hC]
  have hM' := hM
  unfold CFSG.StandardType.MarkedModel at hM'
  rw [ht, hrk, hch, hdg] at hM'
  obtain ⟨hadm, F, hfield, hfinite, hcard, ⟨e⟩⟩ := hM'.statedClassicalModel (by decide)
  obtain ⟨-, hℓ2⟩ := hadm
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype F := Fintype.ofFinite F
  have hcard' : Fintype.card F = 2 ^ lab.n := by
    rw [← Nat.card_eq_fintype_card]; exact hcard
  haveI : CharP F 2 := charP_of_card_eq_prime_pow hcard'
  have hF4 : 4 ≤ Nat.card F := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ lab.n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd (n := Nat.card F - 1) (by omega)
  have hodd : Odd (Nat.card F - 1) := by
    rw [hcard]
    have hle : 1 ≤ 2 ^ lab.n := by
      have : 0 < 2 ^ lab.n := pow_pos (by norm_num) _
      omega
    have hev : Even (2 ^ lab.n) := even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega))
    exact Nat.Even.sub_odd hle hev odd_one
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hrdvd)
  have hZ : ¬ r ∣ Nat.card (Subgroup.center K) := by
    intro hdiv
    have hdvdZ : Nat.card (Subgroup.center K) ∣
        Nat.card (CFSG.Open.griessHopfMultiplier (K ⧸ Subgroup.center K)) :=
      _root_.CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.card_center_dvd_hopf hQ
        (MulEquiv.refl _)
    have hSC : StatedClassicalModel (K ⧸ Subgroup.center K) .PSp lab.rank 2 lab.n :=
      hM'.statedClassicalModel (by decide)
    have h4 : Nat.card (CFSG.Open.griessHopfMultiplier (K ⧸ Subgroup.center K)) ∣ 4 :=
      card_griess_psp_dvd_four hSC hn
    have h24 : r ∣ 4 := hdiv.trans (hdvdZ.trans h4)
    have : r = 2 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp
      (hr.dvd_of_dvd_pow (show r ∣ 2 ^ 2 by simpa using h24))
    exact hr2 this
  exact le_evenRank_statedSp_of_markedModel hcard hQ e hZ hr hr2 hrdvd (by omega)


theorem exists_isElemAbelian_torus_quadPlus {F : Type} [Field F] [Finite F] [CharP F 2]
    {ℓ r : ℕ} (hℓ : 3 ≤ ℓ) (hr : r.Prime) (hr2 : r ≠ 2) (hdvd : r ∣ Nat.card F - 1) :
    ∃ E : Subgroup (orthElementaryGroup (quadPlus ℓ F)), IsElemAbelian r E ∧
      Nat.card E = r ^ ℓ ∧
      E ≤ Subgroup.normalizer
        ((posUnip ℓ F).subgroupOf (orthElementaryGroup (quadPlus ℓ F)) :
          Set (orthElementaryGroup (quadPlus ℓ F))) := by
  classical
  have hdvd' : r ∣ Nat.card Fˣ := by rwa [Nat.card_units]
  set μ := rootsOfUnity r F with hμ
  let incl : (Fin ℓ → μ) →* (Fin ℓ → Fˣ) := μ.subtype.compLeft (Fin ℓ)
  let φ : (Fin ℓ → μ) →* ((Fin ℓ ⊕ Fin ℓ → F) ≃ₗ[F] (Fin ℓ ⊕ Fin ℓ → F)) :=
    (torusElt ℓ F).comp incl
  have hφ : Function.Injective φ := by
    intro a b hab
    have h1 : incl a = incl b := torusElt_injective hab
    funext i
    exact Subtype.ext (congrFun h1 i)
  have hμcard : Nat.card μ = r :=
    _root_.CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.OmegaEven.card_rootsOfUnity_of_dvd' hr hdvd'
  have hEelem : IsElemAbelian r φ.range := by
    have htop : IsElemAbelian r (⊤ : Subgroup (Fin ℓ → μ)) := by
      refine ⟨⟨⟨fun a b => Subtype.ext (funext fun i => mul_comm _ _)⟩⟩, fun x _ => ?_⟩
      funext i
      exact Subtype.ext (by
        simpa using congrArg Subtype.val
          (_root_.CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.OmegaEven.rootsOfUnity_pow_eq_one'
            (x i) : (x i) ^ r = 1))
    have h := CFSG.SectionRank.isElemAbelian_map htop φ
    simpa [MonoidHom.range_eq_map] using h
  have hEcard : Nat.card φ.range = r ^ ℓ := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv, Nat.card_fun, hμcard, Nat.card_fin]
  have hEle : φ.range ≤ orthElementaryGroup (quadPlus ℓ F) := by
    rintro _ ⟨a, rfl⟩
    exact torusElt_mem_orthElementaryGroup hℓ (incl a)
  have hEpos : φ.range ≤ posBorel ℓ F := by
    rintro _ ⟨a, rfl⟩
    exact torusElt_mem_posBorel (incl a)
  have hN : posBorel ℓ F ≤ Subgroup.normalizer (posUnip ℓ F : Set _) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer posUnip_le_posBorel).mp posUnip_normal
  have hXle : posUnip ℓ F ≤ orthElementaryGroup (quadPlus ℓ F) :=
    posUnip_le_orthElementaryGroup
  have hEpN : φ.range ≤ Subgroup.normalizer (posUnip ℓ F : Set _) := hEpos.trans hN
  refine ⟨φ.range.subgroupOf (orthElementaryGroup (quadPlus ℓ F)),
    hEelem.subgroupOf _, ?_, ?_⟩
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEle).toEquiv, hEcard]
  · intro e he
    rw [← Subgroup.subgroupOf_normalizer_eq hXle]
    exact hEpN (Subgroup.mem_subgroupOf.mp he)


theorem card_griess_pomegaPlus_dvd_four {X : Type} [Group X] {ℓ n : ℕ}
    (h : StatedClassicalModel X .POmegaPlus ℓ 2 n) (hn : 2 ≤ n ∨ 5 ≤ ℓ) :
    Nat.card (CFSG.Open.griessHopfMultiplier X) ∣ 4 := by
  have hnpos : 1 ≤ n := h.1.2.1
  have hq : 3 ≤ 2 ^ n ∨ (2 ^ n = 2 ∧ 5 ≤ ℓ) := by
    rcases hn with hn | hℓ
    · exact Or.inl (by
        calc 3 ≤ 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn)
    · by_cases hn1 : n = 1
      · exact Or.inr ⟨by rw [hn1]; norm_num, hℓ⟩
      · exact Or.inl (by
          have hn2 : 2 ≤ n := by omega
          calc 3 ≤ 2 ^ 2 := by norm_num
            _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2)
  obtain ⟨-, ⟨e⟩⟩ := CFSG.LieType.Steinberg.CentralExt.GriessClassical.pomegaPlus_row h hq
  rw [Nat.card_congr e.toEquiv,
    _root_.CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_generic_exceptional']
  have hg : genericOrders .POmegaPlus ℓ 2 n = (1, 1) := by
    simp only [genericOrders]
    rw [if_pos (even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega)))]
  have he : exceptionalOrders .POmegaPlus ℓ 2 n = (1, 1) ∨
      exceptionalOrders .POmegaPlus ℓ 2 n = (2, 2) := by
    by_cases h4 : ℓ = 4 ∧ n = 1
    · right
      obtain ⟨rfl, rfl⟩ := h4
      decide
    · left
      by_cases h1 : ℓ = 4
      · subst h1
        have hn1 : n ≠ 1 := fun hn1 => h4 ⟨rfl, hn1⟩
        simp [exceptionalOrders, hn1]
      · simp [exceptionalOrders, h1]
  rcases he with he | he <;> rw [hg, he]
  · simp
  · norm_num

theorem posUnip_subgroupOf_nontrivial_isPGroup {F : Type} [Field F] [Finite F] [CharP F 2]
    {ℓ : ℕ} (hℓ : 2 ≤ ℓ) :
    (posUnip ℓ F).subgroupOf (orthElementaryGroup (quadPlus ℓ F)) ≠ ⊥ ∧
      IsPGroup 2 ((posUnip ℓ F).subgroupOf (orthElementaryGroup (quadPlus ℓ F))) := by
  haveI : Fintype F := Fintype.ofFinite F
  have hlast := (orthogonal_geometry_split_positive_unipotent_matrices
    (r := ℓ) (K := F)).2.2.2.2.2.2.2.2.2.2
  have hpos := hlast 2 (inferInstance : CharP F 2) (inferInstance : Finite F)
  haveI hfinX : Finite ↥((posUnip ℓ F).subgroupOf (orthElementaryGroup (quadPlus ℓ F))) :=
    Nat.finite_of_card_ne_zero (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        posUnip_le_orthElementaryGroup).toEquiv, hpos.1]
      exact pow_ne_zero _ Nat.card_pos.ne')
  constructor
  · have hcardX : Nat.card ((posUnip ℓ F).subgroupOf
        (orthElementaryGroup (quadPlus ℓ F))) = Nat.card (posUnip ℓ F) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe posUnip_le_orthElementaryGroup).toEquiv
    have hgt : 1 < Nat.card ((posUnip ℓ F).subgroupOf
        (orthElementaryGroup (quadPlus ℓ F))) := by
      rw [hcardX, hpos.1]
      have hposF : 0 < Nat.card F := Nat.card_pos
      have hF4 : 2 ≤ Nat.card F := by
        rw [Nat.card_eq_fintype_card]
        exact Fintype.one_lt_card
      have hmul : 0 < ℓ * (ℓ - 1) := Nat.mul_pos (by omega) (by omega)
      calc 1 < Nat.card F ^ 1 := by simpa using lt_of_lt_of_le (by norm_num : 1 < 2) hF4
        _ ≤ Nat.card F ^ (ℓ * (ℓ - 1)) := Nat.pow_le_pow_right hposF hmul
    exact (Subgroup.one_lt_card_iff_ne_bot _).1 hgt
  · refine IsPGroup.iff_orderOf.mpr fun x => ?_
    let e : ↥((posUnip ℓ F).subgroupOf (orthElementaryGroup (quadPlus ℓ F))) ≃* ↥(posUnip ℓ F) :=
      Subgroup.subgroupOfEquivOfLe posUnip_le_orthElementaryGroup
    obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp hpos.2.1 (e x)
    exact ⟨n, by rw [← orderOf_injective e.toMonoidHom e.injective x]; exact hn⟩

private theorem rk2_low_d_ge_aux {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hK : Rk2IsLabel K lab) (htag : lab.tag = .D) (hℓ4 : 4 ≤ lab.rank) (hn : 2 ≤ lab.n) :
    lab.rank ≤ evenRank K := by
  obtain ⟨hQ, hlab, hM⟩ := quasisimple_markedModel_of_isLabel hK
  have htag3 : lab.rank ≠ 3 := by omega
  have ht : markTag lab = .POmegaPlus := by
    simp [CFSG.StandardType.markTag, htag, if_neg htag3]
  have hrk : markRank lab = lab.rank := by
    simp [CFSG.StandardType.markRank, htag, if_neg htag3]
  have hch : markChar lab = 2 := by simp [CFSG.StandardType.markChar, htag]
  have hdg : markDeg lab = lab.n := by simp [CFSG.StandardType.markDeg, htag]
  have hM' := hM
  unfold CFSG.StandardType.MarkedModel at hM'
  rw [ht, hrk, hch, hdg] at hM'
  obtain ⟨hadm, F, hfield, hfinite, hcard, ⟨e⟩⟩ := hM'.statedClassicalModel (by decide)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype F := Fintype.ofFinite F
  have hcard' : Fintype.card F = 2 ^ lab.n := by
    rw [← Nat.card_eq_fintype_card]; exact hcard
  haveI : CharP F 2 := charP_of_card_eq_prime_pow hcard'
  have hF4 : 4 ≤ Nat.card F := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ lab.n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd (n := Nat.card F - 1) (by omega)
  have hodd : Odd (Nat.card F - 1) := by
    rw [hcard]
    have hle : 1 ≤ 2 ^ lab.n := by
      have : 0 < 2 ^ lab.n := pow_pos (by norm_num) _
      omega
    have hev : Even (2 ^ lab.n) := even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega))
    exact Nat.Even.sub_odd hle hev odd_one
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hrdvd)
  have hv : ∃ v : Fin lab.rank ⊕ Fin lab.rank → F, quadPlus lab.rank F v ≠ 0 := by
    let i0 : Fin lab.rank := ⟨0, by omega⟩
    let v : Fin lab.rank ⊕ Fin lab.rank → F :=
      Pi.single (Sum.inl i0) (1 : F) + Pi.single (Sum.inr i0) (1 : F)
    refine ⟨v, ?_⟩
    rw [quadPlus_apply]
    have hv1 : v (Sum.inl i0) = 1 := by simp [v]
    have hv2 : v (Sum.inr i0) = 1 := by simp [v]
    have hterm : ∀ i : Fin lab.rank, v (Sum.inl i) * v (Sum.inr i) =
        if i = i0 then 1 else 0 := by
      intro i
      by_cases hi : i = i0
      · subst hi; rw [hv1, hv2, if_pos rfl, one_mul]
      · rw [if_neg hi]
        have h1 : v (Sum.inl i) = 0 := by
          simp [v, hi]
        rw [h1, zero_mul]
    simp only [hterm]
    rw [Finset.sum_ite_eq']
    simp

  have hbot : (StatedScalars (Fin lab.rank ⊕ Fin lab.rank) F).subgroupOf
      (StatedOmega (StatedQuadPlus lab.rank F)) = ⊥ :=
    CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedOmega_eq_bot
      (Q := quadPlus lab.rank F) (Q₀ := StatedQuadPlus lab.rank F) (coe_quadPlus lab.rank F) hv
  let φ₁ : StatedProj (StatedOmega (StatedQuadPlus lab.rank F)) ≃*
      StatedOmega (StatedQuadPlus lab.rank F) :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans (QuotientGroup.quotientBot)
  let φ₂ : StatedOmega (StatedQuadPlus lab.rank F) ≃*
      orthElementaryGroup (quadPlus lab.rank F) :=
    CFSG.ClassicalGroups.Orthogonal.statedOmegaEquiv (coe_quadPlus lab.rank F)
      (CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadPlus (by omega))
  have hZ : ¬ r ∣ Nat.card (Subgroup.center K) := by
    intro hdiv
    have hdvdZ : Nat.card (Subgroup.center K) ∣
        Nat.card (CFSG.Open.griessHopfMultiplier (K ⧸ Subgroup.center K)) :=
      _root_.CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.card_center_dvd_hopf hQ
        (MulEquiv.refl _)
    have hSC : StatedClassicalModel (K ⧸ Subgroup.center K) .POmegaPlus lab.rank 2 lab.n :=
      hM'.statedClassicalModel (by decide)
    have h4 : Nat.card (CFSG.Open.griessHopfMultiplier (K ⧸ Subgroup.center K)) ∣ 4 :=
      card_griess_pomegaPlus_dvd_four hSC (Or.inl (by omega))
    have h24 : r ∣ 4 := hdiv.trans (hdvdZ.trans h4)
    have : r = 2 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp
      (hr.dvd_of_dvd_pow (show r ∣ 2 ^ 2 by simpa using h24))
    exact hr2 this
  obtain ⟨E, hE, hEcard, hEnorm⟩ :=
    exists_isElemAbelian_torus_quadPlus (F := F) (ℓ := lab.rank) (r := r)
      (by omega) hr hr2 hrdvd
  obtain ⟨hXne, hX2⟩ := posUnip_subgroupOf_nontrivial_isPGroup (F := F) (ℓ := lab.rank) (by omega)
  exact le_evenRank_of_center_quotient (e.trans (φ₁.trans φ₂)) hr hr2 hZ hXne hX2 hE hEcard hEnorm


theorem rk2_low_bc_ge {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hK : Rk2IsLabel K lab) (htag : lab.tag = .B ∨ lab.tag = .C) (hn : 2 ≤ lab.n) :
    lab.rank ≤ evenRank K :=
  rk2_low_bc_ge_aux hK htag hn

theorem rk2_low_d_ge {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hK : Rk2IsLabel K lab) (htag : lab.tag = .D) (hℓ : 4 ≤ lab.rank) (hn : 2 ≤ lab.n) :
    lab.rank ≤ evenRank K :=
  rk2_low_d_ge_aux hK htag hℓ hn

theorem rk2_low_bcd_ge {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hK : Rk2IsLabel K lab) (htag : lab.tag = .B ∨ lab.tag = .C ∨ lab.tag = .D)
    (hn : 2 ≤ lab.n) (hD : lab.tag = .D → 4 ≤ lab.rank) :
    lab.rank ≤ evenRank K := by
  rcases htag with hB | hC | hD'
  · exact rk2_low_bc_ge hK (Or.inl hB) hn
  · exact rk2_low_bc_ge hK (Or.inr hC) hn
  · exact rk2_low_d_ge hK hD' (hD hD') hn


private theorem le_evenRank_statedSp_q2_of_markedModel {K F : Type} [Group K] [Finite K]
    [Field F] [Finite F] [CharP F 2] {ℓ : ℕ} (hℓ : 2 ≤ ℓ)
    (θ : K ⧸ Subgroup.center K ≃* StatedProj (StatedSp ℓ F))
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center K)) :
    ℓ - 1 ≤ evenRank K := by
  have hm : 1 ≤ ℓ - 1 := by omega
  have hle : ℓ - 1 ≤ localRank 3 (StatedProj (StatedSp ℓ F)) := by
    have h := CFSG.RankThree.PartOne.KFU.le_localRank_three_statedSp_blocks
      (K := F) (m := ℓ - 1) hm
    rwa [Nat.sub_add_cancel (by omega : 1 ≤ ℓ)] at h
  obtain ⟨U, hU2, hU0, E, hEN, hEel, hEcard⟩ :=
    CFSG.RankThree.PartOne.exists_elemAbelian_of_le_localRank Nat.prime_three hm hle
  have hE : IsElemAbelian 3 E :=
    CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr hEel
  exact le_evenRank_of_center_quotient θ Nat.prime_three (by norm_num) hZ hU0 hU2 hE hEcard hEN

theorem not_three_dvd_card_center_psp_q2 {K F : Type} [Group K] [Finite K]
    [Field F] [Finite F] [CharP F 2] {ℓ : ℕ} (hℓ2 : 2 ≤ ℓ) (hℓ3 : ℓ ≠ 2)
    (hcard : Nat.card F = 2) (hQ : CFSG.IsQuasisimple K)
    (θ : K ⧸ Subgroup.center K ≃* StatedProj (StatedSp ℓ F)) :
    ¬ 3 ∣ Nat.card (Subgroup.center K) := by
  intro hdiv
  have hdvdZ : Nat.card (Subgroup.center K) ∣
      Nat.card (CFSG.Open.griessHopfMultiplier (StatedProj (StatedSp ℓ F))) :=
    _root_.CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.card_center_dvd_hopf hQ θ
  rcases Nat.lt_or_ge ℓ 4 with hlt | hge
  ·
    have hℓ3' : ℓ = 3 := by omega
    subst hℓ3'
    have hLM : CFSG.Blueprint.LieModel (StatedProj (StatedSp 3 F)) .PSp 3 2 1 :=
      CFSG.LieType.Steinberg.CentralExt.SpClosed.lieModel_statedProj_sp
        (by rw [hcard]; norm_num) ⟨Nat.prime_two, le_rfl, by norm_num, by decide⟩
    obtain ⟨-, ⟨eM⟩⟩ :=
      CFSG.EvenSmallLie.SympSix.multiplier_PSp_three_two_one (StatedProj (StatedSp 3 F)) hLM
    have hMcard : Nat.card (CFSG.Open.griessHopfMultiplier
        (StatedProj (StatedSp 3 F))) = 2 := by
      rw [Nat.card_congr eM.toEquiv, Nat.card_congr Multiplicative.toAdd,
        Nat.card_eq_fintype_card, ZMod.card]
    rw [hMcard] at hdvdZ
    have h3 : 3 ∣ 2 := hdiv.trans hdvdZ
    omega
  ·
    have hLM : CFSG.Blueprint.LieModel (StatedProj (StatedSp ℓ F)) .PSp ℓ 2 1 :=
      CFSG.LieType.Steinberg.CentralExt.SpClosed.lieModel_statedProj_sp
        (by rw [hcard]; norm_num)
        ⟨Nat.prime_two, le_rfl, hℓ2, by
          intro h
          exact hℓ3 (congrArg Prod.fst h)⟩
    obtain ⟨-, ⟨eM⟩⟩ :=
      CFSG.LieType.Steinberg.CentralExt.SpClosed.psp_even_hopfMultiplier
        (K := F) (f := 1) (n := ℓ) (by rw [hcard]; norm_num) le_rfl hℓ2
        (fun h => absurd h (by omega))
    have hMcard : Nat.card (CFSG.Open.griessHopfMultiplier (StatedProj (StatedSp ℓ F))) = 1 := by
      have h1 : Nat.card F - 1 = 1 := by simp [hcard]
      have h2 : Nat.gcd 2 (Nat.card F - 1) = 1 := by simp [h1]
      calc Nat.card (CFSG.Open.griessHopfMultiplier (StatedProj (StatedSp ℓ F)))
          = Nat.card (Multiplicative (ZMod (Nat.gcd 2 (Nat.card F - 1)))) :=
            Nat.card_congr eM.toEquiv
        _ = Nat.card (Multiplicative (ZMod 1)) := by rw [h2]
        _ = 1 := by simp
    rw [hMcard] at hdvdZ
    exact Nat.Prime.not_dvd_one Nat.prime_three (hdiv.trans hdvdZ)


private theorem rk2_low_bc_one_aux {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hK : Rk2IsLabel K lab) (htag : lab.tag = .B ∨ lab.tag = .C) (hn : lab.n = 1) :
    lab.rank - 1 ≤ evenRank K := by
  obtain ⟨hQ, hlab, hM⟩ := quasisimple_markedModel_of_isLabel hK
  have ht : markTag lab = .PSp := by
    rcases htag with hB | hC
    · simp [CFSG.StandardType.markTag, hB]
    · simp [CFSG.StandardType.markTag, hC]
  have hrk : markRank lab = lab.rank := by
    rcases htag with hB | hC
    · simp [CFSG.StandardType.markRank, hB]
    · simp [CFSG.StandardType.markRank, hC]
  have hch : markChar lab = 2 := by
    rcases htag with hB | hC
    · simp [CFSG.StandardType.markChar, hB]
    · simp [CFSG.StandardType.markChar, hC]
  have hdg : markDeg lab = lab.n := by
    rcases htag with hB | hC
    · simp [CFSG.StandardType.markDeg, hB]
    · simp [CFSG.StandardType.markDeg, hC]
  have hM' := hM
  unfold CFSG.StandardType.MarkedModel at hM'
  rw [ht, hrk, hch, hdg] at hM'
  obtain ⟨hadm, F, hfield, hfinite, hcard, ⟨e⟩⟩ := hM'.statedClassicalModel (by decide)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype F := Fintype.ofFinite F
  have hcard2 : Nat.card F = 2 := by rw [hcard, hn]; norm_num
  have hcard' : Fintype.card F = 2 ^ 1 := by
    rw [← Nat.card_eq_fintype_card]; exact hcard2
  haveI : CharP F 2 := charP_of_card_eq_prime_pow hcard'
  have hℓ2 : 2 ≤ lab.rank := by
    rcases htag with hB | hC
    · have h := hlab; simp only [LargeEvenInLambda2, hB] at h; exact h.2.1
    · have h := hlab; simp only [LargeEvenInLambda2, hC] at h; exact h.2.1
  have hℓ3 : lab.rank ≠ 2 := by
    intro h2
    rcases htag with hB | hC
    · have h := hlab; simp only [LargeEvenInLambda2, hB] at h
      have := h.2.2 h2
      omega
    · have h := hlab; simp only [LargeEvenInLambda2, hC] at h
      have := h.2.2 h2
      omega
  exact le_evenRank_statedSp_q2_of_markedModel (F := F) (ℓ := lab.rank) hℓ2 e
    (not_three_dvd_card_center_psp_q2 hℓ2 hℓ3 hcard2 hQ e)


theorem rk2_low_bc_one {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hK : Rk2IsLabel K lab) (htag : lab.tag = .B ∨ lab.tag = .C) (hn : lab.n = 1) :
    lab.rank - 1 ≤ evenRank K :=
  rk2_low_bc_one_aux hK htag hn

end CFSG.LocalAnalysis.GLTheoremA
