module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzCubeOrthTwo
public import CFSG.LieType.SeitzGeneration.ExcHigh.E8FrameFamily
public import CFSG.LieType.SeitzGeneration.ExcHigh.E8FrameProd
public import CFSG.LieType.SeitzGeneration.ExcHigh.E8FiveCore
public import CFSG.LieType.SeitzGeneration.ExcHigh.F4Two
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeSporadicRank
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Assembly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerTorus
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Core
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Plane
public import CFSG.LieType.SeitzGeneration.OuterNarrowClassical
public import CFSG.LieType.Steinberg.CentralExt.PSpEvenMultiplier
public import CFSG.LieType.Steinberg.CentralExt.PSpMultiplier
public import CFSG.RankThree.Chevalley.SteinbergBNF4NativeB2
public import CFSG.RankThree.Chevalley.SteinbergBUF4B2QuarticDescent
public import CFSG.RankThree.Chevalley.SteinbergBUF4CyclotomicFourDescent
public import CFSG.RankThree.Chevalley.SteinbergBUF4CyclotomicFourTools
public import CFSG.RankThree.PartOne.CTP.StdSub
public import CFSG.RankThree.PartOne.K133H.G2Plane
public import CFSG.RankThree.PartOne.SEITZ2.OmegaSetup

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest5

set_option linter.unusedSectionVars false

section Descent

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LieType.SeitzGeneration.ExcHigh
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.TableBExcTwo CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification CFSG.HardMathSupport.Lang.AnisoE8


theorem mem_e8FrameGroup_of_frameSpan_four {K L : Type} [Field K] [Field L] [Algebra K L]
    (Fr : L →+* L) (hFrK : ∀ c : K, Fr (algebraMap K L c) = algebraMap K L c)
    (hfix : ∀ c : L, Fr c = c → c ∈ Set.range (algebraMap K L))
    {y : adjointGroup Tag.E8 K} (hy4 : y ^ 4 = y)
    (hy : baseChangeGL (algebraMap K L) (y : ModGL Tag.E8 K) ∈ frameSpan8 L) :
    y ∈ e8FrameGroup K := by
  have hFY : Units.map (entrywiseHom Fr) (baseChangeGL (algebraMap K L) (y : ModGL Tag.E8 K)) =
      baseChangeGL (algebraMap K L) (y : ModGL Tag.E8 K) := by
    have e : Fr.comp (algebraMap K L) = algebraMap K L := RingHom.ext fun b => hFrK b
    rw [units_map_entrywiseHom_eq_baseChangeGL_self,
      CFSG.LieType.Chevalley.baseChangeGL_baseChangeGL, e]
  rw [← frameProd8_range] at hy
  obtain ⟨x, hx⟩ := hy
  have hFx : Units.map (entrywiseHom Fr) (frameProd8 L x) =
      frameProd8 L (fun i => Matrix.SpecialLinearGroup.map Fr (x i)) :=
    map_frameProd8 L (Units.map (entrywiseHom Fr)) (Matrix.SpecialLinearGroup.map Fr)
      (fun i A => entrywise_rootSL2_of_field Fr (frameE8Root i) A) x
  let FrP : (Fin 8 → SL2 L) →* (Fin 8 → SL2 L) :=
    (Matrix.SpecialLinearGroup.map Fr).compLeft (Fin 8)
  have hFrP : ∀ z, FrP z = fun i => Matrix.SpecialLinearGroup.map Fr (z i) := fun _ => rfl
  have hk : frameProd8 L (x⁻¹ * FrP x) = 1 := by
    rw [map_mul, map_inv, hFrP, ← hFx, hx, hFY, inv_mul_cancel]
  obtain ⟨hkc, hk2⟩ := frameProd8_ker_sq L hk
  have hFrx : FrP x = x * (x⁻¹ * FrP x) := by rw [mul_inv_cancel_left]
  have hk4 : (x⁻¹ * FrP x) ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hk2, one_pow]
  have hx4 : FrP (x ^ 4) = x ^ 4 := by
    rw [map_pow, hFrx, (hkc x).symm.mul_pow, hk4, mul_one]
  have hrat : ∀ i, ∃ B : SL2 K,
      Matrix.SpecialLinearGroup.map (algebraMap K L) B = (x ^ 4) i := by
    intro i
    refine exists_SL2_of_entries8 (algebraMap K L) _ fun a b => hfix _ ?_
    have h := congrArg
      (fun z : Fin 8 → SL2 L => ((z i : SL2 L) : Matrix (Fin 2) (Fin 2) L) a b) hx4
    exact h
  choose u hu using hrat
  have h1 : frameProd8 L (x ^ 4) = baseChangeGL (algebraMap K L) (y : ModGL Tag.E8 K) := by
    rw [map_pow, hx, ← map_pow, ← Subgroup.coe_pow, hy4]
  have hYeq : baseChangeGL (algebraMap K L) (y : ModGL Tag.E8 K) =
      baseChangeGL (algebraMap K L) (frameProd8 K u) := by
    rw [← h1, map_frameProd8 K (baseChangeGL (algebraMap K L))
      (Matrix.SpecialLinearGroup.map (algebraMap K L))
      (fun i A => baseChangeGL_rootSL2_of_field (algebraMap K L) (frameE8Root i) A) u]
    exact congrArg (frameProd8 L) (funext fun i => (hu i).symm)
  have hyu : frameProd8 K u = (y : ModGL Tag.E8 K) :=
    baseChangeGL_injective (algebraMap K L) hYeq.symm
  exact mem_e8FrameGroup_of_frameProd hyu

end Descent

section Datum

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Chevalley CFSG.LieType.SeitzGeneration.ExcHigh
  CFSG.LieType.SeitzGeneration.ExcHighThree
open scoped MatrixGroups


theorem e8_frameDatum_three (K : Type) [Field K] [Finite K]
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ Nat.card K) :
    ∃ z ∈ adjointGroup Tag.E8 (AlgebraicClosure K),
      Units.map (entrywiseHom Fr) z =
        z * canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) frameW8 ∧
      ∀ y : adjointGroup Tag.E8 K, y ^ 3 = 1 →
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL Tag.E8 K) ∈
          (twistedTorusOf (canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) frameW8)
            (Units.map (entrywiseHom Fr))).map (MulAut.conj z).toMonoidHom →
        y ∈ e8FrameGroup K := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  haveI : Fact (ringChar K).Prime := ⟨hℓ⟩
  haveI : CharP K (ringChar K) := ringChar.charP K
  have hq : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  haveI : CharP (AlgebraicClosure K) (ringChar K) :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective _
  have hfr : Fr = iterateFrobenius (AlgebraicClosure K) (ringChar K) (f : ℕ) :=
    RingHom.ext fun x => by rw [hFr, iterateFrobenius_def, hq]
  have hn : canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) frameW8 ∈
      frameCore8 (AlgebraicClosure K) :=
    canonicalRep_mem_frameCore8_of_closure frameW8_mem_closure
  obtain ⟨z, hz, hzeq⟩ := lang_frameCore8 (L := AlgebraicClosure K) (ringChar K)
    (f : ℕ) f.pos _ hn
  have hFz : entrywiseFrobGL Tag.E8 (AlgebraicClosure K) (ringChar K) (f : ℕ) z =
      z * canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) frameW8 := by
    rw [← hzeq, mul_inv_cancel_left]
  refine ⟨z, frameCore8_le_adjointGroup hz, ?_, ?_⟩
  · rw [hfr]
    exact hFz
  · intro y hy3 hyT
    obtain ⟨t, ht, hty⟩ := Subgroup.mem_map.1 hyT
    have htT : t ∈ torusGroup Tag.E8 (AlgebraicClosure K) := (mem_twistedTorusOf.1 ht).1
    have hzS : z ∈ frameSpan8 (AlgebraicClosure K) := frameCore8_le_frameSpan8 hz
    have htS : t ∈ frameSpan8 (AlgebraicClosure K) :=
      torusGroup_le_frameSpan8 (fun x => IsAlgClosed.exists_pow_nat_eq x two_pos) htT
    have hyS : baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL Tag.E8 K) ∈
        frameSpan8 (AlgebraicClosure K) := by
      rw [← hty]
      exact mul_mem (mul_mem hzS htS) (inv_mem hzS)
    refine mem_e8FrameGroup_of_frameSpan_four Fr (fun c => ?_)
      (fun c hc => RankThree.PartOne.KE.mem_range_algebraMap_of_pow_card_eq ((hFr c).symm.trans hc))
      (by rw [pow_succ, hy3, one_mul]) hyS
    rw [hFr, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]

theorem e8_exists_conj_le_frame_of_neg {K : Type} [Field K] [Finite K]
    {E₀ : Subgroup (adjointGroup Tag.E8 K)} (hE₀p : ∀ x ∈ E₀, x ^ 3 = 1)
    (D : LangPlaneData Tag.E8 K E₀) (hw : ∀ u : Fin Tag.E8.rank → ℤ, D.w • u = -u) :
    ∃ k : adjointGroup Tag.E8 K, E₀.map (MulAut.conj k).toMonoidHom ≤ e8FrameGroup K := by
  have hw8 : D.w = frameW8 := eq_frameW8_of_smul_neg hw
  obtain ⟨g, hg, hgF, hh⟩ := e8_frameDatum_three K D.Fr D.hFr
  rw [← hw8] at hgF hh
  obtain ⟨e, he⟩ := e8_exists_rational_of_lang D.Fr D.hFr D.w D.hg0C hg D.hg0 hgF
  refine ⟨e * D.c, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hmap : (MulAut.conj (e * D.c)).toMonoidHom x = e * (D.c * x * D.c⁻¹) * e⁻¹ := by
    show (e * D.c) * x * (e * D.c)⁻¹ = _
    group
  rw [hmap]
  refine hh _ ?_ ?_
  · rw [conj_pow, conj_pow, hE₀p x hx]
    group
  · obtain ⟨t, ht, htb⟩ := Subgroup.mem_map.1 (D.hc x hx)
    refine Subgroup.mem_map.2 ⟨t, ht, ?_⟩
    have htb' : D.g0 * t * D.g0⁻¹ =
        baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((D.c * x * D.c⁻¹ : adjointGroup Tag.E8 K) : ModGL Tag.E8 K) := htb
    show g * t * g⁻¹ = baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((e * (D.c * x * D.c⁻¹) * e⁻¹ : adjointGroup Tag.E8 K) : ModGL Tag.E8 K)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul, map_inv, he,
      ← htb']
    group

end Datum


section D8

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.ExcHigh TauCeti
  CFSG.LieType.Seitz CFSG.AGLEmbedding CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenCubes
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4
open CFSG.ComponentClassification CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.LieType.CurtisTits CFSG.ComponentClassification.CatLeafProof CFSG.TauCetiBridge
  CFSG.HardMathSupport.Lang.AnisoE8 CFSG.HardMathSupport.Lang.AnisoF4 CFSG.Timmesfeld
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.ModelFacts.OrthAut
  CFSG.LieType.SeitzGeneration.ExcHighThree


theorem not_p1ThreeLieList_three_D {r : ℕ} (hr : 5 ≤ r) {q : PrimePower}
    (hv : (LieTypeIndex.D r q).Valid) : ¬ P1ThreeLieList 3 ⟨.D r q, hv⟩ := by
  unfold P1ThreeLieList
  rintro (⟨n, q', hq', -⟩ | ⟨q', -, hq'⟩ | ⟨-, m, hm⟩ | ⟨q', ⟨-, -, hq'⟩ | ⟨-, -, -, hq'⟩⟩ | hch)
  · cases hq'
  · cases hq'
  · cases hm
  · cases hq'
  · cases hq'
  · unfold IsP1ChevTwoIndex at hch
    rcases hch with ⟨-, q', -, -, h⟩ | ⟨-, q', -, -, h⟩ | ⟨h5, -⟩
    · rcases h with h | h | h | h | h | h | h | h <;> (try cases h) <;> omega
    · rcases h with h | h | h | h <;> cases h
    · omega

theorem seitzGoodIndex_three_D {r : ℕ} (hr : 5 ≤ r) {q : PrimePower} (hq2 : ¬ IsTwoPow q 1)
    (hq8 : ¬ IsTwoPow q 3) : SeitzGoodIndex 3 (LieTypeIndex.D r q) := by
  refine Or.inl ?_
  rintro (h | ⟨-, h | h | h | h | h⟩)
  · simp only [Bal207Index] at h
    rcases h with ⟨-, ⟨h | h, -, -⟩ | ⟨h, -⟩⟩
    · exact hq2 h
    · exact hq8 h
    · exact hq2 h
  · simp [IsL2EightIndex] at h
  · simp [Gen2318Index] at h
  · simp [Bal209TwoIndex] at h
  · simp [IsTwistedE6FourIndex] at h
  · rcases h with h | h | h
    · simp [IsF4EightIndex] at h
    · simp only [IsD4FourIndex] at h
      omega
    · simp only [FourIndex] at h
      omega

theorem not_isTwoPow_of_seitzGoodIndex_E8 {q : PrimePower}
    (h : SeitzGoodIndex 3 (LieTypeIndex.E8 q)) : ¬ IsTwoPow q 1 ∧ ¬ IsTwoPow q 3 := by
  rcases h with h | h
  · refine ⟨fun h1 => h ?_, fun h3 => h ?_⟩
    · exact Or.inr ⟨rfl, Or.inr (Or.inl (by simp [Gen2318Index, h1]))⟩
    · exact Or.inr ⟨rfl, Or.inr (Or.inl (by simp [Gen2318Index, h3]))⟩
  · rcases h with h | h | h <;> simp [IsF4EightIndex, IsD4FourIndex, FourIndex] at h

theorem plusModel_cubes_three {K : Type} [Field K] [Finite K] {q : PrimePower}
    (hK : Nat.card K = q.card) (hq2 : ¬ IsTwoPow q 1) (hq8 : ¬ IsTwoPow q 3)
    (hpK : ¬ 3 ∣ Nat.card K)
    (E : Subgroup (StatedProj (StatedOmega (StatedQuadPlus 8 K)))) (hE : IsElemAbelian 3 E)
    (hEc : Nat.card E = 3 ^ 3) : HyperGen 3 ⊤ E := by
  have hv : (LieTypeIndex.D 8 q).Valid :=
    (LieTypeIndex.valid_iff _).mpr ⟨(LieTypeIndex.inStandardRange_iff _).mpr (by norm_num),
      by simp⟩
  refine SeitzExcOpenRest.plusModel_cubes_of_cat hv hK (fun E₀ hE₀ hc => ?_) E hE hEc
  have hpq : 3 ≠ q.p := by
    intro h
    apply hpK
    rw [hK, PrimePower.card_def, ← h]
    exact dvd_pow_self _ q.exponent_pos.ne'
  exact SeitzExcOpenRest.seitzHyperLie_orth_good seitzGoodInnerOrthTwo_holds ⟨.D 8 q, hv⟩ 3
    Nat.prime_three (by norm_num) (by simpa using hpq) (not_p1ThreeLieList_three_D (by norm_num) hv)
    E₀ hE₀ hc ⟨Or.inr (Or.inl ⟨8, q, rfl⟩), seitzGoodIndex_three_D (by norm_num) hq2 hq8⟩

theorem iSup_d8Chain_le_hyperClosure_odd {K : Type} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq1 : ¬ p ∣ Nat.card K - 1)
    (hcube : ∀ E : Subgroup (StatedProj (StatedOmega (StatedQuadPlus 8 K))),
      IsElemAbelian p E → Nat.card E = p ^ 3 → HyperGen p ⊤ E)
    (Ψ : spinGroup (Spin.quadPlus 8 K) →* adjointGroup .E8 K)
    (hker : Ψ.ker ≤ Subgroup.center (spinGroup (Spin.quadPlus 8 K)))
    (hrange : Ψ.range = ⨆ k, e8D8Chain K k)
    (E : Subgroup (adjointGroup .E8 K)) (hE : E ≤ ⨆ k, e8D8Chain K k)
    (hEa : IsElemAbelian p E) (hEc : Nat.card E = p ^ 3) :
    ⨆ k, e8D8Chain K k ≤ hyperClosure p ⊤ E := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hn3 : 3 ≤ 8 := by norm_num
  have : Nonempty (Fin 8 ⊕ Fin 8) := ⟨Sum.inl 0⟩
  have : Finite (spinGroup (quadPlus 8 K)) :=
    CFSG.ClassicalInvolution.ModelFacts.finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  obtain ⟨hπsurj, hcomap, hZ⟩ := spinToStatedProj_quadPlus (n := 8) (K := K) hn3
  set π := spinToStatedProj (quadPlus 8 K) (range_spinMatrix_quadPlus hn3) with hπdef
  have hcen : ¬ p ∣ Nat.card (Subgroup.center (spinGroup (quadPlus 8 K))) :=
    not_dvd_card_center_spin_of_not_dvd_pred (quadPlus 8 K) (range_spinMatrix_quadPlus hn3)
      hZ hcomap
      (fun x hx => spin_mul_self_eq_one ((mem_ker_spinMatrix_quadPlus_iff x).mp hx)) hp2 hpq1
  have hπcop : ¬ p ∣ Nat.card π.ker := by
    rw [hZ]
    exact hcen
  have hΨcop : ¬ p ∣ Nat.card Ψ.ker := fun hd =>
    hcen (hd.trans (Subgroup.card_dvd_of_le hker))
  rw [← hrange]
  exact range_le_hyperClosure_of_cover hp π hπsurj hZ.le hπcop hcube Ψ hΨcop (hrange ▸ hE) hEa
    hEc

theorem hyperGen_E8_of_neg_datum {K : Type} [Field K] [Finite K] (hK : Nat.card K % 3 = 2)
    (hs : ThreeScope LieTypeIndex.E8 K) {E₀ : Subgroup (adjointGroup .E8 K)}
    (hE₀ : IsElemAbelian 3 E₀) (hc : Nat.card E₀ = 3 ^ 3) (D : LangPlaneData .E8 K E₀)
    (hw : ∀ u : Fin Tag.E8.rank → ℤ, D.w • u = -u) : HyperGen 3 ⊤ E₀ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨q, hv, hKq, hgood, -⟩ := hs
  obtain ⟨hq2, hq8⟩ := not_isTwoPow_of_seitzGoodIndex_E8 hgood
  obtain ⟨Ψ, hker, hrange⟩ := exists_psi_D8_E8_of_family (exists_e8D8_family K)
  have hpq1 : ¬ 3 ∣ Nat.card K - 1 := by omega
  have hpK : ¬ 3 ∣ Nat.card K := by omega
  exact hyperGen_of_two_conj (⨆ k, e8D8Chain K k) (e8FrameGroup K) (weylWordElt .E8 K e8Word)
    e8FrameGroup_le_d8 e8FrameGroup_le_conj_d8
    (fun M hX hn => eq_top_of_e8D8Chain_le_of_conj_le M hX hn)
    (fun E hE hEa hEc => iSup_d8Chain_le_hyperClosure_odd Nat.prime_three (by norm_num) hpq1
      (plusModel_cubes_three hKq hq2 hq8 hpK) Ψ hker hrange E hE hEa hEc)
    hE₀ hc (e8_exists_conj_le_frame_of_neg hE₀.2 D hw)

end D8


section F4Frame

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Chevalley CFSG.StandardType.TableBExcTwo
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification CFSG.HardMathSupport.Lang.AnisoF4 WithConv
open scoped MatrixGroups CFSG.ConvolutionPoints


namespace Aux

@[expose] def f4FrameM : Fin 4 → Fin Tag.F4.rank → ℤ :=
  ![![-1, 0, 0, 1], ![1, 0, 0, 0], ![-1, 2, -1, 0], ![-1, 0, 1, -1]]

@[expose] def f4FrameN : Fin Tag.F4.rank → Fin 4 → ℤ :=
  ![![0, 2, 0, 0], ![1, 3, 1, 1], ![2, 4, 0, 2], ![2, 2, 0, 0]]

theorem coroot_f4Frame_single : ∀ (i : Fin 4) (k : Fin Tag.F4.rank),
    2 * iform (f4Frame i) (Pi.single k 1 : Fin Tag.F4.rank → ℤ) / iform (f4Frame i) (f4Frame i) =
      f4FrameM i k := by
  decide +kernel

theorem f4FrameN_mul_f4FrameM : ∀ j k : Fin Tag.F4.rank,
    ∑ i, f4FrameN j i * f4FrameM i k = if j = k then 2 else 0 := by
  decide +kernel

theorem zpow_finsetSum_f4 {G ι : Type*} [CommGroup G] (a : G) (s : Finset ι) (f : ι → ℤ) :
    a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, zpow_add, ih]

end Aux

theorem rootTorusSL2_f4Frame {L : Type} [Field L] (i : Fin 4) (c : Lˣ) :
    rootTorusSL2 Tag.F4 L (f4Frame i) c =
      rootDiagUnit Tag.F4 (fun k => c ^ Aux.f4FrameM i k) := by
  obtain ⟨-, hdH, -, -, hact, -, -, -⟩ :=
    exceptional_Lang_root_rank_one_torus_transport Tag.F4 L (f4Frame_isRoot i)
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hdH c)
  rw [ha]
  congr 1
  funext k
  have h1 := (hact c).2 (Pi.single k 1) (isRoot_single Tag.F4 k)
  rw [ha] at h1
  have h2 : (((rootDiagUnit Tag.F4 a : ModGL Tag.F4 L) : Module.End L (RootModule Tag.F4 L))
      (rootVec Tag.F4 L (Pi.single k 1))) =
        ((a k : Lˣ) : L) • rootVec Tag.F4 L (Pi.single k 1) := by
    change rootDiag a (rootVec Tag.F4 L (Pi.single k 1)) = _
    have hs : rootChar a (Pi.single k 1 : Fin (Tag.rank Tag.F4) → ℤ) = a k := by
      have := rootChar_nsmul_single a k 1
      rwa [one_smul, pow_one] at this
    rw [rootDiag_rootVec _ (isRoot_single Tag.F4 k), hs]
  rw [h2] at h1
  have hne : rootVec Tag.F4 L (Pi.single k 1) ≠ 0 := by
    rw [rootVec_eq_single_of_isRoot (isRoot_single Tag.F4 k)]
    exact Finsupp.single_ne_zero.2 one_ne_zero
  have h3 := smul_left_injective L hne h1
  rw [Aux.coroot_f4Frame_single i k] at h3
  exact Units.ext h3

@[expose] def f4FrameSpan (L : Type) [Field L] : Subgroup (ModGL Tag.F4 L) :=
  ⨆ i : Fin 4, (rootSL2 Tag.F4 L (f4Frame i)).range

theorem rootSL2_mem_f4FrameSpan {L : Type} [Field L] (i : Fin 4) (A : SL2 L) :
    rootSL2 Tag.F4 L (f4Frame i) A ∈ f4FrameSpan L :=
  le_iSup (fun j : Fin 4 => (rootSL2 Tag.F4 L (f4Frame j)).range) i ⟨A, rfl⟩

theorem torusGroup_le_f4FrameSpan {L : Type} [Field L] (hsq : ∀ x : L, ∃ z : L, z ^ 2 = x) :
    torusGroup Tag.F4 L ≤ f4FrameSpan L := by
  intro t ht
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  have hs : ∀ k : Fin Tag.F4.rank, ∃ s : Lˣ, s ^ 2 = b k := by
    intro k
    obtain ⟨z, hz⟩ := hsq (b k : L)
    have hz0 : z ≠ 0 := by
      rintro rfl
      exact (b k).ne_zero (by rw [← hz]; ring)
    exact ⟨Units.mk0 z hz0, Units.ext (by simp [hz])⟩
  choose s hs using hs
  let c : Fin 4 → Lˣ := fun i => ∏ j : Fin Tag.F4.rank, s j ^ Aux.f4FrameN j i
  let v : Fin 4 → Fin Tag.F4.rank → Lˣ := fun i k => c i ^ Aux.f4FrameM i k
  have hv : ∀ i, rootDiagUnitHom Tag.F4 L (v i) ∈ f4FrameSpan L := by
    intro i
    have h := rootTorusSL2_f4Frame (L := L) i (c i)
    have hv' : rootDiagUnitHom Tag.F4 L (v i) = rootTorusSL2 Tag.F4 L (f4Frame i) (c i) := by
      rw [h]
      rfl
    rw [hv']
    exact rootSL2_mem_f4FrameSpan i (HSL (c i))
  have hb : b = ∏ i : Fin 4, v i := by
    funext k
    rw [Finset.prod_apply]
    have hexp : ∀ i : Fin 4, v i k =
        ∏ j : Fin Tag.F4.rank, s j ^ (Aux.f4FrameN j i * Aux.f4FrameM i k) := by
      intro i
      simp only [v, c, ← Finset.prod_zpow, ← zpow_mul]
    rw [Finset.prod_congr rfl fun i _ => hexp i, Finset.prod_comm]
    have hcol : ∀ j : Fin Tag.F4.rank, ∏ i : Fin 4, s j ^ (Aux.f4FrameN j i * Aux.f4FrameM i k) =
        s j ^ (if j = k then (2 : ℤ) else 0) := by
      intro j
      rw [← Aux.f4FrameN_mul_f4FrameM j k, Aux.zpow_finsetSum_f4]
    rw [Finset.prod_congr rfl fun j _ => hcol j]
    rw [Finset.prod_eq_single k (fun j _ hj => by rw [if_neg hj, zpow_zero])
      (fun h => absurd (Finset.mem_univ k) h), if_pos rfl]
    rw [zpow_two, ← pow_two, hs k]
  have hmem : b ∈ (f4FrameSpan L).comap (rootDiagUnitHom Tag.F4 L) := by
    rw [hb]
    exact Subgroup.prod_mem _ fun i _ => hv i
  exact hmem

@[expose] def f4FrameCharAdd : (Fin Tag.F4.rank → ℤ) →+ (Fin 3 → ZMod 2) where
  toFun v s := ((v (![0, 2, 3] s) : ℤ) : ZMod 2)
  map_zero' := by ext s; simp
  map_add' u v := by ext s; simp

@[expose] def f4FrameChar :
    Multiplicative (Fin Tag.F4.rank → ℤ) →* Multiplicative (Fin 3 → ZMod 2) :=
  AddMonoidHom.toMultiplicative f4FrameCharAdd

theorem f4FrameChar_eq_one_iff (α : Fin Tag.F4.rank → ℤ) :
    f4FrameChar (Multiplicative.ofAdd α) = 1 ↔ α 0 % 2 = 0 ∧ α 2 % 2 = 0 ∧ α 3 % 2 = 0 := by
  have h : f4FrameChar (Multiplicative.ofAdd α) = Multiplicative.ofAdd (f4FrameCharAdd α) := rfl
  rw [h, ← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff, funext_iff]
  simp only [Pi.zero_apply, f4FrameCharAdd, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    intCast_zmod_two_eq_zero_iff_E8]
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2⟩
  · rintro ⟨h0, h1, h2⟩ s
    fin_cases s
    · exact h0
    · exact h1
    · exact h2

theorem f4Frame_coord_even : ∀ i : Fin 4,
    f4Frame i 0 % 2 = 0 ∧ f4Frame i 2 % 2 = 0 ∧ f4Frame i 3 % 2 = 0 := by
  decide +kernel

theorem f4Frame_mem_kernelRoots (i : Fin 4) : f4Frame i ∈ kernelRoots f4FrameChar :=
  ⟨f4Frame_isRoot i, (f4FrameChar_eq_one_iff _).2 (f4Frame_coord_even i)⟩

theorem neg_mem_kernelRoots_f4FrameChar {α : Fin Tag.F4.rank → ℤ}
    (hα : α ∈ kernelRoots f4FrameChar) : -α ∈ kernelRoots f4FrameChar := by
  refine ⟨IsRoot.neg hα.1, ?_⟩
  obtain ⟨h0, h2, h3⟩ := (f4FrameChar_eq_one_iff α).1 hα.2
  refine (f4FrameChar_eq_one_iff (-α)).2 ?_
  simp only [Pi.neg_apply]
  omega

theorem eq_f4Frame_of_mem_kernelRoots {α : Fin Tag.F4.rank → ℤ}
    (hα : α ∈ kernelRoots f4FrameChar) :
    ∃ i : Fin 4, α = f4Frame i ∨ α = -f4Frame i := by
  obtain ⟨hroot, hker⟩ := hα
  obtain ⟨h0, h2, h3⟩ := (f4FrameChar_eq_one_iff α).1 hker
  have key : ∀ β ∈ rootFinset .F4, β 0 % 2 = 0 → β 2 % 2 = 0 → β 3 % 2 = 0 →
      ∃ i : Fin 4, β = f4Frame i ∨ β = -f4Frame i := by
    decide +kernel
  exact key α (mem_rootFinset.2 hroot) h0 h2 h3

@[expose] def f4FrameW : WeylGroup Tag.F4 :=
  ((List.finRange 4).map fun i => rootReflection (f4Frame i)).prod

theorem f4FrameW_smul_foldr (l : List (Fin 4)) (v : Fin Tag.F4.rank → ℤ) :
    (l.map fun i => rootReflection (f4Frame i)).prod • v =
      l.foldr (fun i u => u - corootPair (f4Frame i) u • f4Frame i) v := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, mul_smul, ih, List.foldr_cons,
      rootReflection_smul (f4Frame_isRoot a)]

theorem f4FrameW_fold_single : ∀ k : Fin Tag.F4.rank,
    (List.finRange 4).foldr (fun i u => u - corootPair (f4Frame i) u • f4Frame i)
      (Pi.single k 1 : Fin Tag.F4.rank → ℤ) = -Pi.single k 1 := by
  decide +kernel

theorem f4FrameW_eq_f4Neg : f4FrameW = f4Neg :=
  ext_single fun k => by
    rw [f4FrameW, f4FrameW_smul_foldr, f4FrameW_fold_single, f4Neg_smul]

theorem f4Neg_mem_closure :
    f4Neg ∈ Subgroup.closure ((fun α => rootReflection α) '' kernelRoots f4FrameChar) := by
  rw [← f4FrameW_eq_f4Neg]
  unfold f4FrameW
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  exact Subgroup.subset_closure ⟨f4Frame i, f4Frame_mem_kernelRoots i, rfl⟩

@[expose] def f4FrameCore (L : Type) [Field L] : Subgroup (ModGL Tag.F4 L) :=
  torusGroup Tag.F4 L ⊔ rootSpan Tag.F4 L (kernelRoots f4FrameChar)

theorem f4FrameCore_le_f4FrameSpan {L : Type} [Field L] [IsAlgClosed L] :
    f4FrameCore L ≤ f4FrameSpan L := by
  unfold f4FrameCore
  refine sup_le (torusGroup_le_f4FrameSpan (L := L) fun x =>
    IsAlgClosed.exists_pow_nat_eq x two_pos) ?_
  unfold rootSpan
  refine iSup₂_le fun α hα => ?_
  have hrange : ∀ j : Fin 4, (rootSL2 Tag.F4 L (f4Frame j)).range ≤ f4FrameSpan L := fun j =>
    le_iSup (fun k : Fin 4 => (rootSL2 Tag.F4 L (f4Frame k)).range) j
  obtain ⟨i, rfl | rfl⟩ := eq_f4Frame_of_mem_kernelRoots hα
  · exact (le_sup_left.trans (range_rootSL2_of_isRoot (K := L)
      (f4Frame_isRoot i)).symm.le).trans (hrange i)
  · exact (le_sup_right.trans (range_rootSL2_of_isRoot (K := L)
      (f4Frame_isRoot i)).symm.le).trans (hrange i)

theorem f4FrameCore_le_adjointGroup {L : Type} [Field L] :
    f4FrameCore L ≤ adjointGroup Tag.F4 L :=
  sup_le CFSG.RankThree.PartOne.KE.torusGroup_le_adjointGroup'
    (rootSpan_le_adjointGroup L _)

theorem canonicalRep_mem_f4FrameCore_of_closure {L : Type} [Field L] {y : WeylGroup Tag.F4}
    (hy : y ∈ Subgroup.closure ((fun α => rootReflection α) '' kernelRoots f4FrameChar)) :
    canonicalRep (coxeterSystem Tag.F4) L y ∈ f4FrameCore L := by
  let R : Subgroup (WeylGroup Tag.F4) :=
    { carrier := {x | canonicalRep (coxeterSystem Tag.F4) L x ∈ f4FrameCore L}
      mul_mem' := fun {x x'} hx hx' => by
        obtain ⟨k, hk, hkk⟩ := canonicalRep_mul_mem (τ := Tag.F4) (R := L) x x'
        have hmul : canonicalRep (coxeterSystem Tag.F4) L (x * x') =
            k⁻¹ * (canonicalRep (coxeterSystem Tag.F4) L x *
              canonicalRep (coxeterSystem Tag.F4) L x') := by
          rw [hkk]
          group
        show canonicalRep (coxeterSystem Tag.F4) L (x * x') ∈ f4FrameCore L
        rw [hmul]
        exact mul_mem (inv_mem (Subgroup.mem_sup_left hk)) (mul_mem hx hx')
      one_mem' := by
        show canonicalRep (coxeterSystem Tag.F4) L 1 ∈ f4FrameCore L
        rw [canonicalRep_one]
        exact one_mem _
      inv_mem' := fun {x} hx => by
        obtain ⟨k, hk, hkk⟩ := canonicalRep_mul_mem (τ := Tag.F4) (R := L) x x⁻¹
        rw [mul_inv_cancel, canonicalRep_one, mul_one] at hkk
        have hinv : canonicalRep (coxeterSystem Tag.F4) L x⁻¹ =
            (canonicalRep (coxeterSystem Tag.F4) L x)⁻¹ * k := by
          rw [← hkk]
          group
        show canonicalRep (coxeterSystem Tag.F4) L x⁻¹ ∈ f4FrameCore L
        rw [hinv]
        exact mul_mem (inv_mem hx) (Subgroup.mem_sup_left hk) }
  have hgen : ∀ r ∈ (fun α => rootReflection α) '' kernelRoots f4FrameChar, r ∈ R := by
    rintro r ⟨α, hα, rfl⟩
    show canonicalRep (coxeterSystem Tag.F4) L (rootReflection α) ∈ f4FrameCore L
    have hn := canonicalRep_rootReflection_mem (τ := Tag.F4) (K := L) hα.1
    have hsub : rootSubgroup Tag.F4 L α ⊔ rootSubgroup Tag.F4 L (-α) ≤ f4FrameCore L :=
      sup_le ((rootSubgroup_le_rootSpan (τ := Tag.F4) (K := L) hα).trans le_sup_right)
        ((rootSubgroup_le_rootSpan (τ := Tag.F4) (K := L)
          (neg_mem_kernelRoots_f4FrameChar hα)).trans le_sup_right)
    exact (sup_le le_sup_left hsub) hn
  exact (Subgroup.closure_le R).2 (fun r hr => hgen r hr) hy

section Lang

variable {L : Type} [Field L] [IsAlgClosed L] (ℓ : ℕ) [Fact ℓ.Prime] [CharP L ℓ]

theorem entrywiseFrobGL_mem_f4FrameCore (e : ℕ) {g : ModGL Tag.F4 L} (hg : g ∈ f4FrameCore L) :
    entrywiseFrobGL Tag.F4 L ℓ e g ∈ f4FrameCore L := by
  have hmap : (f4FrameCore L).map (entrywiseFrobGL Tag.F4 L ℓ e) ≤ f4FrameCore L := by
    rw [f4FrameCore, Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨h, hh, rfl⟩
      obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
      rw [entrywiseFrobGL_rootDiagUnit_eq_map]
      exact Subgroup.mem_sup_left (rootDiagUnit_mem_torusGroup _)
    · rw [rootSpan, Subgroup.map_iSup]
      refine iSup_le fun α => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hα => ?_
      rw [rootSubgroup, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
      exact Subgroup.mem_sup_right (le_iSup₂_of_le (f := fun β (_ : β ∈ kernelRoots f4FrameChar) =>
        rootSubgroup Tag.F4 L β) α hα le_rfl (Subgroup.subset_closure
          ⟨iterateFrobenius L ℓ e c, (entrywiseFrobGL_pinnedX ℓ e α c).symm⟩))
  exact hmap ⟨g, hg, rfl⟩

theorem lang_f4FrameCore (e : ℕ) (he : 1 ≤ e) :
    ∀ c ∈ f4FrameCore L, ∃ z ∈ f4FrameCore L, z⁻¹ * entrywiseFrobGL Tag.F4 L ℓ e z = c := by
  have hZ : IsConnectedAlgebraicSubgroup L
      ((f4FrameCore L).map (modGLPoint Tag.F4 L).toMonoidHom) :=
    isConnectedAlgebraicSubgroup_torus_sup_rootSpan_kernelRoots (τ := Tag.F4) (k := L) f4FrameChar
  have hst : ∀ g ∈ f4FrameCore L, frobTwistGL Tag.F4 L ℓ e 1 g ∈ f4FrameCore L := fun g hg => by
    rw [frobTwistGL_apply, one_mul, inv_one, mul_one]
    exact entrywiseFrobGL_mem_f4FrameCore ℓ e hg
  obtain ⟨-, -, -, hlang⟩ := exists_frobTwist_restriction ℓ hZ he 1 hst
  intro c hc
  obtain ⟨z, hz, hzc⟩ := hlang c hc
  exact ⟨z, hz, by rw [frobTwistGL_apply, one_mul, inv_one, mul_one] at hzc; exact hzc⟩

end Lang

end F4Frame


section F4Prod

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.LieType.SeitzGeneration.ExcHighThree
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.TableBExcTwo CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification CFSG.HardMathSupport.Lang.AnisoF4


section Prod

variable (L : Type) [Field L]

theorem range_rootSL2_f4Frame (i : Fin 4) :
    (rootSL2 Tag.F4 L (f4Frame i)).range =
      (rootPairF4 L (f4Frame i)).map (adjointGroup Tag.F4 L).subtype := by
  have h1 := map_subtype_rootGroup (K := L) (rootOperatorFamily Tag.F4) (f4Frame_isRoot i)
  have h2 := map_subtype_rootGroup (K := L) (rootOperatorFamily Tag.F4)
    (IsRoot.neg (f4Frame_isRoot i))
  rw [range_rootSL2_of_isRoot (f4Frame_isRoot i), ← h1, ← h2, ← Subgroup.map_sup]

theorem f4Frame_rootSL2_commute (i j : Fin 4) (hij : i ≠ j) (A B : SL2 L) :
    Commute (rootSL2 Tag.F4 L (f4Frame i) A) (rootSL2 Tag.F4 L (f4Frame j) B) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := f4Frame_facts i j hij
  have hc := commutes_rootPair_of_noG2 (K := L)
    CFSG.LieType.Steinberg.Adjoint.noG2_F4
    (f4Frame_isRoot i) (f4Frame_isRoot j) h1 h2 h3 h4 h5
  obtain ⟨x, hx, hxA⟩ : rootSL2 Tag.F4 L (f4Frame i) A ∈
      (rootPairF4 L (f4Frame i)).map (adjointGroup Tag.F4 L).subtype := by
    rw [← range_rootSL2_f4Frame]
    exact ⟨A, rfl⟩
  obtain ⟨y, hy, hyB⟩ : rootSL2 Tag.F4 L (f4Frame j) B ∈
      (rootPairF4 L (f4Frame j)).map (adjointGroup Tag.F4 L).subtype := by
    rw [← range_rootSL2_f4Frame]
    exact ⟨B, rfl⟩
  rw [← hxA, ← hyB]
  exact congrArg Subtype.val (hc x hx y hy)

theorem f4Frame_rootSL2_pairwise : Pairwise fun i j : Fin 4 => ∀ (x y : SL2 L),
    Commute (rootSL2 Tag.F4 L (f4Frame i) x) (rootSL2 Tag.F4 L (f4Frame j) y) :=
  fun _ _ hij x y => f4Frame_rootSL2_commute L _ _ hij x y

@[expose] def f4FrameProd : (Fin 4 → SL2 L) →* ModGL Tag.F4 L :=
  MonoidHom.noncommPiCoprod (fun i => rootSL2 Tag.F4 L (f4Frame i)) (f4Frame_rootSL2_pairwise L)

theorem f4FrameProd_mulSingle (i : Fin 4) (A : SL2 L) :
    f4FrameProd L (Pi.mulSingle i A) = rootSL2 Tag.F4 L (f4Frame i) A := by
  unfold f4FrameProd
  rw [MonoidHom.noncommPiCoprod_mulSingle]

theorem f4FrameProd_range : (f4FrameProd L).range = f4FrameSpan L :=
  MonoidHom.noncommPiCoprod_range _

theorem f4FrameProd_ker_center {k : Fin 4 → SL2 L} (hk : f4FrameProd L k = 1) (i : Fin 4) :
    k i ∈ Subgroup.center (SL2 L) := by
  classical
  rw [Subgroup.mem_center_iff]
  intro A
  have hc : f4FrameProd L (Pi.mulSingle i A * k * (Pi.mulSingle i A)⁻¹ * k⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hk, inv_one, mul_one, mul_one,
      mul_inv_cancel]
  have hc' : Pi.mulSingle i A * k * (Pi.mulSingle i A)⁻¹ * k⁻¹ =
      Pi.mulSingle i (A * k i * A⁻¹ * (k i)⁻¹) := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [Pi.mulSingle_eq_of_ne hj]
  rw [hc', f4FrameProd_mulSingle] at hc
  have h1 : A * k i * A⁻¹ * (k i)⁻¹ = 1 :=
    rootSL2_injective_of_field (f4Frame i) (hc.trans (map_one _).symm)
  have h2 : A * k i * A⁻¹ = k i := mul_inv_eq_one.1 h1
  exact mul_inv_eq_iff_eq_mul.1 h2

theorem f4FrameProd_ker_sq {k : Fin 4 → SL2 L} (hk : f4FrameProd L k = 1) :
    (∀ x : Fin 4 → SL2 L, Commute k x) ∧ k ^ 2 = 1 := by
  refine ⟨fun x => funext fun i => ?_, funext fun i => ?_⟩
  · exact ((Subgroup.mem_center_iff.1 (f4FrameProd_ker_center L hk i)) (x i)).symm
  · exact sq_eq_one_of_mem_center_SL2_E8 L (f4FrameProd_ker_center L hk i)

theorem map_f4FrameProd {L' : Type} [Field L'] (f : ModGL Tag.F4 L →* ModGL Tag.F4 L')
    (g : SL2 L →* SL2 L')
    (hfg : ∀ i A, f (rootSL2 Tag.F4 L (f4Frame i) A) = rootSL2 Tag.F4 L' (f4Frame i) (g A))
    (x : Fin 4 → SL2 L) : f (f4FrameProd L x) = f4FrameProd L' (fun i => g (x i)) := by
  rw [f4FrameProd, f4FrameProd, MonoidHom.noncommPiCoprod_apply,
    MonoidHom.noncommPiCoprod_apply, Finset.map_noncommProd]
  exact Finset.noncommProd_congr rfl (fun i _ => hfg i (x i)) _

end Prod

theorem mem_f4FrameGroup_of_frameProd {K : Type} [Field K] {y : adjointGroup Tag.F4 K}
    {u : Fin 4 → SL2 K} (hu : f4FrameProd K u = (y : ModGL Tag.F4 K)) : y ∈ f4FrameGroup K := by
  have hmem : (y : ModGL Tag.F4 K) ∈ (f4FrameGroup K).map (adjointGroup Tag.F4 K).subtype := by
    rw [f4FrameGroup, Subgroup.map_iSup, ← hu]
    have h : f4FrameProd K u ∈ (f4FrameProd K).range := ⟨u, rfl⟩
    rw [f4FrameProd_range, f4FrameSpan] at h
    simpa only [range_rootSL2_f4Frame] using h
  obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 hmem
  rwa [Subtype.ext hzy] at hz

theorem mem_f4FrameGroup_of_frameSpan_four {K L : Type} [Field K] [Field L] [Algebra K L]
    (Fr : L →+* L) (hFrK : ∀ c : K, Fr (algebraMap K L c) = algebraMap K L c)
    (hfix : ∀ c : L, Fr c = c → c ∈ Set.range (algebraMap K L))
    {y : adjointGroup Tag.F4 K} (hy4 : y ^ 4 = y)
    (hy : baseChangeGL (algebraMap K L) (y : ModGL Tag.F4 K) ∈ f4FrameSpan L) :
    y ∈ f4FrameGroup K := by
  have hFY : Units.map (entrywiseHom Fr) (baseChangeGL (algebraMap K L) (y : ModGL Tag.F4 K)) =
      baseChangeGL (algebraMap K L) (y : ModGL Tag.F4 K) := by
    have e : Fr.comp (algebraMap K L) = algebraMap K L := RingHom.ext fun b => hFrK b
    rw [units_map_entrywiseHom_eq_baseChangeGL_self,
      CFSG.LieType.Chevalley.baseChangeGL_baseChangeGL, e]
  rw [← f4FrameProd_range] at hy
  obtain ⟨x, hx⟩ := hy
  have hFx : Units.map (entrywiseHom Fr) (f4FrameProd L x) =
      f4FrameProd L (fun i => Matrix.SpecialLinearGroup.map Fr (x i)) :=
    map_f4FrameProd L (Units.map (entrywiseHom Fr)) (Matrix.SpecialLinearGroup.map Fr)
      (fun i A => entrywise_rootSL2_of_field Fr (f4Frame i) A) x
  let FrP : (Fin 4 → SL2 L) →* (Fin 4 → SL2 L) :=
    (Matrix.SpecialLinearGroup.map Fr).compLeft (Fin 4)
  have hFrP : ∀ z, FrP z = fun i => Matrix.SpecialLinearGroup.map Fr (z i) := fun _ => rfl
  have hk : f4FrameProd L (x⁻¹ * FrP x) = 1 := by
    rw [map_mul, map_inv, hFrP, ← hFx, hx, hFY, inv_mul_cancel]
  obtain ⟨hkc, hk2⟩ := f4FrameProd_ker_sq L hk
  have hFrx : FrP x = x * (x⁻¹ * FrP x) := by rw [mul_inv_cancel_left]
  have hk4 : (x⁻¹ * FrP x) ^ 4 = 1 := by
    have e4 : (x⁻¹ * FrP x) ^ 4 = ((x⁻¹ * FrP x) ^ 2) ^ 2 := by rw [← pow_mul]
    rw [e4, hk2, one_pow]
  have hx4 : FrP (x ^ 4) = x ^ 4 := by
    rw [map_pow, hFrx, (hkc x).symm.mul_pow, hk4, mul_one]
  have hrat : ∀ i, ∃ B : SL2 K,
      Matrix.SpecialLinearGroup.map (algebraMap K L) B = (x ^ 4) i := by
    intro i
    refine exists_SL2_of_entries8 (algebraMap K L) _ fun a b => hfix _ ?_
    have h := congrArg
      (fun z : Fin 4 → SL2 L => ((z i : SL2 L) : Matrix (Fin 2) (Fin 2) L) a b) hx4
    exact h
  choose u hu using hrat
  have h1 : f4FrameProd L (x ^ 4) = baseChangeGL (algebraMap K L) (y : ModGL Tag.F4 K) := by
    rw [map_pow, hx, ← map_pow, ← Subgroup.coe_pow, hy4]
  have hYeq : baseChangeGL (algebraMap K L) (y : ModGL Tag.F4 K) =
      baseChangeGL (algebraMap K L) (f4FrameProd K u) := by
    rw [← h1, map_f4FrameProd K (baseChangeGL (algebraMap K L))
      (Matrix.SpecialLinearGroup.map (algebraMap K L))
      (fun i A => baseChangeGL_rootSL2_of_field (algebraMap K L) (f4Frame i) A) u]
    exact congrArg (f4FrameProd L) (funext fun i => (hu i).symm)
  have hyu : f4FrameProd K u = (y : ModGL Tag.F4 K) :=
    baseChangeGL_injective (algebraMap K L) hYeq.symm
  exact mem_f4FrameGroup_of_frameProd hyu

theorem f4_frameDatum_three (K : Type) [Field K] [Finite K]
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ Nat.card K) :
    ∃ z ∈ adjointGroup Tag.F4 (AlgebraicClosure K),
      Units.map (entrywiseHom Fr) z =
        z * canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) f4Neg ∧
      ∀ y : adjointGroup Tag.F4 K, y ^ 3 = 1 →
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL Tag.F4 K) ∈
          (twistedTorusOf (canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) f4Neg)
            (Units.map (entrywiseHom Fr))).map (MulAut.conj z).toMonoidHom →
        y ∈ f4FrameGroup K := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  haveI : Fact (ringChar K).Prime := ⟨hℓ⟩
  haveI : CharP K (ringChar K) := ringChar.charP K
  have hq : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  haveI : CharP (AlgebraicClosure K) (ringChar K) :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective _
  have hfr : Fr = iterateFrobenius (AlgebraicClosure K) (ringChar K) (f : ℕ) :=
    RingHom.ext fun x => by rw [hFr, iterateFrobenius_def, hq]
  have hn : canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) f4Neg ∈
      f4FrameCore (AlgebraicClosure K) :=
    canonicalRep_mem_f4FrameCore_of_closure f4Neg_mem_closure
  obtain ⟨z, hz, hzeq⟩ := lang_f4FrameCore (L := AlgebraicClosure K) (ringChar K)
    (f : ℕ) f.pos _ hn
  have hFz : entrywiseFrobGL Tag.F4 (AlgebraicClosure K) (ringChar K) (f : ℕ) z =
      z * canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) f4Neg := by
    rw [← hzeq, mul_inv_cancel_left]
  refine ⟨z, f4FrameCore_le_adjointGroup hz, ?_, ?_⟩
  · rw [hfr]
    exact hFz
  · intro y hy3 hyT
    obtain ⟨t, ht, hty⟩ := Subgroup.mem_map.1 hyT
    have htT : t ∈ torusGroup Tag.F4 (AlgebraicClosure K) := (mem_twistedTorusOf.1 ht).1
    have hzS : z ∈ f4FrameSpan (AlgebraicClosure K) := f4FrameCore_le_f4FrameSpan hz
    have htS : t ∈ f4FrameSpan (AlgebraicClosure K) :=
      torusGroup_le_f4FrameSpan (fun x => IsAlgClosed.exists_pow_nat_eq x two_pos) htT
    have hyS : baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL Tag.F4 K) ∈
        f4FrameSpan (AlgebraicClosure K) := by
      rw [← hty]
      exact mul_mem (mul_mem hzS htS) (inv_mem hzS)
    refine mem_f4FrameGroup_of_frameSpan_four Fr (fun c => ?_)
      (fun c hc => RankThree.PartOne.KE.mem_range_algebraMap_of_pow_card_eq ((hFr c).symm.trans hc))
      (by rw [pow_succ, hy3, one_mul]) hyS
    rw [hFr, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]

theorem f4_exists_conj_le_frame_of_neg {K : Type} [Field K] [Finite K]
    {E₀ : Subgroup (adjointGroup Tag.F4 K)} (hE₀p : ∀ x ∈ E₀, x ^ 3 = 1)
    (D : LangPlaneData Tag.F4 K E₀) (hw : ∀ u : Fin Tag.F4.rank → ℤ, D.w • u = -u) :
    ∃ k : adjointGroup Tag.F4 K, E₀.map (MulAut.conj k).toMonoidHom ≤ f4FrameGroup K := by
  have hwN : D.w = f4Neg :=
    FaithfulSMul.eq_of_smul_eq_smul (α := Fin Tag.F4.rank → ℤ) fun u => by
      rw [hw u, f4Neg_smul]
  obtain ⟨g, hg, hgF, hh⟩ := f4_frameDatum_three K D.Fr D.hFr
  rw [← hwN] at hgF hh
  have hbij : Function.Bijective D.Fr := by
    refine ⟨D.Fr.injective, fun c => ?_⟩
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq c (Nat.card_pos (α := K))
    exact ⟨z, by rw [D.hFr z, hz]⟩
  have hmem : g * D.g0⁻¹ ∈ adjointGroup Tag.F4 (AlgebraicClosure K) := mul_mem hg (inv_mem D.hg0C)
  have hfix : Units.map (entrywiseHom D.Fr) (g * D.g0⁻¹) = g * D.g0⁻¹ := by
    rw [map_mul, map_inv, hgF, D.hg0]
    group
  obtain ⟨e', he'mem, he'⟩ := Subgroup.mem_map.1
    (CFSG.RankThree.Chevalley.mem_map_adjointGroup_of_frobenius_fixed (τ := Tag.F4) (Or.inr rfl)
      D.Fr D.hFr hbij hmem hfix)
  set e : adjointGroup Tag.F4 K := ⟨e', he'mem⟩ with hedef
  have he : baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL Tag.F4 K) =
      g * D.g0⁻¹ := he'
  refine ⟨e * D.c, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hmap : (MulAut.conj (e * D.c)).toMonoidHom x = e * (D.c * x * D.c⁻¹) * e⁻¹ := by
    show (e * D.c) * x * (e * D.c)⁻¹ = _
    group
  rw [hmap]
  refine hh _ ?_ ?_
  · rw [conj_pow, conj_pow, hE₀p x hx]
    group
  · obtain ⟨t, ht, htb⟩ := Subgroup.mem_map.1 (D.hc x hx)
    refine Subgroup.mem_map.2 ⟨t, ht, ?_⟩
    have htb' : D.g0 * t * D.g0⁻¹ =
        baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((D.c * x * D.c⁻¹ : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) := htb
    show g * t * g⁻¹ = baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((e * (D.c * x * D.c⁻¹) * e⁻¹ : adjointGroup Tag.F4 K) : ModGL Tag.F4 K)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul, map_inv, he,
      ← htb']
    group

end F4Prod


section B4

open scoped MatrixGroups
open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.ExcHigh TauCeti
  CFSG.LieType.Seitz CFSG.AGLEmbedding CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenCubes
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4
open CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.LieType.CurtisTits
  CFSG.ComponentClassification.CatLeafProof CFSG.TauCetiBridge CFSG.AGLEmbeddingD2
  CFSG.HardMathSupport.Lang.AnisoF4 CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.ModelFacts.OrthAut CFSG.RankThree.PartOne.KCSpFull
  CFSG.LieType.SeitzGeneration.ExcHighThree CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)


theorem not_p1ThreeLieList_three_B {r : ℕ} (hr : 3 ≤ r) {q : PrimePower} (hq2 : q.p ≠ 2)
    (hv : (LieTypeIndex.B r q).Valid) : ¬ P1ThreeLieList 3 ⟨.B r q, hv⟩ := by
  unfold P1ThreeLieList
  rintro (⟨n, q', hq', -⟩ | ⟨q', -, hq'⟩ | ⟨-, m, hm⟩ | ⟨q', ⟨-, -, hq'⟩ | ⟨-, -, -, hq'⟩⟩ | hch)
  · cases hq'
  · cases hq'
  · cases hm
  · injection hq' with h1 h2
    omega
  · cases hq'
  · unfold IsP1ChevTwoIndex at hch
    rcases hch with ⟨-, q', hq'2, -, h⟩ | ⟨-, q', hq'2, -, h⟩ | ⟨h5, -⟩
    · rcases h with h | h | h | h | h | h | h | h <;> (try cases h) <;> exact hq2 hq'2
    · rcases h with h | h | h | h
      · injection h with h1 h2
        omega
      all_goals cases h
    · omega

theorem seitzGoodIndex_three_B {r : ℕ} {q : PrimePower} (hq2 : q.p ≠ 2) :
    SeitzGoodIndex 3 (LieTypeIndex.B r q) := by
  refine Or.inl ?_
  rintro (h | ⟨-, h | h | h | h | h⟩)
  · simp only [Bal207Index] at h
    rcases h with ⟨-, ⟨h, -⟩ | ⟨h, -⟩⟩
    · exact hq2 h.1
    · exact hq2 h.1
  · simp [IsL2EightIndex] at h
  · simp [Gen2318Index] at h
  · simp [Bal209TwoIndex] at h
  · simp [IsTwistedE6FourIndex] at h
  · rcases h with h | h | h
    · simp [IsF4EightIndex] at h
    · simp [IsD4FourIndex] at h
    · simp [FourIndex] at h

theorem oddModel_cubes_three {K : Type} [Field K] [Finite K] {q : PrimePower}
    (hK : Nat.card K = q.card) (hq2 : q.p ≠ 2) (hpK : ¬ 3 ∣ Nat.card K)
    (E : Subgroup (StatedProj (StatedOmega (StatedQuadOdd 4 K)))) (hE : IsElemAbelian 3 E)
    (hEc : Nat.card E = 3 ^ 3) : HyperGen 3 ⊤ E := by
  have hv : (LieTypeIndex.B 4 q).Valid :=
    (LieTypeIndex.valid_iff _).mpr ⟨(LieTypeIndex.inStandardRange_iff _).mpr ⟨by omega,
      fun h => by omega⟩, by simp⟩
  refine SeitzExcOpenRest.oddModel_cubes_of_cat hv (by norm_num) hq2 hK (fun E₀ hE₀ hc => ?_)
    E hE hEc
  have hpq : 3 ≠ q.p := by
    intro h
    apply hpK
    rw [hK, PrimePower.card_def, ← h]
    exact dvd_pow_self _ q.exponent_pos.ne'
  exact SeitzExcOpenRest.seitzHyperLie_orth_good seitzGoodInnerOrthTwo_holds ⟨.B 4 q, hv⟩ 3
    Nat.prime_three (by norm_num) (by simpa using hpq)
    (not_p1ThreeLieList_three_B (by norm_num) hq2 hv) E₀ hE₀ hc
    ⟨Or.inl ⟨4, q, rfl, by norm_num, hq2⟩, seitzGoodIndex_three_B hq2⟩

theorem iSup_b4Chain_le_hyperClosure_three {K : Type} [Field K] [Finite K]
    (hK3 : Nat.card K % 3 = 2) (hK2 : Nat.card K ≠ 2)
    (hodd : (2 : K) ≠ 0 → ∀ E : Subgroup (StatedProj (StatedOmega (StatedQuadOdd 4 K))),
      IsElemAbelian 3 E → Nat.card E = 3 ^ 3 → HyperGen 3 ⊤ E)
    (E : Subgroup (adjointGroup .F4 K)) (hE : E ≤ ⨆ k, b4Chain K k)
    (hEa : IsElemAbelian 3 E) (hEc : Nat.card E = 3 ^ 3) :
    ⨆ k, b4Chain K k ≤ hyperClosure 3 ⊤ E := by
  classical
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have : Fact (3 : ℕ).Prime := ⟨hp⟩
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  have hpK : ¬ 3 ∣ Nat.card K := by omega
  have hpq1 : ¬ 3 ∣ Nat.card K - 1 := by omega
  by_cases h2 : (2 : K) = 0
  · have hc : ringChar K = 2 := by
      have hd : ringChar K ∣ 2 := ringChar.dvd (by exact_mod_cast h2)
      exact (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 hd
    have : CharP K 2 := ringChar.of_eq hc
    have hK2' : Nat.card K = 2 ^ (n : ℕ) := by rw [hK, hc]
    have hK4 : 4 ≤ Nat.card K := by omega
    obtain ⟨Ψ, hker, hrange, -, -⟩ := exists_psi_B4_F4_frame_even hK2' hK4
    have hcen : ¬ 3 ∣ Nat.card (Subgroup.center (StatedSp 4 K)) := by
      rw [CFSG.LieType.Universal.Symplectic.center_eq,
        show (StatedScalars (Fin 4 ⊕ Fin 4) K).subgroupOf (StatedSp 4 K) =
          CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spScalars 4 K from rfl,
        CFSG.LocalAnalysis.ComponentInitial.card_spScalars_eq_gcd K (by norm_num)]
      intro hd
      have h2' := (Nat.dvd_prime Nat.prime_two).1 (hd.trans (Nat.gcd_dvd_left 2 _))
      omega
    have hΨcop : ¬ 3 ∣ Nat.card Ψ.ker := fun hd =>
      hcen (hd.trans (Subgroup.card_dvd_of_le hker))
    have hπcop : ¬ 3 ∣ Nat.card (proj 4 K).ker := fun hd =>
      hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes (coprime_card_ker_proj (by norm_num) hp hp2) hd
        (dvd_refl 3))
    rw [← hrange]
    exact range_le_hyperClosure_of_cover hp (proj 4 K)
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.proj_surjective (r := 4) (K := K))
      ker_proj_le_center hπcop
      (fun E' hE' hE'c => hyperGen_statedProj_sp hp hp2 (natCast_ne_zero_of_not_dvd_card hp hpK)
        (by norm_num) (by omega) E' hE' hE'c)
      Ψ hΨcop (hrange ▸ hE) hEa hEc
  · have hℓ2 : ringChar K ≠ 2 := by
      intro h
      apply h2
      have : CharP K 2 := h ▸ ringChar.charP K
      exact CharTwo.two_eq_zero
    obtain ⟨Ψ, hΨker, hΨrange, -, -⟩ := exists_psi_B4_F4_frame hℓ hℓ2 hK h2
    have hn3 : 3 ≤ 4 := by norm_num
    have : Nonempty (Fin 4 ⊕ Fin 4 ⊕ Unit) := ⟨Sum.inr (Sum.inr ())⟩
    have : Finite (spinGroup (quadOdd 4 K)) :=
      CFSG.ClassicalInvolution.ModelFacts.finite_spinGroup_of_ker _
        (coe_ker_spinMatrix_quadOdd h2)
    obtain ⟨hπsurj, hcomap, hZ⟩ := spinToStatedProj_quadOdd (n := 4) h2 hn3
    set π := spinToStatedProj (quadOdd 4 K) (range_spinMatrix_quadOdd h2 hn3) with hπdef
    have hcen : ¬ 3 ∣ Nat.card (Subgroup.center (spinGroup (quadOdd 4 K))) :=
      not_dvd_card_center_spin_of_not_dvd_pred (quadOdd 4 K) (range_spinMatrix_quadOdd h2 hn3)
        hZ hcomap
        (fun x hx => spin_mul_self_eq_one ((mem_ker_spinMatrix_quadOdd_iff h2 x).mp hx)) hp2
        hpq1
    have hπcop : ¬ 3 ∣ Nat.card π.ker := by
      rw [hZ]
      exact hcen
    have hΨcop : ¬ 3 ∣ Nat.card Ψ.ker := fun hd =>
      hcen (hd.trans (Subgroup.card_dvd_of_le hΨker))
    rw [← hΨrange]
    exact range_le_hyperClosure_of_cover hp π hπsurj hZ.le hπcop (hodd h2) Ψ hΨcop
      (hΨrange ▸ hE) hEa hEc

theorem card_ne_two_of_not_p1ThreeLieList_F4 {q : PrimePower} {hv : (LieTypeIndex.F4 q).Valid}
    (h : ¬ P1ThreeLieList 3 ⟨.F4 q, hv⟩) : q.card ≠ 2 := by
  intro h2
  apply h
  have hpe : q.p ^ q.exponent = 2 := by rw [← PrimePower.card_def, h2]
  have hp2 : q.p = 2 := (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1
    (hpe ▸ dvd_pow_self _ q.exponent_pos.ne')
  have he1 : q.exponent = 1 := by
    rw [hp2] at hpe
    have : (2 : ℕ) ^ q.exponent = 2 ^ 1 := by rw [hpe, pow_one]
    exact Nat.pow_right_injective le_rfl this
  unfold P1ThreeLieList
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, q, hp2, he1, ?_⟩))))
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))

theorem hyperGen_F4_of_neg_datum {K : Type} [Field K] [Finite K] (hK : Nat.card K % 3 = 2)
    (hs : ThreeScope LieTypeIndex.F4 K) {E₀ : Subgroup (adjointGroup .F4 K)}
    (hE₀ : IsElemAbelian 3 E₀) (hc : Nat.card E₀ = 3 ^ 3) (D : LangPlaneData .F4 K E₀)
    (hw : ∀ u : Fin Tag.F4.rank → ℤ, D.w • u = -u) : HyperGen 3 ⊤ E₀ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨q, hv, hKq, -, hlist⟩ := hs
  have hK2 : Nat.card K ≠ 2 := by
    rw [hKq]
    exact card_ne_two_of_not_p1ThreeLieList_F4 hlist
  have hpK : ¬ 3 ∣ Nat.card K := by omega
  have hodd : (2 : K) ≠ 0 → ∀ E : Subgroup (StatedProj (StatedOmega (StatedQuadOdd 4 K))),
      IsElemAbelian 3 E → Nat.card E = 3 ^ 3 → HyperGen 3 ⊤ E := by
    intro h2 E hE hEc
    have hq2 : q.p ≠ 2 := by
      intro h
      apply h2
      have hd : 2 ∣ Nat.card K := by
        rw [hKq, PrimePower.card_def, h]
        exact dvd_pow_self _ q.exponent_pos.ne'
      have : Fintype K := Fintype.ofFinite K
      obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
      have hc2 : ringChar K = 2 := by
        rw [Nat.card_eq_fintype_card, hn] at hd
        exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hℓ).1
          (Nat.prime_two.dvd_of_dvd_pow hd)).symm
      have : CharP K 2 := ringChar.of_eq hc2
      exact CharTwo.two_eq_zero
    exact oddModel_cubes_three hKq hq2 hpK E hE hEc
  exact hyperGen_of_two_conj (⨆ k, b4Chain K k) (f4FrameGroup K)
    (CFSG.LieType.Chevalley.weylElement .F4 K (f4Node 3)) f4FrameGroup_le_b4
    f4FrameGroup_le_conj_b4 (fun M hX hn => eq_top_of_b4Chain_le_of_conj_le M hX hn)
    (fun E hE hEa hEc => iSup_b4Chain_le_hyperClosure_three hK hK2 hodd E hE hEa hEc)
    hE₀ hc (f4_exists_conj_le_frame_of_neg hE₀.2 D hw)

end B4

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest5

end
