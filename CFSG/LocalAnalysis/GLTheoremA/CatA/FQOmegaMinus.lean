module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQOmega
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPOmegaEven
public import CFSG.LocalAnalysis.StandardType.MarkingClassical
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcLevi
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotFieldNormalizeAutMain
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotBLiftAniso
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatCovers
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotGlobalClass
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotLeviFactFour
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualFRHigher
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualLeviGlue
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotUniqueGen
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
public import CFSG.Quasithin.Background.G11Stmts
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescent
public import CFSG.RankThree.PartOne.KC.SymplecticOrthogonalNoninner
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace FQ

open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.FP
  CFSG.LocalAnalysis.GLTheoremA.YS09Field CFSG.Assembly CFSG.Open
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCOrthogonalDescent
  CFSG.RankThree.PartOne.KCOrthogonalNoninner CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.RankThree.PartOne.KCOrthogonalAut CFSG.RankThree.Classical.SteinbergBY
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
  CFSG.HardMathSupport.Lang.Coordinator CFSG.HardMathSupport.Lang.UnitaryAutomorphisms
  CFSG.HardMathSupport.Lang
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

section Fixed

variable {K : Type} [Field K] [Finite K] [CharP K 2] (k : Subfield K) {n : ℕ}
  {Q₀ : QuadraticForm k (Fin (2 * n) → k)}

theorem card_subfieldFixedGroup_eq_model {Q : QuadraticForm K (Fin (2 * n) → K)}
    (hext : IsExtension k Q₀ Q) (hnd₀ : (QuadraticMap.polarBilin Q₀).Nondegenerate)
    (hT₀ : ∃ U : Submodule k (Fin (2 * n) → k), Module.finrank k U = 3 ∧ ∀ u ∈ U, Q₀ u = 0)
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate) :
    Nat.card (subfieldFixedGroup k Q₀ Q) = Nat.card (matrixProjectiveDerived Q₀) := by
  have hd : 0 < 2 * n := three_le_of_totallySingular k hT₀
  have hle := CFSG.RankThree.PartOne.FieldFix.subfieldFixedGroup_le_derivedImage hext hnd₀ hT₀ hnd
  have heq : subfieldFixedGroup k Q₀ Q = subfieldDerivedImage k hext :=
    le_antisymm hle (subfieldDerivedImage_le k hext)
  rw [heq]
  exact Nat.card_congr (MonoidHom.ofInjective (incl_injective k hext hd)).toEquiv.symm

end Fixed

theorem omegaMinus_card_fixedSubgroup {G : Type} [Group G] [Finite G] {n f : ℕ}
    (hcl : StatedClassicalModel G .POmegaMinus n 2 f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (α : MulAut G) (hαp : α ^ p = 1) (hαin : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner G) :
    ∃ f₀ : ℕ, f = p * f₀ ∧
      Nat.card (fixedSubgroup α) = lieOrderNumerator .POmegaMinus n (2 ^ f₀) := by
  have hcl' := hcl
  obtain ⟨⟨hℓ, hf, hn4⟩, F, _, _, hF, b, c, hirr, ⟨e⟩⟩ := hcl
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hchar, -⟩ := coordinate_model_witness_minus hcl' F hF b c hirr e
  have : Fact p.Prime := ⟨hp⟩
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaMinus
    (Or.inr (Or.inr rfl)) n 2 f hcl' hn1 F hF b c hirr e
  set θ := coordinateMinusWitnessEquiv F hn1 b c e with hθ
  set Q := coordinateQuadMinus n F hn1 b c with hQ
  set β := MulAut.congr θ α with hβdef
  have hβp : β ^ p = 1 := by rw [hβdef, ← map_pow, hαp, map_one]
  have hβout : β ∉ OuterAutomorphisms.inner (matrixProjectiveDerived Q) :=
    fun hin => hαin ((congr_mem_inner_iff θ α).mp hin)
  have hβ1 : β ≠ 1 := fun h1 => hβout (h1 ▸ (OuterAutomorphisms.inner _).one_mem)
  have hβord : orderOf β = p := orderOf_eq_prime hβp hβ1
  rw [← card_fixedSubgroup_congr θ α]
  change ∃ f₀ : ℕ, f = p * f₀ ∧ Nat.card (fixedSubgroup β) = lieOrderNumerator .POmegaMinus n (2 ^ f₀)
  have hE : β ∈ matrixProjectiveImage Q := by
    rw [matrixProjectiveImage_eq_top_minus F n hn4 b c hirr]
    exact Subgroup.mem_top _
  have hD : β ∉ (linearConjugationHom Q).range := by
    intro hD
    obtain ⟨hHD, k, hk⟩ := hgates.2.2.1
    exact hβout (mem_of_pow_eq_one_of_relIndex_eq_two_pow hk hp hp2 hD hβp)
  have hdesc := Proving.orthogonal_prime_semilinear_actual_fixed_form_descent' G .POmegaMinus
    (Or.inr (Or.inr rfl)) n 2 f p hcl' hp hp2 hn1 F hF b c hirr e β hE hD hβord
  obtain ⟨g, hg⟩ := hE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord, hcard, U, cc, Q₀, hUκ, hUr, hFFD, hDisp⟩ := hrest g.val.right ⟨g, hg, rfl⟩
  obtain ⟨b', c', hirr', ν, S₀, -, hCM, hT⟩ := hDisp
  obtain ⟨S, ν', -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT
  have hord' : orderOf U.val.right = p := by rw [hUr]; exact hord
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = 2 ^ (f / p) := by
    rw [hUr]; exact hcard
  have hfp : 1 ≤ f / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) hp.pos
  have hdeg : Module.finrank (semilinearFixedSubfield U.val.right) F = p := by
    have hK' : Nat.card F = 2 ^ ((f / p) * p) := by rw [Nat.div_mul_cancel hpf]; exact hF
    exact finrank_subfield_eq _ hℓ hfp hcard' hK'
  have hsetup := subfieldSetup_minus (semilinearFixedSubfield U.val.right)
    (σ := U.val.right) (fun x => Iff.rfl) hp hp2 hord' hn4 hdeg b' c' hirr'
  have hΘ' : ∀ x, Θ (β x) = matrixProjectiveConjugationHom _ g' (Θ x) := fun x => by
    rw [← hUκ]; exact hΘ x
  have hfix := card_fixedSubgroup_eq_subfieldFixedGroup hsetup Θ g' hg'l hg'r hΘ'
  refine ⟨f / p, (Nat.mul_div_cancel' hpf).symm, ?_⟩
  rw [hfix, ← hcard']
  haveI : CharP F 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hF
  rw [card_subfieldFixedGroup_eq_model _ hsetup.hext hsetup.hnd₀ hsetup.hT₀ hsetup.hnd]
  exact card_model_minus_eq _ n hn4 hirr'


section Order

open CFSG.StandardType (omegaMinusProjEquiv statedClassicalModel_omegaMinus)

theorem twoPart_lieOrderNumerator_omegaMinus {l e : ℕ} (hl : 1 ≤ l) (he : 1 ≤ e) :
    twoPart (lieOrderNumerator .POmegaMinus l (2 ^ e)) = 2 ^ (e * (l * (l - 1))) := by
  have hq : Even (2 ^ e) := (Nat.even_pow' (by omega)).mpr even_two
  have hodd1 : Odd ((2 ^ e) ^ l + 1) :=
    ((Nat.even_pow' (by omega)).mpr hq).add_one
  have hodd2 : Odd (∏ i ∈ Finset.Icc 1 (l - 1), ((2 ^ e) ^ (2 * i) - 1)) :=
    CFSG.SeitzReduction.OmegaPilot.odd_prod_pow_sub_one hq Nat.one_le_two_pow _
      (fun i => 2 * i) fun i hi => by
        simp only [Finset.mem_Icc] at hi
        omega
  have h : lieOrderNumerator .POmegaMinus l (2 ^ e) = 2 ^ (e * (l * (l - 1))) *
      (((2 ^ e) ^ l + 1) * ∏ i ∈ Finset.Icc 1 (l - 1), ((2 ^ e) ^ (2 * i) - 1)) := by
    simp only [lieOrderNumerator]
    rw [← pow_mul, mul_assoc]
  rw [h, twoPart_two_pow_mul_odd (hodd1.mul hodd2)]

theorem card_omegaMinus_proj {K : Type} [Field K] [Finite K] [CharP K 2] {l : ℕ} (hl : 4 ≤ l)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nat.card (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (l - 1) b c))) =
      lieOrderNumerator .POmegaMinus l (Nat.card K) := by
  rw [Nat.card_congr (CFSG.StandardType.omegaMinusProjEquiv l b c).toEquiv]
  have h3 := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega_quadMinus (K := K)
    (n := l) hl hirr
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  have h4 : ((∏ i ∈ Finset.Icc 1 (l - 1), (Nat.card K ^ (2 * i) - 1) : ℕ) : ℤ) =
      ∏ i ∈ Finset.Icc 1 (l - 1), ((Nat.card K : ℤ) ^ (2 * i) - 1) := by
    push_cast
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Nat.cast_sub (Nat.one_le_pow _ _ hq)]
    push_cast
    rfl
  apply Nat.cast_injective (R := ℤ)
  rw [h3]
  simp only [lieOrderNumerator]
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, h4]
  push_cast
  ring

theorem stOrderBody_omegaMinus {l n : ℕ} (hl : 4 ≤ l) (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (I F : Set (MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (l - 1) b c)))))
    (hF : InnFree p F) :
    StOrderBody p (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (l - 1) b c))) I F := by
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  intro f hf hord
  have hcl := statedClassicalModel_omegaMinus l n hK b c hirr ⟨Nat.prime_two, hn, hl⟩
  haveI : Finite (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (l - 1) b c))) :=
    Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  have hαp : f ^ p = 1 := hord ▸ pow_orderOf_eq_one f
  obtain ⟨f₀, hf0, hfix⟩ := omegaMinus_card_fixedSubgroup hcl hp hp2 f hαp
    (fun h => hF f hf hord h)
  have hf1 : 1 ≤ f₀ := by
    rcases Nat.eq_zero_or_pos f₀ with h0 | h0
    · rw [h0, mul_zero] at hf0; omega
    · exact h0
  have h1 : fixNum f = lieOrderNumerator .POmegaMinus l (2 ^ f₀) := by
    rw [fixNum_eq_card_fixSub]
    exact hfix
  rw [h1, card_omegaMinus_proj hl hirr, hK,
    twoPart_lieOrderNumerator_omegaMinus (by omega) hf1,
    twoPart_lieOrderNumerator_omegaMinus (by omega) hn, ← pow_mul]
  congr 1
  rw [hf0]
  ring

end Order

end FQ

end CFSG.LocalAnalysis.GLTheoremA
