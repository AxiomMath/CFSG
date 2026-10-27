module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3Field
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3FieldU
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryTransport
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3Iso
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.LieType.Steinberg.CentralExt.PSUMultiplier
import CFSG.LieType.Steinberg.CentralExt.SUOddClosed
import CFSG.LieType.Steinberg.CentralExt.UnitaryPerfect
import CFSG.LocalAnalysis.SteinbergBNUnitaryThreeOuterInvolutionRigidity
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAUGen
import CFSG.RankThree.SteinbergR3EUnitaryFieldDescent
import CFSG.GroupTheory.WeirSylow.CrossRankUnitary
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.Foundations
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.LocalAnalysis.GLTheoremA.P55.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.Pump
public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsProp65
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.TopScalarLiftSquare
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import Certificates.Certificate43
import CFSG.GH74.GLS.IVK.Proofs2.OddTools
import CFSG.GH74.GLS.Stage2.Local.P34Main
import CFSG.GH74.GLS.Stage2.Local.P34S5A
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL4
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL4Cases
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL4Kill
import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUGraphCore
import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUGraphDescent
import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUInnerPaired
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedGraphSymm

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.P3

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

section PrimeForm

variable {p f : ℕ} {K : Type} [Field K] [Finite K] (h : UnitaryFieldData p f K) {N : ℕ}

theorem mem_inner_of_mem_primeFormD {C : GL (Fin N) K} (h3 : ¬ 3 ∣ p ^ f + 1)
    {α : MulAut (primeFormP h (C : Matrix (Fin N) (Fin N) K))}
    (hα : α ∈ primeFormD h (C : Matrix (Fin N) (Fin N) K)) (hα3 : α ^ 3 = 1) :
    α ∈ (MulAut.conj : primeFormP h (C : Matrix (Fin N) (Fin N) K) →*
      MulAut (primeFormP h (C : Matrix (Fin N) (Fin N) K))).range := by
  set D := primeFormD h (C : Matrix (Fin N) (Fin N) K)
  set y : D ⧸ (inner (primeFormP h (C : Matrix (Fin N) (Fin N) K))).subgroupOf D :=
    QuotientGroup.mk ⟨α, hα⟩ with hy
  have hy3 : y ^ 3 = 1 := by
    rw [hy, ← QuotientGroup.mk_pow,
      show (⟨α, hα⟩ : D) ^ 3 = 1 from Subtype.ext (by rw [Subgroup.coe_pow]; exact hα3),
      QuotientGroup.mk_one]
  have h2 : orderOf y ∣ p ^ f + 1 :=
    (orderOf_dvd_natCard y).trans (card_primeFormD_quotient_dvd h C)
  have hy1 : orderOf y = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hy3) with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ h2) h3
  rw [orderOf_eq_one_iff, hy, QuotientGroup.eq_one_iff] at hy1
  exact Subgroup.mem_subgroupOf.mp hy1

theorem exists_modelB_primeFormP (hN : N = 4 ∨ N = 5) (hp3 : p ≠ 3) (h3 : ¬ 3 ∣ p ^ f + 1)
    (hfield : ∀ σ : K ≃+* K, orderOf σ = 3 →
      ModelB (primeFormP h ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K))
        (primeFormFieldHom h isPrimeFormGram_one σ))
    (β : MulAut (primeFormP h ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)))
    (hβ3 : β ^ 3 = 1)
    (hβ : β ∉ (MulAut.conj : primeFormP h ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) →*
      MulAut (primeFormP h ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K))).range) :
    ∃ (g : primeFormP h ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K))
      (ψ : MulAut (primeFormP h ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K))),
      β = MulAut.conj g * ψ ∧
        ModelB (primeFormP h ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) ψ := by
  have hN3 : 3 ≤ N := by omega
  have hq : ¬(N = 3 ∧ p ^ f = 2) := fun h' => by omega
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set φ := primeFormFieldFactor h isPrimeFormGram_one hN3 hq β with hφ
  have hφ3 : φ ^ 3 = 1 := by rw [hφ, ← map_pow, hβ3, map_one]
  have hφ1 : φ ≠ 1 := fun h1 => hβ (mem_inner_of_mem_primeFormD h h3
    (by rw [← ker_primeFormFieldFactor h isPrimeFormGram_one hN3 hq]; exact h1) hβ3)
  have hβ1 : β ≠ 1 := fun h1 => hβ ⟨1, by rw [h1, map_one]⟩
  obtain ⟨-, -, -, -, -, M, hM⟩ :=
    CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent h hN3 hq
      Nat.prime_three (by norm_num) (Ne.symm hp3) β (orderOf_eq_prime hβ3 hβ1) φ rfl
      (orderOf_eq_prime hφ3 hφ1)
  refine ⟨1, MulAut.congr (primeFormConjHom h _ M) (primeFormFieldHom h isPrimeFormGram_one φ),
    ?_, ModelB.congr _ (hfield φ (orderOf_eq_prime hφ3 hφ1))⟩
  rw [map_one, one_mul]
  calc β = primeFormConjHom h _ M * primeFormFieldHom h isPrimeFormGram_one φ *
        (primeFormConjHom h _ M)⁻¹ := by rw [← hM]; group
    _ = _ := MulEquiv.ext fun _ => rfl

private theorem nonempty_statedProj_equiv_primeFormP (hN : 1 ≤ N) :
    Nonempty (StatedProj (StatedSU N (p ^ f) K) ≃*
      primeFormP h ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) :=
  ⟨(CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv h hN).symm.trans
    (CFSG.LocalAnalysis.unitaryPSUEquivPrimeFormOne h N)⟩

theorem card_le_nine_primeFormP (hN : N = 4 ∨ N = 5) (h3 : 3 ∣ p ^ f - 1)
    (F : Subgroup (primeFormP h ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)))
    (hF : IsElemAbelian 3 F) : Nat.card F ≤ 3 ^ 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := nonempty_statedProj_equiv_primeFormP h (N := N) (by omega)
  have hr : CFSG.Open.pRank 3
      (⊤ : Subgroup (primeFormP h ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K))) ≤ 2 := by
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
    refine (CFSG.GroupTheory.WeirSylow.pRank_top_statedProj_statedSU_le_div_two ⟨1, rfl⟩
      (by rw [h.card, ← pow_mul, mul_comm]) (by omega) h3).trans ?_
    omega
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 hF.isPGroup
  rw [hj]
  exact Nat.pow_le_pow_right (by norm_num)
    ((CFSG.SectionRank.le_pRank (by norm_num) le_top hF hj).trans hr)

theorem center_primeFormP_eq_bot (hN : N = 4 ∨ N = 5) :
    Subgroup.center (primeFormP h ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) = ⊥ := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨e⟩ := nonempty_statedProj_equiv_primeFormP h (N := N) (by omega)
  rw [← Subgroup.map_center_eq e, CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.ka_center_bot_pu
    (by rw [h.card, ← pow_mul, mul_comm]) (by omega) (fun h' => by
      rw [Prod.mk.injEq] at h'
      omega), Subgroup.map_bot]

end PrimeForm

section Main

theorem P3Hyp.center_eq_bot_of_psu {q : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}
    (H : P3Hyp q S B) {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
    (hK : Nat.card K = (p ^ f) ^ 2) (hf : 1 ≤ f) (hq4 : 4 ≤ p ^ f) {N : ℕ} (hN : N = 4 ∨ N = 5)
    (h3 : ¬ 3 ∣ p ^ f + 1) (e : PSimple 3 S ≃* StatedProj (StatedSU N (p ^ f) K)) :
    Subgroup.center ↥S = ⊥ := by
  refine H.center_eq_bot_of_multiplier e ?_
  have hM : Nonempty (CFSG.Open.griessHopfMultiplier (StatedProj (StatedSU N (p ^ f) K)) ≃*
      Multiplicative (ZMod (Nat.gcd N (p ^ f + 1)))) := by
    rcases hN with rfl | rfl
    · exact (CFSG.LieType.Steinberg.CentralExt.SUClosed.psu_hopfMultiplier hK (by decide) le_rfl
        hq4).2
    · exact (CFSG.LieType.Steinberg.CentralExt.SUOdd.psu_odd_hopfMultiplier hK hf (by norm_num)
        (by decide) (by simp)).2
  obtain ⟨eM⟩ := hM
  rw [Nat.card_congr eM.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  exact fun hd => h3 (hd.trans (Nat.gcd_dvd_right _ _))

theorem p3At_twistedA_of_field
    (hfield : ∀ (K : Type) [Field K] [Finite K] (p f : ℕ)
      (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K), p ≠ 2 → p ≠ 3 →
      ∀ (n : ℕ), (n = 4 ∨ n = 5) → ∀ σ : K ≃+* K, orderOf σ = 3 →
        ModelB (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormP h
            ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
          (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormFieldHom h
            CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.isPrimeFormGram_one σ))
    {n : ℕ} (hn3 : 3 ≤ n) (hn4 : n ≤ 4) {Q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA n Q).Valid) (h3 : 3 ∣ Q.card - 1) : P3At ⟨_, hv⟩ := by
  rintro q Ω _ _ S B H hchar ⟨e⟩
  have hQq : Q.p = q := by
    change (TauCeti.LieTypeIndex.twistedA n Q).characteristic = q at hchar
    rwa [TauCeti.LieTypeIndex.characteristic_twistedA] at hchar
  obtain ⟨⟨hp, hf, -, -⟩, K, _, _, hK, ⟨e₁⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA n Q hv e
  haveI : Fact Q.p.Prime := ⟨hp⟩
  haveI : CharP K Q.p := CFSG.LieType.Steinberg.charP_of_card_eq_sq_pow hp hK
  have h : UnitaryFieldData Q.p Q.exponent K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hp2 : Q.p ≠ 2 := hQq ▸ H.two
  have hp3 : Q.p ≠ 3 := hQq ▸ H.three
  have h31 : 3 ∣ Q.p ^ Q.exponent - 1 := by rwa [TauCeti.PrimePower.card_def] at h3
  have hQ5 : 5 ≤ Q.p ^ Q.exponent :=
    (hp.five_le_of_ne_two_of_ne_three hp2 hp3).trans (Nat.le_self_pow Q.exponent_pos.ne' _)
  have h31' : ¬ 3 ∣ Q.p ^ Q.exponent + 1 := by omega
  have hN : n + 1 = 4 ∨ n + 1 = 5 := by omega
  have hZ : Subgroup.center ↥S = ⊥ := H.center_eq_bot_of_psu hK hf (by omega) hN h31' e₁
  obtain ⟨e₂⟩ := nonempty_statedProj_equiv_primeFormP h (N := n + 1) (by omega)
  obtain ⟨φ, hφ, hφS⟩ := exists_embedding_of_mulEquiv H hZ (e₂.symm.trans e₁.symm)
  exact Or.inl (concA_of_outer H hZ φ hφ hφS (center_primeFormP_eq_bot h hN)
    (card_le_nine_primeFormP h hN h31)
    (exists_modelB_primeFormP h hN hp3 h31' (hfield K Q.p Q.exponent h hp2 hp3 (n + 1) hN)))

theorem p3At_twistedA_of_dvd_sub_one {n : ℕ} (hn3 : 3 ≤ n) (hn4 : n ≤ 4) {Q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA n Q).Valid) (h3 : 3 ∣ Q.card - 1) : P3At ⟨_, hv⟩ :=
  p3At_twistedA_of_field (fun K _ _ p f h hp2 hp3 n hn σ hσ =>
    Field.modelB_primeFormP h hp2 hp3 hn hσ) hn3 hn4 hv h3

end Main

end CFSG.LocalAnalysis.GLTheoremA.S267.P3

end
