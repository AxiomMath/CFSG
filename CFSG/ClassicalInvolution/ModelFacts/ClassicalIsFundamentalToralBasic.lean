module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthLift
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSplit
public import CFSG.ClassicalInvolution.Balance.SL2
public import CFSG.ClassicalInvolution.PerfectCase.Basic
public import CFSG.GroupTheory.ABGLocalTools.PStabilityQDickson
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.ClassicalInvolution.LBalance.Main
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalLift
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSplitProd
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearDescentFixedBasis
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.PrimeComplementQuotientComponents
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Open CFSG.ClassicalInvolution
open scoped MatrixGroups commutatorElement

theorem odd_and_five_le_card_galoisField {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) : Odd (Nat.card (GaloisField p f)) ∧ 5 ≤ Nat.card (GaloisField p f) := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  exact ⟨by rw [hcard]; exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow, by rw [hcard]; exact hq⟩

theorem eq_bot_of_normal_of_odd_sl2 {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (h4 : 4 ≤ Nat.card F) (N : Subgroup SL(2, F)) (hNn : N.Normal) (hN : Odd (Nat.card N)) :
    N = ⊥ := by
  have hq : CFSG.IsQuasisimple SL(2, F) :=
    native_isQuasisimple (isQuasisimple_specialLinearGroup_two h4)
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hq
    hNn.isSubnormal with h | h
  · exfalso
    have h2 : Even (Nat.card SL(2, F)) := by
      have : orderOf (-1 : SL(2, F)) ∣ Nat.card SL(2, F) := orderOf_dvd_natCard _
      rw [sl2_orderOf_neg_one hodd] at this
      exact even_iff_two_dvd.2 this
    rw [h, Subgroup.card_top] at hN
    exact (Nat.not_even_iff_odd.2 hN) h2
  · have hc : Nat.card (Subgroup.center SL(2, F)) = 2 := CFSG.ABGLocalTools.card_center_sl2 hodd
    have hle : Nat.card N ≤ Nat.card (Subgroup.center SL(2, F)) :=
      Nat.card_le_card_of_injective (Subgroup.inclusion h) (Subgroup.inclusion_injective h)
    rw [hc] at hle
    obtain ⟨k, hk⟩ := hN
    have : Nat.card N = 1 := by omega
    exact Subgroup.eq_bot_of_card_eq N this

theorem surjective_of_injective_of_isQuasisimple_of_equiv_sl2 {J : Type*} [Group J] [Finite J]
    {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F)) (h4 : 4 ≤ Nat.card F)
    (hJ : CFSG.IsQuasisimple J) (O : Subgroup J) [O.Normal] (hOodd : Odd (Nat.card O))
    (eJ : J ⧸ O ≃* SL(2, F)) (ι : SL(2, F) →* J) (hι : Function.Injective ι) :
    Function.Surjective ι := by
  let ρ : SL(2, F) →* J ⧸ O := (QuotientGroup.mk' O).comp ι
  have hρinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    refine eq_bot_of_normal_of_odd_sl2 hodd h4 ρ.ker (MonoidHom.normal_ker ρ) ?_
    have hmem : ∀ x : ρ.ker, ι x.1 ∈ O := fun x =>
      (QuotientGroup.eq_one_iff _).1 (MonoidHom.mem_ker.mp x.2)
    let ψ : ρ.ker →* O :=
      { toFun := fun x => ⟨ι x.1, hmem x⟩
        map_one' := Subtype.ext (map_one ι)
        map_mul' := fun x y => Subtype.ext (map_mul ι x.1 y.1) }
    have hψ : Function.Injective ψ := fun x y h => by
      have h' : ι x.1 = ι y.1 := by
        have := congrArg (fun u : O => (u : J)) h
        simpa [ψ] using this
      exact Subtype.ext (hι h')
    exact hOodd.of_dvd_nat (Subgroup.card_dvd_of_injective ψ hψ)
  have hcard : Nat.card (J ⧸ O) = Nat.card SL(2, F) := Nat.card_congr eJ.toEquiv
  have hρbij : Function.Bijective ρ :=
    hρinj.bijective_of_nat_card_le (by rw [hcard])
  have hOc : O ≤ Subgroup.center J := by
    rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hJ
      (Subgroup.Normal.isSubnormal inferInstance : O.IsSubnormal) with h | h
    · exfalso
      have h0 : Nat.card (J ⧸ O) = 1 := by rw [h]; simp
      rw [hcard] at h0
      have : Nontrivial SL(2, F) := ⟨⟨-1, 1, sl2_neg_one_ne_one hodd⟩⟩
      exact absurd h0 (Finite.one_lt_card (α := SL(2, F))).ne'
    · exact h
  have hJ' : ∀ y : J, ∃ x : SL(2, F), ∃ o ∈ O, y = ι x * o := by
    intro y
    obtain ⟨x, hx⟩ := hρbij.2 (QuotientGroup.mk y)
    refine ⟨x, (ι x)⁻¹ * y, ?_, by group⟩
    have : QuotientGroup.mk (ι x) = (QuotientGroup.mk y : J ⧸ O) := hx
    exact QuotientGroup.eq.1 this
  have hcomm : ∀ y₁ y₂ : J, ⁅y₁, y₂⁆ ∈ ι.range := by
    intro y₁ y₂
    obtain ⟨x₁, o₁, ho₁, rfl⟩ := hJ' y₁
    obtain ⟨x₂, o₂, ho₂, rfl⟩ := hJ' y₂
    rw [commutatorElement_mul_central (hOc ho₁) (hOc ho₂), ← map_commutatorElement ι x₁ x₂]
    exact ⟨_, rfl⟩
  have hperf : ⁅(⊤ : Subgroup J), (⊤ : Subgroup J)⁆ = (⊤ : Subgroup J) :=
    hJ.1.commutator_eq_top
  have hle : (⊤ : Subgroup J) ≤ ι.range := by
    have h1 : ⁅(⊤ : Subgroup J), (⊤ : Subgroup J)⁆ ≤ ι.range :=
      Subgroup.commutator_le.2 fun g₁ _ g₂ _ => hcomm g₁ g₂
    rwa [hperf] at h1
  intro y
  exact hle (Subgroup.mem_top y)

end CFSG.ClassicalInvolution.ModelFacts
