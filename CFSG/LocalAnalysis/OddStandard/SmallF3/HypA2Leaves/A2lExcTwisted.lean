module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lRowBlock
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lRows
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieModel
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCover
public import CFSG.LieType.HighestRoot.CentTwistedE6Main
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvShape

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.Blueprint CFSG.ComponentClassification
open CFSG.ClassicalInvolution.Generic (modelUniv IsFundTag IsLongestRoot)
open CFSG.ComponentClassification.RankTwoOddLie (centralInv centralInv_mem
  centralInv_mem_centralizer centralInv_sq centralInv_ne_one nonempty_rankOne_equiv)
open CFSG.GH74.GLS.IVK.GHInv (isQuasisimple_sl2)
open CFSG.OddStandard.SmallF3.HypA2 (TypU)
open scoped MatrixGroups

section Cover

variable {K X : Type} [Group K] [Group X] {F : Type} [Field F] [Finite F]

theorem a2l_datum_of_cover [Finite K] (ψ : K →* X) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ center K) {R : Subgroup K} (eR : R ≃* SL(2, F))
    (hodd : Odd (Nat.card F)) (h9 : 9 ≤ Nat.card F)
    (hCZ : centralizer ({centralInv eR} : Set K) ≤ normalizer (R : Set K))
    (hinj : ∀ x ∈ R, ψ x = 1 → x = 1) : a2lDatum X := by
  have hz2 : centralInv eR * centralInv eR = 1 := by
    have := centralInv_sq eR
    rwa [pow_two] at this
  have hz1 : centralInv eR ≠ 1 := centralInv_ne_one eR hodd
  have hzR : centralInv eR ∈ R := centralInv_mem eR
  have hRc : R ≤ centralizer ({centralInv eR} : Set K) := by
    intro x hx
    rw [mem_centralizer_singleton_iff]
    exact (mem_centralizer_iff.1 (centralInv_mem_centralizer eR)) x hx
  have hRn : ∀ g ∈ centralizer ({centralInv eR} : Set K), ∀ x ∈ R, g * x * g⁻¹ ∈ R :=
    fun g hg x hx => (mem_normalizer_iff.1 (hCZ hg) x).1 hx
  have hq : CFSG.IsQuasisimple ↥R :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eR.symm (isQuasisimple_sl2 (by omega))
  have hN : HarrisLit.IsSLTwoOver (Nat.card F) ↥R := by
    haveI := Fintype.ofFinite F
    exact ⟨F, inferInstance, inferInstance, Nat.card_eq_fintype_card.symm, ⟨eR⟩⟩
  refine a2lDatum_of_block_normal ψ hψ hker hodd (by omega) hz2 ?_ (J := R) (N := R) le_rfl hzR
    hRc hRn hq hinj hN (a2l_typU_of_isSLTwoOver hodd h9 hN)
  intro h
  exact hz1 (hinj _ hzR h)

end Cover

section Model


theorem a2l_exists_cover {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n r e : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hFT : IsFundTag t) (hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n r e)
    {X : Type} [Group X] (hX : LieModel X t n r e) :
    ∃ ψ : (modelUniv t n r e hr).K →* X,
      Function.Surjective ψ ∧ ψ.ker ≤ center (modelUniv t n r e hr).K := by
  obtain ⟨-, hY⟩ := CFSG.ClassicalInvolution.ModelFacts.modelClauseZero t n r e hr hFT hadm
  obtain ⟨E⟩ := CFSG.ClassicalInvolution.Upgrade.lieModel_unique hr2 hFT hX hY
  refine ⟨E.symm.toMonoidHom.comp (QuotientGroup.mk' _), ?_, fun k hk => ?_⟩
  · exact E.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  · have h1 : E.symm (QuotientGroup.mk' (center (modelUniv t n r e hr).K) k) = 1 := hk
    rw [map_eq_one_iff _ E.symm.injective] at h1
    exact (QuotientGroup.eq_one_iff k).1 h1


theorem a2l_twistedE6_datum {X : Type} [Group X] {f : ℕ} (hf : 2 ≤ f)
    (hX : LieModel X .twistedE6 0 3 f) : a2lDatum X := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hadm := hX.admissible
  have hFT : IsFundTag .twistedE6 := trivial
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hf0 : f ≠ 0 := by omega
  obtain ⟨ψ, hψ, hker⟩ := a2l_exists_cover Nat.prime_three hp2 hFT hadm hX
  haveI : Finite (modelUniv .twistedE6 0 3 f Nat.prime_three).K :=
    CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv hp2 Nat.prime_three hFT hadm
  have hq3 : 3 ^ f ≠ 3 := fun h => by
    have := Nat.pow_right_injective (by norm_num : 2 ≤ 3) (h.trans (pow_one 3).symm)
    omega
  obtain ⟨γ, hγR, hγl, hCC⟩ := CFSG.LieType.HighestRoot.highestRootCZ_modelUniv_twistedE6 3 f 0
    hp2 (by omega) fun h => absurd h hq3
  have hγ : IsLongestRoot (modelUniv .twistedE6 0 3 f Nat.prime_three).D γ := ⟨hγR, hγl⟩
  obtain ⟨eR⟩ := nonempty_rankOne_equiv hp2 hFT hadm hγ
  have hcard : Nat.card (GaloisField 3 f) = 3 ^ f := GaloisField.card 3 f hf0
  haveI : Finite (GaloisField 3 f) := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  have hodd : Odd (Nat.card (GaloisField 3 f)) := by
    rw [hcard]
    exact (by decide : Odd 3).pow
  have h9 : 9 ≤ Nat.card (GaloisField 3 f) := by
    rw [hcard]
    calc (9 : ℕ) = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hz2 : orderOf (centralInv eR) = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (centralInv_sq eR) (centralInv_ne_one eR hodd)
  refine a2l_datum_of_cover ψ hψ hker eR hodd h9 (hCC _ (centralInv_mem eR) hz2).1
    fun x hx hx1 => ?_
  have hxc : x ∈ center (modelUniv .twistedE6 0 3 f Nat.prime_three).K :=
    hker (MonoidHom.mem_ker.2 hx1)
  refine CFSG.ClassicalInvolution.ModelFacts.fundNoncentral_generic 3 .twistedE6 0 f hFT hadm
    (by rintro ⟨h, -⟩; cases h) _
    ⟨1, γ, Or.inl hγ, (CFSG.ClassicalInvolution.ModelFacts.map_conj_one _).symm⟩ x hx fun y => ?_
  rw [← Subgroup.mem_center_iff.mp hxc y, mul_inv_cancel_right, mul_inv_cancel]
  exact one_mem _

end Model

@[expose] def a2lTwistedE6Three : Prop :=
  ∀ (X : Type) [Group X] [Finite X], LieModel X .twistedE6 0 3 1 → a2lDatum X

section Rows


theorem a2lRowTwistedE6_of_three (h3 : a2lTwistedE6Three) : a2lRowTwistedE6 := by
  intro X _ _ f hX
  have hf : 1 ≤ f := hX.admissible.2.1
  rcases Nat.lt_or_ge f 2 with hlt | hge
  · obtain rfl : f = 1 := by omega
    exact h3 X hX
  · exact a2l_twistedE6_datum hge hX

end Rows

end CFSG.OddStandard.SmallF3.HypA2Leaves
