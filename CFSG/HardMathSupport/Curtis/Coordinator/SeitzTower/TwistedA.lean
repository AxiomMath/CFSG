module

public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.UnitaryTower
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.UnitaryCover
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.UnitaryBlocks
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieOffCharNonNormalLinear

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower

open CFSG.AGLEmbedding CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LieType.SeitzGeneration CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem exists_primeFormP_mulEquiv_of_statedModel {G : Type} [Group G] {N ℓ f : ℕ}
    (h : StatedClassicalModel G .PSU N ℓ f) :
    ∃ (K : Type) (_ : Field K) (hU : UnitaryFieldData ℓ f K),
      Nonempty (G ≃* StatedProj (StatedSU N (ℓ ^ f) K)) ∧
      Nonempty (G ≃* primeFormP hU ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) := by
  obtain ⟨⟨hℓ, hm, hn3, hne⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hU : UnitaryFieldData ℓ f K := ⟨hℓ, hm, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq : ¬(N = 3 ∧ ℓ ^ f = 2) := fun ⟨h1, h2⟩ => hne (by rw [h1, h2])
  obtain ⟨⟨eT⟩, -⟩ := unitary_prime_form_full_semilinear_realization hU
    (isPrimeFormGram_one (n := N)) hn3 hq
  exact ⟨K, inferInstance, hU, ⟨e⟩,
    ⟨(e.trans (unitaryPSUEquiv hU (by omega)).symm).trans eT.symm⟩⟩

theorem p1OffCharAlmostSimpleNonNormalAt_twistedA {n : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA n q).Valid) :
    P1OffCharAlmostSimpleNonNormalAt ⟨.twistedA n q, hv⟩ := by
  refine p1OffCharAlmostSimpleNonNormalAt_of_towerOrCover fun p _ hp2 hpd hno => ?_
  have hp : p.Prime := Fact.out
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hpℓ : p ≠ q.p := by simpa using hpd
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hmodel := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA n q hv (MulEquiv.refl _)
  have hn2 : 2 ≤ n := by
    have := hmodel.1.2.2.1
    omega
  have hq : ¬ (n + 1 = 3 ∧ q.p ^ q.exponent = 2) := fun h => hmodel.1.2.2.2 (by rw [h.1, h.2])
  obtain ⟨K, _, hU, ⟨e₀⟩, ⟨e⟩⟩ := exists_primeFormP_mulEquiv_of_statedModel hmodel
  have : Finite K := hU.finite
  have hcube : HasThreeIndep (StatedProj (StatedSU (n + 1) (q.p ^ q.exponent) K)) p → False :=
    fun h => hno (exists_isElemAbelian_card_of_not_rankLE2 hp (not_rankLE2_of_mulEquiv e₀ hp h)).2
  have hgcd0 : 0 < Nat.gcd (n + 1) (q.p ^ q.exponent + 1) := Nat.gcd_pos_of_pos_left _ (by omega)
  have hgcdle : Nat.gcd (n + 1) (q.p ^ q.exponent + 1) ≤ n + 1 := Nat.gcd_le_left _ (by omega)
  have htower : ¬ p ∣ Nat.totient (Nat.gcd (n + 1) (q.p ^ q.exponent + 1)) →
      OutTowerAt (TauCeti.CFSGIndex.lie ⟨.twistedA n q, hv⟩).Group p ∨
        DetCoverAt (TauCeti.CFSGIndex.lie ⟨.twistedA n q, hv⟩).Group p :=
    fun h => Or.inl (OutTowerAt.of_mulEquiv e (outTowerAt_primeFormP hU (by omega) hq hp h))
  by_cases hqn : (-((q.p : ZMod p) ^ q.exponent)) ^ (n + 1) = 1
  · by_cases hq1 : p ∣ q.p ^ q.exponent + 1
    · by_cases hn4 : 4 ≤ n
      · exact absurd (hasThreeIndep_psu hU (by omega) hp hq1) hcube
      · exact htower (not_dvd_totient_of_lt hp hp2 hgcd0 (by omega))
    · set e' := Nat.gcd (n + 1) (p - 1) with he'
      have he1 : 1 ≤ e' := Nat.gcd_pos_of_pos_left _ (by omega)
      have hep : e' ≤ p - 1 := Nat.gcd_le_right _ (by omega)
      have hen : e' ∣ n + 1 := Nat.gcd_dvd_left _ _
      by_cases h3e : 3 * e' ≤ n + 1
      · exfalso
        apply hcube
        have hz : (-((q.p : ZMod p) ^ q.exponent)) ≠ 0 :=
          neg_ne_zero.mpr (CFSG.RankThree.PartOne.KCUnitaryPlane.natCast_pow_ne_zero hp hpℓ
            q.prime_p)
        have h2 : (-((q.p : ZMod p) ^ q.exponent)) ^ (p - 1) = 1 :=
          ZMod.pow_card_sub_one_eq_one hz
        have h3 : (-((q.p : ZMod p) ^ q.exponent)) ^ e' = 1 := pow_gcd_eq_one.2 ⟨hqn, h2⟩
        let σ : (Fin e' × Fin 3) ⊕ Fin (n + 1 - 3 * e') ≃ Fin (n + 1) :=
          (Equiv.sumCongr finProdFinEquiv (Equiv.refl _)).trans
            (finSumFinEquiv.trans (finCongr (by omega)))
        exact hasThreeIndep_psu_blocks hU σ he1 hp h3 hq1
      · have hn2e : n + 1 ≤ 2 * e' := by
          obtain ⟨t, ht⟩ := hen
          have ht2 : t ≤ 2 := by
            by_contra h
            push Not at h
            have : 3 * e' ≤ e' * t := by nlinarith
            omega
          rw [ht]
          nlinarith
        exact htower (not_dvd_totient_of_lt hp hp2 hgcd0 (by omega))
  · right
    exact (detCoverAt_primeFormP hU (by omega) hq hpℓ hqn).of_mulEquiv e

end CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower
