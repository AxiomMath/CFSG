module

public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
import CFSG.FeitThompson.Local.OutsideSigmaDerivedCentralizerCyclic
import CFSG.FeitThompson.Local.TauOneDisplacementReflectedConfiguration
import CFSG.FeitThompson.Local.SinglePrimeOrbitFixedLine
import CFSG.FeitThompson.OddOrder.ComparisonWordFixedVector
import CFSG.FeitThompson.Local.FixedPointsNormalizedProductFixedFree
import CFSG.FeitThompson.Representations.SolvableFrobeniusKernelTICoherence
import CFSG.FeitThompson.Local.MixedFittingComplementCoreEquality
import CFSG.FeitThompson.Local.MixedFittingCentralizerConstrained
import CFSG.FeitThompson.Local.KappaPrimeLineFixedEquivalence
import CFSG.FeitThompson.Local.PrimeOrderFixedFreeKernelCoprime
import CFSG.FeitThompson.Representations.ChiefActionKernelNormalQuotientLayers
import CFSG.FeitThompson.Foundations.SolvableSubgroupSolvable
public import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
public import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
public import CFSG.FeitThompson.Foundations.HallImageQuotient
public import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
public import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions
public import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable
public import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
public import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
public import CFSG.FeitThompson.Representations.AlgebraicIntegersRing
public import CFSG.FeitThompson.Representations.NormalInducedSupportBasis
public import CFSG.FeitThompson.Representations.SchurLemmaIntertwiningMaps
public import Mathlib

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson CFSG.FeitThompson Subgroup

universe u

variable {G : Type u} [Group G] [Finite G]

theorem isPiSubgroup_compl_sigmaPrimes {M K : Subgroup G}
    (hK : ∀ s : ℕ, s.Prime → s ∣ Nat.card ↥K → s ∉ sigmaPrimes M) :
    IsPiSubgroup (sigmaPrimes M)ᶜ K :=
  isPiSubgroup_iff.2 fun s hs => by
    rw [Nat.mem_primeFactors] at hs
    exact hK s hs.1 hs.2.1

omit [Finite G] in
theorem inf_centralizer_sup_eq_bot {S K₀ P : Subgroup G}
    (hnormS : S ⊔ K₀ ≤ normalizer (S : Set G)) (hdisj : Disjoint S K₀)
    (hPS : P ≤ normalizer (S : Set G)) (hPK : P ≤ normalizer (K₀ : Set G))
    (hS : S ⊓ centralizer (P : Set G) = ⊥) (hK : K₀ ⊓ centralizer (P : Set G) = ⊥) :
    (S ⊔ K₀) ⊓ centralizer (P : Set G) = ⊥ := by
  have h := coe_sup_inf_centralizer_eq (H := S) (Q := K₀) (P := P)
    (Subgroup.normal_subgroupOf_of_le_normalizer hnormS) hdisj hPS hPK
  refine SetLike.coe_injective ?_
  rw [h, hS, hK]
  simp

theorem isNilpotent_of_inf_centralizer_eq_bot {V P : Subgroup G} [Group.IsSolvable ↥V]
    {p : ℕ} (hp : p.Prime) (hPcard : Nat.card ↥P = p)
    (hPV : P ≤ normalizer (V : Set G))
    (hVP : V ⊓ centralizer (P : Set G) = ⊥) :
    Group.IsNilpotent ↥V := by
  have hPbot : P ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hPcard
    exact hp.one_lt.ne hPcard
  refine SibleySolvableCoherence.isNilpotent_of_isSolvable (L := V ⊔ P) le_sup_left le_sup_right
    (sup_le le_normalizer hPV) rfl ?_ hPbot ?_
  ·
    have hPab : IsMulCommutative ↥P := by
      have := Fact.mk hp
      have : IsCyclic ↥P := isCyclic_of_prime_card hPcard
      infer_instance
    refine le_bot_iff.1 (le_trans (le_inf inf_le_left ?_) (le_of_eq hVP))
    exact inf_le_right.trans (Subgroup.le_centralizer P)
  · intro u hu hu1
    have hz : zpowers u = P := zpowers_eq_of_natCard_eq_prime hp hPcard hu hu1
    rw [← centralizer_coe_eq_of_zpowers_eq hz]
    exact hVP

theorem FTS_outside_sigma_fixed_free_line_commutator
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FPL_global_sylow_normalizer_derived.{u})
    (h₃ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FTS_outside_sigma_fixed_free_line_commutator.{u} := by
  intro G _ _ hG M K P p hM hp hpσ hKM hKab hKπ hpK hPN hPcard hSP
  obtain ⟨hPK, hPM⟩ := le_inf_iff.1 hPN
  set S : Subgroup G := sigmaCore M with hSdef
  set K₀ : Subgroup G := ⁅K, P⁆ with hK₀def
  have hsolvM : Group.IsSolvable ↥M := hG.isSolvable_of_ne_top M hM.1
  have hK₀K : K₀ ≤ K := commutator_le_left_of_le_normalizer hPK
  have hK₀M : K₀ ≤ M := hK₀K.trans hKM
  have hPK₀ : P ≤ normalizer ((K₀ : Subgroup G) : Set G) :=
    le_normalizer_commutator_of_le_normalizer hPK
  have hcopPK : (Nat.card ↥P).Coprime (Nat.card ↥K) := by
    rw [hPcard]; exact (Nat.Prime.coprime_iff_not_dvd hp).2 hpK
  have hK₀P : K₀ ⊓ centralizer ((P : Subgroup G) : Set G) = ⊥ :=
    inf_centralizer_commutator_eq_bot_of_coprime hPK hKab hcopPK
  have hcopSK₀ : (Nat.card ↥S).Coprime (Nat.card ↥K₀) :=
    coprime_natCard_of_isPiSubgroup disjoint_compl_right (isPiSubgroup_sigmaCore M)
      ((isPiSubgroup_compl_sigmaPrimes hKπ).of_le hK₀K)
  have hdisj : Disjoint S K₀ := Subgroup.disjoint_of_coprime_natCard hcopSK₀
  have hMS : M ≤ normalizer ((S : Subgroup G) : Set G) := le_normalizer_sigmaCore M
  have hSM : S ≤ M := sigmaCore_le M
  set V : Subgroup G := S ⊔ K₀ with hVdef
  have hVM : V ≤ M := sup_le hSM hK₀M
  have hVP : V ⊓ centralizer ((P : Subgroup G) : Set G) = ⊥ :=
    inf_centralizer_sup_eq_bot (hVM.trans hMS) hdisj (hPM.trans hMS) hPK₀ hSP hK₀P
  have hsolvV : Group.IsSolvable ↥V := isSolvable_of_le hVM
  have hPV : P ≤ normalizer ((V : Subgroup G) : Set G) :=
    le_normalizer_sup (hPM.trans hMS) hPK₀
  have hnil : Group.IsNilpotent ↥V := isNilpotent_of_inf_centralizer_eq_bot hp hPcard hPV hVP
  have hK₀S : K₀ ≤ centralizer ((S : Subgroup G) : Set G) :=
    le_centralizer_of_coprime_natCard_of_isNilpotent V hnil le_sup_right le_sup_left hcopSK₀.symm
  have hK₀M' : K₀ ≤ (⁅M, M⁆ : Subgroup G) := Subgroup.commutator_mono hKM hPM
  have hY : K₀ ⊓ centralizer ((S : Subgroup G) : Set G) ⊓ (⁅M, M⁆ : Subgroup G) = K₀ := by
    rw [inf_eq_left.2 hK₀S, inf_eq_left.2 hK₀M']
  have hcyc := FTS_outside_sigma_derived_centralizer_cyclic h₁ h₂ h₃ G hG M K₀ K₀ hM hK₀M
    (fun s hs hdvd => hKπ s hs (hdvd.trans (Subgroup.card_dvd_of_le hK₀K))) hY.symm
  exact ⟨hK₀S, hcyc.1, hcyc.2⟩

end

end CFSG.FeitThompson.Proofs
