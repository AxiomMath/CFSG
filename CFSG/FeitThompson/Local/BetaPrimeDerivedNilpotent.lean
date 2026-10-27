module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.BetaCoreHallQuotient
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

open CFSG.FeitThompson Subgroup

universe u

variable {G : Type u} [Group G]

theorem isNilpotent_of_inf_eq_bot_of_isNilpotent_quotient {B K Y : Subgroup G}
    [hN : (B.subgroupOf K).Normal]
    (hnil : Group.IsNilpotent (↥K ⧸ B.subgroupOf K))
    (hYK : Y ≤ K) (hYB : Y ⊓ B = ⊥) : Group.IsNilpotent ↥Y := by
  have := hnil
  set φ : ↥Y →* (↥K ⧸ B.subgroupOf K) :=
    (QuotientGroup.mk' (B.subgroupOf K)).comp (Subgroup.inclusion hYK) with hφ
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
    have hxB : (x : G) ∈ B := by
      have hx' : Subgroup.inclusion hYK x ∈ B.subgroupOf K := by
        simpa [hφ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff] using hx
      simpa [Subgroup.mem_subgroupOf] using hx'
    have hmem : (x : G) ∈ Y ⊓ B := ⟨x.2, hxB⟩
    rw [hYB] at hmem
    exact Subtype.ext (by simpa using hmem)
  have : Group.IsNilpotent ↥φ.range := Subgroup.isNilpotent _
  exact Group.nilpotent_of_mulEquiv (MonoidHom.ofInjective hinj).symm

theorem inf_betaCore_eq_bot [Finite G] {M Y : Subgroup G}
    (hY : ∀ p ∈ (Nat.card Y).primeFactors, p ∉ betaPrimes ↥M) :
    Y ⊓ betaCore M = ⊥ := by
  refine disjoint_iff.1 (Subgroup.disjoint_of_coprime_natCard (Nat.coprime_of_dvd ?_))
  intro k hk hkY hkB
  refine hY k (Nat.mem_primeFactors.2 ⟨hk, hkY, Nat.card_pos.ne'⟩) ?_
  exact isPiSubgroup_iff.1 (isPiSubgroup_betaCore M) k
    (Nat.mem_primeFactors.2 ⟨hk, hkB, Nat.card_pos.ne'⟩)

theorem FTS_beta_prime_derived_nilpotent
    (h₁ : CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FTS_beta_prime_derived_nilpotent.{u} := by
  intro G _ _ hG M hM Y hYM' hYβ
  obtain ⟨-, -, -, -, -, hN, hnil⟩ := FTS_beta_core_hall_quotient h₁ h₂ G hG M hM
  have := hN
  exact isNilpotent_of_inf_eq_bot_of_isNilpotent_quotient hnil hYM' (inf_betaCore_eq_bot hYβ)

end

end CFSG.FeitThompson.Proofs
