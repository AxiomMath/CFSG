module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.SigmaCoreConjugateTrivialExceptionalPlane
import CFSG.FeitThompson.Local.ExceptionalSylowAbelian
import CFSG.FeitThompson.Local.ExceptionalPlaneMaximalElementaryAbelian
import CFSG.FeitThompson.Local.HallCutoffPrimeTorsionNormal
import CFSG.FeitThompson.Local.SmallRankLineInMaximalPlane
import CFSG.FeitThompson.Local.RankThreeNormalAbelianSelfCentralizing
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.Local.ControlledNormalElementaryPlane
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

open CFSG.FeitThompson CFSG.FeitThompson
open Subgroup Pointwise

universe u

variable {G : Type*} [Group G]

theorem exists_notMem_notMem_mul_inv_notMem [Finite G] {V M : Subgroup G}
    (hodd : Odd (Nat.card G)) (hVM : ¬ V ≤ M) :
    ∃ g₁ ∈ V, ∃ g₂ ∈ V, g₁ ∉ M ∧ g₂ ∉ M ∧ g₂ * g₁⁻¹ ∉ M := by
  classical
  set W : Subgroup ↥V := M.subgroupOf V with hWdef
  have hWne : W ≠ ⊤ := by
    intro h
    exact hVM fun x hx => by
      have : (⟨x, hx⟩ : ↥V) ∈ W := h ▸ Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.1 this
  have hdvd : W.index ∣ Nat.card G :=
    W.index_dvd_card.trans (Subgroup.card_subgroup_dvd_card V)
  have hoddW : Odd W.index := hodd.of_dvd_nat hdvd
  have hne1 : W.index ≠ 1 := fun h => hWne (Subgroup.index_eq_one.1 h)
  have h3 : 3 ≤ W.index := by obtain ⟨k, hk⟩ := hoddW; omega
  have : Finite (↥V ⧸ W) := Quotient.finite _
  have : Fintype (↥V ⧸ W) := Fintype.ofFinite _
  have hcard : 3 ≤ Fintype.card (↥V ⧸ W) := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card]; exact h3
  have hlt : 1 < (Finset.univ.erase (QuotientGroup.mk (s := W) 1)).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]; omega
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 hlt
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective (s := W) x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective (s := W) y
  have ha : a ∉ W := fun h => (Finset.mem_erase.1 hx).1 (QuotientGroup.eq.2 (by simpa using h))
  have hb : b ∉ W := fun h => (Finset.mem_erase.1 hy).1 (QuotientGroup.eq.2 (by simpa using h))
  have hab : a⁻¹ * b ∉ W := fun h => hxy (QuotientGroup.eq.2 h)
  refine ⟨(a : G)⁻¹, inv_mem a.2, (b : G)⁻¹, inv_mem b.2, ?_, ?_, ?_⟩
  · exact fun h => ha (Subgroup.mem_subgroupOf.2 (by simpa using inv_mem h))
  · exact fun h => hb (Subgroup.mem_subgroupOf.2 (by simpa using inv_mem h))
  · intro h
    refine hab (inv_mem_iff.1 (Subgroup.mem_subgroupOf.2 ?_))
    push_cast
    simpa [mul_assoc] using h

theorem mem_normalizer_of_conjBy_eq_conjBy {A₀ : Subgroup G} {g₁ g₂ : G}
    (h : conjBy A₀ g₁ = conjBy A₀ g₂) : g₂ * g₁⁻¹ ∈ normalizer (A₀ : Set G) := by
  have hiff : ∀ x : G, g₁ * x * g₁⁻¹ ∈ A₀ ↔ g₂ * x * g₂⁻¹ ∈ A₀ := by
    intro x
    have h1 : x ∈ conjBy A₀ g₁ ↔ x ∈ conjBy A₀ g₂ := by rw [h]
    simpa only [mem_conjBy] using h1
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have key : g₂ * (g₁⁻¹ * y * g₁) * g₂⁻¹ = (g₂ * g₁⁻¹) * y * (g₂ * g₁⁻¹)⁻¹ := by group
  constructor
  · intro hy
    have h1 : g₁ * (g₁⁻¹ * y * g₁) * g₁⁻¹ ∈ A₀ := by simpa [mul_assoc] using hy
    have h2 := (hiff (g₁⁻¹ * y * g₁)).1 h1
    rwa [key] at h2
  · intro hy
    rw [← key] at hy
    have h2 := (hiff (g₁⁻¹ * y * g₁)).2 hy
    simpa [mul_assoc] using h2

theorem FTS_exceptional_plane_fixed_free_lines
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FPL_low_rank_sylow_central_product.{u})
    (h₃ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FTS_exceptional_plane_fixed_free_lines.{u} := by
  intro G _ _ hG p M A₀ A P hc
  have := hG.isSimpleGroup
  have hp : p.Prime := hc.prime
  have hAea : IsElementaryAbelian p A :=
    isElementaryAbelian_of_nonempty_mulEquiv_pi hc.isElementaryAbelianPlane
  have hAcard : Nat.card ↥A = p ^ 2 := hc.isElementaryAbelianPlane.natCard hp.ne_zero
  have hPcard : Nat.card ↥P = p ^ (Nat.card ↥M).factorization p := hc.isSylowSubgroupOf.2
  obtain ⟨-, hNP, -, hAmax⟩ := exceptional_maximal_plane hG.not_isMulCommutative
    hG.odd_natCard hG.isSolvable hc.isCoatom hp hc.notMem_sigmaPrimes hc.natCard_A₀ hc.le_of_A₀
    hc.le_of_A hc.le_of_P hPcard hAea hAcard hc.normalizer_le
  have hPab : IsMulCommutative ↥P :=
    (FTS_exceptional_sylow_abelian h₁ h₂ h₃ G hG p M A₀ A P hc).1
  have hOmega : powEqOneSubgroup p P = A := by
    have hle : A ≤ powEqOneSubgroup p P := fun x hx =>
      mem_powEqOneSubgroup_of_pow_eq_one (hc.le_of_A hx) (hAea.pow_eq_one hx)
    have hea : IsElementaryAbelian p (powEqOneSubgroup p P) :=
      isElementaryAbelian_iff.2 ⟨isMulCommutative_of_le powEqOneSubgroup_le,
        fun x hx => pow_eq_one_of_mem_powEqOneSubgroup hx⟩
    exact ((lt_or_eq_of_le hle).resolve_left (hAmax _ hea)).symm
  have hAset : (A : Set G) = {x : G | x ∈ P ∧ x ^ p = 1} := by
    rw [← hOmega]; ext x; simp [mem_powEqOneSubgroup]
  obtain ⟨g₁, hg₁V, g₂, hg₂V, hg₁M, hg₂M, hgM⟩ :=
    exists_notMem_notMem_mul_inv_notMem (V := normalizer (P : Set G)) (M := M) hG.odd_natCard hNP
  have hkey : ∀ g : G, g ∈ normalizer (P : Set G) →
      conjBy A₀ g ≤ A ∧ Nat.card ↥(conjBy A₀ g) = p ∧
        (g ∉ M → sigmaCore M ⊓ centralizer ((conjBy A₀ g : Subgroup G) : Set G) = ⊥) := by
    intro g hgV
    have hPg : MulAut.conj g⁻¹ • P = P := mem_normalizer_iff_conj_smul_eq.1 (inv_mem hgV)
    have hAg : conjBy A g = A := smul_eq_self_of_coe_eq_setOf _ p hPg hAset
    refine ⟨?_, by rw [natCard_conjBy, hc.natCard_A₀], fun hgM => ?_⟩
    · calc conjBy A₀ g ≤ conjBy A g := conjBy_le_conjBy_iff.2 hc.le_of_A₀
        _ = A := hAg
    ·
      have hAMg : A ≤ conjBy M g := by
        rw [← hAg]
        exact conjBy_le_conjBy_iff.2 (hc.le_of_A.trans hc.le_of_P)
      exact (FTS_exceptional_core_conjugate_intersection h₁ h₃ G hG p M A₀ A P hc g hgM hAMg).2
  obtain ⟨hA₁le, hA₁card, hA₁free⟩ := hkey g₁ hg₁V
  obtain ⟨hA₂le, hA₂card, hA₂free⟩ := hkey g₂ hg₂V
  have hne : conjBy A₀ g₁ ≠ conjBy A₀ g₂ := fun h =>
    hgM (hc.normalizer_le (mem_normalizer_of_conjBy_eq_conjBy h))
  have hfree₁ := hA₁free hg₁M
  refine ⟨hAset, ?_, conjBy A₀ g₁, conjBy A₀ g₂, hA₁le, hA₂le, hne, hA₁card, hA₂card,
    hfree₁, hA₂free hg₂M⟩
  refine le_antisymm ?_ bot_le
  calc sigmaCore M ⊓ centralizer (A : Set G)
      ≤ sigmaCore M ⊓ centralizer ((conjBy A₀ g₁ : Subgroup G) : Set G) :=
        inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hA₁le))
    _ = ⊥ := hfree₁

end

end CFSG.FeitThompson.Proofs
