module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.OutsideSigmaCoreCentralizerRankOne
import CFSG.FeitThompson.Local.CoprimePlaneGeneratesSolvableGroup
import all CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
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

open CFSG.FeitThompson CFSG.FeitThompson.Prep08
  Subgroup

universe u

variable {G : Type u} [Group G] [Finite G]

theorem sigmaCore_le_inf_centralizer_of_notMem_sigmaPrimes {p : ℕ} {M A : Subgroup G}
    (hp : p.Prime) (hplane : IsPlaneAt p A) (hAM : A ≤ M) (hpσ : p ∉ sigmaPrimes M)
    (hb2 : ∀ Y ≤ A, Nat.card ↥Y = p →
      sigmaCore M ⊓ centralizer ((Y : Subgroup G) : Set G) ≤
        M ⊓ centralizer ((A : Subgroup G) : Set G))
    (hsolv : Group.IsSolvable ↥M) :
    sigmaCore M ≤ M ⊓ centralizer ((A : Subgroup G) : Set G) := by
  have hfact := Fact.mk hp
  obtain ⟨hAcomm, hAexp⟩ := isElementaryAbelian_iff.1 hplane.isElementaryAbelian
  have hnormal := sigmaCore_normal_subgroupOf M
  set S' : Subgroup ↥M := (sigmaCore M).subgroupOf M with hS'def
  set A' : Subgroup ↥M := A.subgroupOf M with hA'def
  have hA'card : Nat.card ↥A' = p ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv, hplane.natCard]
  have hA'exp : ∀ a : ↥A', a ^ p = 1 := fun a => Subtype.ext (Subtype.ext (hAexp _ a.2))
  have hpS : ¬ p ∣ Nat.card ↥S' := by
    intro hdvd
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (sigmaCore_le M)).toEquiv] at hdvd
    exact hpσ (isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore M) p
      (Nat.mem_primeFactors.2 ⟨hp, hdvd, Nat.card_pos.ne'⟩))
  let ρ : ↥A' →* MulAut ↥S' := (MulAut.conjNormal (H := S')).comp A'.subtype
  have hgen : ⨆ (a : ↥A') (_ : a ≠ 1), autFixedSubgroup (ρ a) = ⊤ :=
    iSup_autFixedSubgroup_eq_top hp hA'card hA'exp ρ hpS
  let f : ↥S' →* G := M.subtype.comp S'.subtype
  have hfmem : ∀ w : ↥S', f w ∈ sigmaCore M := fun w => w.2
  have key : ∀ a : ↥A', a ≠ 1 →
      autFixedSubgroup (ρ a) ≤ Subgroup.comap f (M ⊓ centralizer ((A : Subgroup G) : Set G)) := by
    intro a ha
    have hgA : ((a : ↥M) : G) ∈ A := a.2
    have hg1 : ((a : ↥M) : G) ≠ 1 := fun h => ha (Subtype.ext (Subtype.ext h))
    have hgord : orderOf ((a : ↥M) : G) = p := orderOf_eq_prime (hAexp _ hgA) hg1
    have hYle : Subgroup.zpowers ((a : ↥M) : G) ≤ A := (Subgroup.zpowers_le).2 hgA
    have hYcard : Nat.card ↥(Subgroup.zpowers ((a : ↥M) : G)) = p := by
      rw [Nat.card_zpowers, hgord]
    intro w hw
    have hfix : ρ a w = w := mem_autFixedSubgroup.1 hw
    have hcomm : ((a : ↥M) : G) * f w * ((a : ↥M) : G)⁻¹ = f w := by
      have := congrArg (fun x : ↥S' => ((x : ↥M) : G)) hfix
      simpa [ρ, f, MulAut.conjNormal_apply] using this
    have hmem : f w ∈ sigmaCore M ⊓
        centralizer ((Subgroup.zpowers ((a : ↥M) : G) : Subgroup G) : Set G) := by
      refine ⟨hfmem w, ?_⟩
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
      rw [Set.mem_singleton_iff] at hy
      subst hy
      calc ((a : ↥M) : G) * f w = ((a : ↥M) : G) * f w * ((a : ↥M) : G)⁻¹ * ((a : ↥M) : G) := by
            group
        _ = f w * ((a : ↥M) : G) := by rw [hcomm]
    exact Subgroup.mem_comap.2 (hb2 _ hYle hYcard hmem)
  have htop : (⊤ : Subgroup ↥S') ≤
      Subgroup.comap f (M ⊓ centralizer ((A : Subgroup G) : Set G)) := by
    rw [← hgen]
    exact iSup₂_le key
  intro b hb
  exact Subgroup.mem_comap.1 (htop (Subgroup.mem_top (⟨⟨b, sigmaCore_le M hb⟩, hb⟩ : ↥S')))

omit [Finite G] in
theorem forall_prime_dvd_natCard_notMem_sigmaPrimes_of_isPlaneAt {p : ℕ} {M A : Subgroup G}
    (hp : p.Prime) (hplane : IsPlaneAt p A) (hpσ : p ∉ sigmaPrimes M) :
    ∀ q : ℕ, q.Prime → q ∣ Nat.card ↥A → q ∉ sigmaPrimes M := by
  intro q hq hdvd
  rw [hplane.natCard] at hdvd
  exact (Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow hdvd) ▸ hpσ

theorem notMem_sigmaPrimes_absurd {p : ℕ} {M A : Subgroup G} (hp : p.Prime)
    (hplane : IsPlaneAt p A)
    (hle : sigmaCore M ≤ M ⊓ centralizer ((A : Subgroup G) : Set G))
    (hrank : elementaryAbelianPRank p ↥(A ⊓ centralizer ((sigmaCore M : Subgroup G) : Set G)) ≤ 1) :
    False := by
  have hAC : A ≤ centralizer ((sigmaCore M : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff.1 (hle.trans inf_le_right)
  rw [inf_eq_left.2 hAC, hplane.elementaryAbelianPRank_eq hp] at hrank
  omega

theorem FTS_nonunique_lines_force_sigma
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FPL_global_sylow_normalizer_derived.{u})
    (h₃ : Statements.FTS_nonunique_line_centralizer_bounds.{u})
    (h₄ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FTS_nonunique_lines_force_sigma.{u} := by
  intro G _ _ hG M A p hsetup
  have hp : p.Prime := hsetup.prime
  by_contra hpσ
  have hsolvM : Group.IsSolvable ↥M := hG.isSolvable_of_ne_top M hsetup.isCoatom_M.1
  obtain ⟨-, hb2, -, -⟩ := h₃ G hG M A p hsetup
  have hle := sigmaCore_le_inf_centralizer_of_notMem_sigmaPrimes hp hsetup.isPlane hsetup.le hpσ
    (hb2 hpσ) hsolvM
  have hrank := FTS_outside_sigma_core_centralizer_rank_one h₁ h₂ h₄ G hG M A
    hsetup.isCoatom_M hsetup.le
    (forall_prime_dvd_natCard_notMem_sigmaPrimes_of_isPlaneAt hp hsetup.isPlane hpσ) p
  exact notMem_sigmaPrimes_absurd hp hsetup.isPlane hle hrank

end

end CFSG.FeitThompson.Proofs
