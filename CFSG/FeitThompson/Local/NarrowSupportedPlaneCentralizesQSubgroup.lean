module

public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.SupportedPlaneSylowNormalizer
import CFSG.FeitThompson.Local.OddAutomorphismMaximalPlaneDerivedPrimePower
import CFSG.FeitThompson.Local.MaximalPlaneDerivedNormalComplement
import CFSG.FeitThompson.Local.CriticalSubgroupFixedLine
public import CFSG.FeitThompson.Representations.AlgebraicIntegersRing
public import CFSG.FeitThompson.Representations.NormalInducedSupportBasis
public import CFSG.FeitThompson.Representations.SchurLemmaIntertwiningMaps

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup CFSG.FeitThompson

universe u

variable {G : Type*} [Group G] [Finite G] {p q : ℕ}

theorem maximal_isElementaryAbelian_of_maximal_isElementaryAbelianSubgroup {X : Type*} [Group X]
    {A : Subgroup X} (h : Maximal (IsElementaryAbelianSubgroup q) A) :
    Maximal (IsElementaryAbelian q) A :=
  ⟨isElementaryAbelian_iff_isElementaryAbelianSubgroup.2 h.prop, fun _B hB hle =>
    h.le_of_ge (isElementaryAbelian_iff_isElementaryAbelianSubgroup.1 hB) hle⟩

omit [Finite G] in
theorem commutator_normalizer_le_normalizer (Q : Subgroup G) :
    ⁅normalizer (Q : Set G), normalizer (Q : Set G)⁆ ≤ normalizer (Q : Set G) :=
  Subgroup.commutator_le.2 fun _g₁ h₁ _g₂ h₂ =>
    mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)

theorem commutator_eq_bot_of_le_commutator_normalizer (hodd : Odd (Nat.card G))
    (hp : p.Prime) (hq : q.Prime) (hqodd : Odd q) (hpq : p ≠ q) {Q : Subgroup G}
    (hQ : IsPGroup q Q)
    (halt : IsCyclic Q ∨ ∃ B : Subgroup Q, Maximal (IsElementaryAbelian q) B ∧ Nat.card B = q ^ 2)
    {P : Subgroup G} (hP : IsPGroup p P)
    (hPN : P ≤ ⁅normalizer (Q : Set G), normalizer (Q : Set G)⁆) :
    ⁅P, Q⁆ = ⊥ := by
  set M : Subgroup G := normalizer (Q : Set G) with hM
  set φ := Q.normalizerMonoidHom with hφ
  have hBodd : Odd (Nat.card φ.range) :=
    Odd.of_dvd_nat hodd ((Subgroup.card_range_dvd φ).trans (Subgroup.card_subgroup_dvd_card M))
  have hcomm : IsPGroup q ↥⁅φ.range, φ.range⁆ :=
    isPGroup_commutator_subgroup_of_odd_aut_of_isCyclic_or_maximal_plane hq hqodd hQ halt hBodd
  have hPM : P ≤ M := hPN.trans (commutator_normalizer_le_normalizer Q)
  have hP' : P.subgroupOf M ≤ _root_.commutator M := by
    have h := Subgroup.comap_mono (f := M.subtype) hPN
    rwa [← Subgroup.map_subtype_commutator M,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective] at h
  have hmapc : (_root_.commutator ↥M).map φ = ⁅φ.range, φ.range⁆ := by
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map]
  have himg : (P.subgroupOf M).map φ ≤ ⁅φ.range, φ.range⁆ := by
    rw [← hmapc]; exact Subgroup.map_mono hP'
  have hq2 : IsPGroup q ((P.subgroupOf M).map φ) := hcomm.to_le himg
  have hp2 : IsPGroup p ((P.subgroupOf M).map φ) := hP.comap_subtype.map φ
  have hcard : Nat.card ((P.subgroupOf M).map φ) = 1 :=
    natCard_eq_one_of_isPGroup_of_isPGroup hp hq hpq hp2 hq2
  have hker : P.subgroupOf M ≤ φ.ker :=
    (Subgroup.map_eq_bot_iff _).1 (Subgroup.card_eq_one.1 hcard)
  rw [hφ, Subgroup.normalizerMonoidHom_ker] at hker
  refine Subgroup.commutator_eq_bot_iff_le_centralizer.2 fun x hx => ?_
  have hmem : (⟨x, hPM hx⟩ : M) ∈ (centralizer (Q : Set G)).subgroupOf M :=
    hker (Subgroup.mem_subgroupOf.2 hx)
  exact Subgroup.mem_subgroupOf.1 hmem

theorem FTS_supported_plane_narrow_centralization
    (h₁ : Statements.FPL_global_sylow_normalizer_derived.{u})
    (h₂ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FTS_supported_plane_narrow_centralization.{u} := by
  intro G _ _ hG p q hp hq hpq A hA Q hQp hAQ hQmem hqC halt
  obtain ⟨P, hAP, hfact, hPN⟩ :=
    FTS_supported_plane_sylow_normalizer h₁ h₂ G hG p q hp hq hpq A hA Q hQp hAQ hQmem hqC
  have hodd := hG.odd_natCard
  have hqodd : Odd q := Odd.of_dvd_nat hodd (hqC.trans (Subgroup.card_subgroup_dvd_card _))
  refine ⟨P, hAP, hfact, hPN, ?_⟩
  exact commutator_eq_bot_of_le_commutator_normalizer hodd hp hq hqodd hpq hQp
    (halt.imp id fun ⟨B, hB⟩ =>
      ⟨B, maximal_isElementaryAbelian_of_maximal_isElementaryAbelianSubgroup hB.1, hB.2⟩)
    P.isPGroup' hPN

end

end CFSG.FeitThompson.Proofs
