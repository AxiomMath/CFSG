module

public import CFSG.ClassicalInvolution.Asc77.AscC25J8
public import CFSG.ClassicalInvolution.Asc77.AscC25V32
public import CFSG.ClassicalInvolution.Asc77.AscR10QV
public import CFSG.ClassicalInvolution.Asc77.AscR10G2R
public import CFSG.ClassicalInvolution.Asc77.AscC25J5
public import CFSG.ClassicalInvolution.Asc77.AscC25J6
public import CFSG.ClassicalInvolution.Asc77.AscC25J7

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25J

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.ClassicalInvolution.Asc77.C25V CFSG.ClassicalInvolution.Asc77.C25H
  CFSG.ClassicalInvolution.Asc77.C25X CFSG.ClassicalInvolution.Asc77.T3CII
  CFSG.ClassicalInvolution.Asc77.C25I CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Asc77.T3
open scoped MatrixGroups commutatorElement

section Nbr

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' : Subgroup G} {z : G}


theorem crossIn_nbr_twin (d : TwinCtx p f Ω K K' z) {a : G}
    (hzKa : z ∈ K ⊓ Subgroup.centralizer ({a} : Set G))
    (hΩ : HypOmegaModU (.sl2 3 1) (conjFamily (crossIn K a)))
    {c₁ c₂ : ↥(Subgroup.centralizer ({a} : Set G))}
    (h : conjSub c₂ (crossIn K a) ∈
      omegaNbr (conjFamily (crossIn K a)) (conjSub c₁ (crossIn K a))) :
    conjSub (c₂ : G) K ∈ twinSet Ω (conjSub (c₁ : G) K) := by
  by_contra htw
  have hΩg : HypOmegaGen (conjFamily (crossIn K a)) :=
    hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hΩ
  obtain ⟨-, hne, R₀, hR, hRle, hRN⟩ := h
  obtain ⟨⟨x, hx, y, hy, hxy⟩, h8⟩ := exists_ne_comm_of_mem_rSetGen hΩg hR
  have hR2 := isPGroup_of_mem_rSet hR
  have hne' : conjSub (c₁ : G) (K ⊓ Subgroup.centralizer ({a} : Set G)) ≠
      conjSub (c₂ : G) (K ⊓ Subgroup.centralizer ({a} : Set G)) := by
    intro h
    apply hne
    apply Subgroup.map_injective (Subgroup.centralizer ({a} : Set G)).subtype_injective
    rw [map_conjSub_crossIn, map_conjSub_crossIn, h]
  refine crossIn_false_of_le_normalizer d hzKa c₁.2 c₂.2 hne' htw
    (hR2.map (Subgroup.centralizer ({a} : Set G)).subtype)
    ⟨(x : G), Subgroup.mem_map_of_mem _ hx, (y : G), Subgroup.mem_map_of_mem _ hy,
      fun h => hxy (Subtype.ext h)⟩ ?_ ?_ ?_
  · rw [← Nat.card_congr (Subgroup.equivMapOfInjective R₀ _
      (Subgroup.centralizer ({a} : Set G)).subtype_injective).toEquiv]
    omega
  · rw [← map_conjSub_crossIn]
    exact Subgroup.map_mono hRle
  · rw [← map_conjSub_crossIn]
    exact (Subgroup.map_mono hRN).trans (Subgroup.le_normalizer_map _)

theorem crossIn_member_eq {a : G} {c₁ c₂ : ↥(Subgroup.centralizer ({a} : Set G))}
    (h : conjSub (c₁ : G) K = conjSub (c₂ : G) K) :
    conjSub c₁ (crossIn K a) = conjSub c₂ (crossIn K a) := by
  apply Subgroup.map_injective (Subgroup.centralizer ({a} : Set G)).subtype_injective
  rw [map_conjSub_crossIn, map_conjSub_crossIn]
  exact conjSub_cross_eq c₁.2 c₂.2 h

theorem crossIn_nbr_eq (d : TwinCtx p f Ω K K' z) {a : G}
    (hzKa : z ∈ K ⊓ Subgroup.centralizer ({a} : Set G))
    (hΩ : HypOmegaModU (.sl2 3 1) (conjFamily (crossIn K a)))
    {w : ↥(Subgroup.centralizer ({a} : Set G))} (hw : conjSub (w : G) K = K')
    {c₁ c₂ : ↥(Subgroup.centralizer ({a} : Set G))}
    (h : conjSub c₂ (crossIn K a) ∈
      omegaNbr (conjFamily (crossIn K a)) (conjSub c₁ (crossIn K a))) :
    conjSub c₂ (crossIn K a) = conjSub (c₁ * w) (crossIn K a) := by
  have htw := crossIn_nbr_twin d hzKa hΩ h
  have h1 := twinSet_conj d.hΩ.conjInvariant htw (c₁ : G)⁻¹
  rw [conjSub_inv_conjSub, d.htw] at h1
  have e1 : conjSub ((c₁ : G)⁻¹) (conjSub (c₂ : G) K) = conjSub ((c₁ : G)⁻¹ * (c₂ : G)) K := by
    rw [conjSub_mul]
  rw [e1] at h1
  rcases h1 with h1 | h1
  · exfalso
    apply h.2.1
    apply crossIn_member_eq
    have h2 := congrArg (conjSub (c₁ : G)) h1
    rw [← conjSub_mul, mul_inv_cancel_left] at h2
    exact h2
  · apply crossIn_member_eq
    have h2 := congrArg (conjSub (c₁ : G)) h1
    rw [← conjSub_mul, mul_inv_cancel_left, ← hw, ← conjSub_mul] at h2
    exact h2

end Nbr

end CFSG.ClassicalInvolution.Asc77.C25J
