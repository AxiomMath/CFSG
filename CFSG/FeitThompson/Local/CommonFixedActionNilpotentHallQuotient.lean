module

public import CFSG.FeitThompson.Foundations.NormalHallContainsPiSubgroups
public import CFSG.FeitThompson.Local.FittingEqualsChiefActionKernel
public import CFSG.FeitThompson.Local.CommonPrimeFixedComplementLayout
import CFSG.FeitThompson.Local.PrimeFixedKernelsEqualFitting
import CFSG.FeitThompson.Local.FittingSplitsNormalHall
import CFSG.FeitThompson.Local.HallCoreLargestNilpotentNormalHall

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup Pointwise

universe u

variable {X : Type u} [Group X] {q : ℕ} {S K Z D : Subgroup X}

theorem isNilpotent_quotient_subgroupOf_of_sup_eq {N S D : Subgroup X} [N.Normal]
    (hD : Group.IsNilpotent ↥D) (hDS : D ≤ S) (hsup : N ⊔ D = S) :
    Group.IsNilpotent (↥S ⧸ N.subgroupOf S) := by
  have := hD
  refine Group.nilpotent_of_surjective
    ((QuotientGroup.mk' (N.subgroupOf S)).comp (Subgroup.inclusion hDS)) ?_
  intro x
  induction x using QuotientGroup.induction_on with
  | _ s =>
    have hs : (s : X) ∈ ((N ⊔ D : Subgroup X) : Set X) := by rw [hsup]; exact s.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left N D (le_normalizer_of_normal D N),
      Set.mem_mul] at hs
    obtain ⟨n, hn, d, hd, hnd⟩ := hs
    refine ⟨⟨d, hd⟩, ?_⟩
    have hmem : (⟨d, hDS hd⟩ : ↥S)⁻¹ * s ∈ N.subgroupOf S := by
      rw [Subgroup.mem_subgroupOf]
      change ((⟨d, hDS hd⟩ : ↥S)⁻¹ * s : X) ∈ N
      have heq : ((⟨d, hDS hd⟩ : ↥S)⁻¹ * s : X) = d⁻¹ * n * d := by
        simp only [Subgroup.coe_inv, ← hnd]
        group
      rw [heq]
      simpa using ‹N.Normal›.conj_mem n hn d⁻¹
    change (QuotientGroup.mk (Subgroup.inclusion hDS ⟨d, hd⟩) : ↥S ⧸ N.subgroupOf S)
      = QuotientGroup.mk s
    exact QuotientGroup.eq.2 hmem

theorem fittingRaw_le_sup_centralizer_of_isHallPiSubgroup [Finite X] {π : Set ℕ} {N : Subgroup X}
    (hN : N.Normal) (hnil : Group.IsNilpotent ↥N) (hHall : IsHallPiSubgroup π N) :
    fittingRaw X ≤ N ⊔ centralizer (N : Set X) := by
  have := hnil
  have hFN : (fittingRaw ↥N).map N.subtype = N := by
    rw [fittingRaw_eq_top_of_isNilpotent ↥N, ← MonoidHom.range_eq_map, N.range_subtype]
  have hπ : fittingPiPart π X = N := by
    rw [← map_subtype_fittingRaw_eq_fittingPiPart hN hHall, hFN]
  have hcomm : fittingPiPart πᶜ X ≤ centralizer (N : Set X) := by
    rw [← hπ, ← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm,
      commutator_fittingPiPart_compl]
  rw [← fittingPiPart_sup_compl π X, hπ]
  exact sup_le_sup_left hcomm N

theorem fittingRaw_le_hallCore_sup_centralizer [Finite X] :
    fittingRaw X ≤ hallCore X ⊔ centralizer ((hallCore X : Subgroup X) : Set X) :=
  fittingRaw_le_sup_centralizer_of_isHallPiSubgroup hallCore_normal hallCore_isNilpotent
    (isHallSubgroup_iff_isHallPiSubgroup.1 isHallSubgroup_hallCore)

theorem coe_hallCore_sup_centralizer_hallCore :
    ((hallCore X ⊔ centralizer ((hallCore X : Subgroup X) : Set X) : Subgroup X) : Set X)
      = (hallCore X : Set X) * (centralizer ((hallCore X : Subgroup X) : Set X) : Set X) :=
  Subgroup.coe_mul_of_right_le_normalizer_left _ _ (le_normalizer_of_normal _ _)

namespace IsCommonPrimeFixedSetup

variable (h : IsCommonPrimeFixedSetup X q S K Z) (hDS : D ≤ S)
  (hDhall : IsHallSubgroup ({q}ᶜ : Set ℕ) (D.subgroupOf S))
  (hDK : K ≤ normalizer (D : Set X))

include h

theorem bot_lt_hallCore :
    haveI := h.finite
    ⊥ < hallCore X := by
  have := h.finite
  exact lt_of_lt_of_le h.bot_lt_pCoreIn h.pCoreIn_le_hallCore

include hDS hDhall hDK

theorem isPrimeFixedSectionSetup :
    haveI := h.finite
    IsPrimeFixedSectionSetup X q (pCoreIn q S) D K Z := by
  have := h.finite
  have hQS : pCoreIn q S ≤ S := pCoreIn_le q S
  have hZ : Z = pCoreIn q S ⊓ centralizer (K : Set X) :=
    le_antisymm (le_inf h.Z_le_pCoreIn (h.Z_eq.le.trans inf_le_right))
      ((inf_le_inf_right _ hQS).trans h.Z_eq.ge)
  exact
  { prime := h.prime
    odd_natCard := h.odd_natCard
    isSolvable := h.isSolvable
    normal_Q := h.normal_pCoreIn
    isPGroup_Q := h.isPGroup_pCoreIn
    coe_mul_coe := Subgroup.IsComplement.mul_eq (h.isComplement'_pCoreIn_sup hDS hDhall hDK)
    inf_Q_sup := disjoint_iff.1 (h.isComplement'_pCoreIn_sup hDS hDhall hDK).disjoint
    normal_D := IsCommonPrimeFixedSetup.normal_subgroupOf_sup hDK
    inf_D_K := h.inf_D_K_eq_bot hDS
    coprime_Q := h.coprime_natCard_pCoreIn_sup hDS hDhall hDK
    coprime_D_K := Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le hDS) h.coprime
    D_ne_bot := h.ne_bot_of_isHallSubgroup hDS hDhall
    K_ne_bot := h.K_ne_bot
    inf_centralizer_D := fun k hk hk1 => h.inf_centralizer_eq_bot_of_mem hDS hDhall k hk hk1
    inf_centralizer_Q := fun k hk hk1 => h.inf_pCoreIn_centralizer_eq k hk hk1
    Z_eq := hZ
    natCard_Z := h.natCard_Z }

theorem fittingRaw_eq_pCoreIn_sup_centralizer :
    haveI := h.finite
    fittingRaw X = pCoreIn q S ⊔ centralizer ((pCoreIn q S : Subgroup X) : Set X) := by
  have := h.finite
  exact (h.isPrimeFixedSectionSetup hDS hDhall hDK).fittingRaw_eq_sup_centralizer_Q
    (h.inf_centralizer_lt_pCoreIn hDS hDhall) (h.isNilpotent_of_isHallSubgroup hDS hDhall)

theorem fittingRaw_le_S :
    haveI := h.finite
    fittingRaw X ≤ S := by
  have := h.finite
  have hle := (h.isPrimeFixedSectionSetup hDS hDhall hDK).fittingRaw_le_sup_Q_D
    (h.inf_centralizer_lt_pCoreIn hDS hDhall) (h.isNilpotent_of_isHallSubgroup hDS hDhall)
  rwa [h.sup_pCoreIn_eq' hDS hDhall] at hle

theorem commutator_S_le_fittingRaw :
    haveI := h.finite
    ⁅S, S⁆ ≤ fittingRaw X := by
  have := h.finite
  have hle := (h.isPrimeFixedSectionSetup hDS hDhall hDK).commutator_sup_Q_D_le_fittingRaw
    (h.inf_centralizer_lt_pCoreIn hDS hDhall) (h.isNilpotent_of_isHallSubgroup hDS hDhall)
  rwa [h.sup_pCoreIn_eq' hDS hDhall] at hle

theorem hallCore_le_S :
    haveI := h.finite
    hallCore X ≤ S := by
  have := h.finite
  exact hallCore_le_fittingRaw.trans (h.fittingRaw_le_S hDS hDhall hDK)

theorem hallCore_sup_eq :
    haveI := h.finite
    hallCore X ⊔ D = S := by
  have := h.finite
  refine le_antisymm (sup_le (h.hallCore_le_S hDS hDhall hDK) hDS) ?_
  rw [← h.sup_pCoreIn_eq' hDS hDhall]
  exact sup_le_sup_right h.pCoreIn_le_hallCore D

theorem isNilpotent_quotient_hallCore :
    haveI := h.finite
    Group.IsNilpotent (↥S ⧸ (hallCore X).subgroupOf S) := by
  have := h.finite
  exact isNilpotent_quotient_subgroupOf_of_sup_eq (h.isNilpotent_of_isHallSubgroup hDS hDhall)
    hDS (h.hallCore_sup_eq hDS hDhall hDK)

theorem fittingRaw_eq_hallCore_sup_centralizer :
    haveI := h.finite
    fittingRaw X = hallCore X ⊔ centralizer ((hallCore X : Subgroup X) : Set X) := by
  have := h.finite
  refine le_antisymm fittingRaw_le_hallCore_sup_centralizer (sup_le hallCore_le_fittingRaw ?_)
  rw [h.fittingRaw_eq_pCoreIn_sup_centralizer hDS hDhall hDK]
  exact le_sup_of_le_right (Subgroup.centralizer_le (by exact_mod_cast h.pCoreIn_le_hallCore))

end IsCommonPrimeFixedSetup

theorem common_prime_fixed_hall_core_quotient {X : Type u} [Group X] {q : ℕ}
    {S K Z D : Subgroup X} (h : IsCommonPrimeFixedSetup X q S K Z) (hDS : D ≤ S)
    (hDhall : IsHallSubgroup ({q}ᶜ : Set ℕ) (D.subgroupOf S))
    (hDK : K ≤ Subgroup.normalizer (D : Set X)) :
    haveI := h.finite
    ⊥ < hallCore X ∧ hallCore X ≤ S ∧
      Group.IsNilpotent (↥S ⧸ (hallCore X).subgroupOf S) ∧
      ⁅S, S⁆ ≤ fittingRaw X ∧
      fittingRaw X = hallCore X ⊔ Subgroup.centralizer ((hallCore X : Subgroup X) : Set X) ∧
      fittingRaw X ≤ S :=
  haveI := h.finite
  ⟨h.bot_lt_hallCore, h.hallCore_le_S hDS hDhall hDK,
    h.isNilpotent_quotient_hallCore hDS hDhall hDK, h.commutator_S_le_fittingRaw hDS hDhall hDK,
    h.fittingRaw_eq_hallCore_sup_centralizer hDS hDhall hDK, h.fittingRaw_le_S hDS hDhall hDK⟩

end CFSG.FeitThompson
