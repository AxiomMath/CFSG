module

public import CFSG.FeitThompson.Representations.AbelianFrobeniusKernelTICoherence
public import Mathlib.GroupTheory.Nilpotent
import CFSG.FeitThompson.Representations.PGroupFrobeniusTISibleyCoherence
import CFSG.FeitThompson.Representations.LargeAbelianizationDescendingCoherence
import CFSG.FeitThompson.Local.NilpotentFrobeniusAbelianizationPrimePower
import CFSG.FeitThompson.Representations.InductionIntegerIsometryTISupport
import CFSG.FeitThompson.Representations.SibleyCentralLinearJoining
import CFSG.FeitThompson.Local.SupportingFrobeniusComplementShape

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace SibleyNilpotentCoherence

open Subgroup NormalInducedFamily
open scoped Pointwise

variable {G : Type*} [Group G] [Fintype G] {L H E : Subgroup G} [Fintype ↥L]

omit [Fintype G] [Fintype ↥L] in
theorem subgroupOf_ne_bot (hHL : H ≤ L) (hHbot : H ≠ ⊥) : H.subgroupOf L ≠ ⊥ := by
  intro h
  rw [Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_eq_left.2 hHL] at h
  exact hHbot h

omit [Fintype G] [Fintype ↥L] in
theorem isTIWithNormalizer_sdiff (hHbot : H ≠ ⊥)
    (hstab : ∀ g : G, (fun x => g⁻¹ * x * g) '' ((H : Set G) \ {1}) = (H : Set G) \ {1} ↔ g ∈ L)
    (hTIor : ∀ g : G, (fun x => g⁻¹ * x * g) '' ((H : Set G) \ {1}) = (H : Set G) \ {1} ∨
      (fun x => g⁻¹ * x * g) '' ((H : Set G) \ {1}) ∩ ((H : Set G) \ {1}) = ∅) :
    IsTIWithNormalizer ((H : Set G) \ {1}) L := by
  have : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).2 hHbot
  obtain ⟨x, hx⟩ := exists_ne (1 : ↥H)
  exact isTIWithNormalizer_of_conj_image_eq_or_disjoint
    ⟨(x : G), x.2, by simpa using hx⟩ (by simp) hTIor hstab

omit [Fintype G] in
theorem indFam_subgroupOf_subset_Irr (hHL : H ≤ L) (hEL : E ≤ L)
    (hnormH : L ≤ normalizer (H : Set G)) (hsup : H ⊔ E = L) (hinf : H ⊓ E = ⊥) (hHbot : H ≠ ⊥)
    (hCfree : ∀ u ∈ E, u ≠ 1 → H ⊓ centralizer ({u} : Set G) = ⊥) :
    indFam (H.subgroupOf L) (nonprincipalIrr ↥(H.subgroupOf L)) ⊆ Irr ↥L :=
  have _ : (H.subgroupOf L).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hHL).2 hnormH
  indFam_nonprincipalIrr_subset_Irr (subgroupOf_ne_bot hHL hHbot)
    (SibleyPGroupCoherence.isComplement'_subgroupOf hHL hEL hnormH hsup hinf)
    (free_subgroupOf hHL hCfree)

omit [Fintype G] in
theorem charSpanZero_le_dadeZDomain_sdiff (hHL : H ≤ L) (hEL : E ≤ L)
    (hnormH : L ≤ normalizer (H : Set G)) (hsup : H ⊔ E = L) (hinf : H ⊓ E = ⊥) (hHbot : H ≠ ⊥)
    (hCfree : ∀ u ∈ E, u ≠ 1 → H ⊓ centralizer ({u} : Set G) = ⊥) :
    charSpanZero (indFam (H.subgroupOf L) (nonprincipalIrr ↥(H.subgroupOf L)))
      ≤ dadeZDomain L ((H : Set G) \ {1}) :=
  have _ : (H.subgroupOf L).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hHL).2 hnormH
  charSpanZero_le_dadeZDomain (indFam_mono _ nonprincipalIrr_subset_Irr)
    (indFam_subgroupOf_subset_Irr (E := E) hHL hEL hnormH hsup hinf hHbot hCfree)
    (SibleyPGroupCoherence.sdiff_eq_sdiff_map_subgroupOf hHL)

theorem isCoherent_indFam_nonprincipalIrr [Group.IsNilpotent ↥H]
    (hLodd : Odd (Nat.card ↥L)) (hHL : H ≤ L) (hEL : E ≤ L)
    (hnormH : L ≤ normalizer (H : Set G)) (hsup : H ⊔ E = L) (hinf : H ⊓ E = ⊥)
    (hHbot : H ≠ ⊥) (hEbot : E ≠ ⊥)
    (hCfree : ∀ u ∈ E, u ≠ 1 → H ⊓ centralizer ({u} : Set G) = ⊥)
    (hstab : ∀ g : G, (fun x => g⁻¹ * x * g) '' ((H : Set G) \ {1}) = (H : Set G) \ {1} ↔ g ∈ L)
    (hTIor : ∀ g : G, (fun x => g⁻¹ * x * g) '' ((H : Set G) \ {1}) = (H : Set G) \ {1} ∨
      (fun x => g⁻¹ * x * g) '' ((H : Set G) \ {1}) ∩ ((H : Set G) \ {1}) = ∅)
    (τ : charSpanZero (indFam (H.subgroupOf L) (nonprincipalIrr ↥(H.subgroupOf L))) →+
      virtualChars G)
    (hτ : ∀ f, (τ f : G → ℂ) = indClassFun L (f : ↥L → ℂ)) :
    IsCoherent (indFam (H.subgroupOf L) (nonprincipalIrr ↥(H.subgroupOf L))) τ := by
  classical
  have hnormOf : (H.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHL).2 hnormH
  have hHOfbot : H.subgroupOf L ≠ ⊥ := subgroupOf_ne_bot hHL hHbot
  have hnil : Group.IsNilpotent ↥(H.subgroupOf L) :=
    (Group.isNilpotent_congr (Subgroup.subgroupOfEquivOfLe hHL)).2 ‹_›
  have hcompl := SibleyPGroupCoherence.isComplement'_subgroupOf hHL hEL hnormH hsup hinf
  have hmul : ((H.subgroupOf L : Subgroup ↥L) : Set ↥L) *
      ((E.subgroupOf L : Subgroup ↥L) : Set ↥L) = Set.univ := hcompl.mul_eq
  have hinfOf : H.subgroupOf L ⊓ E.subgroupOf L = ⊥ := disjoint_iff.1 hcompl.disjoint
  have hCOf := free_subgroupOf hHL hCfree
  have hA := SibleyPGroupCoherence.sdiff_eq_sdiff_map_subgroupOf (P := H) hHL
  have hTI := isTIWithNormalizer_sdiff hHbot hstab hTIor
  have hpair := SibleyCentralLinearJoining.conjInv_image_eq_or_inter_eq_empty hTI
  by_cases hidx : 4 * Nat.card ↥(E.subgroupOf L) ^ 2 + 1 <
      (⁅H.subgroupOf L, H.subgroupOf L⁆ : Subgroup ↥L).relIndex (H.subgroupOf L)
  ·
    exact isCoherent_kerLayerIndFam_bot_of_coe_eq_indClassFun (E := E.subgroupOf L) hLodd
      hHOfbot hmul hinfOf hCOf hA hstab hpair hidx
      (kerLayerIndFam_bot_eq_indFam_nonprincipalIrr _).symm τ hτ
  ·
    obtain ⟨p, a, d, hp, ha, hd, hcard, -⟩ :=
      exists_prime_pow_natCard_nonempty_mulEquiv_quotientFactor_commutator_self
        (E := E.subgroupOf L) hLodd hHOfbot hCOf (not_lt.1 hidx)
    have hcardH : Nat.card ↥H = p ^ a := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHL).toEquiv]; exact hcard
    have hpodd : Odd p := by
      refine hLodd.of_dvd_nat (dvd_trans ?_ (Subgroup.card_dvd_of_le hHL))
      rw [hcardH]
      exact dvd_pow_self p (by omega)
    exact SibleyPGroupCoherence.isCoherent_indFam_nonprincipalIrr hp hpodd ha hcardH hLodd hHL
      hEL hnormH hsup hinf hEbot hCfree hstab hTIor τ hτ

theorem isCoherent_indCharSpanZeroHom [Group.IsNilpotent ↥H]
    (hLodd : Odd (Nat.card ↥L)) (hHL : H ≤ L) (hEL : E ≤ L)
    (hnormH : L ≤ normalizer (H : Set G)) (hsup : H ⊔ E = L) (hinf : H ⊓ E = ⊥)
    (hHbot : H ≠ ⊥) (hEbot : E ≠ ⊥)
    (hCfree : ∀ u ∈ E, u ≠ 1 → H ⊓ centralizer ({u} : Set G) = ⊥)
    (hstab : ∀ g : G, (fun x => g⁻¹ * x * g) '' ((H : Set G) \ {1}) = (H : Set G) \ {1} ↔ g ∈ L)
    (hTIor : ∀ g : G, (fun x => g⁻¹ * x * g) '' ((H : Set G) \ {1}) = (H : Set G) \ {1} ∨
      (fun x => g⁻¹ * x * g) '' ((H : Set G) \ {1}) ∩ ((H : Set G) \ {1}) = ∅) :
    IsCoherent (indFam (H.subgroupOf L) (nonprincipalIrr ↥(H.subgroupOf L)))
      ((isTIWithNormalizer_sdiff hHbot hstab hTIor).indCharSpanZeroHom
        (charSpanZero_le_dadeZDomain_sdiff (E := E) hHL hEL hnormH hsup hinf hHbot hCfree)) :=
  isCoherent_indFam_nonprincipalIrr (E := E) hLodd hHL hEL hnormH hsup hinf hHbot hEbot hCfree
    hstab hTIor _ (IsTIWithNormalizer.coe_indCharSpanZeroHom _ _)

end SibleyNilpotentCoherence

end CFSG.FeitThompson

end
