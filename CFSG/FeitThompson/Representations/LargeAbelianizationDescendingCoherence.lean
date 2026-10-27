module

public import CFSG.FeitThompson.Representations.NormalKernelLayerWeightedDegreeSum
public import Mathlib.GroupTheory.Nilpotent
public import CFSG.FeitThompson.Representations.AbelianFrobeniusKernelTICoherence
import CFSG.FeitThompson.Representations.LargeAbelianizationFrobeniusIsometryCoherence
import CFSG.FeitThompson.Representations.InductionIntegerIsometryTISupport
import CFSG.FeitThompson.Representations.SolvableFrobeniusKernelInducedIndexDegree

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open NormalInducedFamily
open scoped Pointwise

section Bot

variable {L : Type*} [Group L]

theorem kerLayerIrr_bot_eq_nonprincipalIrr (K : Subgroup L) :
    kerLayerIrr (⊥ : Subgroup L) K = nonprincipalIrr ↥K := by
  ext θ
  rw [mem_kerLayerIrr, mem_nonprincipalIrr]
  refine ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, fun n hn => ?_, h.2⟩⟩
  rw [show n = 1 from Subtype.ext (by simpa using hn)]

theorem kerLayerIndFam_bot_eq_indFam_nonprincipalIrr [Fintype L] (K : Subgroup L) :
    kerLayerIndFam (⊥ : Subgroup L) K = indFam K (nonprincipalIrr ↥K) := by
  ext f
  rw [mem_kerLayerIndFam, mem_indFam, kerLayerIrr_bot_eq_nonprincipalIrr]

end Bot

variable {G : Type*} [Group G] [Fintype G] {L : Subgroup G} [Fintype ↥L] {A : Set G}
  {H E : Subgroup ↥L} {S : Set (↥L → ℂ)}

omit [Fintype G] in
theorem charSpanZero_kerLayerIndFam_bot_le_dadeZDomain [H.Normal] (hH : H ≠ ⊥)
    (hmul : (H : Set ↥L) * (E : Set ↥L) = Set.univ) (hinf : H ⊓ E = ⊥)
    (hC : ∀ u ∈ E, u ≠ 1 → H ⊓ Subgroup.centralizer {u} = ⊥)
    (hA : A = ((H.map L.subtype : Subgroup G) : Set G) \ {1}) :
    charSpanZero (kerLayerIndFam (⊥ : Subgroup ↥L) H) ≤ dadeZDomain L A :=
  charSpanZero_le_dadeZDomain kerLayerIndFam_subset_indFam
    (kerLayerIndFam_subset_Irr_of_frobenius (E := E) _ hH hmul hinf hC) hA

theorem isCoherent_kerLayerIndFam_bot_of_coe_eq_indClassFun_of_lt_relIndex [H.Normal]
    [Group.IsNilpotent ↥H] (hodd : Odd (Nat.card ↥L)) (hH : H ≠ ⊥)
    (hmul : (H : Set ↥L) * (E : Set ↥L) = Set.univ) (hinf : H ⊓ E = ⊥)
    (hC : ∀ u ∈ E, u ≠ 1 → H ⊓ Subgroup.centralizer {u} = ⊥)
    (hA : A = ((H.map L.subtype : Subgroup G) : Set G) \ {1})
    (hstab : ∀ g : G, (fun x => g⁻¹ * x * g) '' A = A ↔ g ∈ L)
    (hpair : ∀ g k : G, (fun x => g⁻¹ * x * g) '' A = (fun x => k⁻¹ * x * k) '' A ∨
      ((fun x => g⁻¹ * x * g) '' A) ∩ ((fun x => k⁻¹ * x * k) '' A) = ∅)
    (hidx : 4 * H.index ^ 2 + 1 < (⁅H, H⁆ : Subgroup ↥L).relIndex H)
    (hS : S = kerLayerIndFam (⊥ : Subgroup ↥L) H) (τ : charSpanZero S →+ virtualChars G)
    (hτ : ∀ f, (τ f : G → ℂ) = indClassFun L (f : ↥L → ℂ)) :
    IsCoherent S τ := by
  subst hS
  have hTI : IsTIWithNormalizer A L :=
    isTIWithNormalizer_of_stabilizer_eq_and_pairwise hH hA hstab hpair
  have hle := charSpanZero_kerLayerIndFam_bot_le_dadeZDomain (E := E) hH hmul hinf hC hA
  refine isCoherent_kerLayerIndFam_bot_of_lt_relIndex_commutator (E := E) hodd hH hmul hinf hC
    hidx τ ?_ ?_
  · intro f g
    rw [hτ, hτ]
    exact hTI.cfInner_indClassFun (mem_dadeDomain_of_mem_dadeZDomain (hle f.2))
      (mem_dadeDomain_of_mem_dadeZDomain (hle g.2))
  · intro f
    rw [hτ]
    exact hTI.indClassFun_apply_one fun x hx => (mem_dadeZDomain.1 (hle f.2)).2 x hx

theorem isCoherent_kerLayerIndFam_bot_of_coe_eq_indClassFun [H.Normal]
    [Group.IsNilpotent ↥H] (hodd : Odd (Nat.card ↥L)) (hH : H ≠ ⊥)
    (hmul : (H : Set ↥L) * (E : Set ↥L) = Set.univ) (hinf : H ⊓ E = ⊥)
    (hC : ∀ u ∈ E, u ≠ 1 → H ⊓ Subgroup.centralizer {u} = ⊥)
    (hA : A = ((H.map L.subtype : Subgroup G) : Set G) \ {1})
    (hstab : ∀ g : G, (fun x => g⁻¹ * x * g) '' A = A ↔ g ∈ L)
    (hpair : ∀ g k : G, (fun x => g⁻¹ * x * g) '' A = (fun x => k⁻¹ * x * k) '' A ∨
      ((fun x => g⁻¹ * x * g) '' A) ∩ ((fun x => k⁻¹ * x * k) '' A) = ∅)
    (hidx : 4 * Nat.card ↥E ^ 2 + 1 < (⁅H, H⁆ : Subgroup ↥L).relIndex H)
    (hS : S = kerLayerIndFam (⊥ : Subgroup ↥L) H) (τ : charSpanZero S →+ virtualChars G)
    (hτ : ∀ f, (τ f : G → ℂ) = indClassFun L (f : ↥L → ℂ)) :
    IsCoherent S τ :=
  isCoherent_kerLayerIndFam_bot_of_coe_eq_indClassFun_of_lt_relIndex (E := E) hodd hH hmul hinf
    hC hA hstab hpair
    (by rwa [index_eq_card_of_isComplement'
      (isComplement'_of_mul_eq_univ_of_inf_eq_bot hmul hinf)]) hS τ hτ

theorem isCoherent_tiIndCharSpanZeroHom_kerLayerIndFam_bot [H.Normal]
    [Group.IsNilpotent ↥H] (hodd : Odd (Nat.card ↥L)) (hH : H ≠ ⊥)
    (hmul : (H : Set ↥L) * (E : Set ↥L) = Set.univ) (hinf : H ⊓ E = ⊥)
    (hC : ∀ u ∈ E, u ≠ 1 → H ⊓ Subgroup.centralizer {u} = ⊥)
    (hA : A = ((H.map L.subtype : Subgroup G) : Set G) \ {1})
    (hstab : ∀ g : G, (fun x => g⁻¹ * x * g) '' A = A ↔ g ∈ L)
    (hpair : ∀ g k : G, (fun x => g⁻¹ * x * g) '' A = (fun x => k⁻¹ * x * k) '' A ∨
      ((fun x => g⁻¹ * x * g) '' A) ∩ ((fun x => k⁻¹ * x * k) '' A) = ∅)
    (hidx : 4 * Nat.card ↥E ^ 2 + 1 < (⁅H, H⁆ : Subgroup ↥L).relIndex H) :
    IsCoherent (kerLayerIndFam (⊥ : Subgroup ↥L) H)
      ((isTIWithNormalizer_of_stabilizer_eq_and_pairwise hH hA hstab hpair).indCharSpanZeroHom
        (charSpanZero_kerLayerIndFam_bot_le_dadeZDomain (E := E) hH hmul hinf hC hA)) :=
  isCoherent_kerLayerIndFam_bot_of_coe_eq_indClassFun (E := E) hodd hH hmul hinf hC hA hstab
    hpair hidx rfl _ (IsTIWithNormalizer.coe_indCharSpanZeroHom _ _)

end CFSG.FeitThompson
