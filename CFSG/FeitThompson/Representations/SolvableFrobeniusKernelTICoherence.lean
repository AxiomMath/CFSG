module

public import CFSG.FeitThompson.Representations.SibleyNilpotentFrobeniusCoherence
import CFSG.FeitThompson.Local.SolvableFrobeniusKernelNilpotent
import CFSG.FeitThompson.Local.SupportingFrobeniusComplementShape
import CFSG.FeitThompson.Representations.PGroupFrobeniusTISibleyCoherence

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace SibleySolvableCoherence

open Subgroup

variable {G : Type*} [Group G] {L H E : Subgroup G}

theorem natCard_eq_relIndex (hHL : H ≤ L) (hEL : E ≤ L)
    (hnormH : L ≤ normalizer (H : Set G)) (hsup : H ⊔ E = L) (hinf : H ⊓ E = ⊥) :
    Nat.card ↥E = H.relIndex L := by
  have hcompl := SibleyPGroupCoherence.isComplement'_subgroupOf hHL hEL hnormH hsup hinf
  rw [Subgroup.relIndex, hcompl.symm.index_eq_card,
    Nat.card_congr (subgroupOfEquivOfLe hEL).toEquiv]

theorem isNilpotent_of_isSolvable [Finite G] [Group.IsSolvable ↥H] (hHL : H ≤ L) (hEL : E ≤ L)
    (hnormH : L ≤ normalizer (H : Set G)) (hsup : H ⊔ E = L) (hinf : H ⊓ E = ⊥) (hEbot : E ≠ ⊥)
    (hCfree : ∀ u ∈ E, u ≠ 1 → H ⊓ centralizer ({u} : Set G) = ⊥) :
    Group.IsNilpotent ↥H := by
  have _ : (H.subgroupOf L).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hHL).2 hnormH
  have _ : Group.IsSolvable ↥(H.subgroupOf L) :=
    Group.isSolvable_of_isSolvable_injective (f := (subgroupOfEquivOfLe hHL).toMonoidHom)
      (by simpa using (subgroupOfEquivOfLe hHL).injective)
  have hcompl := SibleyPGroupCoherence.isComplement'_subgroupOf hHL hEL hnormH hsup hinf
  have hnilOf : Group.IsNilpotent ↥(H.subgroupOf L) :=
    isNilpotent_of_isSolvable_of_inf_centralizer_eq_bot (disjoint_iff.1 hcompl.disjoint)
      (SibleyNilpotentCoherence.subgroupOf_ne_bot hEL hEbot) (free_subgroupOf hHL hCfree)
  exact (Group.isNilpotent_congr (subgroupOfEquivOfLe hHL)).1 hnilOf

variable [Fintype G] [Fintype ↥L]

theorem isCoherent_indFam_nonprincipalIrr [Group.IsSolvable ↥H]
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
    IsCoherent (indFam (H.subgroupOf L) (nonprincipalIrr ↥(H.subgroupOf L))) τ :=
  have : Group.IsNilpotent ↥H :=
    isNilpotent_of_isSolvable hHL hEL hnormH hsup hinf hEbot hCfree
  SibleyNilpotentCoherence.isCoherent_indFam_nonprincipalIrr (E := E) hLodd hHL hEL hnormH hsup
    hinf hHbot hEbot hCfree hstab hTIor τ hτ

theorem isCoherent_indCharSpanZeroHom [Group.IsSolvable ↥H]
    (hLodd : Odd (Nat.card ↥L)) (hHL : H ≤ L) (hEL : E ≤ L)
    (hnormH : L ≤ normalizer (H : Set G)) (hsup : H ⊔ E = L) (hinf : H ⊓ E = ⊥)
    (hHbot : H ≠ ⊥) (hEbot : E ≠ ⊥)
    (hCfree : ∀ u ∈ E, u ≠ 1 → H ⊓ centralizer ({u} : Set G) = ⊥)
    (hstab : ∀ g : G, (fun x => g⁻¹ * x * g) '' ((H : Set G) \ {1}) = (H : Set G) \ {1} ↔ g ∈ L)
    (hTIor : ∀ g : G, (fun x => g⁻¹ * x * g) '' ((H : Set G) \ {1}) = (H : Set G) \ {1} ∨
      (fun x => g⁻¹ * x * g) '' ((H : Set G) \ {1}) ∩ ((H : Set G) \ {1}) = ∅) :
    IsCoherent (indFam (H.subgroupOf L) (nonprincipalIrr ↥(H.subgroupOf L)))
      ((SibleyNilpotentCoherence.isTIWithNormalizer_sdiff hHbot hstab hTIor).indCharSpanZeroHom
        (SibleyNilpotentCoherence.charSpanZero_le_dadeZDomain_sdiff (E := E) hHL hEL hnormH hsup
          hinf hHbot hCfree)) :=
  isCoherent_indFam_nonprincipalIrr (E := E) hLodd hHL hEL hnormH hsup hinf hHbot hEbot hCfree
    hstab hTIor _ (IsTIWithNormalizer.coe_indCharSpanZeroHom _ _)

end SibleySolvableCoherence

end CFSG.FeitThompson

end
