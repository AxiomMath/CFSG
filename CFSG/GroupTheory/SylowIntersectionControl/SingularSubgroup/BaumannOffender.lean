module

public import CFSG.GroupTheory.SylowIntersectionControl.SingularSubgroup.Centralizer
import CFSG.Quasithin.Background.B2FactorizationOffender
import CFSG.Quasithin.Background.C1GNNotation
import CFSG.Quasithin.Background.SmithC27Setup
import CFSG.HardMathSupport.RichardWeiss.Proving.EqualityOffender

public section

namespace CFSG.GroupTheory.GomiThm45Counterexample

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {Ω : Type} [Group Ω] [Finite Ω] {c : GNPairChoice Ω} {G S : Subgroup Ω}

private theorem sInf_centralizer_eq_pCoreOf_g45lb (h : GomiThm45Counterexample c G S) :
    S ⊓ Subgroup.centralizer (gomiV G : Set Ω) = pCoreOf 2 G := by
  have hQS : pCoreOf 2 G ≤ S :=
    CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf h.isSylowTwoOf
  have hQC : pCoreOf 2 G ≤ Subgroup.centralizer (gomiV G : Set Ω) :=
    CFSG.Quasithin.SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf G
  refine le_antisymm ?_ (le_inf hQS hQC)
  intro x hx
  exact inf_centralizer_inf_le_pCoreOf h ⟨⟨h.isSylowTwoOf.1 hx.1, hx.2⟩, hx.1⟩

private theorem inf_centralizer_eq_inf_pCoreOf_g45lb (h : GomiThm45Counterexample c G S)
    {A : Subgroup Ω} (hAS : A ≤ S) :
    A ⊓ Subgroup.centralizer (gomiV G : Set Ω) = A ⊓ pCoreOf 2 G := by
  conv_rhs => rw [← sInf_centralizer_eq_pCoreOf_g45lb h, ← inf_assoc,
    inf_eq_left.mpr hAS]

private theorem relIndex_centralizer_eq_relIndex_pCoreOf_g45lb
    (h : GomiThm45Counterexample c G S) {A : Subgroup Ω} (hAS : A ≤ S) :
    (Subgroup.centralizer (gomiV G : Set Ω)).relIndex A = (pCoreOf 2 G).relIndex A := by
  rw [← Subgroup.inf_relIndex_right (H := Subgroup.centralizer (gomiV G : Set Ω)) (K := A),
    ← Subgroup.inf_relIndex_right (H := pCoreOf 2 G) (K := A),
    inf_comm (Subgroup.centralizer (gomiV G : Set Ω)) A, inf_comm (pCoreOf 2 G) A,
    inf_centralizer_eq_inf_pCoreOf_g45lb h hAS]

theorem pCoreOf_sup_eq_of_relIndex_eq (h : GomiThm45Counterexample c G S) {A : Subgroup Ω}
    (hAS : A ≤ S)
    (hrel : (Subgroup.centralizer (gomiV G : Set Ω)).relIndex A =
      (Subgroup.centralizer (gomiV G : Set Ω)).relIndex S) :
    pCoreOf 2 G ⊔ A = S := by
  have hQS : pCoreOf 2 G ≤ S :=
    CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf h.isSylowTwoOf
  have hQAS : pCoreOf 2 G ⊔ A ≤ S := sup_le hQS hAS
  have hAnorm : A ≤ Subgroup.normalizer (pCoreOf 2 G : Set Ω) :=
    hAS.trans (h.isSylowTwoOf.1.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G))
  have hsup : (pCoreOf 2 G).relIndex (pCoreOf 2 G ⊔ A) = (pCoreOf 2 G).relIndex A := by
    have h0 := CFSG.Quasithin.B2F.relIndex_sup_eq_of_le_normalizer'
      (D := pCoreOf 2 G) (T := A) hAnorm
    rwa [sup_comm] at h0
  have hrelA : (Subgroup.centralizer (gomiV G : Set Ω)).relIndex A =
      (pCoreOf 2 G).relIndex A :=
    relIndex_centralizer_eq_relIndex_pCoreOf_g45lb h hAS
  have hrelS : (Subgroup.centralizer (gomiV G : Set Ω)).relIndex S =
      (pCoreOf 2 G).relIndex S :=
    relIndex_centralizer_eq_relIndex_pCoreOf_g45lb h le_rfl
  have hQSA : (pCoreOf 2 G).relIndex S = (pCoreOf 2 G).relIndex (pCoreOf 2 G ⊔ A) := by
    rw [← hrelS, ← hrel, hrelA, ← hsup]
  have hmul := Subgroup.relIndex_mul_relIndex (H := pCoreOf 2 G)
    (K := pCoreOf 2 G ⊔ A) (L := S) le_sup_left hQAS
  have hone : (pCoreOf 2 G ⊔ A).relIndex S = 1 := by
    have hpos : 0 < (pCoreOf 2 G).relIndex (pCoreOf 2 G ⊔ A) :=
      Nat.pos_of_dvd_of_pos
        (Subgroup.relIndex_dvd_card (pCoreOf 2 G) (pCoreOf 2 G ⊔ A)) Nat.card_pos
    have hm : (pCoreOf 2 G ⊔ A).relIndex S *
        (pCoreOf 2 G).relIndex (pCoreOf 2 G ⊔ A) =
        1 * (pCoreOf 2 G).relIndex (pCoreOf 2 G ⊔ A) := by
      calc (pCoreOf 2 G ⊔ A).relIndex S * (pCoreOf 2 G).relIndex (pCoreOf 2 G ⊔ A)
          = (pCoreOf 2 G).relIndex (pCoreOf 2 G ⊔ A) *
              (pCoreOf 2 G ⊔ A).relIndex S := mul_comm _ _
        _ = (pCoreOf 2 G).relIndex S := hmul
        _ = (pCoreOf 2 G).relIndex (pCoreOf 2 G ⊔ A) := hQSA
        _ = 1 * (pCoreOf 2 G).relIndex (pCoreOf 2 G ⊔ A) := (one_mul _).symm
    exact Nat.eq_of_mul_eq_mul_right hpos hm
  exact le_antisymm hQAS (Subgroup.relIndex_eq_one.mp hone)

theorem isMaxElemAbelian_gomiV_sup (h : GomiThm45Counterexample c G S) {A : Subgroup Ω}
    (hA : IsMaxElemAbelian S A)
    (hrel : (Subgroup.centralizer (gomiV G : Set Ω)).relIndex A =
      (Subgroup.centralizer (A : Set Ω)).relIndex (gomiV G)) :
    IsMaxElemAbelian S (gomiV G ⊔ (pCoreOf 2 G ⊓ A)) := by
  have hmax := CFSG.HardMathSupport.RichardWeiss.Proving.isMaxElemAbelian_sup_of_relIndex_le hA
    (gomiV_moduleSetting G).1 (gomiV_le_sylow h)
    (by rw [Subgroup.inf_relIndex_left, Subgroup.inf_relIndex_left]; exact hrel.le)
  rwa [inf_centralizer_eq_inf_pCoreOf_g45lb h hA.1, inf_comm A, sup_comm (pCoreOf 2 G ⊓ A)]
    at hmax

theorem gomiV_inf_centralizer_le (h : GomiThm45Counterexample c G S) :
    gomiV G ⊓ Subgroup.centralizer (S : Set Ω) ≤ omegaOneCenterOf (thompsonJ S) :=
  (inf_le_inf_left (gomiV G) (Subgroup.centralizer_le
    (SetLike.coe_subset_coe.mpr (CFSG.Quasithin.C1GN.thompsonJ_le S)))).trans
    (CFSG.Quasithin.inf_centralizer_thompsonJ_le (gomiV_moduleSetting G).1 (gomiV_le_sylow h))

end CFSG.GroupTheory.GomiThm45Counterexample
