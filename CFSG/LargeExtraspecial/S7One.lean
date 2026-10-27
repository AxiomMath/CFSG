module

public import CFSG.LargeExtraspecial.S7Basic
public import CFSG.LargeExtraspecial.S6SixC
public import CFSG.LargeExtraspecial.S6SixB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S7

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem finrank_commSpace_eq (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) :
    finrank (ZMod 2) (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) =
      finrank (ZMod 2) (Tt S g t) + finrank (ZMod 2) (Vt S g t) := by
  obtain ⟨e, -⟩ := timmesfeld_6_6_three H ht ht1
  set U := commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) with hU
  have h1 := e.finrank_eq
  rw [Subspace.dual_finrank_eq] at h1
  have h2 := Submodule.finrank_quotient_add_finrank ((Tt S g t).comap U.subtype)
  have h3 : finrank (ZMod 2) ((Tt S g t).comap U.subtype) = finrank (ZMod 2) (Tt S g t) :=
    (Submodule.comapSubtypeEquivOfLe Tt_le_commSpace).finrank_eq
  omega

theorem timmesfeld_7_1 (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hN : Nbar S g t = zpowers t) (hL : LinCase S g ht) :
    False := by
  have hn := width_eq_of_linCase H C ht ht1 hN hL
  have hm := hL.two_le_finrank
  have hT := Submodule.finrank_mono (Vt_le_Tt H hNo ht1 hL)
  have hU := finrank_commSpace_eq H ht ht1
  have htt : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) * (t : S.Qt ≃ₗ[ZMod 2] S.Qt) = 1 :=
    congrArg Subtype.val (mul_self_of_mem_Lbar S H.conj_mem ht)
  have h2 := two_mul_finrank_commSpace_le htt
  have hQ := S.finrank_Qt_eq_two_mul_width
  omega

end CFSG.LargeExtraspecial.S7
