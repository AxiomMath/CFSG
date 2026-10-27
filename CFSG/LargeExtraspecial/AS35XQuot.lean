module

public import CFSG.LargeExtraspecial.AS35XBasic
public import CFSG.LargeExtraspecial.AS35XGen

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.RankThree.OrthogonalInvolutions

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem center_noInvol_X : ∀ c ∈ center S.LbarAsc, c * c = 1 → c = 1 :=
  fun _ hc hcc => eq_one_of_mem_center_X hc hcc

theorem mul_self_X {d : S.LbarAsc} (hd : (d : S.O) ∈ S.DbarAsc) : d * d = 1 :=
  Subtype.ext (mul_self_of_mem_DbarAsc_X hd)

theorem transpositionData_X (hS : S.SixHyp) (hst : S.Asc512Standing) {d : S.O}
    (hd : d ∈ S.DbarAsc) :
    S12TranspositionData (⊤ : Subgroup (S.LbarAsc ⧸ center S.LbarAsc)) S.EhatAsc
      (QuotientGroup.mk' (center S.LbarAsc) ⟨d, subset_closure hd⟩) := by
  refine AS35X.transpositionData center_noInvol_X closure_closure_coe_preimage hd
    (fun e he => ?_) (fun x e he => ?_) (fun e he => mul_self_X he) (fun e he h => ?_)
    (fun a ha b hb => ?_) (fun a ha b hb h4 => ?_)
  · obtain ⟨x, hx, hxe⟩ := hst.conj d hd e he
    exact ⟨⟨x, hx⟩, Subtype.ext hxe⟩
  · exact S.conj_mem_DbarAsc_L (LbarAsc_le_Mbar_X x.2) he
  · exact (isTypeA_of_mem_DbarAsc_X hS he).2.1 (by rw [h]; rfl)
  · rw [← Subgroup.orderOf_coe, Subgroup.coe_mul]
    exact orderOf_mul_le_four_X hS ha hb
  · rw [← Subgroup.orderOf_coe, Subgroup.coe_mul] at h4
    show ((a * b) ^ 2 : S.LbarAsc).1 ∈ S.DbarAsc
    rw [Subgroup.coe_pow, Subgroup.coe_mul]
    exact sq_mem_DbarAsc_X hS ha hb h4

theorem EhatAsc_eq_isConj_X (hS : S.SixHyp) (hst : S.Asc512Standing) {d : S.O}
    (hd : d ∈ S.DbarAsc) :
    S.EhatAsc = {g | IsConj (QuotientGroup.mk' (center S.LbarAsc) ⟨d, subset_closure hd⟩) g} := by
  have hD := transpositionData_X hS hst hd
  ext τ
  simp only [Set.mem_ofPred_eq, isConj_iff]
  constructor
  · intro hτ
    obtain ⟨x, -, hx⟩ := hD.cls τ hτ
    exact ⟨x, hx.symm⟩
  · rintro ⟨c, rfl⟩
    exact hD.conj c (mem_top c) _ hD.mem

end Setting

end CFSG.LargeExtraspecial
