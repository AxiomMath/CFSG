module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitQuot0
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitBlock
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z A : Subgroup X} [Z.Normal]

theorem lit_solvable_litC (h : LitCtx Z A) : Group.IsSolvable ↥(litC Z A) := by
  have hA : A ≤ litC Z A := lit_A_le_litC h
  haveI hAn : (A.subgroupOf (litC Z A)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hA]
    intro a c ha hc
    rw [mem_litC] at hc
    exact (Subgroup.mem_normalizer_iff.mp hc.1 a).mp ha
  haveI hsolA : Group.IsSolvable ↥(A.subgroupOf (litC Z A)) := by
    haveI : Group.IsNilpotent ↥(A.subgroupOf (litC Z A)) :=
      (h.isPGroup_A.of_equiv (Subgroup.subgroupOfEquivOfLe hA).symm).isNilpotent
    infer_instance
  haveI hsolQ : Group.IsSolvable (↥(litC Z A) ⧸ A.subgroupOf (litC Z A)) := by
    apply CFSG.FeitThompson.isSolvable_of_odd_natCard _
    refine Nat.not_even_iff_odd.mp (fun he => h.sylow ?_)
    exact even_iff_two_dvd.mp he
  refine Group.isSolvable_of_ker_le_range (A.subgroupOf (litC Z A)).subtype
    (QuotientGroup.mk' (A.subgroupOf (litC Z A))) ?_
  rw [QuotientGroup.ker_mk', Subgroup.range_subtype]

theorem lit_T_solvable (h : LitCtx Z A) {T : Subgroup X}
    (hT : IsQuotIso T (T ⊓ litC Z A) ↥blockStab) : Group.IsSolvable ↥T := by
  obtain ⟨_, φ, hsurj, hker⟩ := hT
  haveI hsolC : Group.IsSolvable ↥(litC Z A) := lit_solvable_litC h
  haveI hinf : Group.IsSolvable ↥(T ⊓ litC Z A) :=
    Group.isSolvable_of_surjective
      (f := (Subgroup.subgroupOfEquivOfLe
        (inf_le_right : T ⊓ litC Z A ≤ litC Z A)).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe
        (inf_le_right : T ⊓ litC Z A ≤ litC Z A)).surjective
  haveI hker_sol : Group.IsSolvable ↥φ.ker := by
    rw [hker]
    exact Group.isSolvable_of_surjective
      (f := (Subgroup.subgroupOfEquivOfLe
        (inf_le_left : T ⊓ litC Z A ≤ T)).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe
        (inf_le_left : T ⊓ litC Z A ≤ T)).symm.surjective
  haveI : Group.IsSolvable ↥blockStab := lit_isSolvable_blockStab
  refine Group.isSolvable_of_ker_le_range φ.ker.subtype φ ?_
  rw [Subgroup.range_subtype]

theorem lit_T_card (h : LitCtx Z A) {T : Subgroup X} (hTN : T ≤ normalizer (A : Set X))
    (hT : IsQuotIso T (T ⊓ litC Z A) ↥blockStab) : 72 ∣ (litP Z).relIndex T := by
  obtain ⟨_, φ, hsurj, hker⟩ := hT
  have hrel : (T ⊓ litC Z A).relIndex T = 72 := by
    change ((T ⊓ litC Z A).subgroupOf T).index = 72
    rw [← hker, Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective φ hsurj,
      Nat.card_congr (Subgroup.topEquiv (G := ↥blockStab)).toEquiv]
    exact lit_card_blockStab
  have hKL : T ⊓ litP Z ≤ T ⊓ litC Z A := by
    intro x hx
    rw [Subgroup.mem_inf] at hx ⊢
    exact ⟨hx.1, (lit_normalizer_inf_litP_le h) ⟨hTN hx.1, hx.2⟩⟩
  have htower := Subgroup.relIndex_mul_relIndex (H := T ⊓ litP Z)
    (K := T ⊓ litC Z A) (L := T) hKL inf_le_left
  rw [← Subgroup.inf_relIndex_right (H := litP Z) (K := T), inf_comm]
  rw [← htower, hrel]
  exact dvd_mul_left 72 _

end CFSG.OddStandard.HigherRank.YamadaG23
