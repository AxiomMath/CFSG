module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS10I1416QPerm
public import CFSG.Alternating.Multipliers.Main
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ProvedRows

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open

theorem card_le_sixteen_of_alt {n : ℕ} (hn : n ≤ 8) (F : Subgroup (alternatingGroup (Fin n)))
    (hF : IsElemAbelian 2 F) : Nat.card F ≤ 16 := by
  have hG : IsElemAbelian 2 (F.map (alternatingGroup (Fin n)).subtype) :=
    CFSG.SectionRank.isElemAbelian_map hF _
  have hc : Nat.card (F.map (alternatingGroup (Fin n)).subtype) = Nat.card F :=
    Subgroup.card_map_of_injective (alternatingGroup (Fin n)).subtype_injective
  have h := card_sq_le_perm_elemAb (Fin n) _ hG
  have hfin : Nat.card (Fin n) = n := Nat.card_eq_fintype_card.trans (Fintype.card_fin n)
  rw [hc, hfin] at h
  have h256 : 2 ^ n ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) hn
  by_contra hcon
  have h17 : 17 ≤ Nat.card F := by omega
  have : 17 ^ 2 ≤ Nat.card F ^ 2 := Nat.pow_le_pow_left h17 2
  norm_num at h256 this
  omega

theorem griess_card_alt_five :
    Nat.card (CFSG.Open.griessHopfMultiplier (alternatingGroup (Fin 5))) = 2 :=
  (CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.card_hopfMultiplier_eq_card_griessHopfMultiplier
    _).symm.trans (CFSG.Alternating.Multipliers.hopfMultiplier_alternatingGroup_five).2

theorem griess_card_alt_six :
    Nat.card (CFSG.Open.griessHopfMultiplier (alternatingGroup (Fin 6))) = 6 :=
  (CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.card_hopfMultiplier_eq_card_griessHopfMultiplier
    _).symm.trans (CFSG.Alternating.Multipliers.hopfMultiplier_alternatingGroup_six).2

theorem griess_card_alt_eight :
    Nat.card (CFSG.Open.griessHopfMultiplier (alternatingGroup (Fin 8))) = 2 :=
  (CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.card_hopfMultiplier_eq_card_griessHopfMultiplier
    _).symm.trans (CFSG.Alternating.Multipliers.card_hopfMultiplier_alternatingGroup (by norm_num))

theorem twoRank_lt_six_of_alt {J : Type} [Group J] [Finite J] (hJ : Group.IsPerfect J) {n : ℕ}
    (hn : n ≤ 8) {m : ℕ} (hm : Odd m)
    (e : J ⧸ Subgroup.center J ≃* alternatingGroup (Fin n))
    (hZ : Nat.card (Subgroup.center J) ∣ 2 * m) : twoRank J < 6 := by
  refine twoRank_lt_six_of_center_quotient hJ hm hZ (fun F hF => ?_)
  have hF' : IsElemAbelian 2 (F.map e.toMonoidHom) := CFSG.SectionRank.isElemAbelian_map hF _
  have hc : Nat.card (F.map e.toMonoidHom) = Nat.card F :=
    Subgroup.card_map_of_injective e.injective
  rw [← hc]
  exact card_le_sixteen_of_alt hn _ hF'

end CFSG.LocalAnalysis.GLTheoremA

end
