module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj

public section

namespace CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523

open Subgroup CFSG

theorem le_sup_inf_centralizer_commutator {H : Type*} [Group H] [Finite H] (S E : Subgroup H)
    (hS2 : IsPGroup 2 S) (hE3 : IsPGroup 3 E) (hEN : E ≤ normalizer (S : Set H)) :
    S ≤ (S ⊓ centralizer (E : Set H)) ⊔ ⁅S, E⁆ := by
  have : Subgroup.Normalizes E S := ⟨hEN⟩
  have hsolv : Group.IsSolvable S := by
    have := hS2.isNilpotent
    infer_instance
  have hcop : Nat.Coprime (Nat.card E) (Nat.card S) := by
    obtain ⟨a, ha⟩ := hE3.exists_card_eq
    obtain ⟨b, hb⟩ := hS2.exists_card_eq
    rw [ha, hb]
    exact Nat.Coprime.pow _ _ (by norm_num)
  have htop := fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime
    (G := ↥S) (A := ↥E) hsolv hcop
  have hfix := fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn S E hEN
  have hcomm := commutatorAction_subgroup_conj_map_eq_commutator S E hEN
  have hmap := congrArg (fun T : Subgroup S => T.map S.subtype) htop
  simp only [Subgroup.map_sup] at hmap
  rw [hfix, hcomm, Subgroup.map_subgroupOf_eq_of_le (by
    intro x hx; exact hx.1), ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmap
  exact hmap.symm.le

end CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523
