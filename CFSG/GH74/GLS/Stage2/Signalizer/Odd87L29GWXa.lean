module

public import CFSG.GH74.GLS.Stage2.Local.Defs
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29Burnside
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87.L29GW

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local CFSG.GorensteinWalter

theorem pPrimeCore_eq_bot_of_normal {D : Type} [Group D] [Finite D] (hO : pPrimeCore 2 D = ⊥)
    (M : Subgroup D) [M.Normal] : pPrimeCore 2 ↥M = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [pPrimeCore_eq_bot_iff] at hO
  have hN : ((pPrimeCore 2 ↥M).map M.subtype).Normal := inferInstance
  have h := hO _ hN (by
    rw [Subgroup.card_map_of_injective M.subtype_injective]
    exact pPrimeCore_coprime_card)
  exact (Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective).1 h

theorem isSolvable_of_cyclic_sylow_two {M : Type} [Group M] [Finite M] (S : Sylow 2 M)
    (hS : IsCyclic ↥S) : Group.IsSolvable M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨N, hN, hodd, j, hj⟩ := L29Burnside.exists_normal_two_compl_of_cyclic S hS
  have hsolN : Group.IsSolvable ↥N := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hq : IsPGroup 2 (M ⧸ N) := IsPGroup.of_card (n := j) (by rw [← Subgroup.index, hj])
  have : Group.IsNilpotent (M ⧸ N) := hq.isNilpotent
  have : Group.IsSolvable (M ⧸ N) := inferInstance
  exact Group.isSolvable_of_subgroup_quotient N

theorem hasDihedralSylowTwo_of_cyclic_or_dihedral {M : Type} [Group M] [Finite M]
    (hns : ¬ Group.IsSolvable M) (hS : ∀ S : Sylow 2 M, IsCyclic ↥S ∨ IsDihedral ↥S) :
    HasDihedralSylowTwo M := by
  intro S
  have hd : IsDihedral ↥S :=
    (hS S).resolve_left fun hc => hns (isSolvable_of_cyclic_sylow_two S hc)
  obtain ⟨_, k, -, hk, ⟨e⟩⟩ := hd
  obtain ⟨a, ha⟩ := S.isPGroup'.exists_card_eq
  have hcard : 2 ^ a = 2 * k := by
    rw [← ha]
    exact (Nat.card_congr e.toEquiv).trans DihedralGroup.nat_card
  cases a with
  | zero => omega
  | succ b =>
    rw [pow_succ] at hcard
    generalize hp : 2 ^ b = t at hcard
    have hkt : k = t := by omega
    subst hkt
    have hb : 1 ≤ b := by
      rcases Nat.eq_zero_or_pos b with rfl | hb
      · simp at hp
        omega
      · exact hb
    exact ⟨b, hb, ⟨hp ▸ e⟩⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87.L29GW
