module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ChiefFactors.Core
public import CFSG.Milestones.OO_odd_order_solvable
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalOddPSubgroupAlternating
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalOddPSubgroupPGL2
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalOddPSubgroupSymmetricFour
public import CFSG.Assembly.Defs

public noncomputable section

namespace CFSG.DihedralBlueprint

open GorensteinWalter

universe u

variable {G : Type u} [Group G] [Finite G]

theorem normal_odd_eq_bot_of_no_normal_oddP
    (hprime : ∀ (p : ℕ), p.Prime → Odd p → ∀ P : Subgroup G,
      P.Normal → IsPGroup p P → P = ⊥)
    (N : Subgroup G) (hnormal : N.Normal) (hodd : Odd (Nat.card N)) : N = ⊥ := by
  by_contra hne
  obtain ⟨M, hMnormal, hMN, hMne, hmin⟩ := exists_minimal_normal_le N hnormal hne
  let : M.Normal := hMnormal
  let : IsMinimalNormal M := ⟨fun K hKnormal hKM => by
    by_cases hK : K = ⊥
    · exact Or.inl hK
    · exact Or.inr (hmin K hKnormal hKM hK)⟩
  have hModd : Odd (Nat.card M) := hodd.of_dvd_nat (Subgroup.card_dvd_of_le hMN)
  let : Group.IsSolvable M := CFSG.Milestones.odd_order_solvable hModd
  obtain ⟨p, hp, helem⟩ := minimalNormal_solvable_exists_isElementaryAbelian M
  let : IsElementaryAbelian p M := helem
  let : Fact p.Prime := ⟨hp⟩
  have hMp : IsPGroup p M := IsElementaryAbelian.isPGroup p M
  have hpdvd : p ∣ Nat.card M := by
    rcases hMp.card_eq_or_dvd with hcard | hdvd
    · exact (hMne ((Subgroup.eq_bot_iff_card M).mpr hcard)).elim
    · exact hdvd
  have hpodd : Odd p := hModd.of_dvd_nat hpdvd
  exact hMne (hprime p hp hpodd M hMnormal hMp)

theorem normal_odd_eq_bot_of_aFour_model
    (he : Nonempty (G ≃* alternatingGroup (Fin 4)))
    (N : Subgroup G) (hnormal : N.Normal) (hodd : Odd (Nat.card N)) : N = ⊥ := by
  apply normal_odd_eq_bot_of_no_normal_oddP _ N hnormal hodd
  intro p hp hpodd P hPnormal hPp
  exact GorensteinWalter.normal_pSubgroup_eq_bot_of_mulEquiv_alternatingGroup_four
    he p hp hpodd P hPnormal hPp

theorem normal_odd_eq_bot_of_sFour_model
    (he : Nonempty (G ≃* Equiv.Perm (Fin 4)))
    (N : Subgroup G) (hnormal : N.Normal) (hodd : Odd (Nat.card N)) : N = ⊥ := by
  apply normal_odd_eq_bot_of_no_normal_oddP _ N hnormal hodd
  intro p hp hpodd P hPnormal hPp
  exact GorensteinWalter.normal_pSubgroup_eq_bot_of_mulEquiv_perm_four
    he p hp hpodd P hPnormal hPp

theorem normal_odd_eq_bot_of_alternating_model {n : ℕ} (hn : 5 ≤ n)
    (he : Nonempty (G ≃* alternatingGroup (Fin n)))
    (N : Subgroup G) (hnormal : N.Normal) (hodd : Odd (Nat.card N)) : N = ⊥ := by
  apply normal_odd_eq_bot_of_no_normal_oddP _ N hnormal hodd
  intro p hp hpodd P hPnormal hPp
  exact GorensteinWalter.normal_pSubgroup_eq_bot_of_mulEquiv_alternatingGroup
    hn he p hp hpodd P hPnormal hPp

open scoped MatrixGroups

theorem normal_odd_eq_bot_of_psl2_model (K : Type u) [Field K] [Finite K]
    (hK : GorensteinWalter.IsOddPrimePower (Nat.card K))
    (e : G ≃* PSL2 K)
    (N : Subgroup G) (hnormal : N.Normal) (hodd : Odd (Nat.card N)) : N = ⊥ := by
  apply normal_odd_eq_bot_of_no_normal_oddP _ N hnormal hodd
  intro p hp hpodd P hPnormal hPp
  have hmap := GorensteinWalter.normal_pSubgroup_eq_bot_of_psl2_odd K hK p hp hpodd
    (P.map e.toMonoidHom) (hPnormal.map e.toMonoidHom e.surjective)
    (hPp.map e.toMonoidHom)
  exact (Subgroup.map_eq_bot_iff_of_injective P e.injective).mp hmap

theorem normal_odd_eq_bot_of_pgl2_model (K : Type u) [Field K] [Finite K]
    (hK : GorensteinWalter.IsOddPrimePower (Nat.card K))
    (e : G ≃* PGL2 K)
    (N : Subgroup G) (hnormal : N.Normal) (hodd : Odd (Nat.card N)) : N = ⊥ := by
  apply normal_odd_eq_bot_of_no_normal_oddP _ N hnormal hodd
  intro p hp hpodd P hPnormal hPp
  have hmap := GorensteinWalter.normal_pSubgroup_eq_bot_of_pgl2_odd K hK p hp hpodd
    (P.map e.toMonoidHom) (hPnormal.map e.toMonoidHom e.surjective)
    (hPp.map e.toMonoidHom)
  exact (Subgroup.map_eq_bot_iff_of_injective P e.injective).mp hmap

end CFSG.DihedralBlueprint
