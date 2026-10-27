module

public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup

theorem cyclic_index_two_rank_bound {G : Type*} [Group G] [Finite G] {H : Subgroup G}
    (hH : IsCyclic H) (hind : H.index ≤ 2) : CFSG.pRank 2 G ≤ 2 := by
  have hpos : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hHn : H.Normal := by
    rcases (show H.index = 1 ∨ H.index = 2 by omega) with h | h
    · rw [Subgroup.index_eq_one] at h
      rw [h]
      infer_instance
    · exact Subgroup.normal_of_index_eq_two h
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  refine CFSG.SectionRank.pRank_le (by norm_num) fun E _ hE => ?_
  have h1 : Nat.card (H.subgroupOf E) ≤ 2 := by
    let φ : H.subgroupOf E →* H :=
      { toFun := fun x => ⟨(x : E), x.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hφ : Function.Injective φ := fun x y hxy => by
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : H => (z : G)) hxy
    have : IsCyclic (H.subgroupOf E) := isCyclic_of_injective φ hφ
    have hexp : Monoid.exponent (H.subgroupOf E) ∣ 2 :=
      Monoid.exponent_dvd_of_forall_pow_eq_one fun x => by
        apply Subtype.ext
        apply Subtype.ext
        simpa using hE.2 ((x : E) : G) (x : E).2
    rw [← IsCyclic.exponent_eq_card]
    exact Nat.le_of_dvd (by norm_num) hexp
  have h2 : (H.subgroupOf E).index ≤ 2 :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hpos) (relIndex_dvd_index_of_normal (H := H) (K := E))).trans
      hind
  have h3 := Subgroup.card_mul_index (H.subgroupOf E)
  calc Nat.card E = Nat.card (H.subgroupOf E) * (H.subgroupOf E).index := h3.symm
    _ ≤ 2 * 2 := Nat.mul_le_mul h1 h2
    _ = 2 ^ 2 := by norm_num

end CFSG.LocalAnalysis.ComponentInitial
