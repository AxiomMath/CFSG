module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IR5A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IZ3E

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {X : Type} [Group X] [Finite X] (N : Subgroup X) [N.Normal]

theorem z4i_Qf_lift (hN : Odd (Nat.card N)) {P Q : Subgroup X} (hP : IsPGroup 2 P) (hQP : Q ≤ P)
    (h : z4iQf (P.map (z4iπ N)) = Q.map (z4iπ N)) : z4iQf P = Q := by
  have hker : Odd (Nat.card (z4iπ N).ker) := by rw [z4iπ_ker]; exact hN
  have hψ : Function.Injective ((z4iπ N).comp P.subtype) :=
    CFSG.RankThree.OddKernel.injective_restrict_of_odd (z4iπ N) hker hP
  have hrange : ((z4iπ N).comp P.subtype).range = P.map (z4iπ N) := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_map, Subgroup.map_top, Subgroup.range_subtype]
  have hQfmap : (z4iQf P).map (z4iπ N) = z4iQf (P.map (z4iπ N)) := by
    rw [z4iQf_subtype, Subgroup.map_map, ← hrange, z4iQf_range _ hψ]
  have hle : z4iQf P ≤ P := by
    rw [z4iQf_subtype]
    exact Subgroup.map_subtype_le _
  exact z4i_eq_of_map_eq N hN hP hle hQP (by rw [hQfmap, h])

theorem z4i_index_two_lift (hN : Odd (Nat.card N)) {P : Subgroup X} (hP : IsPGroup 2 P)
    {M : Subgroup (X ⧸ N)} (hMP : M ≤ P.map (z4iπ N))
    (hM2 : M.relIndex (P.map (z4iπ N)) = 2) :
    ∃ M' : Subgroup X, M' ≤ P ∧ M'.relIndex P = 2 ∧ M'.map (z4iπ N) = M := by
  let M' : Subgroup X := P ⊓ M.comap (z4iπ N)
  have hM'le : M' ≤ P := inf_le_left
  have hM'2 : IsPGroup 2 M' := hP.to_le hM'le
  have hmap : M'.map (z4iπ N) = M := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · intro y hy
      obtain ⟨p, hp, hpe⟩ := hMP hy
      exact ⟨p, ⟨hp, Subgroup.mem_comap.mpr (by rw [hpe]; exact hy)⟩, hpe⟩
  have hcardP : Nat.card (P.map (z4iπ N)) = Nat.card P := z4i_card_map N hN hP
  have hcardM' : Nat.card (M'.map (z4iπ N)) = Nat.card M' := z4i_card_map N hN hM'2
  have hcard : Nat.card M = Nat.card M' := by rw [← hmap, hcardM']
  have hrel1 : M.relIndex (P.map (z4iπ N)) * Nat.card M = Nat.card P := by
    have hrc := Subgroup.relIndex_mul_card (H := M) (K := P.map (z4iπ N))
    rw [inf_of_le_left hMP, hcardP] at hrc
    exact hrc
  have hrel2 : M'.relIndex P * Nat.card M' = Nat.card P := by
    have hrc := Subgroup.relIndex_mul_card (H := M') (K := P)
    rw [inf_of_le_left hM'le] at hrc
    exact hrc
  have h2 : 2 * Nat.card M' = Nat.card P := by
    rw [hM2, hcard] at hrel1
    exact hrel1
  have hpos : 0 < Nat.card M' := Nat.card_pos_iff.mpr ⟨⟨1⟩, inferInstance⟩
  refine ⟨M', hM'le, ?_, hmap⟩
  exact Nat.eq_of_mul_eq_mul_right hpos (by rw [hrel2, h2])

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
