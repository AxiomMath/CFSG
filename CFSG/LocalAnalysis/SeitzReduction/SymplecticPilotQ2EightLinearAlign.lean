module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphAlign

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear)
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] {N : ℕ}
  {hK : Nat.card K = 2} {e : L ≃* StatedSp N K}

theorem q2Coord_plane_ne_radical (p : Fin N) :
    q2Coord N 1 (Sum.inl (Sum.inl p)) ≠ q2Coord N 1 (Sum.inr 0) := fun h =>
  Sum.inl_ne_inr ((q2Coord N 1).injective h)

theorem q2Graph_transvection_radical_ne [CharP K 2] (hK : Nat.card K = 2) (p : Fin N) :
    q2Graph 1 hK (SpecialLinearGroup.transvection (q2Coord_plane_ne_radical p) (1 : K)) ≠
      SpecialLinearGroup.transvection (q2Coord_plane_ne_radical p) (1 : K) := by
  set a := q2Coord N 1 (Sum.inl (Sum.inl p)) with ha
  set b := q2Coord N 1 (Sum.inr 0) with hb
  have hab : a ≠ b := q2Coord_plane_ne_radical p
  intro h
  have h1 := congrArg (fun z : SpecialLinearGroup (Fin (2 * N + 1)) K =>
    (z : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K) a b) h
  have hinv : (SpecialLinearGroup.transvection hab (1 : K))⁻¹ =
      SpecialLinearGroup.transvection hab 1 :=
    inv_eq_of_mul_eq_one_right (q2Transvection_one_mul_self hab)
  rw [coe_q2Graph, hinv, q2GramMat_mul_mul_apply, transpose_apply,
    SpecialLinearGroup.transvection_coe] at h1
  have hpa : q2Par N 1 a = q2Coord N 1 (Sum.inl (Sum.inr p)) := by
    rw [ha, q2Par_q2Coord]; rfl
  have hpb : q2Par N 1 b = b := by
    rw [hb, q2Par_q2Coord]; rfl
  rw [hpa, hpb] at h1
  simp only [Matrix.add_apply, single_apply, Matrix.one_apply,
    (q2Coord N 1).injective.eq_iff, ha, hb] at h1
  simp at h1

theorem transvection_radical_mem_q2Block {p : Fin N} {R : Finset (Fin N)} (hp : p ∉ R) :
    SpecialLinearGroup.transvection (q2Coord_plane_ne_radical p) (1 : K) ∈ q2Block 1 K R := by
  refine LinearPilot.transvection_mem_blockSpecialLinear _ ?_ ?_ 1
  · rw [Finset.mem_compl, q2Coord_mem_planeCoordsQ2]
    exact hp
  · rw [Finset.mem_compl, q2Coord_mem_planeCoordsQ2]
    exact not_inPlanes_inr R 0

theorem exists_nsLinParamAgree_odd [CharP K 2] (hN : 4 ≤ N)
    (P : ∀ k : Fin N, NsLinParam hK 1 e k) :
    ∃ Q : ∀ k : Fin N, NsLinParam hK 1 e k, NsLinParamAgree Q := by
  classical
  have hcomp := fun {k l : Fin N} (R : NsLinParam hK 1 e k) (R' : NsLinParam hK 1 e l)
      (hkl : k ≠ l) => NsLinParam.eq_or_eq_q2Graph_of_overlap le_rfl hN hkl R R'
  set o : Fin N := ⟨0, by omega⟩ with ho
  let Ag : ∀ k : Fin N, NsLinParam hK 1 e k → Prop := fun k R =>
    ∀ (x : SpecialLinearGroup (Fin (2 * N + 1)) K) (hx : x ∈ q2Block 1 K {k, o}),
      R.Φ ⟨x, q2Block_pair_le_left k o hx⟩ = (P o).Φ ⟨x, q2Block_pair_le_right k o hx⟩
  let Q : ∀ k : Fin N, NsLinParam hK 1 e k := fun k =>
    if Ag k (P k) then P k else (P k).twist
  have hQoo : Q o = P o := by
    change (if Ag o (P o) then P o else (P o).twist) = P o
    exact ite_eq_left (fun x hx => rfl)
  have hQo : ∀ k : Fin N, Ag k (Q k) := by
    intro k
    by_cases h : Ag k (P k)
    · change Ag k (if Ag k (P k) then P k else (P k).twist)
      rw [ite_eq_left h]
      exact h
    · change Ag k (if Ag k (P k) then P k else (P k).twist)
      rw [ite_eq_right h]
      have hk : k ≠ o := by
        rintro rfl
        exact h fun x hx => rfl
      rcases hcomp (P k) (P o) hk with h1 | h1
      · exact absurd h1 h
      · intro x hx
        rw [NsLinParam.twist_Φ_apply]
        have hγx : q2Graph 1 hK x ∈ q2Block 1 K {k, o} := q2Graph_mem_q2Block hK hx
        have h2 := h1 _ hγx
        have h3 : (P o).Φ ⟨q2Graph 1 hK (q2Graph 1 hK x),
            q2Block_pair_le_right k o (q2Graph_mem_q2Block hK hγx)⟩ =
            (P o).Φ ⟨x, q2Block_pair_le_right k o hx⟩ :=
          congrArg (P o).Φ (Subtype.ext (by
            change q2Graph 1 hK (q2Graph 1 hK x) = x
            rw [← MulAut.mul_apply, q2Graph_mul_self, MulAut.one_apply]))
        rw [← h3, ← h2]
        rfl
  refine ⟨Q, fun k l x hx hx' => ?_⟩
  by_cases hkl : k = l
  · subst hkl
    rfl
  have hxkl : x ∈ q2Block 1 K {k, l} := mem_q2Block_pair hx hx'
  have hagreeo : ∀ {m : Fin N} (y : SpecialLinearGroup (Fin (2 * N + 1)) K)
      (hy : y ∈ q2Block 1 K {m}) (hy' : y ∈ q2Block 1 K {o}),
      (Q m).Φ ⟨y, hy⟩ = (P o).Φ ⟨y, hy'⟩ :=
    fun y hy hy' => hQo _ y (mem_q2Block_pair hy hy')
  by_cases hko' : k = o
  · subst hko'
    rw [hQoo] at *
    exact (hagreeo x hx' hx).symm
  by_cases hlo : l = o
  · subst hlo
    rw [hQoo]
    exact hagreeo x hx hx'
  rcases hcomp (Q k) (Q l) hkl with h1 | h1
  · exact h1 x hxkl
  · exfalso
    obtain ⟨p, hp⟩ : ({o, k, l}ᶜ : Finset (Fin N)).Nonempty := compl_triple_nonempty hN o k l
    simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hp
    set y := SpecialLinearGroup.transvection (q2Coord_plane_ne_radical (N := N) p) (1 : K)
      with hy
    have hyk : y ∈ q2Block 1 K {k} := transvection_radical_mem_q2Block (by simpa using hp.2.1)
    have hyl : y ∈ q2Block 1 K {l} := transvection_radical_mem_q2Block (by simpa using hp.2.2)
    have hyo : y ∈ q2Block 1 K {o} := transvection_radical_mem_q2Block (by simpa using hp.1)
    have hγy := fun {R : Finset (Fin N)} (h : y ∈ q2Block 1 K R) => q2Graph_mem_q2Block hK h
    have h2 := h1 y (mem_q2Block_pair hyk hyl)
    rw [hagreeo y hyk hyo, hagreeo _ (hγy hyl) (hγy hyo)] at h2
    have h3 := congrArg Subtype.val ((P o).injective h2)
    exact q2Graph_transvection_radical_ne hK p h3.symm

end CFSG.SeitzReduction.SymplecticPilot
