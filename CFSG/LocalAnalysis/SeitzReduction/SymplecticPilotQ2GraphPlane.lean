module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2RowPieces
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphModel

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear pairEmbed
  pairEmbed_apply)
open CFSG.LieType.Steinberg.Sp (blockMat)
open scoped MatrixGroups

variable {N ε : ℕ} {K : Type} [Field K]

theorem q2PlaneNe (p : Fin N) :
    q2Coord N ε (Sum.inl (Sum.inl p)) ≠ q2Coord N ε (Sum.inl (Sum.inr p)) := fun h =>
  Sum.inl_ne_inr (Sum.inl.inj ((q2Coord N ε).injective h))

theorem q2Embed_longBlock (hK : Nat.card K = 2) (p : Fin N) (A : SL(2, K)) :
    q2Embed ε hK (longBlock K N p A) = pairEmbed (q2PlaneNe (ε := ε) p) A := by
  apply Subtype.ext
  ext a b
  obtain ⟨w, rfl⟩ := (q2Coord N ε).surjective a
  obtain ⟨w', rfl⟩ := (q2Coord N ε).surjective b
  rw [q2Embed_apply_q2Coord, mat_longBlock, pairEmbed_apply]
  simp only [Finset.mem_insert, Finset.mem_singleton, (q2Coord N ε).injective.eq_iff]
  rcases w with (u | u) | e <;> rcases w' with (v | v) | e' <;>
    simp [blockMat, Matrix.one_apply, Sum.inl.injEq, Sum.inr.injEq] <;>
    by_cases h1 : u = p <;> by_cases h2 : v = p <;> simp_all [eq_comm]

theorem pairEmbed_sl2Upper {n : ℕ} {a b : Fin n} (hab : a ≠ b) (c : K) :
    pairEmbed hab (sl2Upper c) = SpecialLinearGroup.transvection hab c := by
  apply Subtype.ext
  ext i j
  rw [pairEmbed_apply, SpecialLinearGroup.transvection_coe, Matrix.add_apply, single_apply]
  simp only [Finset.mem_insert, Finset.mem_singleton, sl2Upper]
  by_cases hi : i = a <;> by_cases hj : j = a <;> by_cases hi' : i = b <;> by_cases hj' : j = b <;>
    simp_all [Matrix.one_apply, eq_comm]

theorem pairEmbed_sl2Lower {n : ℕ} {a b : Fin n} (hab : a ≠ b) (c : K) :
    pairEmbed hab (sl2Lower c) = SpecialLinearGroup.transvection hab.symm c := by
  apply Subtype.ext
  ext i j
  rw [pairEmbed_apply, SpecialLinearGroup.transvection_coe, Matrix.add_apply, single_apply]
  simp only [Finset.mem_insert, Finset.mem_singleton, sl2Lower]
  by_cases hi : i = a <;> by_cases hj : j = a <;> by_cases hi' : i = b <;> by_cases hj' : j = b <;>
    simp_all [Matrix.one_apply, eq_comm]

theorem longBlock_mem_spBlock {I : Finset (Fin N)} {p : Fin N} (hp : p ∈ I) (A : SL(2, K)) :
    longBlock K N p A ∈ spBlock K I := by
  rw [mem_spBlock]
  intro r t hrt
  refine isSupp_longBlock p A r t fun h => hrt ⟨?_, ?_⟩
  · rcases mem_coords.1 h.1 with rfl | rfl <;> exact hp
  · rcases mem_coords.1 h.2 with rfl | rfl <;> exact hp

section Centralizer

theorem diag_eq_one_of_row (hK : Nat.card K = 2) {n : ℕ} (x : SpecialLinearGroup (Fin n) K)
    (a : Fin n) (hrow : ∀ b, b ≠ a → (x : Matrix (Fin n) (Fin n) K) a b = 0) :
    (x : Matrix (Fin n) (Fin n) K) a a = 1 := by
  refine q2_eq_one_of_ne_zero hK fun h0 => ?_
  have hdet := x.2
  rw [Matrix.det_eq_zero_of_row_eq_zero a fun b => by
    by_cases hb : b = a
    · rw [hb, h0]
    · exact hrow b hb] at hdet
  exact zero_ne_one hdet

theorem eq_one_of_commute_q2Embed [CharP K 2] (hK : Nat.card K = 2) (hε : ε ≤ 1)
    {R : Finset (Fin N)} {x : SpecialLinearGroup (Fin (2 * N + ε)) K} (hx : x ∈ q2Block ε K R)
    (hc : ∀ y ∈ spBlock K Rᶜ, x * q2Embed ε hK y = q2Embed ε hK y * x) : x = 1 := by
  rw [q2Block, mem_blockSpecialLinear] at hx
  have hpat : ∀ p, p ∉ R → LinearPilot.TPattern
      ({q2Coord N ε (Sum.inl (Sum.inl p)), q2Coord N ε (Sum.inl (Sum.inr p))} :
        Finset (Fin (2 * N + ε))) (x : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K) := by
    intro p hp
    have hpR : p ∈ Rᶜ := Finset.mem_compl.2 hp
    refine LinearPilot.pattern_of_commute_transvections
      (by rw [Finset.card_pair (q2PlaneNe p)]) fun i hi j hj hij => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · exact absurd rfl hij
    · rw [← pairEmbed_sl2Upper, ← q2Embed_longBlock hK]
      exact hc _ (longBlock_mem_spBlock hpR _)
    · have h := hc _ (longBlock_mem_spBlock hpR (sl2Lower 1))
      rw [q2Embed_longBlock hK, pairEmbed_sl2Lower] at h
      exact h
    · exact absurd rfl hij
  have hrowcol : ∀ a b, a ≠ b → (x : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K) a b = 0 := by
    intro a b hab
    by_cases ha : a ∈ planeCoordsQ2 ε R
    · rw [hx a b (Or.inl (by simpa using ha)), Matrix.one_apply_ne hab]
    by_cases hb : b ∈ planeCoordsQ2 ε R
    · rw [hx a b (Or.inr (by simpa using hb)), Matrix.one_apply_ne hab]
    obtain ⟨w, rfl⟩ := (q2Coord N ε).surjective a
    obtain ⟨w', rfl⟩ := (q2Coord N ε).surjective b
    rw [q2Coord_mem_planeCoordsQ2] at ha hb
    rcases w with u | e
    · have hp : planeOf u ∉ R := ha
      have hu : q2Coord N ε (Sum.inl u) ∈ ({q2Coord N ε (Sum.inl (Sum.inl (planeOf u))),
          q2Coord N ε (Sum.inl (Sum.inr (planeOf u)))} : Finset (Fin (2 * N + ε))) := by
        rcases u with u | u <;> simp
      exact ((hpat _ hp).1 _ hu _ (Ne.symm hab)).2
    · rcases w' with v | e'
      · have hp : planeOf v ∉ R := hb
        have hv : q2Coord N ε (Sum.inl v) ∈ ({q2Coord N ε (Sum.inl (Sum.inl (planeOf v))),
            q2Coord N ε (Sum.inl (Sum.inr (planeOf v)))} : Finset (Fin (2 * N + ε))) := by
          rcases v with v | v <;> simp
        exact ((hpat _ hp).1 _ hv _ hab).1
      · exact absurd (congrArg (q2Coord N ε) (congrArg Sum.inr
          (Fin.ext (by have := e.2; have := e'.2; omega)))) hab
  apply Subtype.ext
  ext a b
  rw [Matrix.SpecialLinearGroup.coe_one]
  by_cases hab : a = b
  · subst hab
    rw [Matrix.one_apply_eq]
    exact diag_eq_one_of_row hK x a fun b hb => hrowcol a b (Ne.symm hb)
  · rw [Matrix.one_apply_ne hab]
    exact hrowcol a b hab

end Centralizer

end CFSG.SeitzReduction.SymplecticPilot
