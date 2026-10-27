module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeBadCube
public import CFSG.HardMathSupport.Malle.SeitzCube.E6ThreeSL3Data
public import CFSG.RankThree.E6.LargePrimeStabilizers

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.RankThree.E6 (e6RootVec)
open CFSG.HardMathSupport.Malle.SeitzCube (e6A2Root wordProd_smul_E6)

@[expose] def bmGram (x y : Fin 6 → ℤ) : ℤ :=
  2 * (x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3 + x 4 * y 4 + x 5 * y 5) -
    (x 0 * y 2 + x 2 * y 0) - (x 1 * y 3 + x 3 * y 1) - (x 2 * y 3 + x 3 * y 2) -
    (x 3 * y 4 + x 4 * y 3) - (x 4 * y 5 + x 5 * y 4)

theorem iform_eq_bmGram (x y : Fin Tag.E6.rank → ℤ) : iform x y = bmGram x y := by
  rw [CFSG.RankThree.E6.iform_eq_e6Form]
  have key : ∀ x y : Fin 6 → ℤ,
      ∑ i : Fin 6, x i * ∑ j : Fin 6, Tag.cartanE 6 i j * y j = bmGram x y := by
    intro x y
    simp [Fin.sum_univ_six, Tag.cartanE, bmGram]
    ring
  exact key x y

@[expose] def bmCandA : List (Fin Tag.E6.rank → ℤ) :=
  [![-1, 0, -1, 0, 0, 0], ![-1, 0, 0, 0, 0, 0], ![0, 0, -1, 0, 0, 0], ![0, 0, 1, 0, 0, 0],
    ![1, 0, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0]]

@[expose] def bmCandB : List (Fin Tag.E6.rank → ℤ) :=
  [![-1, -2, -2, -3, -2, -1], ![0, 0, 0, 0, -1, -1], ![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 0],
    ![0, 1, 0, 0, 0, 0], ![1, 1, 2, 3, 2, 1]]

@[expose] def bmCandC : List (Fin Tag.E6.rank → ℤ) :=
  [![-1, -1, -2, -2, -1, -1], ![-1, -1, -1, -2, -1, -1], ![0, -1, -1, -2, -1, -1],
    ![0, 0, 0, 1, 0, 0], ![0, 0, 1, 1, 0, 0], ![0, 1, 0, 1, 1, 1], ![0, 1, 1, 1, 1, 1],
    ![1, 0, 1, 1, 0, 0], ![1, 1, 1, 1, 1, 1]]

theorem bmCand_completeA : ∀ m : Fin 72, e6RootVec m 3 % 3 = 0 →
    (e6RootVec m 1 + e6RootVec m 4 + e6RootVec m 5) % 3 = 0 → e6RootVec m ∈ bmCandA := by
  decide +kernel

theorem bmCand_completeB : ∀ m : Fin 72, e6RootVec m 3 % 3 = 0 →
    (e6RootVec m 1 + e6RootVec m 4 + e6RootVec m 5) % 3 = 1 → e6RootVec m ∈ bmCandB := by
  decide +kernel

theorem bmCand_completeC : ∀ m : Fin 72, e6RootVec m 3 % 3 = 1 →
    (e6RootVec m 1 + e6RootVec m 4 + e6RootVec m 5) % 3 = 0 → e6RootVec m ∈ bmCandC := by
  decide +kernel

@[expose] def bmV (r : Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ) (x : Fin Tag.E6.rank → ℤ) :
    Fin Tag.E6.rank → ℤ :=
  fun k => x 0 * r 0 k + x 1 * r 1 k + x 2 * r 2 k + x 3 * r 3 k + x 4 * r 4 k + x 5 * r 5 k

abbrev bmCube (r : Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ) : Prop :=
  ∀ i : Fin Tag.E6.rank,
    bmV r (bmV r (bmV r (Pi.single i 1))) = (Pi.single i 1 : Fin Tag.E6.rank → ℤ)

@[expose] def bmMat (r0 r1 r2 r3 r4 r5 : Fin Tag.E6.rank → ℤ) :
    Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ :=
  ![r0, r1, r2, r3, r4, r5]

@[expose] def bmFixA : Fin Tag.E6.rank → ℤ := ![-1, 0, -1, 0, 0, 0]

@[expose] def bmFixB : Fin Tag.E6.rank → ℤ := ![-1, -2, -2, -3, -2, -1]

@[expose] def bmTw : Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ :=
  ![![-1, 0, -1, 0, 0, 0], ![-1, -2, -2, -3, -2, -1], ![1, 0, 0, 0, 0, 0], ![0, 1, 1, 1, 1, 1],
    ![0, 0, 0, 0, -1, -1], ![0, 0, 0, 0, 1, 0]]

@[expose] def bmTw2 : Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ :=
  ![![0, 0, 1, 0, 0, 0], ![1, 1, 2, 3, 2, 1], ![-1, 0, -1, 0, 0, 0], ![0, -1, -1, -2, -1, -1],
    ![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, -1, -1]]

@[expose] def bmTs : Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ :=
  ![![0, 0, 1, 0, 0, 0], ![-1, -2, -2, -3, -2, -1], ![-1, 0, -1, 0, 0, 0], ![1, 1, 1, 1, 1, 1],
    ![0, 0, 0, 0, -1, -1], ![0, 0, 0, 0, 1, 0]]

@[expose] def bmTs2 : Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ :=
  ![![-1, 0, -1, 0, 0, 0], ![1, 1, 2, 3, 2, 1], ![1, 0, 0, 0, 0, 0], ![-1, -1, -1, -2, -1, -1],
    ![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, -1, -1]]

set_option maxRecDepth 100000 in
theorem bm_enum : ∀ r3 ∈ bmCandC, ∀ r2 ∈ bmCandA, bmGram r2 r3 = -1 →
    ∀ r4 ∈ bmCandB, bmGram r4 r3 = -1 → bmGram r4 r2 = 0 →
    ∀ r1 ∈ bmCandB, bmGram r1 r3 = -1 → bmGram r1 r2 = 0 → bmGram r1 r4 = 0 →
    ∀ r0 ∈ bmCandA, bmGram r0 r3 = 0 → bmGram r0 r2 = -1 → bmGram r0 r4 = 0 →
      bmGram r0 r1 = 0 →
    ∀ r5 ∈ bmCandB, bmGram r5 r3 = 0 → bmGram r5 r2 = 0 → bmGram r5 r4 = -1 →
      bmGram r5 r1 = 0 → bmGram r5 r0 = 0 →
    bmCube (bmMat r0 r1 r2 r3 r4 r5) →
      bmV (bmMat r0 r1 r2 r3 r4 r5) bmFixA = bmFixA ∨
      bmV (bmMat r0 r1 r2 r3 r4 r5) bmFixB = bmFixB ∨
      bmMat r0 r1 r2 r3 r4 r5 = bmTw ∨ bmMat r0 r1 r2 r3 r4 r5 = bmTw2 ∨
      bmMat r0 r1 r2 r3 r4 r5 = bmTs ∨ bmMat r0 r1 r2 r3 r4 r5 = bmTs2 := by
  decide +kernel

theorem bm_foldr_Tw : ∀ i : Fin Tag.E6.rank,
    e6BadWord.foldr (reflect .E6) (Pi.single i 1) = bmTw i := by
  decide +kernel

theorem bm_foldr_Tw2 : ∀ i : Fin Tag.E6.rank,
    (e6BadWord ++ e6BadWord).foldr (reflect .E6) (Pi.single i 1) = bmTw2 i := by
  decide +kernel

theorem bm_foldr_Ts : ∀ i : Fin Tag.E6.rank,
    ([0] ++ e6BadWord ++ [0]).foldr (reflect .E6) (Pi.single i 1) = bmTs i := by
  decide +kernel

theorem bm_foldr_Ts2 : ∀ i : Fin Tag.E6.rank,
    ([0] ++ e6BadWord ++ e6BadWord ++ [0]).foldr (reflect .E6) (Pi.single i 1) = bmTs2 i := by
  decide +kernel

@[expose] def bmPi : Fin 3 → Fin 3 := ![2, 0, 1]

theorem bm_foldr_e6A2Root : ∀ a b : Fin 3,
    e6BadWord.foldr (reflect .E6) (e6A2Root 0 a b) = e6A2Root 0 (bmPi a) (bmPi b) := by
  decide +kernel

theorem bm_smul_e6A2Root (a b : Fin 3) :
    (coxeterSystem .E6).wordProd e6BadWord • e6A2Root 0 a b = e6A2Root 0 (bmPi a) (bmPi b) := by
  rw [wordProd_smul_E6, bm_foldr_e6A2Root]

@[expose] def bmMoveA : List (Fin Tag.E6.rank) := [0, 2]

@[expose] def bmMoveB : List (Fin Tag.E6.rank) := [2, 0]

@[expose] def bmMoveC : List (Fin Tag.E6.rank) :=
  [3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 2, 3, 0, 2, 1, 3, 4, 0]

theorem bm_foldr_comm : ∀ i : Fin Tag.E6.rank,
    (bmMoveA ++ e6BadWord).foldr (reflect .E6) (Pi.single i 1) =
      (e6BadWord ++ bmMoveA).foldr (reflect .E6) (Pi.single i 1) ∧
    (bmMoveB ++ e6BadWord).foldr (reflect .E6) (Pi.single i 1) =
      (e6BadWord ++ bmMoveB).foldr (reflect .E6) (Pi.single i 1) ∧
    (bmMoveC ++ e6BadWord).foldr (reflect .E6) (Pi.single i 1) =
      (e6BadWord ++ bmMoveC).foldr (reflect .E6) (Pi.single i 1) ∧
    ([0] ++ ([0] ++ e6BadWord ++ [0])).foldr (reflect .E6) (Pi.single i 1) =
      (e6BadWord ++ [0]).foldr (reflect .E6) (Pi.single i 1) := by
  decide +kernel

theorem bm_wordProd_comm {u v u' v' : List (Fin Tag.E6.rank)}
    (h : ∀ i : Fin Tag.E6.rank, (u ++ v).foldr (reflect .E6) (Pi.single i 1) =
      (u' ++ v').foldr (reflect .E6) (Pi.single i 1)) :
    (coxeterSystem .E6).wordProd u * (coxeterSystem .E6).wordProd v =
      (coxeterSystem .E6).wordProd u' * (coxeterSystem .E6).wordProd v' := by
  refine ext_single fun i => ?_
  rw [← CoxeterSystem.wordProd_append, ← CoxeterSystem.wordProd_append, wordProd_smul_E6,
    wordProd_smul_E6, h i]

theorem bm_comm_moveA :
    (coxeterSystem .E6).wordProd bmMoveA * (coxeterSystem .E6).wordProd e6BadWord =
      (coxeterSystem .E6).wordProd e6BadWord * (coxeterSystem .E6).wordProd bmMoveA :=
  bm_wordProd_comm fun i => (bm_foldr_comm i).1

theorem bm_comm_moveB :
    (coxeterSystem .E6).wordProd bmMoveB * (coxeterSystem .E6).wordProd e6BadWord =
      (coxeterSystem .E6).wordProd e6BadWord * (coxeterSystem .E6).wordProd bmMoveB :=
  bm_wordProd_comm fun i => (bm_foldr_comm i).2.1

theorem bm_comm_moveC :
    (coxeterSystem .E6).wordProd bmMoveC * (coxeterSystem .E6).wordProd e6BadWord =
      (coxeterSystem .E6).wordProd e6BadWord * (coxeterSystem .E6).wordProd bmMoveC :=
  bm_wordProd_comm fun i => (bm_foldr_comm i).2.2.1

theorem bm_comm_s :
    (coxeterSystem .E6).wordProd [0] * (coxeterSystem .E6).wordProd ([0] ++ e6BadWord ++ [0]) =
      (coxeterSystem .E6).wordProd e6BadWord * (coxeterSystem .E6).wordProd [0] :=
  bm_wordProd_comm fun i => (bm_foldr_comm i).2.2.2

@[expose] def bmInvA : Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ :=
  ![![-1, 0, -1, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0], ![0, 0, 1, 1, 0, 0],
    ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]

@[expose] def bmInvB : Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ :=
  ![![0, 0, 1, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![-1, 0, -1, 0, 0, 0], ![1, 0, 1, 1, 0, 0],
    ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]

@[expose] def bmInvC : Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ :=
  ![![1, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1], ![-1, 0, 0, 0, 0, 0],
    ![0, -1, -1, -1, -1, -1], ![0, 1, 0, 0, 0, 0], ![1, 1, 2, 3, 2, 1]]

theorem bm_foldr_inv : ∀ j : Fin Tag.E6.rank,
    bmMoveA.reverse.foldr (reflect .E6) (Pi.single j 1) = bmInvA j ∧
    bmMoveB.reverse.foldr (reflect .E6) (Pi.single j 1) = bmInvB j ∧
    bmMoveC.reverse.foldr (reflect .E6) (Pi.single j 1) = bmInvC j := by
  decide +kernel

theorem bm_inv_smul {u : List (Fin Tag.E6.rank)} {T : Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ}
    (h : ∀ j : Fin Tag.E6.rank, u.reverse.foldr (reflect .E6) (Pi.single j 1) = T j)
    (j : Fin Tag.E6.rank) :
    ((coxeterSystem .E6).wordProd u)⁻¹ • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = T j := by
  rw [← CoxeterSystem.wordProd_reverse, wordProd_smul_E6, h j]

theorem bm_inv_moveA (j : Fin Tag.E6.rank) :
    ((coxeterSystem .E6).wordProd bmMoveA)⁻¹ • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) =
      bmInvA j :=
  bm_inv_smul (fun j => (bm_foldr_inv j).1) j

theorem bm_inv_moveB (j : Fin Tag.E6.rank) :
    ((coxeterSystem .E6).wordProd bmMoveB)⁻¹ • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) =
      bmInvB j :=
  bm_inv_smul (fun j => (bm_foldr_inv j).2.1) j

theorem bm_inv_moveC (j : Fin Tag.E6.rank) :
    ((coxeterSystem .E6).wordProd bmMoveC)⁻¹ • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) =
      bmInvC j :=
  bm_inv_smul (fun j => (bm_foldr_inv j).2.2) j

theorem bm_smul_Tw (i : Fin Tag.E6.rank) :
    (coxeterSystem .E6).wordProd e6BadWord • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) = bmTw i := by
  rw [wordProd_smul_E6, bm_foldr_Tw]

theorem bm_wordProd_eq_of_smul {v : WeylGroup .E6} {l : List (Fin Tag.E6.rank)}
    {T : Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ}
    (hT : ∀ i : Fin Tag.E6.rank, l.foldr (reflect .E6) (Pi.single i 1) = T i)
    (h : ∀ i : Fin Tag.E6.rank, v • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) = T i) :
    v = (coxeterSystem .E6).wordProd l :=
  ext_single fun i => by rw [h i, wordProd_smul_E6, hT i]

theorem bm_sum_six {M : Type*} [AddCommMonoid M] (f : Fin Tag.E6.rank → M) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 :=
  Fin.sum_univ_six f

theorem bm_smul_eq_bmV (v : WeylGroup .E6) (x : Fin Tag.E6.rank → ℤ) :
    v • x = bmV (fun i => v • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) x := by
  have hx : x = ∑ i : Fin Tag.E6.rank, x i • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  have h1 : v • x = ∑ i : Fin Tag.E6.rank, x i • v • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) := by
    conv_lhs => rw [hx]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm v (x i) _
  rw [h1, bm_sum_six]
  funext k
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rfl

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
