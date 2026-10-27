module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8abBDact

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec8

namespace MB

structure LiftData where
  o : MB × MB × MB × MB
  chat : List MB
  sp : List MB
  s0 : MB
  norms : List (MB × MB × ℕ × MB)

@[expose] def psiOf (o : MB × MB × MB × MB) : List MB :=
  compR1 (conjR1 w₂) (dImgs o.1 o.2.1 o.2.2.1 o.2.2.2)

@[expose] def sigOf (D : LiftData) (e1 : MB) : List MB := (D.sp.headD 1 * e1) :: D.chat

@[expose] def r2Classes : List (List MB × MB) := [
  ([w₂, u, w₁, v * k, z, y, w₁ * y * t, z * k], w₁ * y),
  ([w₂ * z, u, w₁, v * k, z, y, w₁ * y * t, z * k], w₁ * y),
  ([w₂, u, w₁, v * z * k, z, y, w₁ * y * t, z * k], w₁ * y),
  ([w₂ * z, u, w₁, v * z * k, z, y, w₁ * y * t, z * k], w₁ * y),
  ([w₂ * w₁ * v * y * t * k, u * k, w₁, v * z * k, z, z * y * k, w₁ * y * t * k, z * k],
    u * w₁ * v * z * k),
  ([w₂ * w₁ * v * z * y * t * k, u * k, w₁, v * z * k, z, z * y * k, w₁ * y * t * k, z * k],
    u * w₁ * v * z * k),
  ([w₂ * w₁ * v * y * t, u * k, w₁, v * k, z, z * y * k, w₁ * y * t * k, z * k], u * w₁ * v * z),
  ([w₂ * w₁ * v * z * y * t, u * k, w₁, v * k, z, z * y * k, w₁ * y * t * k, z * k],
    u * w₁ * v * z)]

@[expose] def liftList : List LiftData := [
  ⟨(u, y, 1, k), [u, w₁, v * k, z, y, w₁ * y * t, z * k],
    [w₂, u, w₁, v * k, 1, y, w₁ * y * t, 1], w₁ * y,
    [(1, 1, 0, 1), (1, z, 0, k), (z, 1, 1, 1), (z, z, 1, k)]⟩,
  ⟨(u, y, 1, z * k), [u, w₁, v * z * k, z, y, w₁ * y * t, z * k],
    [w₂, u, w₁, v * k, 1, y, w₁ * y * t, 1], w₁ * y,
    [(1, 1, 2, 1), (1, z, 2, k), (z, 1, 3, 1), (z, z, 3, k)]⟩,
  ⟨(u, y, z, 1), [u * z, w₁, v * z, z, z * y, w₁ * z * y * t, z * k],
    [w₂ * w₁ * y, u, w₁, v * k, 1, y, w₁ * y * t, 1], 1,
    [(1, 1, 3, u * w₁ * z * t * k), (1, z, 3, u * w₁ * z * t), (z, 1, 2, u * w₁ * z * t * k), (z,
      z, 2, u * w₁ * z * t)]⟩,
  ⟨(u, y, z, z), [u * z, w₁, v, z, z * y, w₁ * z * y * t, z * k],
    [w₂ * w₁ * y, u, w₁, v * k, 1, y, w₁ * y * t, 1], 1,
    [(1, 1, 1, u * w₁ * z * t * k), (1, z, 1, u * w₁ * z * t), (z, 1, 0, u * w₁ * z * t * k), (z,
      z, 0, u * w₁ * z * t)]⟩,
  ⟨(u * z, z * y, 1, k), [u, w₁, v * k, z, y, w₁ * y * t, z * k],
    [w₂, u, w₁, v * k, 1, y, w₁ * y * t, 1], w₁ * y,
    [(1, 1, 0, 1), (1, z, 0, k), (z, 1, 1, 1), (z, z, 1, k)]⟩,
  ⟨(u * z, z * y, 1, z * k), [u, w₁, v * z * k, z, y, w₁ * y * t, z * k],
    [w₂, u, w₁, v * k, 1, y, w₁ * y * t, 1], w₁ * y,
    [(1, 1, 2, 1), (1, z, 2, k), (z, 1, 3, 1), (z, z, 3, k)]⟩,
  ⟨(u * z, z * y, z, 1), [u * z, w₁, v * z, z, z * y, w₁ * z * y * t, z * k],
    [w₂ * w₁ * y, u, w₁, v * k, 1, y, w₁ * y * t, 1], 1,
    [(1, 1, 3, u * w₁ * z * t * k), (1, z, 3, u * w₁ * z * t), (z, 1, 2, u * w₁ * z * t * k), (z,
      z, 2, u * w₁ * z * t)]⟩,
  ⟨(u * z, z * y, z, z), [u * z, w₁, v, z, z * y, w₁ * z * y * t, z * k],
    [w₂ * w₁ * y, u, w₁, v * k, 1, y, w₁ * y * t, 1], 1,
    [(1, 1, 1, u * w₁ * z * t * k), (1, z, 1, u * w₁ * z * t), (z, 1, 0, u * w₁ * z * t * k), (z,
      z, 0, u * w₁ * z * t)]⟩,
  ⟨(u, y, k, k), [u * k, w₁, v * z * k, z, z * y * k, w₁ * y * t * k, z * k],
    [w₂ * w₁ * v * y * t * k, u, w₁, v * k, 1, y, w₁ * y * t, 1], u * w₁ * v * z * k,
    [(1, 1, 4, 1), (1, z, 4, k), (z, 1, 5, 1), (z, z, 5, k)]⟩,
  ⟨(u, y, k, z * k), [u * k, w₁, v * k, z, z * y * k, w₁ * y * t * k, z * k],
    [w₂ * w₁ * v * y * t * k, u, w₁, v * k, 1, y, w₁ * y * t, 1], u * w₁ * v * z * k,
    [(k, k, 6, 1), (k, z * k, 6, k), (z * k, k, 7, 1), (z * k, z * k, 7, k)]⟩,
  ⟨(u, y, z * k, 1), [u * z * k, w₁, v, z, y * k, w₁ * z * y * t * k, z * k],
    [w₂ * v * t * k, u, w₁, v * k, 1, y, w₁ * y * t, 1], u * v * z * y * k,
    [(1, 1, 7, u * w₁ * z * t), (1, z, 7, u * w₁ * z * t * k), (z, 1, 6, u * w₁ * z * t), (z, z,
      6, u * w₁ * z * t * k)]⟩,
  ⟨(u, y, z * k, z), [u * z * k, w₁, v * z, z, y * k, w₁ * z * y * t * k, z * k],
    [w₂ * v * t * k, u, w₁, v * k, 1, y, w₁ * y * t, 1], u * v * z * y * k,
    [(k, k, 5, u * w₁ * z * t), (k, z * k, 5, u * w₁ * z * t * k), (z * k, k, 4, u * w₁ * z * t),
      (z * k, z * k, 4, u * w₁ * z * t * k)]⟩,
  ⟨(u * z, z * y, k, k), [u * k, w₁, v * z * k, z, z * y * k, w₁ * y * t * k, z * k],
    [w₂ * w₁ * v * y * t * k, u, w₁, v * k, 1, y, w₁ * y * t, 1], u * w₁ * v * z * k,
    [(1, 1, 4, 1), (1, z, 4, k), (z, 1, 5, 1), (z, z, 5, k)]⟩,
  ⟨(u * z, z * y, k, z * k), [u * k, w₁, v * k, z, z * y * k, w₁ * y * t * k, z * k],
    [w₂ * w₁ * v * y * t * k, u, w₁, v * k, 1, y, w₁ * y * t, 1], u * w₁ * v * z * k,
    [(k, k, 6, 1), (k, z * k, 6, k), (z * k, k, 7, 1), (z * k, z * k, 7, k)]⟩,
  ⟨(u * z, z * y, z * k, 1), [u * z * k, w₁, v, z, y * k, w₁ * z * y * t * k, z * k],
    [w₂ * v * t * k, u, w₁, v * k, 1, y, w₁ * y * t, 1], u * v * z * y * k,
    [(1, 1, 7, u * w₁ * z * t), (1, z, 7, u * w₁ * z * t * k), (z, 1, 6, u * w₁ * z * t), (z, z,
      6, u * w₁ * z * t * k)]⟩,
  ⟨(u * z, z * y, z * k, z), [u * z * k, w₁, v * z, z, y * k, w₁ * z * y * t * k, z * k],
    [w₂ * v * t * k, u, w₁, v * k, 1, y, w₁ * y * t, 1], u * v * z * y * k,
    [(k, k, 5, u * w₁ * z * t), (k, z * k, 5, u * w₁ * z * t * k), (z * k, k, 4, u * w₁ * z * t),
      (z * k, z * k, 4, u * w₁ * z * t * k)]⟩]

theorem liftList_dImgs_mem : ∀ D ∈ liftList,
    ∀ g ∈ dImgs D.o.1 D.o.2.1 D.o.2.2.1 D.o.2.2.2, inR1 g = true := by decide +kernel

theorem liftList_norms_lt : ∀ D ∈ liftList, ∀ q ∈ D.norms, q.2.2.1 < 8 := by decide +kernel

theorem liftList_psi_mem : ∀ D ∈ liftList, ∀ g ∈ psiOf D.o, inR1 g = true := by decide +kernel

theorem liftList_chat : ∀ D ∈ liftList,
    D.chat = compR1 (psiOf D.o) (compR1 (psiOf D.o) (psiOf D.o)) := by decide +kernel

theorem liftList_sp : ∀ D ∈ liftList, D.sp.length = 8 ∧ ∀ i : Fin 8,
    compR1 D.chat (conjR1 (gens.getD i 1)) = compR1 (conjR1 (D.sp.getD i 1)) D.chat := by
  decide +kernel

theorem liftList_s0 : ∀ D ∈ liftList, compR1 D.chat D.chat = conjR1 D.s0 := by decide +kernel

theorem liftList_k : ∀ D ∈ liftList, D.chat.getD 6 1 = z * k := by decide +kernel

theorem liftList_len : ∀ D ∈ liftList, D.chat.length = 7 := by decide +kernel

theorem liftList_combos : ∀ D ∈ liftList, ∀ e1 ∈ Z4, ∀ e2 ∈ Z4,
    applyMB (sigOf D e1) (D.s0 * e2) = D.s0 * e2 →
    compMB (sigOf D e1) (sigOf D e1) = conjMB (D.s0 * e2) →
    ∃ q ∈ D.norms, q.1 = e1 ∧ q.2.1 = e2 := by decide +kernel

theorem liftList_norms : ∀ D ∈ liftList, ∀ q ∈ D.norms, q.2.2.1 < 8 ∧
    compMB (sigOf D q.1) (conjMB q.2.2.2) = (r2Classes.getD q.2.2.1 ([], 1)).1 ∧
    applyMB (sigOf D q.1) q.2.2.2 * (D.s0 * q.2.1) * q.2.2.2 =
      (r2Classes.getD q.2.2.1 ([], 1)).2 := by decide +kernel

theorem liftList_o1 : (liftList.take 8).map LiftData.o = dValid1 := by decide +kernel

theorem liftList_oT : (liftList.drop 8).map LiftData.o = dValidT := by decide +kernel

theorem liftList_chat_gens : ∀ D ∈ liftList, gensR1.map (applyR1 D.chat) = D.chat := by
  decide +kernel

theorem liftList_d1 : ∀ D ∈ liftList.take 8, ∀ q ∈ D.norms, q.2.2.1 < 4 := by decide +kernel

theorem liftList_dT : ∀ D ∈ liftList.drop 8, ∀ q ∈ D.norms, 4 ≤ q.2.2.1 := by decide +kernel

theorem r2Classes_k : ∀ i < 8, (r2Classes.getD i ([], 1)).1.getD 7 1 = z * k ∧
    (r2Classes.getD i ([], 1)).1.length = 8 := by decide +kernel

end MB

end Sec8

end CFSG.ComponentClassification.HSFLit
