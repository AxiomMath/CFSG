module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.QuadDataOmegaDefs

public section

namespace CFSG.EvenSporadicStandard.M24Std.Sym6

open CFSG.Sporadic.Schreier CFSG.QuasithinUnique.Setup.X1 CFSG.Blueprint

@[expose] def tetIdxList : List (Fin 6) :=
  [0, 1, 2, 3, 4, 0, 1, 4, 1, 5, 2, 4, 3, 5, 3, 4, 2, 0, 2, 1, 0, 3, 5, 5]

@[expose] def tetIdx (q : Fin 24) : Fin 6 := tetIdxList.getD q.val 0

@[expose] def tetRep (i : Fin 6) : Fin 24 := [0, 1, 2, 3, 4, 9].getD i.val 0

theorem tetIdx_tetRep : ∀ i : Fin 6, tetIdx (tetRep i) = i := by decide

@[expose] def tetSig (s : S24) : ℕ :=
  ((List.finRange 6).filter fun i => (s : Equiv.Perm (Fin 24)) (tetRep i) = tetRep i).foldl
    (fun acc i => acc + 2 ^ i.val) 0

@[expose] def tetSigTab : List ℕ :=
  [63, 0, 0, 0, 0, 17, 34, 12, 0, 12, 17, 34, 0, 34, 12, 17, 0, 33, 20, 10, 9, 6, 0, 48, 18, 0,
    40, 5, 36, 24, 3, 0, 0, 10, 33, 20, 36, 0, 24, 3, 9, 48, 6, 0, 18, 5, 0, 40, 0, 20, 10, 33,
    18, 40, 5, 0, 36, 3, 0, 24, 9, 0, 48, 6]

@[expose] def wordSxS : List ℤ :=
  [1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1,
    -2, 1, -2, 1, 2, 1, 2, 1, -2]

@[expose] def wordSxT : List ℤ :=
  [1, -2, 1, 2, 1, 2, -1, 2, -1, -2, -1, -2, -1, -2, -1, 2, -1, 2, 2, 1, -2, 1, -2, 1, 2, 1, 2,
    1, 2, 1, 2, -1, -2, -1, -2, -1, 2, -1, 2, -1, -2, -1, 2, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2,
    2, 1, -2, 1, 2]

@[expose] def sxS : S24 := m24Cj wordSxS

@[expose] def sxT : S24 := m24Cj wordSxT

@[expose] def swapImg (i : Fin 6) : Fin 6 := [1, 0, 2, 3, 4, 5].getD i.val 0

@[expose] def rotImg (i : Fin 6) : Fin 6 := [1, 2, 3, 4, 5, 0].getD i.val 0

@[expose] def sxK0 : List S24 :=
  m24E1l ++ (m24E1l.map fun x => qdOmega * x) ++ (m24E1l.map fun x => qdOmega⁻¹ * x)

@[expose] def Sym6PinData : Prop :=
  (∀ x ∈ m24E1l, ∀ p : Fin 24, tetIdx ((x : Equiv.Perm (Fin 24)) p) = tetIdx p) ∧
    (∀ p q : Fin 24, tetIdx p = tetIdx q → ∃ x ∈ m24E1l, (x : Equiv.Perm (Fin 24)) p = q) ∧
    (∀ x ∈ m24E1l, ∀ p : Fin 24, (x : Equiv.Perm (Fin 24)) p = p ↔
      (x : Equiv.Perm (Fin 24)) (tetRep (tetIdx p)) = tetRep (tetIdx p)) ∧
    (∀ p : Fin 24, tetIdx ((qdOmega : Equiv.Perm (Fin 24)) p) = tetIdx p) ∧
    (∀ k ∈ List.range 64, tetSig (qdQ k) = tetSigTab.getD k 99) ∧
    QdNormChk sxS ∧ QdNormChk sxT ∧
    (∀ i : Fin 6, tetIdx ((sxS : Equiv.Perm (Fin 24)) (tetRep i)) = swapImg i) ∧
    (∀ i : Fin 6, tetIdx ((sxT : Equiv.Perm (Fin 24)) (tetRep i)) = rotImg i) ∧
    sxK0.Nodup ∧ ∀ x ∈ m24E1l, qdOmega * x * (qdOmega * x) * (qdOmega * x) = 1

instance : Decidable Sym6PinData := by
  unfold Sym6PinData
  infer_instance

@[expose] def SigEnumBody (y : List ℕ) : Prop :=
  (∀ k ∈ List.range 64, tetSigTab.getD (qdLin y k) 99 = tetSigTab.getD k 99) →
    (∀ k ∈ List.range 64, qdLin y k = k) ∨
    (∀ k ∈ List.range 64, qdLin y k = qdPsiTab.getD k 0) ∨
    (∀ k ∈ List.range 64, qdLin y k = qdPsiInvTab.getD k 0)

instance (y : List ℕ) : Decidable (SigEnumBody y) := by
  unfold SigEnumBody
  infer_instance

@[expose] def SigEnum : Prop :=
  ∀ p₁ ∈ qdPairs, ∀ p₂ ∈ qdPairs, ∀ p₃ ∈ qdPairs,
    SigEnumBody [p₁.1, p₁.2, p₂.1, p₂.2, p₃.1, p₃.2]

instance : Decidable SigEnum := by
  unfold SigEnum
  infer_instance

end CFSG.EvenSporadicStandard.M24Std.Sym6
