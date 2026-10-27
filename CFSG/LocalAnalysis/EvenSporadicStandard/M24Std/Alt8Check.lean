module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.SplitBLetters

public section

namespace CFSG.EvenSporadicStandard.M24Std.Alt8

open CFSG.Sporadic.Schreier CFSG.QuasithinUnique.Setup.X1 CFSG.Certificates
  CFSG.EvenSporadicStandard.M24Std.SplitB

@[expose] def octPt : Fin 8 → Fin 24 := ![2, 4, 7, 10, 11, 15, 16, 18]

@[expose] def octIdx : Fin 24 → Fin 8 :=
  ![0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 3, 4, 0, 0, 0, 5, 6, 0, 7, 0, 0, 0, 0, 0]

@[expose] def InO (q : Fin 24) : Prop := octPt (octIdx q) = q

instance (q : Fin 24) : Decidable (InO q) := by unfold InO; infer_instance

@[expose] def octP0 : Fin 24 := 0

@[expose] def octConjW : List ℤ :=
  [1, 2, 1, -2, 1, -2, 1, -2, -2, -1, 2, -1, 2, -1, 2, -1, 2, -1, 2, -1, 2, -1, 2, -1, -2, -1, -2,
   -1, -2, -1, -2, -1, -2, -1, -2, -1, -2, -1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1,
   2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, -1, -2, -1, -2, -1, 2, -1, -2, -1, 2, -1, -2, -1, -2, -1, 2,
   -1, -2, -2, -1, 2, -1, 2, -1, 2, -1, 2, -1, -2, -1, -2, -1, 2, -1, 2, -1, 2, -1, 2, -1, -2, -1,
   -2, -1, 2, -1, 2, -1, 2, -1, 2, 1, 2, 1, 2]

@[expose] def sigImg : Fin 12 → Fin 8 → Fin 8 :=
  ![![5, 7, 3, 2, 6, 0, 4, 1],
    ![6, 3, 7, 1, 5, 4, 0, 2],
    ![1, 0, 4, 6, 2, 7, 3, 5],
    ![4, 7, 6, 5, 0, 3, 2, 1],
    ![1, 0, 5, 6, 7, 2, 3, 4],
    ![3, 6, 7, 0, 5, 4, 1, 2],
    ![3, 2, 1, 0, 5, 4, 7, 6],
    ![7, 5, 4, 6, 2, 1, 3, 0],
    ![5, 7, 6, 4, 3, 0, 2, 1],
    ![7, 4, 5, 6, 1, 2, 3, 0],
    ![6, 2, 1, 7, 5, 4, 0, 3],
    ![4, 7, 3, 2, 0, 6, 5, 1]]

@[expose] def sigInv : Fin 12 → Fin 8 → Fin 8 :=
  ![![5, 7, 3, 2, 6, 0, 4, 1],
    ![6, 3, 7, 1, 5, 4, 0, 2],
    ![1, 0, 4, 6, 2, 7, 3, 5],
    ![4, 7, 6, 5, 0, 3, 2, 1],
    ![1, 0, 5, 6, 7, 2, 3, 4],
    ![3, 6, 7, 0, 5, 4, 1, 2],
    ![3, 2, 1, 0, 5, 4, 7, 6],
    ![7, 5, 4, 6, 2, 1, 3, 0],
    ![5, 7, 6, 4, 3, 0, 2, 1],
    ![7, 4, 5, 6, 1, 2, 3, 0],
    ![6, 2, 1, 7, 5, 4, 0, 3],
    ![4, 7, 3, 2, 0, 6, 5, 1]]

theorem sigInv_left (k : Fin 12) : Function.LeftInverse (sigInv k) (sigImg k) := by
  revert k; decide

theorem sigInv_right (k : Fin 12) : Function.RightInverse (sigInv k) (sigImg k) := by
  revert k; decide

@[expose] def octSig (k : Fin 12) : Equiv.Perm (Fin 8) :=
  ⟨sigImg k, sigInv k, sigInv_left k, sigInv_right k⟩

@[expose] def alt8Words : List (List ℤ) :=
  [[-10, -3, 6, 12, 2, 4, 12, 6, -9, 11, 12, -10, -8, -5, -3],
   [-10, -8, -5, -3, 1, 9, -6, -12, -4, -2, -12, -7, -1, -7, -4, -1],
   [3, 5, 8, 10, -11, -2, 1, 9, -6, -12, -4, -2, -5, -3, 1, 3, 10],
   [3, 5, 8, 10, -12, -11, 4, 6, 9, -1, -5, -3, 1, 3, 10],
   [-12, -2, -1, -12, -6, -1, -9, -1],
   [3, 5, 8, 10, -11, -2, -5, -3, 1, 3, 10],
   [-12, -2, 6, 12],
   [-5, -3, -8, -3, -1],
   [1, 2, 4, 3, 5],
   [-3],
   [-5, -3, -3],
   [-7, -6, -6],
   [-6],
   [-12, -2, 4, 6, 9, -1, -5, -3, -9, -1, -4],
   [-4],
   [-1],
   [-9, -1, -1],
   [-11, -2, -2],
   [-2],
   [-10, -8, -5, -3, -5, -3, -8],
   [-8]]

@[expose] def alt8Cert : RawSchreierDatum 8 :=
  certificate (by decide) ((List.finRange 12).map octSig) alt8Words #v[0, 1, 2, 3, 4, 5]
    (by decide)

@[expose] def Alt8PinData : Prop :=
  (∀ b ∈ m24B0l, ∀ i : Fin 8, (b : Equiv.Perm (Fin 24)) (octPt i) = octPt i) ∧
    (∀ q : Fin 24, (∀ b ∈ m24B0l, (b : Equiv.Perm (Fin 24)) q = q) → InO q) ∧
    (∀ q : Fin 24, ¬ InO q → ∃ b ∈ m24B0l, (b : Equiv.Perm (Fin 24)) octP0 = q) ∧
    ¬ InO octP0 ∧
    (∀ j : Fin 24, j.val < 7 → InO ((m24Cj octConjW : Equiv.Perm (Fin 24)) j) ∨
      (m24Cj octConjW : Equiv.Perm (Fin 24)) j = octP0) ∧
    (∀ k : Fin 12, ∀ i : Fin 8, (tvEl k : Equiv.Perm (Fin 24)) (octPt i) = octPt (octSig k i)) ∧
    (∀ k : Fin 12, Equiv.Perm.sign (octSig k) = 1) ∧
    ValidSchreier alt8Cert ∧ alt8Cert.orderCertificate = 20160

instance : Decidable Alt8PinData := by unfold Alt8PinData; infer_instance

end CFSG.EvenSporadicStandard.M24Std.Alt8
