module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M24TCheckInputs

public section

namespace CFSG.EvenSporadicStandard.M24Std

open CFSG.Sporadic.Schreier CFSG.QuasithinUnique.Setup.X1 CFSG.Blueprint

@[expose] def wordSxtN1 : List ℤ :=
  [2, -1, -2, -1, -2, -1, -2, -1, -2, -1, -2, -1, 2, -1, 2, -1, 2, -1, 2, -1, -2, 1, -2, 1, 2, 1,
    2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2, -1, -2, -1, 2, -1, 2, 1, 2, 1, 2, 1,
    -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2, -2, -1, 2, -1, -2, -1, -2, -1, 2, -1,
    -2, -2, -1, 2, -1, 2, -1, -2, -1, 2, -1, 2, -1, -2, -1, 2, -1, 2, -1, 2, -1]

@[expose] def wordSxtN2 : List ℤ :=
  [2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, -2, -1, -2, -1, 2, -1, -2, -1, -2, -1, -2, -1, -2,
    -1, 2, -1, 2, -1, 2, -1, 2, -1, -2, -1, -2, -1, -2, -1, 2, -1, 2, -1, 2, 1, -2, 1, 2, -1, 2,
    -1, 2, -1, -2, -1, -2, -1, 2, -1, -2, -1, -2, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2,
    1, 2, 1, -2, 1, -2, -1, -2, -1, 2, -1, 2, 1, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2,
    1, 2, 1, -2, 1, -2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1,
    2, 1, 1, 2]

@[expose] def wordSxtR : List ℤ :=
  [-1, 2, -1, 2, -1, -2, -1, 2, -1, 2, -1, -2, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 2, 1, 2, 1, 2,
    1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1, -2, 1, 2, 1, -2, 1, -2,
    1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 1,
    -2, 1, -2, 1, -2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 2, 1, -2, 1, -2,
    -2, -1, -2, -1, 2, -1, 2, -1, 2, -1, 2, -1, -2]

@[expose] def wordSxtQ1 : List ℤ :=
  [1, -2, 1, 2, 1, -2, -1, -2, -1, -2, -1, -2, -1, -2, -1, 2, -1, 2, -1, -2, -1, 2, 2, 1, 2, 1,
    -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, -1, -2, -1, -2, -1, -2,
    -1, -2, -1, -2, -1, 2, -1, 2, -1, 2, -1, 2, -1, -2, -1, 2, -1, -2, -1, 2, -1, -2, -1, -2, 1,
    2, 1, -2, 1, 2, 1, 2, -1, -2, -1, -2, -1, -2, -1, -2, -1, 2, -1, -2, -1, 2, -1, -2, 1, 2, 1,
    -2, 1, 2, 1, -2, 1, 2, 1, 2, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, -2,
    1, 2, 1, -2, 1, 2, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2]

@[expose] def wordSxtQ2 : List ℤ :=
  [2, -1, -2, -1, -2, -1, -2, -1, -2, -1, -2, -1, 2, -1, 2, -1, 2, -1, 2, 2, 1, -2, 1, 2, 1, 2,
    1, -2, 1, 2, 2, -1, 2, -1, -2, -1, 2, -1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1, -2, 1,
    -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, -1, 2, -1, -2, -1, 2, -1,
    -2, -1, -2, -1, -2, -1, -2, -1, 2, -1, -2, -1, -2, -1, -2, -1, -1, 2, -1, 2, -1, -2, -1, -2,
    -1, -2, -1, -2, -1, 2, -1, 2, -1, 2, -1, -2, -1, -2, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2,
    1, -2, -2, 1, 2, 1, 2, 2, -1, 2, -1, 2, -1, -2, -1]

@[expose] def wordSxtQ3 : List ℤ :=
  [2, 1, -2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 2, -1, -2, -1, -2, -1, 2, -1, -2, -2,
    -1, 2, -1, 2, -1, 2, -1, 2, -1, -2, -1, -2, -1, 2, -1, 2, -1, 2, -1, 2, -1, -2, -1, -2, -1, 2,
    -1, 2, -1, 2, -1, 2, 2, -1, -2, -1, 2, -1, 2, -1, 2, -1, -2, -1, -2, -1, 2, -1, 2, -1, -2, -1,
    -2, -1, -2, -1, 2, -1, 2, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, -1, -2, -1, -2,
    -1, 2, -1, 2, -1, 2, -1, -2, -1, 2, -1, -2, -1, -2, -1, -2, -1, -2, -1, -2, -1, -2, 1, 2, 1,
    -2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 2, -1, -2, -1, -2]

@[expose] def wordsSxtQ : List (List ℤ) :=
  [[], [-1, -1], [-1], [1], [-2], [-1, -2], [2, 1], [-1, -1, -2], [-1, -3], [-3], [-1, -1, -3],
    [3, 2, 1], [3, 1], [-1, -2, -3], [-1, -1, -2, -3], [-2, -3]]

@[expose] def sxtGens : List S24 := [m24Cj wordSxtN1, m24Cj wordSxtN2]

@[expose] def sxtR : S24 := m24Cj wordSxtR

@[expose] def sxtQGens : List S24 := [m24Cj wordSxtQ1, m24Cj wordSxtQ2, m24Cj wordSxtQ3]

@[expose] def sxtQ : List S24 := wordsSxtQ.map (evalN NativeSporadic.M24 sxtQGens)

@[expose] def sxtA1 : S24 := m24E1l.getD 1 1

@[expose] def sxtA2 : S24 := m24E1l.getD 22 1

@[expose] def sxtFix (s : S24) : ℕ :=
  (Finset.univ.filter fun i : Fin 24 => (s : Equiv.Perm (Fin 24)) i = i).card

@[expose] def SxtNormChk (l : List S24) (g : S24) : Prop :=
  ∀ x ∈ l, g * x * g⁻¹ ∈ l ∧ g⁻¹ * x * g ∈ l

instance (l : List S24) (g : S24) : Decidable (SxtNormChk l g) := by
  unfold SxtNormChk
  infer_instance

@[expose] def sxtReachStep (gs l : List S24) (pi : ℕ × ℕ) : List S24 :=
  match l[pi.1]?, gs[pi.2]? with
  | some x, some g => l ++ [normH NativeSporadic.M24 (g * x * g⁻¹)]
  | _, _ => l

@[expose] def sxtReachSteps (gs : List S24) (a : S24) (w : List (ℕ × ℕ)) : List S24 :=
  w.foldl (sxtReachStep gs) [a]

@[expose] def sxtW1 : List (ℕ × ℕ) :=
  [(0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1), (3, 1), (4, 1), (5, 0), (5, 1), (6, 1),
    (7, 0), (7, 1), (8, 0), (8, 1), (9, 0), (10, 0), (10, 1), (11, 0), (12, 0), (12, 1), (14, 0),
    (15, 0), (16, 0), (16, 1), (17, 0), (18, 0), (18, 1), (19, 0), (19, 1), (20, 0), (20, 1),
    (23, 1), (24, 1), (26, 0), (26, 1), (27, 0), (27, 1), (30, 0), (31, 1), (32, 0), (34, 1),
    (36, 0), (38, 0)]

@[expose] def sxtW2 : List (ℕ × ℕ) :=
  [(0, 1), (1, 0), (1, 1), (2, 0), (2, 1), (3, 0), (3, 1), (4, 0), (4, 1), (6, 0), (6, 1),
    (7, 0), (8, 0), (9, 0), (11, 0), (13, 0), (15, 0)]

@[expose] def sxtFixClass (a : S24) : List S24 :=
  m24E1l.filter fun s => decide (s ≠ 1 ∧ sxtFix s = sxtFix a)

@[expose] def SxtFixOrbData : Prop :=
  ∀ x q : Fin 24,
    (∀ k ∈ m24E1l, (k : Equiv.Perm (Fin 24)) x = x → (k : Equiv.Perm (Fin 24)) q = q) →
      ∃ f ∈ m24E1l, (f : Equiv.Perm (Fin 24)) x = q

instance : Decidable SxtFixOrbData := by
  unfold SxtFixOrbData
  infer_instance

@[expose] def SxtOrbitData (a : S24) (w : List (ℕ × ℕ)) : Prop :=
  a ∈ m24E1l ∧ a ≠ 1 ∧ ∀ s ∈ sxtFixClass a, s ∈ sxtReachSteps sxtGens a w

instance (a : S24) (w : List (ℕ × ℕ)) : Decidable (SxtOrbitData a w) := by
  unfold SxtOrbitData
  infer_instance

@[expose] def SxtFiveData : Prop :=
  SxtNormChk m24E1l sxtR ∧ sxtR ≠ 1 ∧ sxtR ^ 5 = 1 ∧
    (m24E1l.filter fun x => decide (sxtR * x * sxtR⁻¹ = x)).length = 4 ∧
    sxtQ.length = 16 ∧ sxtQ.Nodup ∧ (1 : S24) ∈ sxtQ ∧ (∀ x ∈ sxtQ, ∀ y ∈ sxtQ, x * y ∈ sxtQ) ∧
    ∀ q ∈ sxtQ, SxtNormChk m24E1l q ∧ q * sxtR * q⁻¹ ∈ [sxtR, sxtR ^ 2, sxtR ^ 3, sxtR ^ 4]

instance : Decidable SxtFiveData := by
  unfold SxtFiveData
  infer_instance

@[expose] def SxtData : Prop :=
  SxtFixOrbData ∧ (∀ g ∈ sxtGens, SxtNormChk m24E1l g) ∧ SxtOrbitData sxtA1 sxtW1 ∧
    SxtOrbitData sxtA2 sxtW2 ∧ (sxtFixClass sxtA1).length = 45 ∧
    (sxtFixClass sxtA2).length = 18 ∧ sxtFix sxtA1 ≠ sxtFix sxtA2 ∧
    (∀ s ∈ m24E1l, s ≠ 1 → sxtFix s = sxtFix sxtA1 ∨ sxtFix s = sxtFix sxtA2) ∧ SxtFiveData

instance : Decidable SxtData := by
  unfold SxtData
  infer_instance

end CFSG.EvenSporadicStandard.M24Std
