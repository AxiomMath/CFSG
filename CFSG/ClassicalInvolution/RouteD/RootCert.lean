module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ClassicalInvolution.RouteD.Basic
public import CFSG.LieType.RootSystem.Basic

public section

namespace CFSG.ClassicalInvolution.RouteD

open TauCeti CFSG.LieType.RootSystem

namespace RootCert

@[expose] def vecOf (n : ℕ) (l : List ℤ) : Fin n → ℤ := fun i => l.getD i 0

@[expose] def dotRow {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) (l : List ℤ) : ℤ :=
  ((List.finRange n).map fun k => A i k * l.getD k 0).sum

@[expose] def reflL {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) (l : List ℤ) : List ℤ :=
  l.mapIdx fun j x => if j = i.val then x - dotRow A i l else x

@[expose] def natL (l : List ℕ) : List ℤ := l.map fun x : ℕ => (x : ℤ)

@[expose] def negL (l : List ℤ) : List ℤ := l.map fun x => -x

@[expose] def allL (P : List (List ℕ)) : List (List ℤ) := P.map natL ++ P.map fun l => negL (natL l)

@[expose] def Cert {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (P T : List (List ℕ))
    (par : List (ℕ × ℕ)) : Prop :=
  n ≤ P.length ∧ (∀ l ∈ P, l.length = n) ∧
    (∀ i : Fin n, vecOf n (natL (P.getD i [])) = Pi.single i 1) ∧
    (∀ k < P.length, ∀ i : Fin n, (T.getD k []).getD i 0 < 2 * P.length ∧
      reflL A i (natL (P.getD k [])) = (allL P).getD ((T.getD k []).getD i 0) []) ∧
    (∀ k < P.length, n ≤ k → (par.getD k (0, 0)).1 < k ∧ (par.getD k (0, 0)).2 < n ∧
      (T.getD (par.getD k (0, 0)).1 []).getD (par.getD k (0, 0)).2 0 = k) ∧
    P.Nodup ∧ (∀ p ∈ P, ∃ x ∈ p, 0 < x)

instance {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (P T : List (List ℕ)) (par : List (ℕ × ℕ)) :
    Decidable (Cert A P T par) := by
  unfold Cert
  infer_instance

variable {n : ℕ}

end RootCert

end CFSG.ClassicalInvolution.RouteD
