module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6ClassesReps

public section

namespace CFSG.SeitzReduction

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

inductive TwistedE6ClassStep
  | ff
  | ppf
  | ppp
  | fp

@[expose] def twistedE6ClassMemB (v : Fin TwistTag.E6.tag.rank → ℤ)
    (L : List (Fin TwistTag.E6.tag.rank → ℤ)) : Bool :=
  L.any (twistedE6TwoVecB v)

theorem twistedE6ClassMemB_iff {v : Fin TwistTag.E6.tag.rank → ℤ}
    {L : List (Fin TwistTag.E6.tag.rank → ℤ)} : twistedE6ClassMemB v L = true ↔ v ∈ L := by
  simp only [twistedE6ClassMemB, List.any_eq_true, twistedE6TwoVecB_iff]
  exact ⟨fun ⟨w, hw, e⟩ => e ▸ hw, fun h => ⟨v, h, rfl⟩⟩

@[expose] def twistedE6ClassCommB (x y : Fin TwistTag.E6.tag.rank → ℤ) : Bool :=
  !twistedE6TwoRootB (x + y) && !twistedE6TwoVecB (x + y) 0

@[expose] def twistedE6ClassCentralB (x : Fin TwistTag.E6.tag.rank → ℤ)
    (R : List (Fin TwistTag.E6.tag.rank → ℤ)) : Bool :=
  R.all (twistedE6ClassCommB x)

@[expose] def twistedE6ClassFixedB (x : Fin TwistTag.E6.tag.rank → ℤ) : Bool :=
  twistedE6TwoVecB (permLattice TwistTag.E6.perm x) x

@[expose] def twistedE6ClassEntryOK (R Dl done : List (Fin TwistTag.E6.tag.rank → ℤ))
    (e : TwistedE6ClassStep × (Fin TwistTag.E6.tag.rank → ℤ) × (Fin TwistTag.E6.tag.rank → ℤ)) :
    Bool :=
  twistedE6TwoRootB e.2.1 && twistedE6TwoRootB e.2.2 && twistedE6TwoRootB (e.2.1 + e.2.2) &&
    decide (0 < height (e.2.1 + e.2.2)) &&
    (twistedE6ClassMemB e.2.1 Dl || twistedE6ClassMemB e.2.2 Dl) &&
    twistedE6ClassCentralB e.2.1 R &&
    twistedE6ClassCentralB (permLattice TwistTag.E6.perm e.2.1) R &&
    twistedE6ClassCentralB e.2.2 R &&
    twistedE6ClassCentralB (permLattice TwistTag.E6.perm e.2.2) R &&
    match e.1 with
    | .ff => twistedE6ClassFixedB e.2.1 && twistedE6ClassFixedB e.2.2 &&
        !twistedE6TwoVecB e.2.1 e.2.2
    | .ppf => !twistedE6ClassFixedB e.2.1 && !twistedE6ClassFixedB e.2.2 &&
        twistedE6ClassFixedB (e.2.1 + e.2.2) && !twistedE6TwoVecB e.2.1 e.2.2 &&
        !twistedE6TwoRootB (e.2.1 + permLattice TwistTag.E6.perm e.2.2) &&
        !twistedE6TwoVecB (e.2.1 + permLattice TwistTag.E6.perm e.2.2) 0 &&
        !twistedE6TwoVecB e.2.1 (permLattice TwistTag.E6.perm e.2.2) &&
        !twistedE6TwoRootB (e.2.1 + e.2.2 + e.2.1) && !twistedE6TwoRootB (e.2.1 + e.2.2 + e.2.2) &&
        !twistedE6TwoVecB (e.2.1 + e.2.2) (-e.2.1) && !twistedE6TwoVecB (e.2.1 + e.2.2) (-e.2.2)
    | .ppp => !twistedE6ClassFixedB e.2.1 && !twistedE6ClassFixedB e.2.2 &&
        !twistedE6ClassFixedB (e.2.1 + e.2.2) && !twistedE6TwoVecB e.2.1 e.2.2 &&
        twistedE6ClassCommB e.2.1 (permLattice TwistTag.E6.perm e.2.2) &&
        twistedE6ClassCommB (permLattice TwistTag.E6.perm (e.2.1 + e.2.2)) e.2.1 &&
        twistedE6ClassCommB (permLattice TwistTag.E6.perm (e.2.1 + e.2.2)) e.2.2
    | .fp => twistedE6ClassFixedB e.2.1 && !twistedE6ClassFixedB e.2.2 &&
        !twistedE6ClassFixedB (e.2.1 + e.2.2) &&
        twistedE6TwoRootB (e.2.2 + (e.2.1 + permLattice TwistTag.E6.perm e.2.2)) &&
        twistedE6ClassFixedB (e.2.2 + (e.2.1 + permLattice TwistTag.E6.perm e.2.2)) &&
        !twistedE6TwoVecB e.2.1 e.2.2 &&
        !twistedE6TwoVecB e.2.1 (permLattice TwistTag.E6.perm e.2.2) &&
        !twistedE6TwoVecB e.2.2 (e.2.1 + permLattice TwistTag.E6.perm e.2.2) &&
        twistedE6ClassCommB (e.2.2 + (e.2.1 + permLattice TwistTag.E6.perm e.2.2))
          (e.2.1 + permLattice TwistTag.E6.perm e.2.2) &&
        twistedE6ClassMemB (e.2.2 + (e.2.1 + permLattice TwistTag.E6.perm e.2.2)) done

@[expose] def twistedE6ClassTableOK (R Dl : List (Fin TwistTag.E6.tag.rank → ℤ)) :
    List (Fin TwistTag.E6.tag.rank → ℤ) →
      List (TwistedE6ClassStep × (Fin TwistTag.E6.tag.rank → ℤ) × (Fin TwistTag.E6.tag.rank → ℤ)) →
        Bool
  | _, [] => true
  | done, e :: es => twistedE6ClassEntryOK R Dl done e &&
      twistedE6ClassTableOK R Dl ((e.2.1 + e.2.2) :: done) es

@[expose] def twistedE6ClassTargets
    (T : List (TwistedE6ClassStep × (Fin TwistTag.E6.tag.rank → ℤ) ×
      (Fin TwistTag.E6.tag.rank → ℤ))) : List (Fin TwistTag.E6.tag.rank → ℤ) :=
  T.map fun e => e.2.1 + e.2.2

@[expose] def twistedE6ClassCheck (R : List (Fin TwistTag.E6.tag.rank → ℤ)) (h : ℤ)
    (T : List (TwistedE6ClassStep × (Fin TwistTag.E6.tag.rank → ℤ) ×
      (Fin TwistTag.E6.tag.rank → ℤ)))
    (L : List (Fin TwistTag.E6.tag.rank → ℤ)) : Bool :=
  R.all twistedE6TwoRootB &&
    twistedE6ClassTableOK R (twistedE6ClassTargets T) [] T &&
    (twistedE6ClassTargets T).all (fun x => twistedE6ClassCentralB x R &&
      twistedE6ClassCentralB (permLattice TwistTag.E6.perm x) R &&
      twistedE6ClassMemB (permLattice TwistTag.E6.perm x) (twistedE6ClassTargets T)) &&
    (List.range TwistTag.E6.tag.rootCertificate.roots.length).all (fun k =>
      decide (height (TwistTag.E6.tag.rootCertificate.root k) ≤ 0) ||
        ((decide (height (TwistTag.E6.tag.rootCertificate.root k) < h) ||
          twistedE6ClassMemB (TwistTag.E6.tag.rootCertificate.root k) (twistedE6ClassTargets T)) &&
        (twistedE6ClassMemB (TwistTag.E6.tag.rootCertificate.root k) L ||
          (twistedE6ClassTargets T).any fun δ =>
            twistedE6TwoRootB (TwistTag.E6.tag.rootCertificate.root k + δ)))) &&
    L.all (fun γ => twistedE6TwoRootB γ && decide (0 < height γ) &&
      (twistedE6ClassTargets T).all fun δ => !twistedE6TwoRootB (γ + δ)) &&
    L.all (fun γ => L.all fun γ' => !twistedE6TwoRootB (γ + γ'))

@[expose] def twistedE6ClassUTable : List (TwistedE6ClassStep × (Fin TwistTag.E6.tag.rank → ℤ) ×
    (Fin TwistTag.E6.tag.rank → ℤ)) :=
  [(.ff, ![0, 1, 0, 0, 0, 0], ![1, 1, 2, 3, 2, 1]),
    (.ff, ![0, -1, 0, 0, 0, 0], ![1, 2, 2, 3, 2, 1]),
    (.ff, ![0, -1, 0, -1, 0, 0], ![1, 2, 2, 3, 2, 1]),
    (.ppp, ![0, 0, 0, 0, 1, 1], ![1, 1, 1, 2, 1, 0]),
    (.ppp, ![0, 0, 0, 0, 0, 1], ![1, 1, 2, 2, 1, 0]),
    (.fp, ![0, 0, 1, 1, 1, 0], ![0, 1, 0, 1, 1, 1]),
    (.ff, ![0, -1, -1, -1, -1, 0], ![1, 2, 2, 3, 2, 1]),
    (.fp, ![0, 0, 1, 1, 1, 0], ![1, 1, 1, 1, 0, 0]),
    (.fp, ![0, 0, 0, 1, 0, 0], ![0, 1, 1, 1, 1, 1]),
    (.ff, ![0, -1, -1, -2, -1, 0], ![1, 2, 2, 3, 2, 1]),
    (.fp, ![0, 0, 0, 1, 0, 0], ![1, 1, 1, 1, 1, 0]),
    (.fp, ![0, 0, 0, -1, 0, 0], ![0, 1, 1, 2, 1, 1]),
    (.ff, ![0, 0, 0, 1, 0, 0], ![0, 1, 1, 1, 1, 0]),
    (.ff, ![0, -1, -1, -2, -1, 0], ![1, 1, 2, 3, 2, 1]),
    (.fp, ![0, 0, 0, -1, 0, 0], ![1, 1, 1, 2, 1, 0]),
    (.fp, ![0, -1, 0, -1, 0, 0], ![0, 1, 1, 2, 1, 1]),
    (.fp, ![0, 0, -1, -1, -1, 0], ![0, 1, 1, 2, 2, 1]),
    (.ff, ![0, 0, 0, -1, 0, 0], ![0, 1, 1, 2, 1, 0]),
    (.fp, ![0, -1, 0, -1, 0, 0], ![1, 1, 1, 2, 1, 0]),
    (.fp, ![0, 0, -1, -1, -1, 0], ![1, 1, 2, 2, 1, 0]),
    (.fp, ![0, -1, -1, -1, -1, 0], ![0, 1, 1, 2, 2, 1]),
    (.ff, ![0, -1, 0, -1, 0, 0], ![0, 1, 1, 2, 1, 0]),
    (.fp, ![0, -1, -1, -1, -1, 0], ![1, 1, 2, 2, 1, 0]),
    (.fp, ![0, -1, -1, -2, -1, 0], ![0, 1, 1, 2, 2, 1]),
    (.ff, ![0, 0, -1, -1, -1, 0], ![0, 1, 1, 2, 1, 0]),
    (.fp, ![0, -1, -1, -2, -1, 0], ![1, 1, 2, 2, 1, 0]),
    (.fp, ![0, -1, -1, -2, -1, 0], ![0, 1, 1, 2, 1, 1]),
    (.ff, ![0, -1, -1, -1, -1, 0], ![0, 1, 1, 2, 1, 0]),
    (.ff, ![0, 0, -1, -1, -1, 0], ![0, 1, 1, 1, 1, 0]),
    (.fp, ![0, -1, -1, -2, -1, 0], ![1, 1, 1, 2, 1, 0])]
@[expose] def twistedE6ClassUAnn : List (Fin TwistTag.E6.tag.rank → ℤ) :=
  [![1, 1, 1, 2, 2, 1], ![1, 1, 2, 2, 1, 1], ![1, 2, 2, 3, 2, 1]]
@[expose] def twistedE6ClassVTable : List (TwistedE6ClassStep × (Fin TwistTag.E6.tag.rank → ℤ) ×
    (Fin TwistTag.E6.tag.rank → ℤ)) :=
  [(.ff, ![0, 1, 0, 0, 0, 0], ![1, 1, 2, 3, 2, 1]),
    (.ff, ![0, -1, 0, 0, 0, 0], ![1, 2, 2, 3, 2, 1]),
    (.ff, ![0, 0, 1, 1, 1, 0], ![1, 1, 1, 1, 1, 1]),
    (.fp, ![1, 0, 1, 1, 1, 1], ![0, 1, 0, 1, 1, 0]),
    (.fp, ![1, 0, 1, 1, 1, 1], ![0, 1, 1, 1, 0, 0]),
    (.fp, ![0, 0, 1, 1, 1, 0], ![0, 1, 0, 1, 1, 1]),
    (.ppf, ![0, 0, 0, 1, 1, 1], ![1, 1, 1, 1, 0, 0]),
    (.fp, ![0, 0, 1, 1, 1, 0], ![1, 1, 1, 1, 0, 0]),
    (.ppp, ![0, 0, 0, 1, 1, 1], ![0, 1, 1, 1, 0, 0]),
    (.ff, ![0, 1, 0, 0, 0, 0], ![1, 0, 1, 1, 1, 1]),
    (.ppp, ![0, 0, 0, 1, 1, 0], ![1, 1, 1, 1, 0, 0]),
    (.ppf, ![0, 0, 0, 1, 1, 0], ![0, 1, 1, 1, 0, 0]),
    (.ff, ![0, -1, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1]),
    (.fp, ![0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 1, 1]),
    (.ff, ![0, 0, 1, 1, 1, 0], ![0, 1, 0, 0, 0, 0]),
    (.fp, ![0, 1, 0, 0, 0, 0], ![1, 0, 1, 1, 0, 0]),
    (.fp, ![0, -1, 0, 0, 0, 0], ![0, 1, 0, 1, 1, 1]),
    (.ff, ![0, -1, 0, 0, 0, 0], ![0, 1, 1, 1, 1, 0]),
    (.fp, ![0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 1, 0]),
    (.fp, ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 1, 0, 0]),
    (.fp, ![0, -1, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0]),
    (.fp, ![0, -1, 0, 0, 0, 0], ![0, 1, 0, 1, 1, 0]),
    (.fp, ![0, -1, 0, 0, 0, 0], ![0, 1, 1, 1, 0, 0])]
@[expose] def twistedE6ClassVAnn : List (Fin TwistTag.E6.tag.rank → ℤ) :=
  [![0, 1, 1, 2, 1, 1], ![1, 1, 1, 2, 1, 0], ![1, 1, 2, 2, 2, 1], ![1, 1, 2, 3, 2, 1],
    ![1, 2, 2, 3, 2, 1]]

@[expose] def twistedE6ClassURoots : List (Fin TwistTag.E6.tag.rank → ℤ) :=
  [twistedE6ClassRootU, twistedE6ClassRootU']

@[expose] def twistedE6ClassVRoots : List (Fin TwistTag.E6.tag.rank → ℤ) :=
  [twistedE6ClassRootA, twistedE6ClassRootA', twistedE6ClassRootB]

theorem twistedE6ClassCheck_U :
    twistedE6ClassCheck twistedE6ClassURoots 4 twistedE6ClassUTable twistedE6ClassUAnn = true := by
  decide +kernel

theorem twistedE6ClassCheck_V :
    twistedE6ClassCheck twistedE6ClassVRoots 6 twistedE6ClassVTable twistedE6ClassVAnn = true := by
  decide +kernel

end CFSG.SeitzReduction
