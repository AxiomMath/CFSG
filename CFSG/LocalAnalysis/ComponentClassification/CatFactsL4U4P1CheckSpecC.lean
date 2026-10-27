module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1Check
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.SmallOddCore.CentSpec

public section

namespace CFSG.ComponentClassification.HarrisLit.P1

open CFSG Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier

variable {n : ℕ}

structure CheckFacts (n NP cap : ℕ) (pg : Array Table) (sift : Table → Bool) (runs : List Run)
    (extra : List Table) : Prop where
  ne : runs ≠ []
  pginv : ∀ g ∈ pg, invOK n g (invT n g) = true
  cent : ∀ R ∈ runs, centDataOK n NP cap pg (pg.map (invT n)) sift R.u R.sylowGens R.sylowOrder
    (R.rows.map (·.row)) = true
  perm : ∀ R ∈ runs, permOK n R.u = true ∧ invOK n R.u (invT n R.u) = true
  primes : ∀ R ∈ runs, ∀ r ∈ R.rows,
    0 < r.row.centOrder ∧ r.row.oddPrimes = oddPrimeDivs r.row.centOrder
  row : ∀ i < runs.length, ∀ r ∈ (runs.getD i default).rows,
    rowOK n cap pg (pg.map (invT n)) sift runs (goodClasses n cap pg (pg.map (invT n)) runs)
      (i == 0) r = true
  extra : ∀ u ∈ extra, extraOK n pg sift u = true
  a6 : permOK 6 a6a = true ∧ permOK 6 a6b = true ∧ oddOK 6 a6a = true ∧ oddOK 6 a6b = true ∧
    enumOK 6 cap 360 [a6a, a6b] = true

structure RowFacts (A₀ : Subgroup (Equiv.Perm (Fin n))) (r : ClassRow) : Prop where
  rep : Rep n r.rep (tp n r.rep)
  ord : orderOf (tp n r.rep) = 2
  outer : r.outer = true ↔ tp n r.rep ∉ A₀
  cent : closure (tp n '' {x | x ∈ r.centGens.toArray}) =
    A₀ ⊓ centralizer ({tp n r.rep} : Set (Equiv.Perm (Fin n)))
  card : Nat.card ↥(A₀ ⊓ centralizer ({tp n r.rep} : Set (Equiv.Perm (Fin n)))) = r.centOrder
  cls : (Sporadic.SmallOddCore.conjClass A₀ (tp n r.rep)).ncard = r.classSize

structure RunFacts (A₀ : Subgroup (Equiv.Perm (Fin n))) (R : Run) : Prop where
  repu : Rep n R.u (tp n R.u)
  repuinv : Rep n (invT n R.u) (tp n R.u)⁻¹
  u2 : tp n R.u ^ 2 = 1
  uout : tp n R.u ∉ A₀
  unorm : ∀ p ∈ A₀, tp n R.u * p * (tp n R.u)⁻¹ ∈ A₀
  memR : ∀ x, x ∈ A₀ ⊔ zpowers (tp n R.u) ↔ x ∈ A₀ ∨ x * tp n R.u ∈ A₀
  row : ∀ r ∈ R.rows, RowFacts A₀ r.row
  cover : ∀ t ∈ A₀ ⊔ zpowers (tp n R.u), orderOf t = 2 →
    ∃ r ∈ R.rows, ∃ g ∈ A₀, t = g * tp n r.row.rep * g⁻¹

variable {A₀ : Subgroup (Equiv.Perm (Fin n))} {pg : Array Table} {gg : ℕ → Equiv.Perm (Fin n)}
  {sift : Table → Bool}

end CFSG.ComponentClassification.HarrisLit.P1
