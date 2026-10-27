module

public import CFSG.LocalAnalysis.GLTheoremA.S8.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S8

variable {K : Type} [Group K]

@[expose] def rowIOf (p : ℕ) (d : K) : Subgroup K :=
  GLAPLayer p (Subgroup.centralizer ({d} : Set K))

@[expose] def rowKOf (p : ℕ) (d : K) (R : Subgroup K) : Subgroup K :=
  GLAPLayer p (rowIOf p d ⊓ Subgroup.normalizer (R : Set K))

@[expose] def rowR0Of (d : K) (R : Subgroup K) : Subgroup K :=
  R ⊓ Subgroup.centralizer ({d} : Set K)

structure I301ARowCfg [Finite K] (row : Row) (R B₁ : Subgroup K) (d : K) : Prop where
  hR : IsExtraSpec2 R ∧ Nat.card R = 2 ^ row.rexp
  hB : IsElemAbelian row.prime B₁ ∧ Nat.card B₁ = row.prime ^ (row.rank - 1)
  hBN : B₁ ≤ Subgroup.normalizer (R : Set K)
  hd : d ∈ B₁ ∧ d ≠ 1
  hI : RowI row row.prime (rowIOf row.prime d)
  hK : RowK row row.prime (rowKOf row.prime d R)
  hR0 : Nat.card (rowR0Of d R) = 2 ^ row.r0exp
  hR0t : IsExtraSpec2 (rowR0Of d R) ∨ Nat.card (rowR0Of d R) = 2
  hK6 : row = .ly ∨ rowKOf row.prime d R =
    GLAPLayer row.prime (Subgroup.centralizer ({d} : Set K) ⊓
      Subgroup.centralizer (centerOf (rowR0Of d R) : Set K))
  hNL : row = .m5 → ∃ J₀ : Subgroup K,
    GLAPComponent 5 (Subgroup.normalizer (R : Set K)) J₀ ∧ catalogIs (PSimple 5 J₀) (sporIs .Co1)
  hMax : ∀ (A : Type) [Group A] [Finite A] (ι : K →* A), Function.Injective ι →
    ι.range.Normal → Subgroup.centralizer (ι.range : Set A) = ⊥ →
    ∀ R' : Subgroup A, IsPGroup 2 R' →
      (rowKOf row.prime d R ⊔ B₁).map ι ≤ Subgroup.normalizer (R' : Set A) →
      R.map ι ≤ R' → R' = R.map ι

@[expose] def I301ARow (row : Row) : Prop :=
  row.center = 1 → ∀ (K : Type) [Group K] [Finite K], catalogIs K (sporIs row.name) →
    ∃ (R B₁ : Subgroup K) (d : K), I301ARowCfg row R B₁ d

end CFSG.LocalAnalysis.GLTheoremA.H301
