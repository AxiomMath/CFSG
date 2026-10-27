module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S8

variable {K : Type} [Group K]

noncomputable abbrev centerQuot (K : Type) [Group K] : K →* K ⧸ Subgroup.center K :=
  QuotientGroup.mk' (Subgroup.center K)

structure I301ACoverCfg [Finite K] (row : Row) (R B₁ : Subgroup K) (d : K) : Prop where
  hR : IsExtraSpec2 R ∧ Nat.card R = 2 ^ row.rexp
  hB : IsElemAbelian row.prime B₁ ∧ Nat.card B₁ = row.prime ^ (row.rank - 1)
  hBZ : B₁ ⊓ Subgroup.center K = ⊥
  hBN : B₁ ≤ Subgroup.normalizer (R : Set K)
  hd : d ∈ B₁ ∧ d ≠ 1
  hI : RowI row row.prime (rowIOf row.prime d)
  hK : RowK row row.prime (rowKOf row.prime d R)
  hR0 : Nat.card (rowR0Of d R) = 2 ^ row.r0exp
  hR0t : IsExtraSpec2 (rowR0Of d R) ∨ Nat.card (rowR0Of d R) = 2
  hK6 : rowKOf row.prime d R =
    GLAPLayer row.prime (Subgroup.centralizer ({d} : Set K) ⊓
      Subgroup.centralizer (centerOf (rowR0Of d R) : Set K))
  hMax : ∀ (A : Type) [Group A] [Finite A] (ι : K ⧸ Subgroup.center K →* A),
    Function.Injective ι → ι.range.Normal → Subgroup.centralizer (ι.range : Set A) = ⊥ →
    ∀ R' : Subgroup A, IsPGroup 2 R' →
      ((rowKOf row.prime d R ⊔ B₁).map (centerQuot K)).map ι ≤
        Subgroup.normalizer (R' : Set A) →
      (R.map (centerQuot K)).map ι ≤ R' → R' = (R.map (centerQuot K)).map ι

@[expose] def I301ARowCover (row : Row) : Prop :=
  row.center = 3 → ∀ (K : Type) [Group K] [Finite K], ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤ →
    Nat.card (Subgroup.center K) = 3 → catalogIs (K ⧸ Subgroup.center K) (sporIs row.name) →
    ∃ (R B₁ : Subgroup K) (d : K), I301ACoverCfg row R B₁ d

end CFSG.LocalAnalysis.GLTheoremA.H301
