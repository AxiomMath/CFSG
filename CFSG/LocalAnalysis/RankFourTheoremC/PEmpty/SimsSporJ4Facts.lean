module

public import CFSG.Sporadic.J4.QTProof

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.SimsSporJ4

open CFSG.Sporadic.J4

structure RowFactsJ (p m n : ℕ) (col : ℕ → ℕ) (N : ℕ) (z u : J) (L : List J) : Prop where
  z_pow : z ^ p = 1
  z_ne : z ≠ 1
  conj : u * z * u⁻¹ = z ^ m
  u_pow : u ^ n = 1
  u_half : u ^ (n / 2) = QT.eta QT.uJ 11 1
  cols : ∀ j < 11, u * QT.uJ j * u⁻¹ = QT.eta QT.uJ 11 (col j)
  comm : ∀ e ∈ L, e * u = u * e
  nodup : L.Nodup
  inv : ∀ e ∈ L, e = 1 ∨ e * e ≠ 1 ∨ e * (z * e * z⁻¹) ≠ z * e * z⁻¹ * e
  length : L.length = N

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.SimsSporJ4

end
