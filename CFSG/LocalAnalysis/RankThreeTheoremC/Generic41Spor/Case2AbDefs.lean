module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (CentSeries)

structure PGroupDataAb (p : ℕ) {Y : Type*} [Group Y] (P T D : Subgroup Y) (x : Y) : Prop where
  T_le : T ≤ P
  D_le : D ≤ P
  sup_eq : T ⊔ D = P
  inf_eq : T ⊓ D = ⊥
  comm : ∀ t ∈ T, ∀ d ∈ D, t * d = d * t
  T_card : Nat.card T = p ^ 2
  T_exp : ∀ t ∈ T, t ^ p = 1
  T_comm : IsMulCommutative T
  D_cyc : IsCyclic D
  x_mem : x ∈ D
  x_ord : orderOf x = p

structure Case2DataAb (p : ℕ) {Y : Type} [Group Y] [Finite Y] (P T D F : Subgroup Y) (x : Y) : Prop where
  prime : p.Prime
  five : 5 ≤ p
  core : primeComplementCore (G := Y) p = ⊥
  catalog : CatalogSimpleSections Y
  rank : CFSG.Open.pRank p (⊤ : Subgroup Y) ≤ 3
  sylow : ∃ S : Sylow p Y, (S : Subgroup Y) = P
  pdata : PGroupDataAb p P T D x
  F_T : ∀ f ∈ F, ∀ t ∈ T, f * t * f⁻¹ ∈ T
  F_trans : ∀ a ∈ T, a ≠ 1 → ∀ b ∈ T, b ≠ 1 → ∃ f ∈ F, f * a * f⁻¹ = b
  series : ∃ N : Subgroup Y, CentSeries p (centralizer ({x} : Set Y)) P N
  wc : ∀ g : Y, (zpowers x).map (MulAut.conj g).toMonoidHom ≤ P →
    (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
