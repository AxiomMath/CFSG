module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.LeviNode
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGTwoData

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.LieType.Universal
  CFSG.LieType.Universal.SpecialLinear CFSG.LieType.Steinberg

section SL

variable {m : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]

theorem nodeLevi_sl (i : Fin m) : NodeLevi (rootDatum m F) i := by
  obtain ⟨φ, hφ, hx, hy⟩ := SL.rankOne (F := F) i
  exact nodeLevi_of_range_sl2 hφ (rankOne_eq_range_of_sl2 SL.isParametrization hx hy)

end SL

section Sp

open CFSG.LieType.Universal.Symplectic

variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]

theorem nodeLevi_sp (i : Fin n) : NodeLevi (Symplectic.rootDatum n F) i := by
  obtain ⟨φ, hφ, hx, hy⟩ := Sp.rankOne (F := F) i
  exact nodeLevi_of_range_sl2 hφ (rankOne_eq_range_of_sl2 Sp.isParametrization hx hy)

end Sp

section SpinPlus

open CFSG.LieType.Universal.Spin

variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]

theorem nodeLevi_spinPlus (hn : 3 ≤ n) (i : Fin n) : NodeLevi (plusDatum n F hn) i := by
  obtain ⟨φ, hφ, hx, hy⟩ := SpinPlus.rankOne (K := F) hn i
  exact nodeLevi_of_range_sl2 hφ
    (rankOne_eq_range_of_sl2 (SpinPlus.isParametrization (K := F) hn) hx hy)

end SpinPlus

section G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.AGLEmbedding.LeviBlock

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem nodeLevi_g2 (i : Fin (Tag.rank .G2)) : NodeLevi (g2Datum K) i := by
  obtain ⟨e⟩ := nonempty_sl2_mulEquiv_rankOne_g2 (F := K) i
  exact nodeLevi_of_equiv_sl2 e

end G2

end CFSG.AGLEmbeddingD2.Tits.GN516
