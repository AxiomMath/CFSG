module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles
public import CFSG.Quasithin.Background.C1GNDefs
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoBaum
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoUThompson
import CFSG.Quasithin.Background.C1GNNotation

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem le_gnA_of_scalarTorus {X : Type} [Group X] [Finite X] {T T₁ T₂ : Subgroup X}
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤) (hc : CFSG.Quasithin.IsC118Pair T T₁ T₂)
    {Ls : Subgroup (X ⧸ gnC T)} (hinv : gnImg T T ≤ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)))
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {E : Subgroup (X ⧸ gnC T)} (hELs : E ≤ Ls)
    (hEU : E ≤ Subgroup.normalizer ((gnImg T T ⊓ Ls : Subgroup (X ⧸ gnC T)) : Set (X ⧸ gnC T)))
    (hEq : ∀ x ∈ E, x ^ q = 1)
    (hscal : ∀ s ∈ gnImg T T, ∃ j : ℕ, ∀ x ∈ E, s * x * s⁻¹ * (x ^ j)⁻¹ ∈ gnImg T T ⊓ Ls)
    (hinvol : ∀ s ∈ gnImg T T, s * s = 1 → ∀ x ∈ E, s * x * s⁻¹ * x⁻¹ ∈ gnImg T T ⊓ Ls) :
    E ≤ gnA T T₁ Ls ∨ E ≤ gnA T T₂ Ls := by
  classical
  have hSU : gnImg T T ≤ Subgroup.normalizer
      ((gnImg T T ⊓ Ls : Subgroup (X ⧸ gnC T)) : Set (X ⧸ gnC T)) := by
    intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx, hinv hx⟩
  have hJ : gnImg T (CFSG.Quasithin.thompsonJ T) ≤
      scalarKer (gnImg T T) (gnImg T T ⊓ Ls) E := by
    refine gnImg_thompsonJ_le_of_sq_eq_one ?_
    intro s hsT hss
    exact (mem_scalarKer_iff hSU).mpr ⟨hsT, fun x hx => hinvol s hsT hss x hx⟩
  exact le_gnA_of_thompsonJ_le_scalarKer hT hc hinv hq hq2 hELs hEU hEq
    (fun s hs => hscal s (Subgroup.map_mono (CFSG.Quasithin.C1GN.baum_le T) hs)) hJ

end CFSG.LocalAnalysis.RankThreeUC.S15

end
