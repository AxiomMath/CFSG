module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1ComponentCases3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.AGLEmbedding (centerQuotientAction)

variable {G : Type} [Group G] [Finite G]

theorem D1ComponentData3.exists_extraspecial {p : ℕ} [Fact p.Prime] {P : Sylow p G}
    {M H R : Subgroup G} {z : G} {Pbar : Sylow p (ReducedCentralizer p z)}
    {zbar : ReducedCentralizer p z} {K : Subgroup (ReducedCentralizer p z)}
    (h : D1ComponentData3 p P M H R z Pbar zbar K) :
    ∃ E L : Subgroup (ReducedCentralizer p z),
      E ≤ (Pbar : Subgroup (ReducedCentralizer p z)) ∧ Nat.card E = p ^ 3 ∧
      (∀ x ∈ E, x ^ p = 1) ∧ (Subgroup.center E).map E.subtype = Subgroup.zpowers zbar ∧
      ∃ e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p),
        StatedSL 2 (ZMod p) ≤
          (L.subgroupOf (Subgroup.normalizer (E : Set (ReducedCentralizer p z)))).map
            (centerQuotientAction E e) := by
  obtain ⟨Pbar', zbar', hPbar', -, hzbar', -, -, -, -, -, E, L, hER, hEcard, hEexp, hEZ, e,
    hSL⟩ := h.input.exists_reduced_data h.glob.simple h.glob.nonab h.glob.kProper
  have hPeq : Pbar' = Pbar := Sylow.ext (hPbar'.trans h.pbar.symm)
  have hzeq : zbar' = zbar := by
    let zC : Subgroup.centralizer ({z} : Set G) :=
      ⟨z, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
    exact (hzbar' zC rfl).symm.trans (h.zbar_eq zC rfl)
  subst hPeq hzeq
  exact ⟨E, L, hER, hEcard, hEexp, hEZ, e, hSL⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
