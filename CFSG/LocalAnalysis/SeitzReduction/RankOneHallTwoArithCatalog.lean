module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneHallTwoArithAltSporSporadic
public import CFSG.LocalAnalysis.SeitzReduction.RankOneHallTwoArithCatalogLie
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.RankThree.PartOne.S11d.PlaneCases

public section

namespace CFSG.SeitzReduction.RankOne

open CFSG.Assembly.LowTwoRank CFSG.Blueprint

theorem catalog_of_hallTwoArith {T : Type} [Group T] [IsSimpleGroup T] (hT : Catalog T)
    (hnonab : ∃ a b : T, a * b ≠ b * a) (H : HallTwoArith (Nat.card T)) :
    StatedClassicalModel T .PSL 3 2 1 ∧ Nat.card T = 168 := by
  rcases RankThree.PartOne.PlaneCases.catalog_cases hT with
    ⟨q, -, ⟨θ⟩⟩ | ⟨k, hk, ⟨θ⟩⟩ | ⟨t, m, p, f, hadm, hmodel⟩ | hs
  · obtain ⟨a, b, hab⟩ := hnonab
    exact (hab (θ.injective (by rw [map_mul, map_mul, mul_comm]))).elim
  · exact (not_hallTwoArith_card_of_mulEquiv_alternatingGroup hk θ H).elim
  · exact statedClassicalModel_of_lieModel_hallTwoArith
      ComponentClassification.CatLeafProof.lieOrderFormulasInput hadm hmodel H
  · exact (not_hallTwoArith_sporadic hs H).elim

theorem catalog_hallTwoArith {T : Type} [Group T] [IsSimpleGroup T] (hT : Catalog T)
    (hnonab : ∃ a b : T, a * b ≠ b * a) {e h : ℕ} (hcard : Nat.card T = 2 ^ e * h)
    (he1 : 1 ≤ e) (hh : Odd h) (hdiv : h ∣ (2 ^ e - 1) * e) :
    StatedClassicalModel T .PSL 3 2 1 ∧ e = 3 ∧ h = 21 := by
  obtain ⟨hm, h168⟩ := catalog_of_hallTwoArith hT hnonab ⟨e, h, he1, hcard, hh, hdiv⟩
  exact ⟨hm, eq_three_of_card_eq_168 h168 hcard hh⟩

end CFSG.SeitzReduction.RankOne
