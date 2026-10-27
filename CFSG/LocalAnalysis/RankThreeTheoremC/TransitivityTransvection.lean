module

public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityCentralizer
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.MaximalPairGeometry

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem ExtremalObstruction.exists_mem_normalizer_not_mem_centralizer (hS : Setting G)
    (hD1 : TheoremD1 G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M D : Subgroup G}
    (hext : ExtremalObstruction p P M D) (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G))
    (hDab : IsMulCommutative D) (hCM : centralizer (D : Set G) ≤ M) :
    ∃ n ∈ (P : Subgroup G), n ∈ normalizer (D : Set G) ∧ n ∉ centralizer (D : Set G) := by
  have hprime := sigmaA_prime p hp
  obtain ⟨hDe, -⟩ := hext.isElemAbelian_of_isMulCommutative hprime hDab
  have hDP : D ≤ P := hext.obstruction.2.1
  by_contra h
  push Not at h
  set A : Subgroup G := (P : Subgroup G) ⊓ normalizer (D : Set G) with hA
  have hAP : A < P := lt_of_le_of_ne inf_le_left fun heq => hPD (by rw [← heq]; exact inf_le_right)
  obtain ⟨m, hmN, hmA⟩ := IsConcreteLE.exists_of_lt
    (pGroup_proper_subgroup_lt_internal_normalizer p hprime P A P.isPGroup' hAP)
  apply hmA
  refine ⟨hmN.1, ?_⟩
  have hmD : ∀ d ∈ D, m * d * m⁻¹ ∈ D := by
    intro d hd
    have hdA : d ∈ A := ⟨hDP hd, le_normalizer hd⟩
    have hconjA : m * d * m⁻¹ ∈ A := (mem_normalizer_iff.mp hmN.2 d).mp hdA
    have hpow : (m * d * m⁻¹) ^ p = 1 := by
      rw [conj_pow, hDe.2 d hd, mul_one, mul_inv_cancel]
    exact hext.mem_of_mem_centralizer_of_isMulCommutative hS hD1 hp hDab hCM
      (h _ hconjA.1 hconjA.2) hpow
  have hle : D.map (MulAut.conj m).toMonoidHom ≤ D := by
    rintro _ ⟨d, hd, rfl⟩
    exact hmD d hd
  exact mem_normalizer_iff_map_conj_eq.mpr
    (Subgroup.eq_of_le_of_card_ge hle (card_map_of_injective (MulAut.conj m).injective).ge)

end CFSG.LocalAnalysis.RankThreeTheoremC
