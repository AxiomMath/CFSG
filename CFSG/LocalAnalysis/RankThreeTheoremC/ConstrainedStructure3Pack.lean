module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ConstrainedStructure3Borel
public import CFSG.LocalAnalysis.RankThreeTheoremC.ConstrainedStructure3Det

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding

structure ReducedStructure3 (p : ℕ) [Fact p.Prime] {X : Type*} [Group X] (R : Sylow p X)
    (X₀ : Subgroup X) (z : X) (E C : Subgroup X) [E.Normal]
    (e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p)) : Prop where
  centralizer_pCore_le : Subgroup.centralizer (CFSG.pCore p X : Set X) ≤ CFSG.pCore p X
  le_pCore : E ≤ CFSG.pCore p X
  card_eq : Nat.card E = p ^ 3
  pow_eq_one : ∀ x ∈ E, x ^ p = 1
  center_eq : (Subgroup.center E).map E.subtype = Subgroup.zpowers z
  isCyclic : IsCyclic C
  zpowers_le : Subgroup.zpowers z ≤ C
  omega_le : ∀ y ∈ C, y ^ p = 1 → y ∈ Subgroup.zpowers z
  le_sylow : C ≤ (R : Subgroup X)
  centralizer_eq : Subgroup.centralizer (E : Set X) = C
  inf_eq : E ⊓ C = Subgroup.zpowers z
  sup_eq : E ⊔ C = CFSG.pCore p X
  relIndex_eq : (CFSG.pCore p X).relIndex (R : Subgroup X) = p
  ker_eq : (centerQuotientActionNormal E e).ker = CFSG.pCore p X
  range_eq : (centerQuotientActionNormal E e).range = StatedSL 2 (ZMod p)
  eq_normalizer : X₀ = Subgroup.normalizer ((R : Subgroup X) : Set X)
  index_eq : X₀.index = p + 1

end CFSG.LocalAnalysis.RankThreeTheoremC

namespace CFSG.AGLEmbedding

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.RankThreeTheoremC

theorem ReducedNongeneration.exists_reducedStructure3 {p : ℕ} [Fact p.Prime] {X : Type*}
    [Group X] [Finite X] {R : Sylow p X} {X₀ : Subgroup X} (h : ReducedNongeneration p X R X₀)
    (hlayer : CFSG.layer X = ⊥) {z : X} (hzc : z ∈ Subgroup.center X) (hzp : orderOf z = p) :
    ∃ (E C : Subgroup X) (_ : E.Normal)
      (e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p)),
      ReducedStructure3 p R X₀ z E C e := by
  have hz : z ∈ Subgroup.centralizer ((R : Subgroup X) : Set X) :=
    Subgroup.center_le_centralizer _ hzc
  obtain ⟨hQc, E, C, hEn, hEQ, hCR, hEcard, hEexp, hEZ, hcyc, hCz, hΩ, -, -, hDC, hEC, hQeq,
    hrel, hker, e, hSL⟩ := h.structure_of_layer_eq_bot3 hlayer hz hzp
  exact ⟨E, C, hEn, e, hQc, hEQ, hEcard, hEexp, hEZ, hcyc, hCz, hΩ, hCR, hDC, hEC, hQeq, hrel,
    Subgroup.ext fun x => (mem_ker_centerQuotientActionNormal hEZ e).trans (hker x).symm,
    range_centerQuotientActionNormal_eq_statedSL hEZ hzp e hSL hzc,
    h.eq_normalizer_of_layer_eq_bot3 hlayer hz hzp,
    h.index_eq_succ_of_layer_eq_bot3 hlayer hz hzp⟩

end CFSG.AGLEmbedding
