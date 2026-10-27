module

public import CFSG.Adapters.LinearFieldTransport
public import CFSG.CGT.Timmesfeld75.L2Pair

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open CFSG.Assembly.LowTwoRank

theorem exists_psl2_galois_of_statedClassicalModel {G : Type} [Group G] {f : ℕ}
    (hG : StatedClassicalModel G .PSL 2 2 f) :
    2 ≤ f ∧ Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f)) := by
  obtain ⟨⟨-, hf1, -, hf2, -⟩, K, _, _, hK, ⟨e⟩⟩ := hG
  have hf : 2 ≤ f := by
    by_contra h
    exact hf2 (by rw [show f = 1 by omega, pow_one])
  exact ⟨hf, ⟨e.trans (CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL K 2 2 f
    (by omega) hK)⟩⟩

theorem psl2_wc {G : Type} [Group G] [Finite G] {f : ℕ}
    (hG : StatedClassicalModel G .PSL 2 2 f) {T : Subgroup G} (hT : IsWC T) (hT1 : T ≠ ⊥) :
    (Nat.card T = 2 ^ f ∧ (∃ S : Sylow 2 G, (S : Subgroup G) = T) ∧ BorelTwoTransitive G T) ∧
      ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 →
        ∃ g ∈ Subgroup.normalizer (T : Set G), g * x * g⁻¹ = y := by
  obtain ⟨hf, he⟩ := exists_psl2_galois_of_statedClassicalModel hG
  obtain ⟨S, hTS⟩ := (isPGroup_two_of_isElemAbelian hT.1).exists_le_sylow
  have hpair : IsL2Pair G (S : Subgroup G) (2 ^ f) := IsL2Pair.of_psl_sylow (by omega) he S
  have hTeq : T = S := hpair.eq_of_isWC hTS hT1 hT
  subst hTeq
  refine ⟨⟨hpair.card_eq, ⟨S, rfl⟩, hpair.conjTwoTransitive, S, rfl⟩, ?_⟩
  intro x hx hx1 y hy hy1
  exact hpair.transitive hx hx1 hy hy1

end CFSG.CGT.Timmesfeld75
