module

public import Mathlib.GroupTheory.Sylow
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.RelIndexPrime

public section

namespace CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs

theorem isConj_of_natCard_eq_prime_of_sylow_cyclic {X : Type*} [Group X] [Finite X] {p : ℕ}
    [hp : Fact p.Prime] (hcyc : ∀ Q : Sylow p X, IsCyclic (Q : Subgroup X))
    {Y₁ Y₂ : Subgroup X} (h₁ : Nat.card Y₁ = p) (h₂ : Nat.card Y₂ = p) :
    ∃ g : X, Y₁.map (MulAut.conj g).toMonoidHom = Y₂ := by
  obtain ⟨Q₁, hQ₁⟩ := (IsPGroup.of_card (n := 1) (by rw [h₁, pow_one])).exists_le_sylow
  obtain ⟨Q₂, hQ₂⟩ := (IsPGroup.of_card (n := 1) (by rw [h₂, pow_one])).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X Q₁ Q₂
  have hQ : Q₁.map (MulAut.conj g).toMonoidHom = (Q₂ : Subgroup X) := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  have hZQ : Y₁.map (MulAut.conj g).toMonoidHom ≤ (Q₂ : Subgroup X) := by
    rw [← hQ]
    exact Subgroup.map_mono hQ₁
  have hY₂Q : Y₂ ≤ (Q₂ : Subgroup X) := hQ₂
  have hZcard : Nat.card (Y₁.map (MulAut.conj g).toMonoidHom) = p :=
    (Nat.card_congr (MulEquiv.subgroupMap (MulAut.conj g) Y₁).toEquiv).symm.trans h₁
  have hsub : (Y₁.map (MulAut.conj g).toMonoidHom).subgroupOf (Q₂ : Subgroup X) =
      Y₂.subgroupOf (Q₂ : Subgroup X) := by
    rw [IsCyclic.subgroup_eq_iff_card_eq]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZQ).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY₂Q).toEquiv, hZcard, h₂]
  have e1 := Subgroup.map_subgroupOf_eq_of_le hZQ
  have e2 := Subgroup.map_subgroupOf_eq_of_le hY₂Q
  rw [hsub] at e1
  exact ⟨g, e1.symm.trans e2⟩

end CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs
