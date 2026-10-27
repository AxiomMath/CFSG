module

public import CFSG.LocalAnalysis.GL83PartI.I_22_6.Gen
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup

public section

namespace GL83

open CFSG.Open GL83.CompFam

theorem component_le_gamma_of_not_normalizes {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {B K : Subgroup X} (hB : IsElemAbelian p B)
    (hSC : ∀ y ∈ Subgroup.centralizer (B : Set X), y ^ p = 1 → y ∈ B)
    (hK : IsComponentOf K ⊤) (hKB : ¬ B ≤ Subgroup.normalizer (K : Set X))
    (hZ : p ∣ Nat.card (Subgroup.center K)) : K ≤ GLBCore p 2 B := by
  have : Fact p.Prime := ⟨hp⟩
  exact (le_layer (mem_conjSet_self B K)).trans
    ((isFam_conjSet hB hK).layer_le_gamma hp2 hSC (mem_conjSet_self B K) hKB hZ)

theorem I_22_6_proved :
    ∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime → p ≠ 2 →
      ∀ B K : Subgroup X, IsElemAbelian p B →
        (∀ y ∈ Subgroup.centralizer (B : Set X), y ^ p = 1 → y ∈ B) →
        IsComponentOf K ⊤ → ¬ B ≤ Subgroup.normalizer (K : Set X) →
        p ∣ Nat.card (Subgroup.center K) → K ≤ GLBCore p 2 B := by
  intro X _ _ p hp hp2 B K hB hSC hK hKB hZ
  exact component_le_gamma_of_not_normalizes hp hp2 hB hSC hK hKB hZ

end GL83
