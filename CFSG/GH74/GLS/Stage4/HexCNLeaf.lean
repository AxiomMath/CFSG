module

public import CFSG.GH74.GLS.Stage4.HexCND4
public import CFSG.GH74.GLS.Stage4.HexCAssembly2

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Rest

namespace CFSG.GH74.GLS.Stage4.Hex

theorem ch6PlusMatrix_nondeg {G : Type} [Group G] [Finite G] {p : ℕ} {H : Subgroup G}
    {r₁ r₂ : G} {U : Subgroup G} {root : ℤ → Subgroup G} {z : G} {S K₁ K₂ F P₀ : Subgroup G}
    {q : ℕ} (h : Ch6PlusMatrix G p H r₁ r₂ U root z S K₁ K₂ F P₀ q) :
    NondegG2 root ∧ NondegX15 root ∧ (3 ≤ q → RootOrdersD4a root q → NondegD4X13 root) := by
  obtain ⟨D, Eg, -, -, ⟨hK, -, -⟩, -, -⟩ := h
  have hO : ∀ a ∈ root 1 ⊔ root (-1), ∀ b ∈ root 4 ⊔ root (-4), a * b = b * a := by
    intro a ha b hb
    rw [← Eg.K₁_eq] at ha
    rw [← Eg.K₂_eq] at hb
    exact hK a ha b hb
  obtain ⟨E₁⟩ := sl2Pos_of_sl2At D.sl2At₁
  exact ⟨nondegG2_of_rgd2 D.toRGD2 E₁ hO, nondegX15_of_rgd2 D.toRGD2 E₁ hO,
    fun h3 hD => nondegD4X13_of_cor97 D E₁ hO h3 hD⟩

theorem ch6NondegLeaf2_proved : Ch6NondegLeaf2 := by
  intro G _ _ _ _ Gs _ q₁ q₂ _ hPlus
  obtain ⟨p, H, r₁, r₂, U, root, z, S, K₁, K₂, F, P₀, q, hm⟩ := hPlus
  obtain ⟨hG2, hX15, hD4⟩ := ch6PlusMatrix_nondeg (p := p) (H := H) (r₁ := r₁) (r₂ := r₂) (U := U)
    (root := root) (z := z) (S := S) (K₁ := K₁) (K₂ := K₂) (F := F) (P₀ := P₀) (q := q) hm
  exact ⟨p, H, r₁, r₂, U, root, z, S, K₁, K₂, F, P₀, q, hm, fun _ _ => ⟨hG2, fun _ => hX15⟩,
    fun h3 hD => ⟨hG2, hD4 h3 hD⟩⟩

end CFSG.GH74.GLS.Stage4.Hex
