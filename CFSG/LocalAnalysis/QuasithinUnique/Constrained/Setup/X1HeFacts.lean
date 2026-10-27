module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeDim
public import CFSG.LocalAnalysis.SectionRank.SporadicCatalogBase

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.Blueprint
open scoped commutatorElement

theorem he_cover
    (E : Type) [Group E] [Finite E] [Group.IsPerfect E]
    (π : E →* NativeSporadic.Carrier .He) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card π.ker)) : π.ker = ⊥ :=
  CFSG.SectionRank.He_perfect_odd_cover_trivial π hπ hC hodd

theorem dim_of_sylow7 {S : Type} [Group S] {x y : S} (hx : x ^ 7 = 1) (hz : ⁅x, y⁆ ≠ 1)
    (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y) (V : Type) [CommGroup V] [Finite V]
    (hV : ∀ v : V, v * v = 1) (σ : S →* MulAut V) (hσ : Function.Injective σ) :
    2 ^ 21 ≤ Nat.card V := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hx' : (σ x) ^ 7 = 1 := by rw [← map_pow, hx, map_one]
  have hz' : ⁅σ x, σ y⁆ ≠ 1 := by
    rw [← map_commutatorElement]
    exact fun h => hz (hσ (h.trans (map_one σ).symm))
  have hzx' : Commute ⁅σ x, σ y⁆ (σ x) := by
    rw [← map_commutatorElement]
    exact hzx.map σ
  have hzy' : Commute ⁅σ x, σ y⁆ (σ y) := by
    rw [← map_commutatorElement]
    exact hzy.map σ
  have h := two_pow_mul_le_card_of_extraspecial hV (p := 7) (by norm_num) hx' hz' hzx' hzy'
  rwa [orderOf_two_zmod_7] at h

theorem he_dim
    (V : Type) [CommGroup V] [Finite V] (hV : ∀ v : V, v * v = 1)
    (σ : NativeSporadic.Carrier .He →* MulAut V) (hσ : Function.Injective σ) :
    2 ^ 21 ≤ Nat.card V := by
  obtain ⟨x, y, -, hx, -, hz, hzx, hzy, -⟩ := CFSG.SectionRank.He_sylow7_cubic_witness
  exact dim_of_sylow7 (S := NativeSporadic.Carrier .He) (x := x) (y := y) hx hz hzx hzy V hV σ hσ

end CFSG.QuasithinUnique.Setup.X1
