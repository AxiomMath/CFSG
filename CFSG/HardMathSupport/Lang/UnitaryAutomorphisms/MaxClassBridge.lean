module

public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.MaxClassLayers
public import CFSG.Walter.W67.Section5.MaxClass

public section

namespace CFSG.HardMathSupport.Lang.UnitaryAutomorphisms

variable {G : Type} [Group G] [Finite G]

theorem cubeSetup_of_card_centralizer (hG : IsPGroup 3 G) {x : G} (hx3 : x ^ 3 = 1)
    (hCx : Nat.card (Subgroup.centralizer ({x} : Set G)) = 9)
    {M : Subgroup G} [M.Normal] (hMi : M.index = 3) (hxM : x ∉ M) (hM81 : 81 ≤ Nat.card M) :
    ∃ n : ℕ, 5 ≤ n ∧ Nat.card G = 3 ^ n ∧
      (⊤ : Subgroup G).lowerCentralSeries (n - 2) ≠ ⊥ ∧ CubeSetup x (lcsFil M) n := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx1 : x ≠ 1 := fun h => hxM (h ▸ M.one_mem)
  have hox : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  obtain ⟨n, -, hcard, hne⟩ := CFSG.Walter.W67.isMaximalClass_of_card_centralizer hG x hox
    (by rw [hCx]; norm_num)
  have hMG : Nat.card M * 3 = Nat.card G := by
    have := Subgroup.card_mul_index M
    rwa [hMi] at this
  have hn5 : 5 ≤ n := by
    by_contra h
    have : Nat.card G ≤ 3 ^ 4 := by
      rw [hcard]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact ⟨n, hn5, hcard, hne, cubeSetup_of_maxClass hG (by omega) hcard hne hx3 hCx hMi hxM⟩

end CFSG.HardMathSupport.Lang.UnitaryAutomorphisms
