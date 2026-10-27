module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.ClassicalInvolution.Phan.Phan3AData
public import CFSG.Monster.B.Co2.BFS
public import Certificates.Data.CFSGNative.CosetTable.Enum
public import Certificates.Data.CFSGNative.Schreier.Check

public section

namespace CFSG.ClassicalInvolution.Phan.Q3G

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.CosetTable

variable {n m : ℕ} {gs : Array (Array ℕ)}

variable {ws : List (List (Fin m × Bool))} {S : Array (Array ℕ)}

theorem commutative_of_card_le_four {G : Type*} [Group G] [Finite G] (h : Nat.card G ≤ 4)
    (x y : G) :
    x * y = y * x := by
  have hpos := Nat.card_pos (α := G)
  have h1 : Nat.card G = 1 ∨ Nat.card G = 2 ∨ Nat.card G = 3 ∨ Nat.card G = 4 := by omega
  rcases h1 with h1 | h1 | h1 | h1
  · have : Subsingleton G := (Nat.card_eq_one_iff_unique.1 h1).1
    exact Subsingleton.elim _ _
  · have : Fact (Nat.Prime (Nat.card G)) := ⟨by rw [h1]; exact Nat.prime_two⟩
    exact (isCyclic_of_prime_card (p := Nat.card G) rfl).commGroup.mul_comm x y
  · have : Fact (Nat.Prime (Nat.card G)) := ⟨by rw [h1]; exact Nat.prime_three⟩
    exact (isCyclic_of_prime_card (p := Nat.card G) rfl).commGroup.mul_comm x y
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hc : IsMulCommutative G :=
      IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by rw [h1]; norm_num)
    exact hc.is_comm.comm x y

theorem ker_le_ker_of_card_le_four {P G : Type*} [Group P] [Group G] [Finite P] [Finite G]
    [IsSimpleGroup G]
    (hnab : ∃ x y : G, x * y ≠ y * x) (π : P →* G) (hπ : Function.Surjective π)
    (K : Subgroup P) [K.Normal] (hK : Nat.card K ≤ 4) : K ≤ π.ker := by
  have hN : (K.map π).Normal := Subgroup.Normal.map inferInstance π hπ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.map π) with h | h
  · intro x hx
    have : π x ∈ K.map π := ⟨x, hx, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact this
  · exfalso
    obtain ⟨x, y, hxy⟩ := hnab
    have hsurj : Function.Surjective (K.map π).subtype :=
      fun g => ⟨⟨g, by rw [h]; trivial⟩, rfl⟩
    have hle : Nat.card G ≤ 4 :=
      calc Nat.card G ≤ Nat.card (K.map π) := Nat.card_le_card_of_surjective _ hsurj
        _ ≤ Nat.card K := Nat.card_le_card_of_surjective _ (π.subgroupMap_surjective K)
        _ ≤ 4 := hK
    exact hxy (commutative_of_card_le_four hle x y)

end CFSG.ClassicalInvolution.Phan.Q3G
