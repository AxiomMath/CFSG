module

public import CFSG.ClassicalInvolution.SL2Facts
public import CFSG.ClassicalInvolution.QuaternionStructure.WitnessCore

public section

namespace CFSG.ClassicalInvolution

open scoped MatrixGroups

private theorem sl2Three_mul_aux :
    ∀ a b : SL(2, ZMod 3), a ^ 4 = 1 → b ^ 4 = 1 → (a * b) ^ 4 = 1 := by
  decide +kernel

private theorem sl2Three_conj_aux :
    ∀ g a : SL(2, ZMod 3), a ^ 4 = 1 → (g * a * g⁻¹) ^ 4 = 1 := by
  decide +kernel

def sl2ThreeQ : Subgroup SL(2, ZMod 3) where
  carrier := {g | g ^ 4 = 1}
  one_mem' := one_pow 4
  mul_mem' := fun {a b} ha hb => sl2Three_mul_aux a b ha hb
  inv_mem' := fun {a} ha => by
    have h : a ^ 4 = 1 := ha
    show a⁻¹ ^ 4 = 1
    rw [inv_pow, h, inv_one]

theorem mem_sl2ThreeQ_iff {g : SL(2, ZMod 3)} : g ∈ sl2ThreeQ ↔ g ^ 4 = 1 := Iff.rfl

theorem sl2ThreeQ_normal : sl2ThreeQ.Normal :=
  ⟨fun a ha g => sl2Three_conj_aux g a ha⟩

theorem natCard_sl2Three : Nat.card SL(2, ZMod 3) = 24 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem natCard_sl2ThreeQ : Nat.card sl2ThreeQ = 8 := by
  change Nat.card {g : SL(2, ZMod 3) // g ^ 4 = 1} = 8
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem sl2ThreeQ_index : sl2ThreeQ.index = 3 := by
  have h := Subgroup.card_mul_index sl2ThreeQ
  rw [natCard_sl2ThreeQ, natCard_sl2Three] at h
  omega

theorem nonempty_mulEquiv_sl2ThreeQ : Nonempty (QuaternionGroup 2 ≃* sl2ThreeQ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 sl2ThreeQ :=
    IsPGroup.of_card (n := 3) (by rw [natCard_sl2ThreeQ]; norm_num)
  let P : Sylow 2 SL(2, ZMod 3) := hp.toSylow (by rw [sl2ThreeQ_index]; norm_num)
  have hodd : Odd (Nat.card (ZMod 3)) := by
    rw [Nat.card_zmod]; exact ⟨1, rfl⟩
  obtain ⟨n, hn3, ⟨e⟩⟩ := CFSG.Semidihedral.OddFieldSL2.sylow_two_quaternion (ZMod 3) hodd P
  have hcard : Nat.card (P : Subgroup SL(2, ZMod 3)) = 8 := natCard_sl2ThreeQ
  have hcard' : Nat.card (QuaternionGroup (2 ^ (n - 2))) = 8 := by
    rw [← Nat.card_congr e.toEquiv, hcard]
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card] at hcard'
  have hn : n - 2 = 1 := by
    have h2 : 2 ^ (n - 2) = 2 ^ 1 := by omega
    exact Nat.pow_right_injective (le_refl 2) h2
  rw [hn] at e
  exact ⟨e.symm⟩

section Solvable

variable {F : Type*} [Field F] [Finite F]

theorem natCard_eq_three_of_isSolvable_sl2 (hodd : Odd (Nat.card F))
    (hs : Group.IsSolvable SL(2, F)) : Nat.card F = 3 := by
  have h2 : 2 ≤ Nat.card F := by
    have : Nontrivial F := inferInstance
    have := Finite.one_lt_card (α := F)
    omega
  by_contra hne
  have h4 : 4 ≤ Nat.card F := by
    rcases hodd with ⟨m, hm⟩
    omega
  have hperf := sl2_isPerfect h4
  have hnt : Nontrivial SL(2, F) := ⟨⟨-1, 1, sl2_neg_one_ne_one hodd⟩⟩
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial SL(2, F)).ne hperf.commutator_eq_top

theorem nonempty_mulEquiv_sl2Three_of_natCard_eq_three (h : Nat.card F = 3) :
    Nonempty (SL(2, F) ≃* SL(2, ZMod 3)) := by
  have : Fintype F := Fintype.ofFinite F
  have hF : Fintype.card F = Fintype.card (ZMod 3) := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, h]
  exact ⟨QuaternionStructure.slRingEquiv (FiniteField.ringEquivOfCardEq hF)⟩

theorem nonempty_mulEquiv_sl2Three_of_isSolvable (hodd : Odd (Nat.card F))
    (hs : Group.IsSolvable SL(2, F)) : Nonempty (SL(2, F) ≃* SL(2, ZMod 3)) :=
  nonempty_mulEquiv_sl2Three_of_natCard_eq_three (natCard_eq_three_of_isSolvable_sl2 hodd hs)

end Solvable

end CFSG.ClassicalInvolution
