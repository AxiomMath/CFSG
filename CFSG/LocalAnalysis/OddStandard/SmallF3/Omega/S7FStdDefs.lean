module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open CFSG.Open (standardComponentIsStandard)

@[expose] def Asc82StandardInputRk2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog G → ¬ CFSG.Blueprint.Catalog G →
    AschA1 G → AschA2 G → (∃ L : Subgroup G, InF L ∧ InC L) →
      ∀ X : Subgroup G, standardComponentIsStandard X → InFStar X →
        2 ≤ pRank 2 ↥(centralizer (X : Set G)) → Chev3 G

theorem s7f_mem_zpowers_two {P : Type*} [Group P] {u x : P} (hu : orderOf u = 2)
    (hx : x ∈ zpowers u) : x = 1 ∨ x = u := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
  rw [← zpow_mod_orderOf, hu, Nat.cast_ofNat]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [h, zpow_zero]
  · right
    rw [h, zpow_one]

theorem s7f_bddAbove_pRank (P : Type*) [Group P] [Finite P] :
    BddAbove {r : ℕ | ∃ A : Subgroup P, IsElementaryAbelian 2 A ∧ Nat.card A = 2 ^ r} := by
  refine ⟨Nat.card P, ?_⟩
  rintro r ⟨B, -, hB⟩
  calc r ≤ 2 ^ r := (Nat.lt_pow_self one_lt_two).le
    _ = Nat.card B := hB.symm
    _ ≤ Nat.card P := Subgroup.card_le_card_group B

theorem s7f_two_le_pRank_of_commute {P : Type*} [Group P] [Finite P] {u v : P}
    (hu : orderOf u = 2) (hv : orderOf v = 2) (huv : u * v = v * u) (hne : u ≠ v) :
    2 ≤ CFSG.pRank 2 P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsElementaryAbelian 2 (zpowers u) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (by rw [← hu]; exact pow_orderOf_eq_one u)
  haveI : IsElementaryAbelian 2 (zpowers v) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (by rw [← hv]; exact pow_orderOf_eq_one v)
  have hle : zpowers v ≤ centralizer (zpowers u : Set P) := by
    rw [zpowers_le, mem_centralizer_iff]
    intro x hx
    rcases s7f_mem_zpowers_two hu hx with rfl | rfl
    · rw [one_mul, mul_one]
    · exact huv
  haveI hA : IsElementaryAbelian 2 ↥(zpowers u ⊔ zpowers v) :=
    IsElementaryAbelian.sup_of_le_centralizer hle
  obtain ⟨k, hk⟩ := (IsElementaryAbelian.isPGroup 2 ↥(zpowers u ⊔ zpowers v)).exists_card_eq
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have hcard : Nat.card ↥(zpowers u ⊔ zpowers v) ≤ Nat.card ↥(zpowers u) := by
      rw [hk, Nat.card_zpowers, hu]
      calc 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 2 := by norm_num
    have heq := eq_of_le_of_card_ge (le_sup_left : zpowers u ≤ zpowers u ⊔ zpowers v) hcard
    have hvu : v ∈ zpowers u := by
      rw [heq]
      exact (le_sup_right : zpowers v ≤ zpowers u ⊔ zpowers v) (mem_zpowers v)
    rcases s7f_mem_zpowers_two hu hvu with h | h
    · rw [h, orderOf_one] at hv
      exact absurd hv (by norm_num)
    · exact hne h.symm
  exact hk2.trans (le_csSup (s7f_bddAbove_pRank P) ⟨_, hA, hk⟩)

variable {G : Type} [Group G]

theorem s7f_nonab_of_quasisimple {X : Subgroup G} (hX : IsQuasisimple ↥X) :
    ∃ a b : G, a * b ≠ b * a := by
  obtain ⟨-, -, a, b, hab⟩ := hX
  induction a using QuotientGroup.induction_on with
  | H a =>
    induction b using QuotientGroup.induction_on with
    | H b =>
      refine ⟨a, b, fun h => hab ?_⟩
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext h

theorem s7f_isQuasisimple_of_inFStar {X : Subgroup G} (h : InFStar X) : IsQuasisimple ↥X := by
  rcases h with h | h
  · exact h.1
  · exact h.1

end CFSG.OddStandard.SmallF3.Omega
