module

public import CFSG.GH74.GLS.Stage1.Thm6.Glue.Data

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Glue

open Subgroup CFSG CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12

variable {G : Type} [Group G]

theorem isElementaryAbelian_of_isEA {X : Type*} [Group X] {E : Subgroup X}
    (hE : ∀ a ∈ E, a * a = 1 ∧ ∀ b ∈ E, a * b = b * a) : IsElementaryAbelian 2 ↥E := by
  have hcomm : IsMulCommutative ↥E := ⟨⟨fun a b => Subtype.ext ((hE a a.2).2 b b.2)⟩⟩
  exact { toIsMulCommutative := hcomm
          exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 (fun g => by
            have := (hE g g.2).1
            exact Subtype.ext (by simpa [pow_two] using this)) }

theorem le_pRank_of_card {X : Type*} [Group X] [Finite X] {A : Subgroup X}
    (hA : IsElementaryAbelian 2 ↥A) {r : ℕ} (hr : Nat.card A = 2 ^ r) : r ≤ pRank 2 X := by
  refine le_csSup ⟨Nat.card X, ?_⟩ ⟨A, hA, hr⟩
  rintro s ⟨B, -, hB⟩
  calc s ≤ 2 ^ s := (Nat.lt_pow_self (by norm_num)).le
    _ = Nat.card B := hB.symm
    _ ≤ Nat.card X := Subgroup.card_le_card_group B

theorem rank2Le_of_pRank_le [Finite G] (x : G) (h : pRank 2 ↥(Cx x) ≤ 3) : Rank2Le (Cx x) 3 := by
  intro E hEC hE
  have hE' : ∀ a ∈ E.subgroupOf (Cx x), a * a = 1 ∧ ∀ b ∈ E.subgroupOf (Cx x), a * b = b * a :=
    fun a ha => ⟨Subtype.ext ((hE _ ha).1), fun b hb => Subtype.ext ((hE _ ha).2 _ hb)⟩
  have hEA : IsElementaryAbelian 2 ↥(E.subgroupOf (Cx x)) := isElementaryAbelian_of_isEA hE'
  obtain ⟨r, hr⟩ := (IsPGroup.iff_card.1 (hEA.isPGroup 2 _) : ∃ n, Nat.card ↥(E.subgroupOf (Cx x)) = 2 ^ n)
  have hcard : Nat.card E = 2 ^ r := by
    rw [← hr]; exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEC).toEquiv).symm
  rw [hcard]
  exact Nat.pow_le_pow_right (by norm_num) ((le_pRank_of_card hEA hr).trans h)

theorem exists_elemAb_eight [Finite G] (x : G) (h : pRank 2 ↥(Cx x) = 3) :
    ∃ E : Subgroup G, E ≤ Cx x ∧ IsElemAb2 E ∧ Nat.card E = 8 := by
  have hne : {r : ℕ | ∃ A : Subgroup ↥(Cx x), IsElementaryAbelian 2 ↥A ∧ Nat.card A = 2 ^ r}.Nonempty :=
    ⟨0, ⊥, by
      have : IsElementaryAbelian 2 ↥(⊥ : Subgroup ↥(Cx x)) :=
        isElementaryAbelian_of_isEA (fun a ha => by
          have : a = 1 := by simpa using ha
          subst this; simp)
      exact this, by simp⟩
  have hbdd : BddAbove {r : ℕ | ∃ A : Subgroup ↥(Cx x), IsElementaryAbelian 2 ↥A ∧
      Nat.card A = 2 ^ r} := by
    refine ⟨Nat.card ↥(Cx x), ?_⟩
    rintro s ⟨B, -, hB⟩
    calc s ≤ 2 ^ s := (Nat.lt_pow_self (by norm_num)).le
      _ = Nat.card B := hB.symm
      _ ≤ Nat.card ↥(Cx x) := Subgroup.card_le_card_group B
  have hmem := Nat.sSup_mem hne hbdd
  rw [show pRank 2 ↥(Cx x) = sSup {r : ℕ | ∃ A : Subgroup ↥(Cx x), IsElementaryAbelian 2 ↥A ∧
      Nat.card A = 2 ^ r} from rfl] at h
  rw [h] at hmem
  obtain ⟨A, hA, hAc⟩ := hmem
  refine ⟨A.map (Cx x).subtype, fun g ⟨a, _, hag⟩ => hag ▸ a.2, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    refine ⟨?_, ?_⟩
    · have := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) a ha
      have h2 : a * a = 1 := by rwa [pow_two] at this
      simpa using congrArg Subtype.val h2
    · rintro _ ⟨b, hb, rfl⟩
      have h1 := (IsMulCommutative.is_comm (M := ↥A)).comm ⟨a, ha⟩ ⟨b, hb⟩
      have h2 : a * b = b * a := by simpa using congrArg Subtype.val h1
      show (a : G) * b = b * a
      exact congrArg Subtype.val h2
  · rw [Subgroup.card_map_of_injective (Cx x).subtype_injective, hAc]
    norm_num

end CFSG.GH74.GLS.Stage1.Thm6.Glue
