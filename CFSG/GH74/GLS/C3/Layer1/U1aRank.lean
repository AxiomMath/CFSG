module

public import CFSG.StronglyEmbedded.SteinbergBURankTwoOddCore
public import CFSG.LieType.SteinbergBRTwoRankBound

public section

namespace CFSG.GH74.GLS.C3.Layer1.U1a

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem two_le_pRank_of_commute {D : Subgroup G} {x y : G} (hx : x ∈ D) (hy : y ∈ D)
    (hx2 : orderOf x = 2) (hy2 : orderOf y = 2) (hxy : x * y = y * x) (hne : x ≠ y) :
    2 ≤ CFSG.pRank 2 ↥D := by
  obtain ⟨V, -, hV, hVcard⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.AlternatingFourGroup.exists_elementary_four_of_commute
      (x := (⟨x, hx⟩ : D)) (y := ⟨y, hy⟩) (by rw [Subgroup.orderOf_mk]; exact hx2)
      (by rw [Subgroup.orderOf_mk]; exact hy2) (Subtype.ext hxy)
      (fun h => hne (congrArg Subtype.val h))
  exact CFSG.LieType.SteinbergBR.le_pRank_of_card one_lt_two V hV (by rw [hVcard]; norm_num)

theorem exists_commuting_involutions {D : Subgroup G} (h : 2 ≤ CFSG.pRank 2 ↥D) :
    ∃ x ∈ D, ∃ y ∈ D, orderOf x = 2 ∧ orderOf y = 2 ∧ x ≠ y ∧ x * y = y * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A, hA, hcard⟩ := CFSG.StronglyEmbedded.SteinbergBU.exists_four_group_of_two_le_pRank
    (G := ↥D) h
  have hA' : CFSG.IsElementaryAbelian 2 ↥A := hA
  have hsq : ∀ a : ↥A, a * a = 1 := by
    intro a
    have h1 : (a : ↥D) ^ 2 = 1 :=
      CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) (a : ↥D) a.2
    have h2 : (a : ↥D) * (a : ↥D) = 1 := by rwa [sq] at h1
    exact Subtype.ext h2
  have hne : A ≠ ⊥ := by
    intro hb
    rw [hb] at hcard
    simp at hcard
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have ha2 : orderOf a = 2 := orderOf_eq_prime (by rw [sq]; exact hsq a) ha1
  have hcardA : Nat.card ↥A = 4 := by rw [hcard]; norm_num
  obtain ⟨b, hb⟩ : ∃ b : ↥A, b ∉ zpowers a := by
    by_contra hcon
    push Not at hcon
    have hle : (⊤ : Subgroup ↥A) ≤ zpowers a := fun b _ => hcon b
    have h4 := Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hle)
    rw [Subgroup.card_top, hcardA, Nat.card_zpowers, ha2] at h4
    omega
  have hb1 : b ≠ 1 := fun h => hb (h ▸ one_mem _)
  have hba : b ≠ a := fun h => hb (h ▸ mem_zpowers a)
  have hb2 : orderOf b = 2 := orderOf_eq_prime (by rw [sq]; exact hsq b) hb1
  have : IsMulCommutative ↥A := hA'.toIsMulCommutative
  refine ⟨((a : ↥A) : ↥D), ((a : ↥A) : ↥D).2, ((b : ↥A) : ↥D), ((b : ↥A) : ↥D).2, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, ha2]
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hb2]
  · intro hab
    exact hba (Subtype.ext (Subtype.ext hab).symm)
  · have := congrArg (fun z : ↥A => (((z : ↥A) : ↥D) : G)) (mul_comm' a b)
    simpa using this

end CFSG.GH74.GLS.C3.Layer1.U1a
