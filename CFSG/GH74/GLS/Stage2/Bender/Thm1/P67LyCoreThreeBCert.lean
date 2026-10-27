module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LyCoreThreeB

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.LyCore

open Subgroup Equiv Equiv.Perm CFSG CFSG.Blueprint CFSG.GH74.GLS.Stage12
  CFSG.Sporadic.Recognition.LyonsSims

theorem lyThreeBOrder_of_J
    (hJ : ∃ y : CFSG.Sporadic.Ly.J, orderOf y = 3 ∧
      Nat.card ↥(centralizer ({y} : Set CFSG.Sporadic.Ly.J)) ≤ 174960) : LyThreeBOrder := by
  intro Y _ _ hY t ρ D x₁ x₂ x₃ S
  classical
  obtain ⟨e⟩ := hY
  obtain ⟨y₀, hy₀, hc₀⟩ := hJ
  let e' : Y ≃* CFSG.Sporadic.Ly.J := e.trans CFSG.Sporadic.Ly.lyEquivJ
  have hy3 : orderOf (e'.symm y₀) = 3 := by rw [MulEquiv.orderOf_eq]; exact hy₀
  have hcy : Nat.card ↥(centralizer ({e'.symm y₀} : Set Y)) ≤ 174960 := by
    have h : Nat.card ↥(centralizer ({y₀} : Set CFSG.Sporadic.Ly.J)) =
        Nat.card ↥(centralizer ({e'.symm y₀} : Set Y)) := by
      refine Nat.card_congr
        { toFun := fun c => ⟨e'.symm c.1, ?_⟩
          invFun := fun d => ⟨e' d.1, ?_⟩
          left_inv := fun c => Subtype.ext (by simp)
          right_inv := fun d => Subtype.ext (by simp) }
      · have h1 := mem_centralizer_singleton_iff.1 c.2
        rw [mem_centralizer_singleton_iff]
        have h := congrArg e'.symm h1
        simpa using h
      · have h1 := mem_centralizer_singleton_iff.1 d.2
        rw [mem_centralizer_singleton_iff]
        have h := congrArg e' h1
        simpa using h
    omega
  have hcen := D.center_centralizer S
  have hc3 := D.card_center_centralizer S
  obtain ⟨eM⟩ := D.centQuot_mcl S.pow₁ S.rho₁
  set M : Subgroup Y := centralizer ({(x₁ : Y)} : Set Y) with hMdef
  have eq : ↥M ⧸ center ↥M ≃* NativeSporadic.McL :=
    (QuotientGroup.quotientMulEquivOfEq hcen).trans eM
  have hcardM : Nat.card ↥M = 2694384000 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥M)
    rw [Nat.card_congr eq.toEquiv, CFSG.Sporadic.McL.card_McL, hc3] at h1
    omega
  rcases (lemma45_classes_of_certificate D S).1 (e'.symm y₀) hy3 with h | h
  · exfalso
    have := CFSG.Sporadic.Recognition.JankoWong.card_centralizer_eq_of_isConj h
    rw [this] at hcy
    have hM : Nat.card ↥(centralizer ({(x₁ : Y)} : Set Y)) = 2694384000 := hcardM
    omega
  · rw [← CFSG.Sporadic.Recognition.JankoWong.card_centralizer_eq_of_isConj h]
    exact hcy

end CFSG.GH74.GLS.Stage2.Bender.Thm1.LyCore
