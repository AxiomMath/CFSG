module

public import CFSG.Monster.Existence.TwoPoint.Classes
public import CFSG.Monster.GMS.Uniqueness
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterTwoA

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabMThreeA

open CFSG.Monster.GMS CFSG.Blueprint
open CFSG.Monster.Existence (OddExhaustive mul_self_of_isConj)
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  (isConj_mul_of_inverts_odd centralizer_inf_centralizer_mul_eq)

variable {d₀ : NativeSporadic.B} {G : Type} [Group G] [Finite G] {a z₀ : G}

section OddType


theorem oddNbrType_zero_of_dvd (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hex : OddExhaustive a z₀) (hOT : OddTypeOrdersCF a z₀) {α s : G} (hα : IsConj a α)
    (hs3 : orderOf s = 3) (hαs : α * s * α⁻¹ = s⁻¹) {n : ℕ}
    (hn : n ∣ Nat.card ↥(Subgroup.centralizer ({α} : Set G) ⊓
      Subgroup.centralizer ({s} : Set G)))
    (hn1 : ¬ n ∣ oddTypeStab 1) (hn2 : ¬ n ∣ oddTypeStab 2) :
    s⁻¹ * α ∈ oddNbr a z₀ α ∧ OddNbrType z₀ α (s⁻¹ * α) 0 ∧ α * (s⁻¹ * α) = s := by
  have hαα : α * α = 1 := mul_self_of_isConj hG.1.1 hα
  have hαi : α⁻¹ = α := inv_eq_of_mul_eq_one_right hαα
  have hsodd : Odd (orderOf s⁻¹) := by rw [orderOf_inv, hs3]; decide
  have hinv' : α * s⁻¹ * α⁻¹ = (s⁻¹)⁻¹ := by
    have := conj_inv (a := s) (b := α)
    rw [hαs, inv_inv] at this
    rw [inv_inv]
    exact this.symm
  have hβA : IsConj a (s⁻¹ * α) := hα.trans (isConj_mul_of_inverts_odd hinv' hsodd)
  have hαβ : α * (s⁻¹ * α) = s := by
    calc α * (s⁻¹ * α) = α * s⁻¹ * α⁻¹ := by rw [hαi]; group
      _ = s := by rw [hinv', inv_inv]
  have hβne : s⁻¹ * α ≠ α := by
    intro h
    have h1 : s⁻¹ = 1 := mul_right_cancel (h.trans (one_mul α).symm)
    rw [inv_eq_one] at h1
    rw [h1, orderOf_one] at hs3
    omega
  have hodd : Odd (orderOf (α * (s⁻¹ * α))) := by rw [hαβ, hs3]; decide
  have hnbr : s⁻¹ * α ∈ oddNbr a z₀ α := hex α (s⁻¹ * α) hα hβA hβne hodd
  have hHeq : Subgroup.centralizer ({α} : Set G) ⊓ Subgroup.centralizer ({s⁻¹ * α} : Set G) =
      Subgroup.centralizer ({α} : Set G) ⊓ Subgroup.centralizer ({s} : Set G) := by
    have := centralizer_inf_centralizer_mul_eq α (s⁻¹ * α)
    rwa [hαβ] at this
  obtain ⟨j, hj, -⟩ := s348_type I.sls I.tableV I.leech I.leechOddPair I.tableIV hG hα hnbr
  have hj0 : j = 0 := by
    by_contra hj0
    have hcard := hOT α (s⁻¹ * α) j hj0 hα hnbr hj
    rw [hHeq] at hcard
    rw [hcard] at hn
    fin_cases j
    · exact hj0 rfl
    · exact hn1 hn
    · exact hn2 hn
  subst hj0
  exact ⟨hnbr, hj, hαβ⟩

theorem isConj_of_oddNbrType_zero (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hex : OddExhaustive a z₀) (hOT : OddTypeOrdersCF a z₀) {α s : G} (hα : IsConj a α)
    (hs3 : orderOf s = 3) (hαs : α * s * α⁻¹ = s⁻¹) {n : ℕ}
    (hn : n ∣ Nat.card ↥(Subgroup.centralizer ({α} : Set G) ⊓
      Subgroup.centralizer ({s} : Set G)))
    (hn1 : ¬ n ∣ oddTypeStab 1) (hn2 : ¬ n ∣ oddTypeStab 2) {w₀ : G}
    (hclass : ∀ x y : G, IsConj a x → y ∈ oddNbr a z₀ x → OddNbrType z₀ x y 0 →
      IsConj (x * y) w₀) :
    IsConj s w₀ := by
  obtain ⟨hnbr, hty, hαβ⟩ := oddNbrType_zero_of_dvd I hG hex hOT hα hs3 hαs hn hn1 hn2
  have := hclass α (s⁻¹ * α) hα hnbr hty
  rwa [hαβ] at this

end OddType

end CFSG.HardMathSupport.Dickson.I271.TabMThreeA
