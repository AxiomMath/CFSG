module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeCLeech
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeCTh
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterTwoA
public import CFSG.Monster.Existence.TwoPoint.Classes
public import CFSG.RankThree.PartOne.CTP.SporadicOrders

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.I271.TabMThreeC

open CFSG.Monster.GMS CFSG.Monster.Existence CFSG.Blueprint CFSG.Open
  CFSG.HardMathSupport.Dickson.I271.TabMFive
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance

section Gms

variable {d₀ : NativeSporadic.B} {G : Type} [Group G] [Finite G] {a z₀ : G}

theorem card_inf_centralizer_of_involutionFacts {K : Type*} [Group K] {H : Subgroup K} {N : ℕ}
    (hF : InvolutionFacts ↥H N) {t : K} (ht : t ∈ H) (ho : orderOf t = 2) :
    Nat.card ↥(H ⊓ Subgroup.centralizer ({t} : Set K)) = N := by
  rw [← card_centralizer_subtype (⟨t, ht⟩ : ↥H)]
  exact hF.1 ⟨t, ht⟩ (by rw [← Subgroup.orderOf_coe]; exact ho)


theorem card_centralizer_le_of_gms (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hex : OddExhaustive a z₀)
    (hcls : ∀ α : G, orderOf α = 2 →
      Nat.card ↥(Subgroup.centralizer ({α} : Set G)) = 2 * monsterBabyOrder → IsConj a α)
    (k α : G) (hk3 : orderOf k = 3) (hα2 : orderOf α = 2)
    (hαc : Nat.card ↥(Subgroup.centralizer ({α} : Set G)) = 2 * monsterBabyOrder)
    (hαk : α * k * α⁻¹ = k⁻¹)
    (hH : Nonempty (↥(Subgroup.centralizer ({α} : Set G) ⊓ Subgroup.centralizer ({k} : Set G)) ≃*
      NativeSporadic.Th)) :
    Nat.card ↥(Subgroup.centralizer ({k} : Set G)) ≤ 3 * 90745943887872000 := by
  obtain ⟨e⟩ := hH
  have hαA : IsConj a α := hcls α hα2 hαc
  have hαα : α * α = 1 := by
    have := pow_orderOf_eq_one α
    rwa [hα2, sq] at this
  have hαi : α⁻¹ = α := inv_eq_of_mul_eq_one_right hαα
  have hkodd : Odd (orderOf k⁻¹) := by rw [orderOf_inv, hk3]; decide
  have hinv' : α * k⁻¹ * α⁻¹ = (k⁻¹)⁻¹ := by
    have := conj_inv (a := k) (b := α)
    rw [hαk, inv_inv] at this
    rw [inv_inv]
    exact this.symm
  have hβA : IsConj a (k⁻¹ * α) := hαA.trans (isConj_mul_of_inverts_odd hinv' hkodd)
  have hαβ : α * (k⁻¹ * α) = k := by
    calc α * (k⁻¹ * α) = α * k⁻¹ * α⁻¹ := by rw [hαi]; group
      _ = k := by rw [hinv', inv_inv]
  have hβne : k⁻¹ * α ≠ α := by
    intro h
    have h1 : k⁻¹ = 1 := mul_right_cancel (h.trans (one_mul α).symm)
    rw [inv_eq_one] at h1
    rw [h1, orderOf_one] at hk3
    omega
  have hodd : Odd (orderOf (α * (k⁻¹ * α))) := by rw [hαβ, hk3]; decide
  have hnbr : k⁻¹ * α ∈ oddNbr a z₀ α := hex α (k⁻¹ * α) hαA hβA hβne hodd
  have hHeq : Subgroup.centralizer ({α} : Set G) ⊓ Subgroup.centralizer ({k⁻¹ * α} : Set G) =
      Subgroup.centralizer ({α} : Set G) ⊓ Subgroup.centralizer ({k} : Set G) := by
    have := centralizer_inf_centralizer_mul_eq α (k⁻¹ * α)
    rwa [hαβ] at this
  have hF : InvolutionFacts ↥(Subgroup.centralizer ({α} : Set G) ⊓
      Subgroup.centralizer ({k} : Set G)) 92897280 :=
    @InvolutionFacts.of_equiv NativeSporadic.Th
      ↥(Subgroup.centralizer ({α} : Set G) ⊓ Subgroup.centralizer ({k} : Set G))
      inferInstance inferInstance e.symm 92897280 involutionFacts_Th
  obtain ⟨j, hj, -⟩ := s348_type I.sls I.tableV I.leech I.leechOddPair I.tableIV hG hαA hnbr
  obtain ⟨w, hwB, hY⟩ := oddNbr.exists_isOddPair hαA hnbr
  have hw2 : orderOf w = 2 := (CFSG.Monster.GMS.orderOf_eq_of_isConj hwB).symm.trans hG.2.1
  have hwH : w ∈ Subgroup.centralizer ({α} : Set G) ⊓ Subgroup.centralizer ({k} : Set G) := by
    rw [← hHeq]
    exact hY.mem_inf
  have hcardH : Nat.card ↥(Subgroup.centralizer ({α} : Set G) ⊓
      Subgroup.centralizer ({k} : Set G) ⊓ Subgroup.centralizer ({w} : Set G)) = 92897280 :=
    card_inf_centralizer_of_involutionFacts hF hwH hw2
  have hcard3 := (s348_card hj hY.mem_inf hwB).2
  have hsub : Subgroup.centralizer ({w} : Set G) ⊓ Subgroup.centralizer ({α} : Set G) ⊓
      Subgroup.centralizer ({k⁻¹ * α} : Set G) =
      (Subgroup.centralizer ({α} : Set G) ⊓ Subgroup.centralizer ({k} : Set G)) ⊓
        Subgroup.centralizer ({w} : Set G) := by
    rw [← hHeq]
    ext x
    simp only [Subgroup.mem_inf]
    tauto
  rw [hsub, hcardH] at hcard3
  have hj1 : j = 1 := by
    fin_cases j
    · exfalso
      norm_num [oddTypeCard] at hcard3
    · rfl
    · exfalso
      norm_num [oddTypeCard] at hcard3
  rw [hj1] at hj
  have hβ3C : k⁻¹ * α ∈ typeSet a z₀ α .threeC := ⟨hnbr, hj⟩
  have hup : ∀ t ∈ Subgroup.centralizer ({α} : Set G) ⊓ Subgroup.centralizer ({k} : Set G),
      orderOf t = 2 → Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓
        Subgroup.centralizer ({k} : Set G)) ≤ 3 * 92897280 := by
    intro t ht ht2
    have := card_centralizer_inf_le_of_threeC I hG hαA hβ3C (by rw [hHeq]; exact ht) ht2
    rwa [hαβ] at this
  have hbound := card_centralizer_le_of_involutionFacts (p := 3) (N := 92897280)
    Nat.prime_three (by norm_num) hk3 hαk inf_le_left inf_le_right hF hup
  have hHcard : Nat.card ↥(Subgroup.centralizer ({α} : Set G) ⊓
      Subgroup.centralizer ({k} : Set G)) = 90745943887872000 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.RankThree.PartOne.CTP.card_Th
  rw [hHcard] at hbound
  exact hbound

end Gms

end CFSG.HardMathSupport.Dickson.I271.TabMThreeC
