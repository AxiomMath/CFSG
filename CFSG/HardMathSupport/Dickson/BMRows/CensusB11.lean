module

public import CFSG.HardMathSupport.Dickson.BMRows.CensusB11Elems
public import CFSG.HardMathSupport.Dickson.BMRows.CensusB11Bender
public import CFSG.HardMathSupport.Dickson.BMRows.CensusB11TwoB
public import CFSG.HardMathSupport.Dickson.BMRows.CensusB11TwoA
public import CFSG.Monster.Existence.BabyOrder
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.FixedFreeRank
public import CFSG.Monster.GMS.BabyReduce
public import CFSG.Monster.GMS.Facts.Section4

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.BMRows.B11

open Equiv CFSG.Blueprint CFSG.Monster.GMS CFSG.HardMathSupport.Dickson.BMRows

theorem card_centralizer_in_centralizer {G : Type*} [Group G] (y : G)
    (g : ↥(Subgroup.centralizer ({y} : Set G))) :
    Nat.card ↥(Subgroup.centralizer ({g} : Set ↥(Subgroup.centralizer ({y} : Set G)))) =
      Nat.card ↥(Subgroup.centralizer ({(g : G)} : Set G) ⊓
        Subgroup.centralizer ({y} : Set G)) := Nat.card_congr
  { toFun := fun u => ⟨u.1.1, Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 u.2)), u.1.2⟩⟩
    invFun := fun u => ⟨⟨u.1, (Subgroup.mem_inf.1 u.2).2⟩, Subgroup.mem_centralizer_singleton_iff.2
      (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 u.2).1))⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

theorem card_centralizer_eq_of_sym5 {G : Type*} [Group G] [Finite G] {y : G}
    (hy : orderOf y = 11) (ψ : Perm (Fin 5) →* G) (hψ : Function.Injective ψ)
    (hc : ∀ σ, ψ σ * y = y * ψ σ)
    (hA : Nat.card ↥(Subgroup.centralizer ({ψ (swap 0 1)} : Set G) ⊓
      Subgroup.centralizer ({y} : Set G)) ∣ 264)
    (hB : Nat.card ↥(Subgroup.centralizer ({ψ (swap 0 1 * swap 2 3)} : Set G) ⊓
      Subgroup.centralizer ({y} : Set G)) ≤ 88) :
    Nat.card ↥(Subgroup.centralizer ({y} : Set G)) = 1320 := by
  have hmem : ∀ σ, ψ σ ∈ Subgroup.centralizer ({y} : Set G) := fun σ =>
    Subgroup.mem_centralizer_singleton_iff.2 (hc σ)
  have hyC : orderOf (⟨y, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ :
      ↥(Subgroup.centralizer ({y} : Set G))) = 11 := by
    rw [Subgroup.orderOf_mk]; exact hy
  refine B11Bender.card_eq_of_eleven_sym5 hyC (fun g => Subtype.ext
    (Subgroup.mem_centralizer_singleton_iff.1 g.2)) (ψ.codRestrict _ hmem)
    (fun a b h => hψ (congrArg Subtype.val h)) ?_ ?_
  · rw [card_centralizer_in_centralizer]
    exact hA
  · rw [card_centralizer_in_centralizer]
    exact hB

theorem factorization_card_B_eleven :
    (Nat.card NativeSporadic.B).factorization 11 = 1 := by
  rw [CFSG.Monster.Existence.card_nativeB, CFSG.Open.monsterBabyOrder,
    show (2 ^ 41 * 3 ^ 13 * 5 ^ 6 * 7 ^ 2 * 11 * 13 * 17 * 19 * 23 * 31 * 47 : ℕ) =
      11 * 377707407384220562834325504000000 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_self (by norm_num), Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

section Assembly


theorem card_centralizer_yEleven_of
    (hA : ∀ {u y : NativeSporadic.B}, BabyInv 0 u → orderOf y = 11 → Commute u y →
      Nat.card ↥(Subgroup.centralizer ({u} : Set NativeSporadic.B) ⊓
        Subgroup.centralizer ({y} : Set NativeSporadic.B)) ∣ 264) :
    Nat.card ↥(Subgroup.centralizer ({yEleven} : Set NativeSporadic.B)) = 1320 := by
  haveI : Finite NativeSporadic.B := CFSG.Monster.B.Pinned.finite_B
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have P := b11_parts
  obtain ⟨ψ, hψ, hc, h0, h02⟩ := exists_sym5_of_parts P
  have hyo : orderOf yEleven = 11 := orderOf_eq_prime P.y_pow P.y_ne
  have hne : b11Reg 1 ≠ 1 := by
    intro h
    have hr := P.rank₀
    rw [h] at hr
    simp at hr
  have hu : BabyInv 0 (ψ (swap 0 1)) := by
    rw [h0]
    exact CFSG.Monster.GMS.BabyInv.of_isConj CFSG.Monster.Existence.babyInv_zero_babyRep_one
      (CFSG.Monster.Existence.isConj_rep_one_of_rank
        (orderOf_eq_prime (by rw [sq]; exact P.sq₀) hne) P.rank₀).symm
  have hsq : b11Reg 1 * b11Reg 6 * (b11Reg 1 * b11Reg 6) = 1 := by
    calc b11Reg 1 * b11Reg 6 * (b11Reg 1 * b11Reg 6)
        = b11Reg 1 * (b11Reg 6 * b11Reg 1) * b11Reg 6 := by group
      _ = b11Reg 1 * (b11Reg 1 * b11Reg 6) * b11Reg 6 := by rw [← P.c₀₂]
      _ = (b11Reg 1 * b11Reg 1) * (b11Reg 6 * b11Reg 6) := by group
      _ = 1 := by rw [P.sq₀, P.sq₂, one_mul]
  have hXo : orderOf (ψ (swap 0 1 * swap 2 3)) = 2 := by
    rw [h02]
    exact orderOf_eq_prime (by rw [sq]; exact hsq) P.ne₀₂
  have hXr : Matrix.rank ((ψ (swap 0 1 * swap 2 3)).val.val - 1) = 2048 := by
    rw [h02]
    exact P.rank₀₂
  exact card_centralizer_eq_of_sym5 hyo ψ hψ hc (hA hu hyo (hc _))
    (B11TwoB.card_centralizer_inf_le_of_rank_2048 hXo hXr hyo (hc _))

theorem card_centralizer_eleven_B_eq_of
    (hA : ∀ {u y : NativeSporadic.B}, BabyInv 0 u → orderOf y = 11 → Commute u y →
      Nat.card ↥(Subgroup.centralizer ({u} : Set NativeSporadic.B) ⊓
        Subgroup.centralizer ({y} : Set NativeSporadic.B)) ∣ 264)
    (y : NativeSporadic.B) (hy : orderOf y = 11) :
    Nat.card ↥(Subgroup.centralizer ({y} : Set NativeSporadic.B)) = 1320 := by
  haveI : Finite NativeSporadic.B := CFSG.Monster.B.Pinned.finite_B
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hyo : orderOf yEleven = 11 := orderOf_eq_prime b11_parts.y_pow b11_parts.y_ne
  obtain ⟨g, k, hyk⟩ :=
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.exists_conj_pow_of_factorization_eq_one
      factorization_card_B_eleven hyo hy
  have hk1 : yEleven ^ k ≠ 1 := by
    intro h1
    rw [h1, mul_one, mul_inv_cancel] at hyk
    rw [hyk, orderOf_one] at hy
    norm_num at hy
  rw [hyk, CFSG.HardMathSupport.Timmesfeld.SporadicBalance.card_centralizer_conj_eq,
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.centralizer_pow_eq_of_prime hyo hk1]
  exact card_centralizer_yEleven_of hA

end Assembly

end CFSG.HardMathSupport.Dickson.BMRows.B11

namespace CFSG.HardMathSupport.Dickson.BMRows

open CFSG.Blueprint

section Final


theorem card_centralizer_eleven_B_eq (y : NativeSporadic.B) (hy : orderOf y = 11) :
    Nat.card ↥(Subgroup.centralizer ({y} : Set NativeSporadic.B)) = 1320 :=
  B11.card_centralizer_eleven_B_eq_of (fun hu hy' huy =>
    card_centralizer_inf_dvd_of_babyInv_zero hu hy' huy) y hy

theorem card_centralizer_eleven_B_le (y : NativeSporadic.B) (hy : orderOf y = 11) :
    Nat.card ↥(Subgroup.centralizer ({y} : Set NativeSporadic.B)) ≤ 1320 :=
  (card_centralizer_eleven_B_eq y hy).le

end Final

end CFSG.HardMathSupport.Dickson.BMRows
