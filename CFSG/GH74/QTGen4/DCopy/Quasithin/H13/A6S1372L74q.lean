module

public import CFSG.Quasithin.H13.A6S1372L74q
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372L74a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372L74p

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} {S : Setting4 G T L V}

section Odd

variable {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G} (hKH : K ≤ H)
  (hHK : H ≤ Subgroup.normalizer (K : Set G))
include hH hKH hHK

theorem card_eq_three_F4 (h1227 : U3.Stmt13_2_2_7_F4)
    (hhat : ¬ IsHatA6 L) (hB : ¬ H13.IsA6Block L)
    (hKU : ¬ K ≤ Subgroup.centralizer ((conjClosure S.V3 H ⊓
      Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G) : Set G))
    (hKM : ¬ K ≤ Subgroup.normalizer (L : Set G)) (hL1K : ¬ S.L1 ≤ K)
    (hexp : ∀ k ∈ K, k ^ 3 ∈ pCoreOf 2 K)
    (hcomm : ∀ k₁ ∈ K, ∀ k₂ ∈ K, k₁ * k₂ * k₁⁻¹ * k₂⁻¹ ∈ pCoreOf 2 K)
    (hCK : K ⊓ Subgroup.centralizer
      (twoReducedProduct (K ⊔ pCoreOf 2 (S.L1 ⊔ T)) : Set G) = pCoreOf 2 K) :
    Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, h3⟩ := A6L74.quot_comm_cube hexp hcomm
  have hP : IsPGroup 3 (↥K ⧸ CFSG.pCore 2 ↥K) := fun y => ⟨1, by rw [pow_one]; exact h3 y⟩
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hH2 : CFSG.Open.pRank 3 H ≤ 2 :=
    pRank_le_two_of_pCoreOf_ne_bot S.h13.qtke hH.1.2 Nat.prime_three (by norm_num)
  rcases Nat.lt_or_ge n 2 with hlt | hge
  · interval_cases n
    ·
      exfalso
      apply hKU
      have hOQ : pCoreOf 2 K ≤ pCoreOf 2 H :=
        le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K).trans hKH)
          (hHK.trans (normalizer_le_normalizer_pCoreOf 2 K)) (pCoreOf_isPGroup 2 K)
      have hsub : Subsingleton (↥K ⧸ CFSG.pCore 2 ↥K) :=
        (Nat.card_eq_one_iff_unique.mp (by rw [hn, pow_zero])).1
      intro k hk
      have h1 : (QuotientGroup.mk ⟨k, hk⟩ : ↥K ⧸ CFSG.pCore 2 ↥K) = 1 := Subsingleton.elim _ _
      rw [QuotientGroup.eq_one_iff] at h1
      have hkO := (A6L74.mem_pCoreOf_iff ⟨k, hk⟩).2 h1
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      exact (Subgroup.mem_centralizer_iff.mp hu.2 k (hOQ hkO)).symm
    · rw [hn, pow_one]
  rcases Nat.lt_or_ge n 3 with hlt3 | hge3
  ·
    exfalso
    have hn2 : n = 2 := by omega
    rw [hn2] at hn
    have h9 : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 9 := by rw [hn]; norm_num
    obtain ⟨x, hxL, hx3, hxK⟩ := exists_L1_not_mem hhat hL1K
    have hxc := comm_L1_of_card_nine_F4 hH hKH hHK h1227 hhat hB hKM hexp hcomm hCK h9 hxL hx3
    have hL1N : S.L1 ≤ Subgroup.normalizer (K : Set G) := (le_sup_left.trans hH.1.1).trans hHK
    have h1 := A6L74.three_le_pRank_of_comm hexp hcomm h9 (hL1N hxL) hx3 hxK hxc
    have hYH : K ⊔ Subgroup.zpowers x ≤ H :=
      sup_le hKH (Subgroup.zpowers_le.2 ((le_sup_left.trans hH.1.1) hxL))
    have h2 := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hYH
    omega
  ·
    exfalso
    have h1 := A6L74.le_pRank_of_card hexp hcomm hn
    have h2 := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hKH
    omega

end Odd

end Setting4

theorem lem1374OneOdd_of_F4 (h1227 : U3.Stmt13_2_2_7_F4)
    (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4) : Lem1374OneOdd_F4 := by
  intro G _ _ T L V S hNS _ hhat H hH hab hB p hp hp2 K hKH hHK _ _ hKU hKU' hKM hL1K hexp
    hcomm _
  have hCK := Setting4.inf_centralizer_R2_eq_F4 hH hKH hHK hNS h13315 h1356two hab hKU'
  have h3 := Setting4.eq_three_F4 hH hKH hHK h1227 hhat hB hKM hp hp2 hexp hcomm hCK
  subst h3
  exact ⟨rfl, Setting4.card_eq_three_F4 hH hKH hHK h1227 hhat hB hKU hKM hL1K hexp hcomm hCK⟩

end CFSG.Quasithin.H13.A6
