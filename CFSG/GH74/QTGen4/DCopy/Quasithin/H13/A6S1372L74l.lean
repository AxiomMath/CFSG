module

public import CFSG.Quasithin.H13.A6S1372L74l
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1357
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3C137

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

theorem inf_centralizer_R2_eq_F4 (hNS : ¬ LieModel G .PSp 3 2 1)
    (h13315 : Stmt13_3_15_F4)
    (h1356two : Input1356Two_F4) (hab : IsElemAbelian 2 (conjClosure S.V3 H))
    (hKU' : K ⊓ Subgroup.centralizer ((conjClosure S.V3 H ⊓
      Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G) : Set G) ≤ pCoreOf 2 K) :
    K ⊓ Subgroup.centralizer
      (twoReducedProduct (K ⊔ pCoreOf 2 (S.L1 ⊔ T)) : Set G) = pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U₀ : Subgroup G := conjClosure S.V3 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G)
    with hU₀def
  have hF := S.hypF91_F4 hNS h13315 h1356two hH
  have hU₀Q : U₀ ≤ pCoreOf 2 H := inf_le_left.trans hF.conjClosure_Vp_le_pCoreOf
  obtain ⟨-, hRK⟩ := pCoreOf_le_R1_and hH hKH hHK
  have hXK : K ⊔ pCoreOf 2 (S.L1 ⊔ T) ≤ Subgroup.normalizer (K : Set G) :=
    sup_le Subgroup.le_normalizer hRK
  have hXH : K ⊔ pCoreOf 2 (S.L1 ⊔ T) ≤ H := sup_le hKH ((pCoreOf_le 2 _).trans hH.1.1)
  have hOQ : pCoreOf 2 K ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K).trans hKH)
      (hHK.trans (normalizer_le_normalizer_pCoreOf 2 K)) (pCoreOf_isPGroup 2 K)
  have hQU : pCoreOf 2 H ≤ Subgroup.centralizer (U₀ : Set G) := fun q hq => by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact (Subgroup.mem_centralizer_iff.mp hu.2 q hq).symm
  exact centralizer_twoReducedProduct_eq le_sup_left hXK
    (hU₀Q.trans ((QH_le_R1 hH).trans le_sup_right)) (hXH.trans S.le_normalizer_U0)
    (A1b.isElemAbelian_of_le inf_le_left hab)
    (le_antisymm hKU' (le_inf (pCoreOf_le 2 K) (hOQ.trans hQU)))

theorem not_thompsonJ_le_F4 (h1227 : U3.Stmt13_2_2_7_F4) (hhat : ¬ IsHatA6 L)
    (hB : ¬ H13.IsA6Block L) (hKM : ¬ K ≤ Subgroup.normalizer (L : Set G)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hexp : ∀ k ∈ K, k ^ p ∈ pCoreOf 2 K)
    (hCK : K ⊓ Subgroup.centralizer
      (twoReducedProduct (K ⊔ pCoreOf 2 (S.L1 ⊔ T)) : Set G) = pCoreOf 2 K) :
    ¬ thompsonJ (pCoreOf 2 (S.L1 ⊔ T)) ≤
      Subgroup.centralizer (twoReducedProduct (K ⊔ pCoreOf 2 (S.L1 ⊔ T)) : Set G) := by
  intro hJ
  obtain ⟨-, hred, hRC, hUR⟩ := R2_data hH hKH hHK hp hp2 hexp hCK
  have hbaum : baum (pCoreOf 2 (S.L1 ⊔ T)) = baum (pCoreOf 2 (K ⊔ pCoreOf 2 (S.L1 ⊔ T))) := by
    rw [← hRC]
    exact baum_eq_baum_centralizer hred.2.2.1 hUR (le_inf (thompsonJ_le_self _) hJ)
  have hRM : Subgroup.normalizer (baum (pCoreOf 2 (S.L1 ⊔ T)) : Set G) ≤
      Subgroup.normalizer (L : Set G) := by
    rcases h1227 G T L V S.L1 S.h13 S.irr S.zv (fun h => absurd h hhat) (fun _ => rfl) S.a6
      with h | h
    · exact normalizer_baum_R1_le_M h
    · exact absurd h hB
  apply hKM
  intro k hk
  apply hRM
  rw [hbaum]
  exact normalizer_le_normalizer_baum _ (le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hk))

theorem eq_three_F4 (h1227 : U3.Stmt13_2_2_7_F4) (hhat : ¬ IsHatA6 L) (hB : ¬ H13.IsA6Block L)
    (hKM : ¬ K ≤ Subgroup.normalizer (L : Set G)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hexp : ∀ k ∈ K, k ^ p ∈ pCoreOf 2 K)
    (hcomm : ∀ k₁ ∈ K, ∀ k₂ ∈ K, k₁ * k₂ * k₁⁻¹ * k₂⁻¹ ∈ pCoreOf 2 K)
    (hCK : K ⊓ Subgroup.centralizer
      (twoReducedProduct (K ⊔ pCoreOf 2 (S.L1 ⊔ T)) : Set G) = pCoreOf 2 K) : p = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJ := not_thompsonJ_le_F4 hH hKH hHK h1227 hhat hB hKM hp hp2 hexp hCK
  obtain ⟨hsyl, hred, -, -⟩ := R2_data hH hKH hHK hp hp2 hexp hCK
  obtain ⟨-, hRK⟩ := pCoreOf_le_R1_and hH hKH hHK
  have hR2 : IsPGroup 2 (pCoreOf 2 (S.L1 ⊔ T)) := pCoreOf_isPGroup 2 _
  set X := K ⊔ pCoreOf 2 (S.L1 ⊔ T) with hX
  set U := twoReducedProduct X with hU
  have hUe : IsElemAbelian 2 U := hred.2.2.1
  have hXU : X ≤ Subgroup.normalizer (U : Set G) := hred.2.1
  have hsolv : Group.IsSolvable ↥(autI hUe X) := by
    rw [← range_convHom hUe X hXU]
    have := A6L74.isSolvable_sup hcomm hR2 hRK
    exact Group.isSolvable_of_surjective (f := (convHom hUe X hXU).rangeRestrict)
      (MonoidHom.rangeRestrict_surjective _)
  obtain ⟨I, -, hJX, -, -, hnat, -⟩ := B2F.structure_of_not_le_of_quot hUe hred hsolv hsyl hJ

  have h3 : 3 ∣ Nat.card X := by
    by_cases hI : I = ∅
    · exfalso
      subst hI
      have hbot : autI hUe (thompsonJ X) = ⊥ := by
        rw [hJX]
        simp
      rw [autI_eq_bot_iff hUe ((thompsonJ_le_self X).trans hXU)] at hbot
      exact hJ ((thompsonJ_le_thompsonJ_of_isSylowTwoOf hsyl).trans hbot)
    · obtain ⟨Lb, hLb⟩ := Finset.nonempty_iff_ne_empty.mpr hI
      obtain ⟨e, -, -⟩ := hnat Lb hLb
      have hL6 : Nat.card Lb = 6 := by
        rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
        decide
      have hLle : Lb ≤ autI hUe X := by
        refine (le_iSup₂_of_le Lb hLb le_rfl : Lb ≤ ⨆ L' ∈ I, L').trans ?_
        rw [← hJX]
        exact autI_mono hUe (thompsonJ_le_self X)
      have hdvd : Nat.card Lb ∣ Nat.card X := by
        refine (Subgroup.card_dvd_of_le hLle).trans ?_
        exact Dvd.intro _ (card_autI_mul_card_inf hUe hXU)
      rw [hL6] at hdvd
      exact (by norm_num : (3 : ℕ) ∣ 6).trans hdvd

  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 3 h3
  have hx3 : (x : G) ^ 3 = 1 := by
    have h1 := pow_orderOf_eq_one x
    rw [hx] at h1
    simpa using congrArg Subtype.val h1
  have hxo : orderOf (x : G) = 3 := by rw [Subgroup.orderOf_coe, hx]
  have hxK : (x : G) ∈ K := A6L74.mem_of_odd_of_mem_sup hR2 hRK x.2 (by decide) hx3
  by_contra hp3
  have hcop : Nat.Coprime p (orderOf (x : G)) := by
    rw [hxo]
    exact (Nat.coprime_primes hp Nat.prime_three).2 hp3
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have hxO : (x : G) ∈ pCoreOf 2 K := by
    rw [← hm]
    exact (pCoreOf 2 K).pow_mem (hexp _ hxK) m
  obtain ⟨b, hb⟩ := pCoreOf_isPGroup 2 K ⟨_, hxO⟩
  have hxb : (x : G) ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
  have h1 := A6L19.eq_one_of_odd_of_two (by decide : Odd 3) hx3 hxb
  rw [h1, orderOf_one] at hxo
  exact absurd hxo (by norm_num)

end Odd

end Setting4

end CFSG.Quasithin.H13.A6
