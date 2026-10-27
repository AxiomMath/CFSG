module

public import CFSG.Quasithin.H13.A6S1372L74i
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6Inputs13_3

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} {S : Setting4 G T L V}

section Setting

variable {H : Subgroup G} (hH : H ∈ S.Hz)
include hH

theorem eq_one_of_cube_of_mem_M_F4 (h1337 : Stmt13_3_7_F4)
    (hhat : ¬ IsHatA6 L) {K : Subgroup G} (hKH : K ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hL1K : ¬ S.L1 ≤ K) {d : G} (hdK : d ∈ K)
    (hd3 : d ^ 3 = 1) (hdM : d ∈ Subgroup.normalizer (L : Set G)) : d = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hd1
  have hdH : d ∈ H := hKH hdK
  have hdV : d ∈ Subgroup.normalizer (V : Set G) := S.inf_M_le_NV' hH ⟨hdH, hdM⟩
  set dn : ↥(Subgroup.normalizer (V : Set G)) := ⟨d, hdV⟩ with hdn
  have hdz : d * S.z * d⁻¹ = S.z := by
    have h1 : d ∈ S.G1 := hH.2.1 hdH
    rw [Setting4.G1, Subgroup.mem_centralizer_singleton_iff] at h1
    rw [h1, mul_inv_cancel_right]
  have hfix := S.fix_e0123 dn hdz
  have hdn3 : dn ^ 3 = 1 := Subtype.ext (by simpa using hd3)
  have hρ3 : S.frame.ρ dn ^ 3 = 1 := by rw [← map_pow, hdn3, map_one]
  have h45 : S.frame.ρ dn ^ 45 = 1 := by
    rw [show (45 : ℕ) = 3 * 15 by norm_num, pow_mul, hρ3, one_pow]
  obtain ⟨h4, h5⟩ := fix45_of_odd _ hfix h45
  obtain ⟨x, hxL, hρx⟩ := S.exists_L1_rho hhat (A6L19.sign_eq_one_of_cube hρ3) h4 h5 hρ3

  have hy : ((x⁻¹ * dn : ↥(Subgroup.normalizer (V : Set G))) : G) ∈
      Subgroup.centralizer (V : Set G) :=
    (S.rho_eq_one_iff _).1 (by rw [map_mul, map_inv, hρx, inv_mul_cancel])
  have h3V : ¬ 3 ∣ Nat.card (Subgroup.centralizer (V : Set G)) :=
    (h1337 G T L V S.h13 S.irr S.a6).resolve_right fun h => hhat h.1
  set m := orderOf (⟨_, hy⟩ : ↥(Subgroup.centralizer (V : Set G))) with hm
  have hm3 : ¬ 3 ∣ m := fun h => h3V (h.trans (orderOf_dvd_natCard _))
  have hym : ((x : G)⁻¹ * d) ^ m = 1 := by
    have h1 := pow_orderOf_eq_one (⟨_, hy⟩ : ↥(Subgroup.centralizer (V : Set G)))
    rw [← hm] at h1
    have h2 := congrArg Subtype.val h1
    simpa using h2

  have hL1H : S.L1 ≤ H := le_sup_left.trans hH.1.1
  have hHN := le_normalizer_sup_QH hKH hHK
  have hxH : (x : G) ∈ H := hL1H hxL
  have hyH : (x : G)⁻¹ * d ∈ H := H.mul_mem (H.inv_mem hxH) hdH
  have hxm : (x : G) ^ m ∈ K ⊔ pCoreOf 2 H := by
    have e : (x : G) = d * ((x : G)⁻¹ * d)⁻¹ := by group
    obtain ⟨l', hl', he⟩ := U3.pow_mem_mul_of_normalizes' (Subgroup.mem_sup_left hdK :
      d ∈ K ⊔ pCoreOf 2 H) (hHN (H.inv_mem hyH)) m
    rw [inv_pow, hym, inv_one, mul_one] at he
    rw [e, he]
    exact hl'
  have hxmO : (x : G) ^ m ∈ pCoreOf 2 S.L1 :=
    S.L1_inf_sup_le hH hhat hKH hHK hL1K ⟨S.L1.pow_mem hxL m, hxm⟩
  have hx3O : (x : G) ^ 3 ∈ pCoreOf 2 S.L1 := S.cube_mem_pCoreOf_L1 hhat hxL

  have hxO : (x : G) ∈ pCoreOf 2 S.L1 := by
    have hcop : Nat.Coprime m 3 := (Nat.coprime_comm.mp
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hm3))
    obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
    have e : (x : G) = ((x : G) ^ m) ^ u * ((x : G) ^ 3) ^ v := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add,
        mul_comm (m : ℤ) u, mul_comm ((3 : ℕ) : ℤ) v, huv, zpow_one]
    rw [e]
    exact (pCoreOf 2 S.L1).mul_mem ((pCoreOf 2 S.L1).zpow_mem hxmO u)
      ((pCoreOf 2 S.L1).zpow_mem hx3O v)

  have hK4 : S.frame.ρ dn ∈ K4L := by
    rw [← hρx]
    exact S.rho_O2L1_mem_K4 hxO x.2
  have hdC : d ∈ Subgroup.centralizer (V : Set G) :=
    (S.rho_eq_one_iff dn).1 (A6L19.K4L_cube _ hK4 hρ3)
  have hord : orderOf (⟨d, hdC⟩ : ↥(Subgroup.centralizer (V : Set G))) = 3 :=
    orderOf_eq_prime (Subtype.ext (by simpa using hd3)) (fun h => hd1 (congrArg Subtype.val h))
  exact h3V (hord ▸ orderOf_dvd_natCard _)

end Setting

end Setting4

end CFSG.Quasithin.H13.A6
