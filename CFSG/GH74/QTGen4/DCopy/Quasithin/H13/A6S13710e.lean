module

public import CFSG.Quasithin.H13.A6S13710e
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S13710c

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

namespace Conf

variable {S}

theorem nu_O2L1_eq_F4 (hNS : ¬ LieModel G .PSp 3 2 1)
    (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4) {H : Subgroup G} (hH : H ∈ S.Hz)
    (hab : IsElemAbelian 2 (conjClosure S.V3 H)) (C : S.Conf H) (hhat : ¬ IsHatA6 L)
    (hna : ¬ IsElemAbelian 2 (conjClosure V H)) (h13314 : Stmt13_3_14_F4) :
    ∃ c₁ : ↥(Subgroup.normalizer (V : Set G)), (c₁ : G) ∈ S.L1 ∧ (c₁ : G) ^ 3 = 1 ∧
      (c₁ : G) ∉ pCoreOf 2 S.L1 ∧
      nu (c₁ : G) (pCoreOf 2 S.L1) =
        16 * ((C.VHg ⊓ pCoreOf 2 (L ⊔ T) ⊓ pCoreOf 2 H).relIndex
          (C.VHg ⊓ pCoreOf 2 (L ⊔ T))) ^ 2 := by
  obtain ⟨c₁, hc₁L, hc₁3, hρc₁, hν⟩ := C.exists_c1_F4 hNS h13315 h1356two hH hab hhat
  refine ⟨c₁, hc₁L, hc₁3, ?_, ?_⟩
  · intro h
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 S.L1 ⟨_, h⟩
    have hk' : (c₁ : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h1 : orderOf (c₁ : G) ∣ Nat.gcd 3 (2 ^ k) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hc₁3) (orderOf_dvd_of_pow_eq_one hk')
    have h2 : Nat.gcd 3 (2 ^ k) = 1 := Nat.Coprime.pow_right _ (by decide : Nat.Coprime 3 2)
    rw [h2, Nat.dvd_one, orderOf_eq_one_iff] at h1
    have h4 : c₁ = 1 := Subtype.ext h1
    rw [h4, map_one] at hρc₁
    exact absurd hρc₁.symm (by decide)
  · rw [S.nu_O2L1_eq_mul hhat c₁ hc₁L hc₁3 hρc₁, S.relIndex_O2L1_eq_four hhat, hν,
      C.nu_cQ_F4 hNS h13315 h1356two hH hab hhat, ← C.A_eq_F4 hNS h13315 h1356two hH hab hhat,
      C.A_inf_QH_F4 hNS h13315 h1356two hH hab hhat hna h13314]
    ring

end Conf

end Setting4

end CFSG.Quasithin.H13.A6
