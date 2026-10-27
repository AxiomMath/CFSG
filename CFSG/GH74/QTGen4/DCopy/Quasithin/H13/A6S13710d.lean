module

public import CFSG.Quasithin.H13.A6S13710d
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S13710c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1378

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

@[expose] def Input13721Six_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (S : Setting4 G T L V),
    ¬ LieModel G .PSp 3 2 1 → ¬ LieModel G .PSU 4 3 1 → ¬ IsHatA6 L → S.G1 ∈ S.Hz →
    IsElemAbelian 2 (conjClosure S.V3 S.G1) → ¬ IsElemAbelian 2 (conjClosure V S.G1) →
    ∀ g : ↥(Subgroup.normalizer (V : Set G)), (g : G) ∈ L → S.frame.ρ g = swap 0 1 * swap 3 5 →
      (∀ c ∈ S.L1, c ^ 3 = 1 → c ∉ pCoreOf 2 S.L1 → 4 ^ 6 ≤ nu c (pCoreOf 2 S.L1)) ∧
      (conjSub (g : G)⁻¹ (conjClosure V S.G1) ⊓ pCoreOf 2 (L ⊔ T) ⊓ pCoreOf 2 S.G1).relIndex
        (conjSub (g : G)⁻¹ (conjClosure V S.G1) ⊓ pCoreOf 2 (L ⊔ T)) ≤ 8

theorem input1379Six_of_F4 (h13315 : Stmt13_3_15_F4)
    (h1356two : Input1356Two_F4) (h13314 : Stmt13_3_14_F4) (h13721 : Input13721Six_F4) :
    Input1379Six_F4 := by
  intro G _ _ T L V S hNS hNU hhat hG1 hab
  by_contra hna
  obtain ⟨C⟩ := S.exists_conf_F4 hNS h13315 h1356two hG1 hab hna
  obtain ⟨h6, h8⟩ := h13721 G T L V S hNS hNU hhat hG1 hab hna C.g C.g_mem C.rho_g
  obtain ⟨c₁, hc₁L, hc₁3, hρc₁, hν⟩ := C.exists_c1_F4 hNS h13315 h1356two hG1 hab hhat
  have hle := S.nu_O2L1_le hhat c₁ hc₁L hc₁3 hρc₁
  rw [hν, C.nu_cQ_F4 hNS h13315 h1356two hG1 hab hhat] at hle
  have hnot : (c₁ : G) ∉ pCoreOf 2 S.L1 :=
    not_mem_pCoreOf_L1 S c₁ hc₁3 (by rw [hρc₁]; decide)
  have h1 := h6 c₁ hc₁L hc₁3 hnot
  have hA : (C.VHg ⊓ pCoreOf 2 (L ⊔ T) ⊓ pCoreOf 2 S.G1).relIndex (C.VHg ⊓ pCoreOf 2 (L ⊔ T)) =
      C.ZI.relIndex C.A := by
    rw [← C.A_eq_F4 hNS h13315 h1356two hG1 hab hhat,
      C.A_inf_QH_F4 hNS h13315 h1356two hG1 hab hhat hna h13314]
  have h8' : C.ZI.relIndex C.A ≤ 8 := by
    rw [← hA]
    exact h8
  have hsq : C.ZI.relIndex C.A ^ 2 ≤ 64 := by
    calc C.ZI.relIndex C.A ^ 2 ≤ 8 ^ 2 := Nat.pow_le_pow_left h8' 2
      _ = 64 := by norm_num
  have h46 : (4 : ℕ) ^ 6 = 4096 := by norm_num
  rw [h46] at h1
  omega

end CFSG.Quasithin.H13.A6
