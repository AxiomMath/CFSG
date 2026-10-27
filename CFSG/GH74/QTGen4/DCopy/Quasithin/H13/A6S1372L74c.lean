module

public import CFSG.Quasithin.H13.A6S1372L74c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372L76N3c

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting4 G T L V)

section Setting

variable {S} (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4)
  {H : Subgroup G} (hH : H ∈ S.Hz)
include hNS h13315 h1356two hH

theorem QH_le_C74_F4 : pCoreOf 2 H ≤ S.C74 H := by
  have hF := S.hypF91_F4 hNS h13315 h1356two hH
  intro q hq
  exact (S.mem_C74_iff).2 ⟨pCoreOf_le 2 H hq, fun u hu =>
    S.V1_le_centralizer_QH_F4 hNS h13315 h1356two hH (hF.commutator_mem_V₁ hq hu)⟩

theorem not_L1_le_C74_F4 (h13314 : Stmt13_3_14_F4)
    (hhat : ¬ IsHatA6 L) : ¬ S.L1 ≤ S.C74 H := by
  intro hle
  have hc := (S.mem_C74_iff).1 (hle (S.cL1_mem hhat))
  have h1 := hc.2 S.v2 (S.v2_mem_UH H)
  have hV3 : (S.cL1 hhat : G) * S.v2 * (S.cL1 hhat : G)⁻¹ * S.v2⁻¹ ∈ S.V3 :=
    S.V3.mul_mem (S.conj_v2_mem_V3 (S.cL1_rho hhat)) (S.V3.inv_mem S.v2_mem_V3)
  exact S.comm_v2_not_mem_V1 (S.cL1_rho hhat)
    (S.V3_inf_centralizer_QH_le_F4 hNS h13315 h1356two hH h13314 ⟨hV3, h1⟩)

theorem not_le_centralizer_U0_F4
    (hab : IsElemAbelian 2 (conjClosure S.V3 H)) {K : Subgroup G} (hKC : K ≤ S.C74 H)
    (hK2 : oTwoRes K = K) (hKQ : ¬ K ≤ pCoreOf 2 H) :
    ¬ K ≤ Subgroup.centralizer ((conjClosure S.V3 H ⊓
      Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hKU
  have hF := S.hypF91_F4 hNS h13315 h1356two hH
  apply hKQ
  rw [← hK2]
  refine (Subgroup.closure_le _).2 ?_
  rintro k ⟨hk, m, hm, hkm⟩
  obtain ⟨hkH, hku⟩ := (S.mem_C74_iff).1 (hKC hk)
  have hkU : k ∈ Subgroup.normalizer (conjClosure S.V3 H : Set G) :=
    le_normalizer_conjClosure S.V3 H hkH

  have hcent : ∀ u ∈ conjClosure S.V3 H, k * u * k⁻¹ = u := by
    intro u hu
    refine A6L74.conj_eq_of_odd hab (inf_le_left :
      conjClosure S.V3 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ≤ conjClosure S.V3 H)
      (fun w hw => ?_) (fun a ha => ⟨(conjClosure S.V3 H).mul_mem
        ((Subgroup.mem_normalizer_iff.mp hkU a).mp ha) ((conjClosure S.V3 H).inv_mem ha),
        hku a ha⟩) hm hkm hu
    have := Subgroup.mem_centralizer_iff.mp (hKU hk) w hw
    rw [← this, mul_inv_cancel_right]

  have hkQ : k ∈ pCoreOf 2 H :=
    (S.mem_QH_iff_tilde_F4 hNS h13315 h1356two hH hkH).2 fun u hu => by
      rw [hcent u hu, mul_inv_cancel]
      exact Subgroup.one_mem _
  exact hkQ

omit hNS h13315 h1356two in

theorem not_le_normalizer_L_F4 (h139 : Stmt13_3_9_F4)
    (hhat : ¬ IsHatA6 L) {K : Subgroup G} (hKH : K ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hK2 : oTwoRes K = K) (hK1 : K ≠ ⊥)
    (hL1K : ¬ S.L1 ≤ K) : ¬ K ≤ Subgroup.normalizer (L : Set G) := by
  intro hKM
  have hz : S.z ∈ fsuV1 T V := S.mem_V1_iff.2 (Or.inr rfl)
  have hzL : S.z ∉ Subgroup.centralizer (L : Set G) := by
    intro h
    have h1 : S.z ∈ V ⊓ Subgroup.centralizer (L : Set G) := ⟨S.z_mem_V, h⟩
    rw [S.zv, Subgroup.mem_bot] at h1
    exact S.z_ne_one h1
  have hKz : K ≤ Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({S.z} : Set G) :=
    le_inf hKM (hKH.trans hH.2.1)
  have hInH : InH T H := ⟨le_sup_right.trans hH.1.1, hH.1.2⟩
  rcases h139 G T L V H K S.z S.h13 S.irr S.a6 hInH hH.2.2 hK2 hKH hHK hz hzL hKz with
    h | ⟨-, hA6, -⟩
  · exact hK1 h
  · exact hL1K (hA6 (S.nonempty_alt6_of_not_hat hhat)).ge

end Setting

end Setting4

end CFSG.Quasithin.H13.A6
