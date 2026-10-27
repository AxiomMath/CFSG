module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372Fourteen
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6Statements
public import CFSG.Quasithin.EmptyFaithful.SBd5Perf
public import CFSG.Quasithin.H13.A6S1372Sixteen

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} {S : Setting4 G T L V}

section NonAb

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4)
  {H : Subgroup G} (hH : H ∈ S.Hz) (hab : IsElemAbelian 2 (conjClosure S.V3 H))
include hNS h13315 h1356two hH hab

theorem eq_of_mem_cComp_of_plus_eq_F4 (hhat : ¬ IsHatA6 L)
    (hNU : ¬ LieModel G .PSU 4 3 1) (hLem : Lem1374One_F4) [IsMulCommutative ↥(conjClosure S.V3 H)]
    {K₁ K₂ : Subgroup G} (h₁ : K₁ ∈ cComp H) (h₂ : K₂ ∈ cComp H)
    (he : autSec (autOn K₁ (conjClosure S.V3 H)) ⊤
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) =
      autSec (autOn K₂ (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) :
    K₁ = K₂ := by
  have hHU : H ≤ Subgroup.normalizer ((conjClosure S.V3 H : Subgroup G) : Set G) :=
    le_normalizer_conjClosure S.V3 H
  have hHC := S.le_normalizer_U0 (H := H)
  set ρ := A6Mod.secAct hHU hHC with hρ
  have hsolv : Group.IsSolvable ρ.ker := by
    rw [S.ker_secAct_plus_F4 hNS h13315 h1356two hH hab hNU hhat hLem]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := (CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := ↥H)).isNilpotent
    infer_instance
  have hbij := LocDbl.cComp_map_bijOn_of_ker H.subtype
    (LocDbl.isSolvable_ker_of_injective _ H.subtype_injective) (⊤ : Subgroup ↥H)
  have htop : (⊤ : Subgroup ↥H).map H.subtype = H := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [htop] at hbij
  obtain ⟨K₁₀, hK₁₀, rfl⟩ := hbij.surjOn h₁
  obtain ⟨K₂₀, hK₂₀, rfl⟩ := hbij.surjOn h₂
  have hmap : ∀ F : Subgroup ↥H, autSec (autOn (F.map H.subtype) (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) =
      F.map ρ := by
    intro F
    ext ψ
    rw [A6Mod.mem_autSec_iff hHU hHC (Subgroup.map_subtype_le F), Subgroup.mem_map]
    constructor
    · rintro ⟨h, ⟨k, hk, hkh⟩, rfl⟩
      have : k = h := Subtype.ext hkh
      exact ⟨k, hk, by rw [this]⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k, ⟨k, hk, rfl⟩, rfl⟩
  rw [hmap, hmap] at he
  rw [LocDbl.map_injOn_cComp ρ hsolv ⊤ hK₁₀ hK₂₀ he]

namespace Conf

variable [IsMulCommutative ↥(conjClosure S.V3 H)] {C : S.Conf H}
  {B : Subgroup (MulAut (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))))}
  {K : Subgroup G}

theorem KData.le_normalizer_F4 (hhat : ¬ IsHatA6 L)
    (hNU : ¬ LieModel G .PSU 4 3 1) (hLem : Lem1374One_F4)
    (hK : C.KData B K) : H ≤ Subgroup.normalizer (K : Set G) := by
  obtain ⟨-, -, hKc, -, -, -, hXN, -⟩ := hK
  have hHU : H ≤ Subgroup.normalizer ((conjClosure S.V3 H : Subgroup G) : Set G) :=
    le_normalizer_conjClosure S.V3 H
  have hHC := S.le_normalizer_U0 (H := H)
  have hrange := S.range_secAct_plus (H := H)
  intro h hh
  have hc := LocDbl.map_conj_mem_cComp hKc (Subgroup.le_normalizer hh)
  have hρX : A6Mod.secAct hHU hHC ⟨h, hh⟩ ∈ autSec (autOn H (conjClosure S.V3 H)) ⊤
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) :=
    hrange ▸ ⟨_, rfl⟩
  have he : autSec (autOn (K.map (MulAut.conj h).toMonoidHom) (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) =
      autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) := by
    rw [A6Mod.autSec_map_conj hHU hHC (le_of_mem_cComp hKc) ⟨h, hh⟩]
    exact B19.map_conj_eq_of_mem_normalizer (hXN hρX)
  exact B19.mem_normalizer_of_map_conj_eq
    (eq_of_mem_cComp_of_plus_eq_F4 hNS h13315 h1356two hH hab hhat hNU hLem hc hKc he)

theorem KData.isFaithfulLocal_F4 (hhat : ¬ IsHatA6 L)
    (hNU : ¬ LieModel G .PSU 4 3 1) (hLem : Lem1374One_F4)
    (hK : C.KData B K)
    (hKU : ¬ K ≤ Subgroup.centralizer ((conjClosure S.V3 H ⊓
      Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G) : Set G)) :
    quasithinIsFaithfulLocal T K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKc : K ∈ cComp H := hK.2.2.1
  set U₀ : Subgroup G := conjClosure S.V3 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G)
    with hU₀def
  have hF := S.hypF91_F4 hNS h13315 h1356two hH
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hHN := hK.le_normalizer_F4 hNS h13315 h1356two hH hab hhat hNU hLem
  have hQH : pCoreOf 2 H ≤ H := pCoreOf_le 2 H
  have hU₀Q : U₀ ≤ pCoreOf 2 H :=
    inf_le_left.trans hF.conjClosure_Vp_le_pCoreOf
  have hU₀N : U₀ ≤ Subgroup.normalizer (K : Set G) := (hU₀Q.trans hQH).trans hHN
  have hKN : K ≤ Subgroup.normalizer (U₀ : Set G) :=
    (le_of_mem_cComp hKc).trans S.le_normalizer_U0
  have hc1 : ⁅U₀, K⁆ ≤ K := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp hU₀N
  have hc2 : ⁅U₀, K⁆ ≤ U₀ :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hKN

  have hp : IsPGroup 2 ↥(⁅U₀, K⁆) := (pCoreOf_isPGroup 2 H).to_le (hc2.trans hU₀Q)
  have hcO : ⁅U₀, K⁆ ≤ pCoreOf 2 K :=
    le_pCoreOf_of_le_normalizer 2 hc1 (fun k hk =>
      SBd5.mem_normalizer_commutator_of (hKN hk) (Subgroup.le_normalizer hk)) hp
  have hOK : pCoreOf 2 K ≤ pCoreOf 2 H := A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hKc)

  have hΩ : ⁅U₀, K⁆ ≤ omegaOneCenterOf (pCoreOf 2 K) := by
    intro x hx
    refine Subgroup.subset_closure ⟨⟨hcO hx, ?_⟩, ?_⟩
    · intro y hy
      exact (hc2 hx).2 y (hOK hy)
    · exact hab.2 x (hc2 hx).1

  have hU₀ab : ∀ x ∈ U₀, ∀ y ∈ U₀, x * y = y * x :=
    fun x hx y hy => congrArg Subtype.val (hab.1.is_comm.comm ⟨x, hx.1⟩ ⟨y, hy.1⟩)
  have hperf : ⁅K, K⁆ = K := perfect_of_mem_cComp hKc
  have hcc : ⁅⁅U₀, K⁆, K⁆ = ⁅U₀, K⁆ :=
    SBd5.commutator_commutator_eq_self hperf hKN hU₀ab
  have hne : ⁅U₀, K⁆ ≠ ⊥ := by
    intro h
    apply hKU
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
    exact Subgroup.le_centralizer_iff.mp h
  have hVY : VY K ≠ ⊥ := by
    intro h
    apply hne
    rw [← hcc, eq_bot_iff, ← h]
    exact Subgroup.commutator_mono hΩ le_rfl
  have hXC : IsXClass K := ⟨ne_bot_of_mem_cComp hKc, eq_oTwoUpper_of_perfect hperf,
    A4.charTwo_of_subnormal (subnormal_of_mem_cComp hKc) hF.charTwo_H⟩
  have hloc := isLocal_of_mem_cComp_of_sylow
    (isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow hTH) hH.1.2 hKc
  exact isFaithfulLocal_iff_isXf.mpr ⟨hloc, hXC, hVY⟩

theorem KData.list13_5_2_F4 (hhat : ¬ IsHatA6 L)
    (hNU : ¬ LieModel G .PSU 4 3 1) (hLem : Lem1374One_F4) (h1352 : Stmt13_5_2_F4)
    (hK : C.KData B K)
    (hKU : ¬ K ≤ Subgroup.centralizer ((conjClosure S.V3 H ⊓
      Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G) : Set G)) :
    (Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) ∨
        LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1 ∨
        Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 6)) ∨
        (Group.IsPerfect (↥K ⧸ CFSG.pCore 2 ↥K) ∧
          Nat.card (Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) = 3 ∧
          Nonempty ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) ≃*
            alternatingGroup (Fin 6)))) :=
  (h1352 G T L S.h13 hNS K
    (hK.isFaithfulLocal_F4 hNS h13315 h1356two hH hab hhat hNU hLem hKU)).1

end Conf

end NonAb

end Setting4

end CFSG.Quasithin.H13.A6
