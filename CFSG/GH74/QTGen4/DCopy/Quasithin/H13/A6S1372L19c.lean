module

public import CFSG.Quasithin.H13.A6S1372L19c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372L24c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6Set14
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3C137

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative commutatorElement

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

section KTilde

variable {S}

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4)
  {H : Subgroup G} (hH : H ∈ S.Hz) (hab : IsElemAbelian 2 (conjClosure S.V3 H))
include hNS h13315 h1356two hH hab

namespace Conf

omit hab in

theorem not_isA6Block_F4 (C : S.Conf H) (hhat : ¬ IsHatA6 L)
    (hna : ¬ IsElemAbelian 2 (conjClosure V H)) (h13314 : Stmt13_3_14_F4) (h1222 : Stmt12_2_2_F4)
    (h323 : Stmt3_2_3) (hab : IsElemAbelian 2 (conjClosure S.V3 H)) :
    ¬ H13.IsA6Block L := by
  intro hB
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx, hx3, -, hxN, hρx⟩ := U3.L15A.exists_X_nonhat S hhat
  have S14 := S14.set14_of_F4 h1222 h323 S S.isV2 (S14.plusData_L1 S hhat)
    (S14.bcase_of S (oTwoRes_le _ hx) hx3 hxN hρx) ⟨fun h => absurd h hhat, fun _ => rfl⟩
  obtain ⟨c₁, hc₁L, hc₁3, -, hν⟩ := C.nu_O2L1_eq_F4 hNS h13315 h1356two hH hab hhat hna h13314
  have h16 := S14.relIndex_R1_le_sixteen (Or.inr hB) hc₁L hc₁3
  have hle : nu (c₁ : G) (pCoreOf 2 S.L1) ≤ nu (c₁ : G) (pCoreOf 2 (S.L1 ⊔ T)) := by
    refine nu_le_nu S.pCoreOf_L1_le_R1 fun y hy => ?_
    have hyR : y ∈ pCoreOf 2 (S.L1 ⊔ T) := (mem_cfix.1 hy).1
    exact (sup_le (le_normalizer_pCoreOf 2 S.L1)
      (S.T_le_normalizer_L1.trans (normalizer_le_normalizer_pCoreOf 2 S.L1)))
      (pCoreOf_le 2 _ hyR)
  have hnuR : nu (c₁ : G) (pCoreOf 2 (S.L1 ⊔ T)) =
      (Subgroup.centralizer ({(c₁ : G)} : Set G)).relIndex (pCoreOf 2 (S.L1 ⊔ T)) := by
    rw [nu, cfix, inf_comm, Subgroup.inf_relIndex_right]
  rw [hν, hnuR] at hle
  set r := (C.VHg ⊓ pCoreOf 2 (L ⊔ T) ⊓ pCoreOf 2 H).relIndex (C.VHg ⊓ pCoreOf 2 (L ⊔ T))
    with hr
  have hr1 : r ≤ 1 := by
    by_contra h
    push Not at h
    have h4 : 2 ^ 2 ≤ r ^ 2 := Nat.pow_le_pow_left h 2
    generalize r ^ 2 = q at h4 hle
    omega
  have hr0 : r ≠ 0 := by
    rw [hr]
    show ((C.VHg ⊓ pCoreOf 2 (L ⊔ T) ⊓ pCoreOf 2 H).subgroupOf
      (C.VHg ⊓ pCoreOf 2 (L ⊔ T))).index ≠ 0
    exact Subgroup.index_ne_zero_of_finite
  have hr1' : r = 1 := by omega
  have hAQ : C.VHg ⊓ pCoreOf 2 (L ⊔ T) ≤ pCoreOf 2 H :=
    (Subgroup.relIndex_eq_one.mp hr1').trans inf_le_right
  apply C.not_UHg_le_QH_F4 hNS h13315 h1356two hH hab hhat hna h13314
  have hA := C.A_eq_F4 hNS h13315 h1356two hH hab hhat
  exact (C.UHg_le_A_F4 hNS h13315 h1356two hH hab).trans (by rw [hA]; exact hAQ)

variable [IsMulCommutative ↥(conjClosure S.V3 H)] {C : S.Conf H}
  {B : Subgroup (MulAut (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))))}
  {K : Subgroup G}

omit hab in

theorem KData.mem_QH_of_T_F4 (hhat : ¬ IsHatA6 L)
    (hNU : ¬ LieModel G .PSU 4 3 1) (hLem : Lem1374One_F4)
    (hab : IsElemAbelian 2 (conjClosure S.V3 H)) (hK : C.KData B K) {t : G} (ht : t ∈ T)
    (hcomm : ∀ k ∈ K, t * k * t⁻¹ * k⁻¹ ∈ pCoreOf 2 H) : t ∈ pCoreOf 2 H := by
  have hKH : K ≤ H := le_of_mem_cComp hK.2.2.1
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have htH : t ∈ H := hTH ht
  have hHU := le_normalizer_conjClosure S.V3 H
  have hHC := S.le_normalizer_U0 (H := H)
  have hone : ∀ y : ↥H, A6Mod.secAct hHU hHC y = 1 ↔ (y : G) ∈ pCoreOf 2 H := fun y =>
    (A6Mod.secAct_eq_one_iff hHU hHC y).trans
      (S.mem_QH_iff_plus_F4 hNS h13315 h1356two hH hab hNU hhat hLem y.2).symm
  set ψ := A6Mod.secAct hHU hHC ⟨t, htH⟩ with hψ
  have hψT : ψ ∈ autSec (autOn T (conjClosure S.V3 H)) ⊤
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) :=
    (A6Mod.mem_autSec_iff hHU hHC hTH).2 ⟨⟨t, htH⟩, ht, rfl⟩
  have hψC : ψ ∈ Subgroup.centralizer ((autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) :
        Subgroup _) : Set _) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨k, hkK, rfl⟩ := (A6Mod.mem_autSec_iff hHU hHC hKH).1 hx
    have hq : A6Mod.secAct hHU hHC (⟨t, htH⟩ * k * ⟨t, htH⟩⁻¹ * k⁻¹) = 1 :=
      (hone _).2 (hcomm k hkK)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hψ] at hq
    calc A6Mod.secAct hHU hHC k * ψ =
        (ψ * A6Mod.secAct hHU hHC k * ψ⁻¹ * (A6Mod.secAct hHU hHC k)⁻¹)⁻¹ * ψ *
          A6Mod.secAct hHU hHC k := by group
      _ = ψ * A6Mod.secAct hHU hHC k := by rw [hq, inv_one, one_mul]
  have h1 : ψ ∈ (⊥ : Subgroup _) := by
    rw [← hK.T_plus_inf_centralizer_eq_bot hab hTH]
    exact ⟨hψT, hψC⟩
  exact (hone ⟨t, htH⟩).1 (Subgroup.mem_bot.1 h1)

end Conf

end KTilde

end Setting4

theorem lem13719L1K_of_F4 (h13315 : Stmt13_3_15_F4)
    (h1356two : Input1356Two_F4) (h13314 : Stmt13_3_14_F4) (hLem : Lem1374One_F4) (h1222 : Stmt12_2_2_F4)
    (h323 : Stmt3_2_3) (h1227 : U3.Stmt13_2_2_7_F4) (h1337 : Stmt13_3_7_F4) : Lem13719L1K_F4 := by
  intro G _ _ T L V S hNS hNU hhat H hH hab hna _ C B K hK hL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hL1K
  have hKH : K ≤ H := le_of_mem_cComp hK.2.2.1
  have hHK := hK.le_normalizer_F4 hNS h13315 h1356two hH hab hhat hNU hLem
  have hL1H : S.L1 ≤ H := le_sup_left.trans hH.1.1
  obtain ⟨α, hαs, hαk⟩ := Setting4.Conf.exists_alpha_L24_F4 hNS h13315 h1356two hH hKH hL
  have hfT : ∀ t ∈ T, (∀ k ∈ K, t * k * t⁻¹ * k⁻¹ ∈ pCoreOf 2 H) → t ∈ pCoreOf 2 H :=
    fun t ht hcomm => hK.mem_QH_of_T_F4 hNS h13315 h1356two hH hhat hNU hLem hab ht hcomm
  obtain ⟨d, hdK, hd3, hdP, hdN⟩ := S.exists_d_normalizer_R1 hhat hH hKH hHK hαs hαk hfT

  have hRM : Subgroup.normalizer (pCoreOf 2 (S.L1 ⊔ T) : Set G) ≤
      Subgroup.normalizer (L : Set G) := by
    rcases h1227 G T L V S.L1 S.h13 S.irr S.zv (fun h => absurd h hhat) (fun _ => rfl) S.a6
      with h | h
    · exact S.normalizer_R1_le_M h
    · exact absurd h (Setting4.Conf.not_isA6Block_F4 hNS h13315 h1356two hH C hhat hna h13314
        h1222 h323 hab)
  have hdH : d ∈ H := hKH hdK

  have hV1V : fsuV1 T V ≤ V := S.V1_le_V2.trans (S.V2_le_V3.trans S.V3_le_V)
  have hV1ne : fsuV1 T V ≠ ⊥ := by
    intro h
    have h2 := S.card_V1
    rw [h, Subgroup.card_bot] at h2
    norm_num at h2
  have hHV1 : H ≤ Subgroup.normalizer (fsuV1 T V : Set G) := hH.2.1.trans S.G1_le_normalizer_V1
  have h126 := (stmt12_2_6_of_F4 h1222 h323 G T L V (S14.hyp1223 S)).2 (fsuV1 T V) H hV1ne hV1V
    hHV1
  have hdV : d ∈ Subgroup.normalizer (V : Set G) := by
    have h1 : d ∈ H ⊓ Subgroup.normalizer (L : Set G) := ⟨hdH, hRM hdN⟩
    rw [h126] at h1
    exact h1.2
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

  set N : Subgroup G := K ⊔ pCoreOf 2 H with hN
  have hKP : K ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    hKH.trans (le_normalizer_pCoreOf 2 H)
  have hON : pCoreOf 2 S.L1 ≤ N := S.pCoreOf_L1_le_KP hH hKH hHK hαs hαk hfT
  have hcN : (S.cL1 hhat : G) ∉ N := fun h => hL1K (S.L1_le_K_of_mem hhat hH hKH hHK hON h)
  have hNH : N ≤ H := sup_le hKH (pCoreOf_le 2 H)
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := by
    intro h hh
    refine A6L19.mem_normalizer_of_conj fun y hy => ?_
    obtain ⟨k, hk, p, hp, rfl⟩ := (A6L19.mem_sup_iff hKP).1 hy
    have e : h * (k * p) * h⁻¹ = (h * k * h⁻¹) * (h * p * h⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _
      (Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hHK hh) k).mp hk))
      (Subgroup.mem_sup_right
        ((Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hh) p).mp hp))
  have hNn : (N.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mpr hHN
  set π := QuotientGroup.mk' (N.subgroupOf H) with hπ
  have hπ1 : ∀ w : ↥H, π w = 1 ↔ (w : G) ∈ N := fun w => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  set c₀ : ↥H := ⟨(S.cL1 hhat : G), hL1H (S.cL1_mem hhat)⟩ with hc₀
  set x' : ↥H := ⟨x, hL1H hxL⟩ with hx'
  set d' : ↥H := ⟨d, hdH⟩ with hd'
  have hπd : π d' = 1 := (hπ1 d').2 (Subgroup.mem_sup_left hdK)
  have hπc3 : π c₀ ^ 3 = 1 := by
    have h1 : c₀ ^ 3 = 1 := Subtype.ext (by simpa using S.cL1_cube hhat)
    rw [← map_pow, h1, map_one]
  have hπc1 : π c₀ ≠ 1 := fun h => hcN ((hπ1 c₀).1 h)
  have hy' : (x'⁻¹ * d') ^ m = 1 := by
    have h1 : (⟨_, hy⟩ : ↥(Subgroup.centralizer (V : Set G))) ^ m = 1 := pow_orderOf_eq_one _
    have h2 := congrArg Subtype.val h1
    rw [SubgroupClass.coe_pow] at h2
    apply Subtype.ext
    rw [SubgroupClass.coe_pow]
    exact h2
  have hπy : π (x'⁻¹ * d') ^ m = 1 := by rw [← map_pow, hy', map_one]
  have hπx : π x' = (π (x'⁻¹ * d'))⁻¹ := by rw [map_mul, map_inv, hπd, mul_one, inv_inv]

  have hxO : (x : G) ∈ pCoreOf 2 S.L1 := by
    rcases S.L1_decomp hhat hxL with h | h | h
    · exact h
    · exfalso
      have h1 : π (c₀ * c₀ * x') = 1 := (hπ1 _).2 (hON h)
      rw [map_mul, map_mul, hπx] at h1
      have h2 : π c₀ * π c₀ = π (x'⁻¹ * d') := by
        calc π c₀ * π c₀ = π c₀ * π c₀ * (π (x'⁻¹ * d'))⁻¹ * π (x'⁻¹ * d') := by group
          _ = π (x'⁻¹ * d') := by rw [h1, one_mul]
      refine hπc1 (A6L19.eq_one_of_pow_three hπc3 (m := 2 * m) (fun h => hm3
        (((Nat.Prime.dvd_mul Nat.prime_three).1 h).resolve_left (by norm_num))) ?_)
      rw [pow_mul, sq, h2, hπy]
    · exfalso
      have h1 : π (c₀ * x') = 1 := (hπ1 _).2 (hON h)
      rw [map_mul, hπx] at h1
      have h2 : π c₀ = π (x'⁻¹ * d') := by
        calc π c₀ = π c₀ * (π (x'⁻¹ * d'))⁻¹ * π (x'⁻¹ * d') := by group
          _ = π (x'⁻¹ * d') := by rw [h1, one_mul]
      exact hπc1 (A6L19.eq_one_of_pow_three hπc3 hm3 (by rw [h2, hπy]))

  have hK4 : S.frame.ρ dn ∈ K4L := by
    rw [← hρx]
    exact S.rho_O2L1_mem_K4 hxO x.2
  have hdC : d ∈ Subgroup.centralizer (V : Set G) :=
    (S.rho_eq_one_iff dn).1 (A6L19.K4L_cube _ hK4 hρ3)
  have hd1 : d ≠ 1 := fun h => hdP (h ▸ (pCoreOf 2 H).one_mem)
  have hord : orderOf (⟨d, hdC⟩ : ↥(Subgroup.centralizer (V : Set G))) = 3 :=
    orderOf_eq_prime (Subtype.ext (by simpa using hd3)) (fun h => hd1 (congrArg Subtype.val h))
  exact h3V (hord ▸ orderOf_dvd_natCard _)

end CFSG.Quasithin.H13.A6
