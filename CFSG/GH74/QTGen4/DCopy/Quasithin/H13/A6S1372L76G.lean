module

public import CFSG.Quasithin.H13.A6S1372L76G
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372L76B

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

structure Ctx76_F4 (H K : Subgroup G) [IsMulCommutative ↥(conjClosure S.V3 H)] (D : FFModel) where

  hNS : ¬ LieModel G .PSp 3 2 1

  h13315 : Stmt13_3_15_F4

  h1356two : Input1356Two_F4

  hH : H ∈ S.Hz

  hab : IsElemAbelian 2 (conjClosure S.V3 H)

  hK : K ∈ cComp H

  hL1K : S.L1 ≤ K

  hHK : H ≤ Subgroup.normalizer (K : Set G)

  hUK : ⁅conjClosure S.V3 H, K⁆ = conjClosure S.V3 H

  π : D.Gam →* ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
    ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))

  β : ↥(commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
    ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) →* ↥D.sec ⧸ D.ker.subgroupOf D.sec

  hR : CFSG.Quasithin.H.Mathieu.RealizesBy D
    (autSec (autOn K (conjClosure S.V3 H)) ⊤ ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
    (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
    (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
      commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) π β

  hπ : Function.Injective π

namespace Ctx76_F4
open CFSG.Quasithin.H13.A6.Setting4.Ctx76_F4

variable {S} {H K : Subgroup G} [IsMulCommutative ↥(conjClosure S.V3 H)] {D : FFModel}
  (C : S.Ctx76_F4 H K D)
include C

theorem hKH_F4 : K ≤ H := le_of_mem_cComp C.hK

theorem hTH_F4 : T ≤ H := le_sup_right.trans C.hH.1.1

theorem hL1H_F4 : S.L1 ≤ H := C.hL1K.trans C.hKH_F4

theorem top_F4 : commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
    ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) = ⊤ :=
  Conf.commV_tilde_eq_top C.hH C.hKH_F4 C.hUK

@[expose] noncomputable def ι_F4 : ↥(conjClosure S.V3 H) →* ↥(commV (autSec
    (autOn K (conjClosure S.V3 H)) ⊤ ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) :=
  (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))).codRestrict _
    fun _ => (Subgroup.eq_top_iff' _).1 C.top_F4 _

theorem ι_coe_F4 (u : ↥(conjClosure S.V3 H)) :
    ((C.ι_F4 u : ↥(commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))) :
        Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) =
      InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) u := rfl

@[expose] noncomputable def βU_F4 : ↥(conjClosure S.V3 H) →* ↥D.sec ⧸ D.ker.subgroupOf D.sec :=
  C.β.comp C.ι_F4

@[expose] noncomputable def κ_F4 : ↥K →* ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
    ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) :=
  ((A6Mod.secAct (le_normalizer_conjClosure S.V3 H) (S.le_normalizer_UV1 C.hH)).comp
    (Subgroup.inclusion C.hKH_F4)).codRestrict _
    fun k => (A6Mod.mem_autSec_iff (le_normalizer_conjClosure S.V3 H)
      (S.le_normalizer_UV1 C.hH) C.hKH_F4).2 ⟨_, k.2, rfl⟩

theorem κ_coe_F4 (k : ↥K) : ((C.κ_F4 k : ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
    ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) : MulAut _) =
      A6Mod.secAct (le_normalizer_conjClosure S.V3 H) (S.le_normalizer_UV1 C.hH)
        ⟨k, C.hKH_F4 k.2⟩ := rfl

theorem κ_surj_F4 : Function.Surjective C.κ_F4 := by
  intro x
  obtain ⟨h, hhK, hx⟩ := (A6Mod.mem_autSec_iff (le_normalizer_conjClosure S.V3 H)
    (S.le_normalizer_UV1 C.hH) C.hKH_F4).1 x.2
  exact ⟨⟨h, hhK⟩, Subtype.ext hx⟩

@[expose] noncomputable def eπ_F4 : D.Gam ≃* ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
    ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) :=
  MulEquiv.ofBijective C.π ⟨C.hπ, C.hR.1⟩

@[expose] noncomputable def α_F4 : ↥K →* D.Gam := C.eπ_F4.symm.toMonoidHom.comp C.κ_F4

theorem π_α_F4 (k : ↥K) : C.π (C.α_F4 k) = C.κ_F4 k := C.eπ_F4.apply_symm_apply (C.κ_F4 k)

theorem α_surj_F4 : Function.Surjective C.α_F4 := C.eπ_F4.symm.surjective.comp C.κ_surj_F4

theorem κ_ι_F4 (k : ↥K) (u : ↥(conjClosure S.V3 H))
    (hku : (k : G) * u * (k : G)⁻¹ ∈ conjClosure S.V3 H) :
    ((C.κ_F4 k : ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) : MulAut _) (C.ι_F4 u).1 =
      (C.ι_F4 ⟨_, hku⟩).1 := by
  rw [C.κ_coe_F4, C.ι_coe_F4, C.ι_coe_F4, A6Mod.secAct_secMk]
  rfl

theorem βU_equiv_F4 (k : ↥K) (u : ↥(conjClosure S.V3 H))
    (hku : (k : G) * u * (k : G)⁻¹ ∈ conjClosure S.V3 H) {m : D.Amb} (hm : m ∈ D.sec)
    (h : C.βU_F4 u = QuotientGroup.mk ⟨m, hm⟩) :
    C.βU_F4 ⟨_, hku⟩ = QuotientGroup.mk ⟨D.act (C.α_F4 k) m, C.hR.2.2.2.2.2.1 _ _ hm⟩ := by
  obtain ⟨-, -, -, -, -, hsec, -, -, -, hβe⟩ := C.hR
  have hu' : ((C.π (C.α_F4 k) : ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) : MulAut _)
      (C.ι_F4 u).1 ∈ commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) :=
    (Subgroup.eq_top_iff' _).1 C.top_F4 _
  have h1 := hβe (C.α_F4 k) (C.ι_F4 u) ⟨m, hm⟩ hu' (hsec _ _ hm) h
  have h2 : (⟨((C.π (C.α_F4 k) : ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) : MulAut _) (C.ι_F4 u).1, hu'⟩ :
        ↥(commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))) = C.ι_F4 ⟨_, hku⟩ := by
    apply Subtype.ext
    show ((C.π (C.α_F4 k) : ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) : MulAut _) (C.ι_F4 u).1 = (C.ι_F4 ⟨_, hku⟩).1
    rw [C.π_α_F4]
    exact C.κ_ι_F4 k u hku
  rw [h2] at h1
  exact h1

theorem βU_eq_one_iff_F4 (u : ↥(conjClosure S.V3 H)) :
    C.βU_F4 u = 1 ↔ ∀ k ∈ K, k * (u : G) * k⁻¹ * (u : G)⁻¹ ∈ fsuV1 T V := by
  have hHU := le_normalizer_conjClosure S.V3 H
  have hHV := S.le_normalizer_UV1 C.hH
  obtain ⟨-, -, -, -, -, -, -, -, hβk, -⟩ := C.hR
  rw [βU_F4, MonoidHom.comp_apply, hβk]
  constructor
  · rintro ⟨hfix, -⟩ k hk
    have h1 : A6Mod.secAct hHU hHV ⟨k, C.hKH_F4 hk⟩
        (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) u) =
        InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) u :=
      hfix _ ((A6Mod.mem_autSec_iff hHU hHV C.hKH_F4).2 ⟨⟨k, C.hKH_F4 hk⟩, hk, rfl⟩)
    have h2 : A6Mod.secAct hHU hHV ⟨k, C.hKH_F4 hk⟩
        (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) u) *
        (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) u)⁻¹ = 1 := by
      rw [h1, mul_inv_cancel]
    rw [A6Mod.secAct_secMk, ← map_inv, ← map_mul, A6Mod.secMk_eq_one_iff] at h2
    simpa [Setup.rho_apply_coe] using h2
  · intro h
    refine ⟨fun x hx => ?_, (C.ι_F4 u).2⟩
    obtain ⟨⟨k, hkH⟩, hk, rfl⟩ := (A6Mod.mem_autSec_iff hHU hHV C.hKH_F4).1 hx
    show A6Mod.secAct hHU hHV ⟨k, hkH⟩
        (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) u) =
      InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) u
    rw [← mul_inv_eq_one, A6Mod.secAct_secMk, ← map_inv, ← map_mul, A6Mod.secMk_eq_one_iff]
    simpa [Setup.rho_apply_coe] using h k hk

theorem α_eq_one_iff_F4 (k : ↥K) :
    C.α_F4 k = 1 ↔ (k : G) ∈ pCoreOf 2 H := by
  rw [show C.α_F4 k = C.eπ_F4.symm (C.κ_F4 k) from rfl, MulEquiv.map_eq_one_iff,
    S.mem_QH_iff_tilde_F4 C.hNS C.h13315 C.h1356two C.hH (C.hKH_F4 k.2),
    ← A6Mod.secAct_eq_one_iff (le_normalizer_conjClosure S.V3 H) (S.le_normalizer_UV1 C.hH)
      ⟨(k : G), C.hKH_F4 k.2⟩, ← C.κ_coe_F4]
  exact Subtype.ext_iff

theorem not_three_dvd_ker_F4 : ¬ 3 ∣ Nat.card C.α_F4.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e : C.α_F4.ker = (pCoreOf 2 H).subgroupOf K := by
    ext k
    rw [MonoidHom.mem_ker, C.α_eq_one_iff_F4, Subgroup.mem_subgroupOf]
  rw [e]
  have h1 : Nat.card ((pCoreOf 2 H).subgroupOf K) = Nat.card (pCoreOf 2 H ⊓ K : Subgroup G) := by
    rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective K.subtype_injective]
  rw [h1]
  obtain ⟨j, hj⟩ := ((pCoreOf_isPGroup 2 H).to_le inf_le_left).exists_card_eq
  rw [hj]
  intro h
  have := Nat.prime_three.dvd_of_dvd_pow h
  omega

theorem not_e9_F4 (h13314 : Stmt13_3_14_F4) {m : D.Amb}
    (hm : m ∈ D.sec) (hxm : C.βU_F4 ⟨S.v2, S.v2_mem_UH H⟩ = QuotientGroup.mk ⟨m, hm⟩)
    {a b : D.Gam}
    (hE : A6L76B.E9Pair a b) (ha : D.act a m * m⁻¹ ∈ D.ker) (hb : D.act b m * m⁻¹ ∈ D.ker) :
    False :=
  not_e9_model_fix_V2_F4 C.hNS C.h13315 C.h1356two C.hH h13314 C.hab C.hKH_F4 C.hR C.hπ
    S.v2_mem_V2 S.v2_not_mem_V1 (C.ι_F4 ⟨S.v2, S.v2_mem_UH H⟩).2 hm hxm hE ha hb

end Ctx76_F4

end Setting4

end CFSG.Quasithin.H13.A6
