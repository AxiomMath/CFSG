module

public import CFSG.Quasithin.H13.A6S1372KeyData
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372EighteenB

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative commutatorElement

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} {S : Setting4 G T L V}

section KTilde

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4)
  {H : Subgroup G} (hH : H ∈ S.Hz) (hab : IsElemAbelian 2 (conjClosure S.V3 H))
include hNS h13315 h1356two hH hab

namespace Conf

variable [IsMulCommutative ↥(conjClosure S.V3 H)] {C : S.Conf H}
  {B : Subgroup (MulAut (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))))}
  {K : Subgroup G}

omit hab in

theorem KData.key_data_F4 (hhat : ¬ IsHatA6 L)
    (hNU : ¬ LieModel G .PSU 4 3 1) (hna : ¬ IsElemAbelian 2 (conjClosure V H))
    (h13314 : Stmt13_3_14_F4) (hLem : Lem1374One_F4) (h1352 : Stmt13_5_2_F4) (h51 : AsB51)
    (hAlt : Lem1376AltNat_F4) (hab : IsElemAbelian 2 (conjClosure S.V3 H)) (hK : C.KData B K)
    (hL24 : ¬ BinaryNaturalSL (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
        (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
        (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
          commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) 2 2) :
    ∃ hL1K : S.L1 ≤ K,
      K ≤ Subgroup.centralizer ((conjClosure S.V3 H ⊓
        Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G) : Set G) ∧
      ⁅conjClosure S.V3 H, K⁆ ⊔ fsuV1 T V = conjClosure S.V3 H ∧
      ∃ (α : ↥K →* alternatingGroup (Fin 6)) (β : ↥(conjClosure S.V3 H) →* ↥W4),
        Function.Surjective α ∧ (∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H) ∧
        Function.Surjective β ∧
        (∀ u : ↥(conjClosure S.V3 H),
          β u = 1 ↔ ∀ k ∈ K, k * (u : G) * k⁻¹ * (u : G)⁻¹ ∈ fsuV1 T V) ∧
        (∀ (k : ↥K) (u : ↥(conjClosure S.V3 H))
          (hku : (k : G) * u * (k : G)⁻¹ ∈ conjClosure S.V3 H),
          β ⟨_, hku⟩ = act4 (α k : Perm (Fin 6)) (β u)) ∧
        ∀ c (hc : c ∈ S.L1), c ^ 3 = 1 → c ∉ pCoreOf 2 S.L1 →
          ∀ w : ↥W4, act4 (α ⟨c, hL1K hc⟩ : Perm (Fin 6)) w = w → w = 1 := by
  have hKH : K ≤ H := le_of_mem_cComp hK.2.2.1
  have hHU := le_normalizer_conjClosure S.V3 H
  have hHV := S.le_normalizer_UV1 hH
  rcases hK.lem13718_F4 hNS h13315 h1356two hH hhat hNU hna h13314 hLem h1352 h51 hAlt hab with
    hL | ⟨halt, hUK, hL1K, -, hfpf⟩
  · exact absurd hL hL24
  set Kt := autSec (autOn K (conjClosure S.V3 H)) ⊤
    ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) with hKt
  have htop : commV Kt = ⊤ := commV_tilde_eq_top hH hKH hUK
  obtain ⟨π, hπ⟩ := halt
  have hπinj := G64.RealizesVia.injective_of_faithful' (G64.altDn_faithful (by norm_num)) hπ
  let e : ↥(alternatingGroup (Fin 6)) ≃* ↥Kt := MulEquiv.ofBijective π ⟨hπinj, hπ.1⟩
  obtain ⟨-, -, -, -, -, -, -, β', hβs, hβk, hβe⟩ := id hπ

  let κ : ↥K →* ↥Kt := ((A6Mod.secAct hHU hHV).comp (Subgroup.inclusion hKH)).codRestrict Kt
    fun k => (A6Mod.mem_autSec_iff hHU hHV hKH).2 ⟨_, k.2, rfl⟩
  have hκ : ∀ k : ↥K, ((κ k : ↥Kt) : MulAut _) = A6Mod.secAct hHU hHV ⟨k, hKH k.2⟩ :=
    fun _ => rfl
  have hκs : Function.Surjective κ := by
    intro x
    obtain ⟨h, hhK, hx⟩ := (A6Mod.mem_autSec_iff hHU hHV hKH).1 x.2
    exact ⟨⟨h, hhK⟩, Subtype.ext hx⟩
  let α : ↥K →* ↥(alternatingGroup (Fin 6)) := e.symm.toMonoidHom.comp κ
  have hπα : ∀ k : ↥K, π (α k) = κ k := fun k => e.apply_symm_apply (κ k)

  let ι : ↥(conjClosure S.V3 H) →* ↥(commV Kt) :=
    (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))).codRestrict (commV Kt)
      fun u => (Subgroup.eq_top_iff' _).1 htop _
  let β : ↥(conjClosure S.V3 H) →* ↥W4 := modW4Equiv.toMonoidHom.comp (β'.comp ι)
  have hβ : ∀ u, β u = modW4Equiv (β' (ι u)) := fun _ => rfl
  have hker : ∀ u : ↥(conjClosure S.V3 H),
      β u = 1 ↔ ∀ k ∈ K, k * (u : G) * k⁻¹ * (u : G)⁻¹ ∈ fsuV1 T V := by
    intro u
    rw [hβ, MulEquiv.map_eq_one_iff, hβk]
    constructor
    · rintro ⟨hfix, -⟩ k hk
      have h1 : A6Mod.secAct hHU hHV ⟨k, hKH hk⟩
          (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) u) =
          InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) u :=
        hfix _ ((A6Mod.mem_autSec_iff hHU hHV hKH).2 ⟨⟨k, hKH hk⟩, hk, rfl⟩)
      have h2 : A6Mod.secAct hHU hHV ⟨k, hKH hk⟩
          (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) u) *
          (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) u)⁻¹ = 1 := by
        rw [h1, mul_inv_cancel]
      rw [A6Mod.secAct_secMk, ← map_inv, ← map_mul, A6Mod.secMk_eq_one_iff] at h2
      simpa [Setup.rho_apply_coe] using h2
    · intro h
      refine ⟨fun x hx => ?_, (ι u).2⟩
      obtain ⟨⟨k, hkH⟩, hk, rfl⟩ := (A6Mod.mem_autSec_iff hHU hHV hKH).1 hx
      show A6Mod.secAct hHU hHV ⟨k, hkH⟩
          (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) u) =
        InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) u
      rw [← mul_inv_eq_one, A6Mod.secAct_secMk, ← map_inv, ← map_mul, A6Mod.secMk_eq_one_iff]
      simpa [Setup.rho_apply_coe] using h k hk
  have hequiv : ∀ (k : ↥K) (u : ↥(conjClosure S.V3 H))
      (hku : (k : G) * u * (k : G)⁻¹ ∈ conjClosure S.V3 H),
      β ⟨_, hku⟩ = act4 (α k : Perm (Fin 6)) (β u) := by
    intro k u hku
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β' (ι u))
    have hact : (FFModel.altDn 6).act (α k) m.1 ∈ (FFModel.altDn 6).sec :=
      G6.permAct_mem_coreMod _ m.2
    have hu' : ((π (α k) : ↥Kt) : MulAut _) ((ι u : ↥(commV Kt)) : Sec _ _) ∈ commV Kt :=
      (Subgroup.eq_top_iff' _).1 htop _
    have h1 := hβe (α k) (ι u) m hu' hact hm.symm
    have h2 : (⟨((π (α k) : ↥Kt) : MulAut _) ((ι u : ↥(commV Kt)) : Sec _ _), hu'⟩ :
        ↥(commV Kt)) = ι ⟨_, hku⟩ := by
      apply Subtype.ext
      show ((π (α k) : ↥Kt) : MulAut _) ((ι u : ↥(commV Kt)) : Sec _ _) =
        Subtype.val (ι ⟨_, hku⟩)
      rw [hπα, hκ]
      rfl
    rw [h2] at h1
    rw [hβ, hβ, h1, ← hm, modW4Equiv_mk, modW4Equiv_mk]
    apply Subtype.ext
    show nrm (G6.permAct 6 _ (show P6 from m.1)) = nrm (G6.permAct 6 _ (nrm (show P6 from m.1)))
    rw [nrm_permAct_nrm]
  refine ⟨hL1K, hK.le_centralizer_U0_F4 hNS h13315 h1356two hH hhat hNU hna h13314 hLem h1352 h51
    hab, ?_, α, β, e.symm.surjective.comp hκs, fun k => ?_, ?_, hker, hequiv, ?_⟩
  · rw [hUK]
    exact sup_eq_left.2 S.V1_le_UH
  ·
    rw [show α k = e.symm (κ k) from rfl, MulEquiv.map_eq_one_iff,
      S.mem_QH_iff_tilde_F4 hNS h13315 h1356two hH (hKH k.2)]
    exact Subtype.ext_iff.trans (A6Mod.secAct_eq_one_iff hHU hHV ⟨k, hKH k.2⟩)
  ·
    intro w
    obtain ⟨t, rfl⟩ := modW4Equiv.surjective w
    obtain ⟨x, rfl⟩ := hβs t
    obtain ⟨u, hu⟩ := InternalSec.secMk_surjective _ (Subtype.val x)
    exact ⟨u, by rw [hβ]; congr 2; exact Subtype.ext hu⟩
  ·
    intro c hc hc3 hcO w hw
    obtain ⟨u, rfl⟩ : ∃ u, β u = w := by
      obtain ⟨t, rfl⟩ := modW4Equiv.surjective w
      obtain ⟨x, rfl⟩ := hβs t
      obtain ⟨u, hu⟩ := InternalSec.secMk_surjective _ (Subtype.val x)
      exact ⟨u, by rw [hβ]; congr 2; exact Subtype.ext hu⟩
    have hcH : c ∈ H := hKH (hL1K hc)
    have hcu : c * (u : G) * c⁻¹ ∈ conjClosure S.V3 H :=
      (Subgroup.mem_normalizer_iff.mp (hHU hcH) _).mp u.2
    have h1 := hequiv ⟨c, hL1K hc⟩ u hcu
    rw [hw] at h1

    have h2 : β ⟨c * (u : G) * c⁻¹ * (u : G)⁻¹,
        (conjClosure S.V3 H).mul_mem hcu ((conjClosure S.V3 H).inv_mem u.2)⟩ = 1 := by
      have e2 : (⟨c * (u : G) * c⁻¹ * (u : G)⁻¹,
          (conjClosure S.V3 H).mul_mem hcu ((conjClosure S.V3 H).inv_mem u.2)⟩ :
          ↥(conjClosure S.V3 H)) = ⟨_, hcu⟩ * u⁻¹ := rfl
      rw [e2, map_mul, map_inv, h1, mul_inv_cancel]
    have h3 := (hker _).1 h2
    exact (hker u).2 (hfpf c hc hc3 hcO u u.2 h3)

end Conf

end KTilde

end Setting4

end CFSG.Quasithin.H13.A6
