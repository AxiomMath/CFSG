module

public import CFSG.Quasithin.H13.A6S1372L76C
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372SixteenTilde

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} {S : Setting4 G T L V}

section KTilde

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4)
  {H : Subgroup G} (hH : H ∈ S.Hz) [IsMulCommutative ↥(conjClosure S.V3 H)]
include hNS h13315 h1356two hH

theorem keyDataG_of_realizesBy_F4 {K : Subgroup G} (hKH : K ≤ H)
    (hUK : ⁅conjClosure S.V3 H, K⁆ = conjClosure S.V3 H) {D : FFModel}
    {π : D.Gam →* ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))}
    {β : ↥(commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) →* ↥D.sec ⧸ D.ker.subgroupOf D.sec}
    (hR : CFSG.Quasithin.H.Mathieu.RealizesBy D
      (autSec (autOn K (conjClosure S.V3 H)) ⊤ ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
      (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
      (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
        commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) π β)
    (hπ : Function.Injective π) {W : Type} [CommGroup W] {act : D.Gam →* MulAut W}
    (e : ↥D.sec ⧸ D.ker.subgroupOf D.sec ≃* W)
    (he : ∀ (γ : D.Gam) (m : ↥D.sec) (hm : D.act γ m ∈ D.sec),
      e (QuotientGroup.mk ⟨D.act γ m, hm⟩) = act γ (e (QuotientGroup.mk m))) :
    Nonempty (S.KeyDataG H K D.Gam W act) := by
  have hHU := le_normalizer_conjClosure S.V3 H
  have hHV := S.le_normalizer_UV1 hH
  let Kt := autSec (autOn K (conjClosure S.V3 H)) ⊤
    ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))
  have htop : commV Kt = ⊤ := Conf.commV_tilde_eq_top hH hKH hUK
  let eπ : D.Gam ≃* ↥Kt := MulEquiv.ofBijective π ⟨hπ, hR.1⟩
  obtain ⟨-, -, -, -, -, hsec, -, hβs, hβk, hβe⟩ := id hR

  let κ : ↥K →* ↥Kt := ((A6Mod.secAct hHU hHV).comp (Subgroup.inclusion hKH)).codRestrict Kt
    fun k => (A6Mod.mem_autSec_iff hHU hHV hKH).2 ⟨_, k.2, rfl⟩
  have hκ : ∀ k : ↥K, ((κ k : ↥Kt) : MulAut _) = A6Mod.secAct hHU hHV ⟨k, hKH k.2⟩ :=
    fun _ => rfl
  have hκs : Function.Surjective κ := by
    intro x
    obtain ⟨h, hhK, hx⟩ := (A6Mod.mem_autSec_iff hHU hHV hKH).1 x.2
    exact ⟨⟨h, hhK⟩, Subtype.ext hx⟩
  let α : ↥K →* D.Gam := eπ.symm.toMonoidHom.comp κ
  have hπα : ∀ k : ↥K, π (α k) = κ k := fun k => eπ.apply_symm_apply (κ k)
  let ι : ↥(conjClosure S.V3 H) →* ↥(commV Kt) :=
    (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))).codRestrict (commV Kt)
      fun u => (Subgroup.eq_top_iff' _).1 htop _
  let β₀ : ↥(conjClosure S.V3 H) →* W := e.toMonoidHom.comp (β.comp ι)
  have hβ₀ : ∀ u, β₀ u = e (β (ι u)) := fun _ => rfl
  have hker : ∀ u : ↥(conjClosure S.V3 H),
      β₀ u = 1 ↔ ∀ k ∈ K, k * (u : G) * k⁻¹ * (u : G)⁻¹ ∈ fsuV1 T V := by
    intro u
    rw [hβ₀, MulEquiv.map_eq_one_iff, hβk]
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
      β₀ ⟨_, hku⟩ = act (α k) (β₀ u) := by
    intro k u hku
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β (ι u))
    have hact : D.act (α k) m.1 ∈ D.sec := hsec _ _ m.2
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
    rw [hβ₀, hβ₀, h1, ← hm, he]
  refine ⟨⟨hKH, α, β₀, eπ.symm.surjective.comp hκs, fun k => ?_, ?_, hker, hequiv, ?_⟩⟩
  · rw [show α k = eπ.symm (κ k) from rfl, MulEquiv.map_eq_one_iff,
      S.mem_QH_iff_tilde_F4 hNS h13315 h1356two hH (hKH k.2)]
    exact Subtype.ext_iff.trans (A6Mod.secAct_eq_one_iff hHU hHV ⟨k, hKH k.2⟩)
  · intro w
    obtain ⟨t, rfl⟩ := e.surjective w
    obtain ⟨x, rfl⟩ := hβs t
    obtain ⟨u, hu⟩ := InternalSec.secMk_surjective _ (Subtype.val x)
    exact ⟨u, by rw [hβ₀]; congr 2; exact Subtype.ext hu⟩
  · rw [hUK]
    exact sup_eq_left.2 S.V1_le_UH

theorem sup_eq_of_realizes6_F4 {K : Subgroup G} (hKH : K ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (hUK : ⁅conjClosure S.V3 H, K⁆ = conjClosure S.V3 H)
    {π : (FFModel.altDn 6).Gam →* ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))}
    {β : ↥(commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) →*
        ↥(FFModel.altDn 6).sec ⧸ (FFModel.altDn 6).ker.subgroupOf (FFModel.altDn 6).sec}
    (hR : CFSG.Quasithin.H.Mathieu.RealizesBy (FFModel.altDn 6)
      (autSec (autOn K (conjClosure S.V3 H)) ⊤ ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
      (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
      (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
        commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) π β)
    (hπ : Function.Injective π) : K ⊔ T = H := by
  have he : ∀ (γ : (FFModel.altDn 6).Gam) (m : ↥(FFModel.altDn 6).sec)
      (hm : (FFModel.altDn 6).act γ m ∈ (FFModel.altDn 6).sec),
      modW4Equiv (QuotientGroup.mk ⟨(FFModel.altDn 6).act γ m, hm⟩) =
        A6L76C.act6 γ (modW4Equiv (QuotientGroup.mk m)) := by
    intro γ m hm
    rw [modW4Equiv_mk, modW4Equiv_mk]
    apply Subtype.ext
    show nrm (G6.permAct 6 _ (show P6 from m.1)) = nrm (G6.permAct 6 _ (nrm (show P6 from m.1)))
    rw [nrm_permAct_nrm]
    rfl
  have : Finite (FFModel.altDn 6).Gam := inferInstanceAs (Finite ↥(alternatingGroup (Fin 6)))
  obtain ⟨D⟩ := keyDataG_of_realizesBy_F4 hNS h13315 h1356two hH hKH hUK hR hπ modW4Equiv he
  exact D.sup_eq A6L76C.endTriv_W4 A6L76C.card_mulAut_alt6 hH
    (S.hypF91_F4 hNS h13315 h1356two hH) hHK

theorem sup_eq_of_realizes7_F4 {K : Subgroup G} (hKH : K ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (hUK : ⁅conjClosure S.V3 H, K⁆ = conjClosure S.V3 H)
    {π : (FFModel.altDn 7).Gam →* ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))}
    {β : ↥(commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) →*
        ↥(FFModel.altDn 7).sec ⧸ (FFModel.altDn 7).ker.subgroupOf (FFModel.altDn 7).sec}
    (hR : CFSG.Quasithin.H.Mathieu.RealizesBy (FFModel.altDn 7)
      (autSec (autOn K (conjClosure S.V3 H)) ⊤ ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
      (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
      (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
        commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) π β)
    (hπ : Function.Injective π) : K ⊔ T = H := by
  have he : ∀ (γ : (FFModel.altDn 7).Gam) (m : ↥(FFModel.altDn 7).sec)
      (hm : (FFModel.altDn 7).act γ m ∈ (FFModel.altDn 7).sec),
      A6L76C.mod7Equiv (QuotientGroup.mk ⟨(FFModel.altDn 7).act γ m, hm⟩) =
        A6L76C.act7 γ (A6L76C.mod7Equiv (QuotientGroup.mk m)) := by
    intro γ m hm
    rw [A6L76C.mod7Equiv_mk, A6L76C.mod7Equiv_mk]
    rfl
  have : Finite (FFModel.altDn 7).Gam := inferInstanceAs (Finite ↥(alternatingGroup (Fin 7)))
  obtain ⟨D⟩ := keyDataG_of_realizesBy_F4 hNS h13315 h1356two hH hKH hUK hR hπ A6L76C.mod7Equiv he
  exact D.sup_eq A6L76C.endTriv_core7 A6L76C.card_mulAut_alt7 hH
    (S.hypF91_F4 hNS h13315 h1356two hH) hHK

end KTilde

end Setting4

end CFSG.Quasithin.H13.A6
