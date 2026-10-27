module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf11H00
import CFSG.ClassicalInvolution.Q3.Q3T7P24EngH
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf9Ctx8Frame
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf9A05
public import CFSG.ClassicalInvolution.Q3.Q3T7P24H01

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem _root_.CFSG.ClassicalInvolution.Q8P.P24.exists_mem_USet_le [Finite G] (hΩ : HypOmegaMod Ω) {J : Subgroup G}
    (hJ : J ∈ Ω) : ∃ U ∈ USet Ω, U ≤ J := by
  obtain ⟨R, hR, hRJ, -⟩ := exists_mem_RSet_ge hJ (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup G))
    bot_le
  obtain ⟨U, hUR, hc, hcard⟩ := (hΩ.isQuatSub_of_mem_RSet hR).exists_cyclic_index_two
  exact ⟨U, mem_USet_of_natCard hJ hRJ hUR hc hcard, hUR.trans hRJ.1⟩

theorem _root_.CFSG.ClassicalInvolution.Q8P.P24.dstarAdj_of_le_normalizer [Finite G] (hΩ :
    HypOmegaMod Ω)
    {K J : Subgroup G} (hJ : J ∈ Ω) (hne : J ≠ K) (hN : J ≤ Subgroup.normalizer (K : Set G)) :
    dstarAdj Ω K J := by
  obtain ⟨U, hU, hUJ⟩ := CFSG.ClassicalInvolution.Q8P.P24.exists_mem_USet_le hΩ hJ
  exact ⟨hJ, Or.inl ⟨hJ, hne, U, hU, hUJ, fun u hu => hN (hUJ hu)⟩⟩
end Asc77

end

section

namespace Asc77.AscE186
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.AscE186
open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}
section Finite
variable [Finite G]

theorem _root_.CFSG.ClassicalInvolution.Q8P.P24.mem_dstarComp_of_twin (hΩ : HypOmegaMod Ω)
    {K L : Subgroup G} (hK : K ∈ Ω) (hL : L ∈ twinSet Ω K) : L ∈ dstarComp Ω K := by
  by_cases hLK : L = K
  · rw [hLK]
    exact Relation.ReflTransGen.refl
  obtain ⟨hLΩ, z, hzK, hzL⟩ := hL
  exact Relation.ReflTransGen.single
    (CFSG.ClassicalInvolution.Q8P.P24.dstarAdj_of_le_normalizer hΩ hLΩ hLK
        (hΩ.le_normalizer_of_twin hLΩ hK hLK hzL hzK))
end Finite
end Asc77.AscE186

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace S24B
open CFSG.ClassicalInvolution.Asc77.S24B
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W₁ : Subgroup G}

theorem exists_conj_of_frame (c : Q3.Q3CL.Thompson.Ctx Ω W₁)
    {e : ↥(muGroup Ω W₁) ≃* Equiv.Perm (Fin 4)}
    (he : ∀ x, x ∈ Thompson.muDelta Ω W₁ ↔ (e x).IsSwap) (F : T7E.Frame4 Ω W₁)
    (hab : T7D.imgQ F.ρ ≠ T7D.imgQ F.ρ')
    (hcomm : T7D.imgQ F.ρ * T7D.imgQ F.ρ' = T7D.imgQ F.ρ' * T7D.imgQ F.ρ)
    (hac : T7D.imgQ F.ρ * T7D.imgQ F.ρ₃ ≠ T7D.imgQ F.ρ₃ * T7D.imgQ F.ρ) {H₀ : Subgroup G}
    (hr : F.ρ.r ∈ H₀) (hr' : F.ρ'.r ∈ H₀) (hs : F.ρ₃.r ∈ H₀) (σ : Thompson.Rep Ω W₁) :
    ∃ h ∈ H₀, conjSub h F.ρ.K = σ.K := by
  let Y : Subgroup ↥(muGroup Ω W₁) :=
    { carrier := {y | ∃ h ∈ H₀ ⊓ Subgroup.normalizer (W₁ : Set G),
        (y : NQuot (W₁ ⊔ OCW W₁)) = Thompson.piG W₁ h}
      one_mem' := ⟨1, ⟨H₀.one_mem, Subgroup.one_mem _⟩,
        (Thompson.piG_of_mem_sup (Subgroup.one_mem _)).symm⟩
      mul_mem' := by
        rintro y₁ y₂ ⟨h₁, hh₁, e₁⟩ ⟨h₂, hh₂, e₂⟩
        refine ⟨h₁ * h₂, Subgroup.mul_mem _ hh₁ hh₂, ?_⟩
        rw [Subgroup.coe_mul, e₁, e₂, Thompson.piG_mul hh₁.2 hh₂.2]
      inv_mem' := by
        rintro y ⟨h, hh, e₁⟩
        refine ⟨h⁻¹, Subgroup.inv_mem _ hh, ?_⟩
        rw [Subgroup.coe_inv, e₁, Thompson.piG_inv hh.2] }
  have hgen : ∀ ρ : Thompson.Rep Ω W₁, ρ.r ∈ H₀ → T7D.imgQ ρ ∈ Y := fun ρ hρ =>
    ⟨ρ.r, ⟨hρ, ρ.r_mem_normalizer⟩, rfl⟩
  have hle : Subgroup.closure ({T7D.imgQ F.ρ, T7D.imgQ F.ρ', T7D.imgQ F.ρ₃} :
      Set ↥(muGroup Ω W₁)) ≤ Y := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h | h <;> rw [h]
    exacts [hgen _ hr, hgen _ hr', hgen _ hs]
  obtain ⟨y, hy⟩ := S4.exists_conj_of_mem he (T7D.imgQ_mem F.ρ) (T7D.imgQ_mem σ)
  have hyY : y ∈ Y :=
    hle (by rw [closure_frame_eq_top' he F hab hcomm hac]; exact Subgroup.mem_top y)
  obtain ⟨h, hh, hyh⟩ := hyY
  have himg : Thompson.piG W₁ h * F.ρ.img * (Thompson.piG W₁ h)⁻¹ = σ.img := by
    rw [← hyh]
    exact congrArg Subtype.val hy
  exact ⟨h, hh.1, c.K_eq_of_img_eq (T7D.conjRep c.hΩ hh.2 F.ρ) σ (by rw [T7D.conjRep_img, himg])⟩
end S24B
end Asc77

end

section

namespace Asc77.S24
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.S24
open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
    CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Asc77
    CFSG.ClassicalInvolution.Disconnected
open CFSG.Open (IsElemAbelian)
set_option linter.unusedSectionVars false
section Gamma
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem oddCore_le_gamma2_of {z : G} {B : Subgroup G} (hB : IsElemAbelian 2 B)
    (hB8 : Nat.card B = 8) (hBC : B ≤ Subgroup.centralizer ({z} : Set G)) :
    oddCoreOf (Subgroup.centralizer ({z} : Set G)) ≤
      gamma2 B (Subgroup.centralizer ({z} : Set G)) :=
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24.oddCore_le_gamma2_of hB hB8 hBC

end Gamma
end Asc77.S24

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace S24B
open CFSG.ClassicalInvolution.Asc77.S24B
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
namespace Ctx8F
open CFSG.ClassicalInvolution.Asc77.S24B.Ctx8
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Asc77.S24B.Ctx8F Ω K K' W S R R' z u)

theorem r_conj_j : C.D.F.ρ.r * C.D.F.j * C.D.F.ρ.r⁻¹ = C.D.F.j * z := by
  rw [← C.x₃_sq, ← conj_pow, C.D.r₃, C.D.comm13.symm.mul_pow, C.x₁_sq]

theorem t_conj_j : C.D.F.ρ'.r * C.D.F.j * C.D.F.ρ'.r⁻¹ = C.D.F.j * z := by
  rw [← C.x₃_sq, ← conj_pow, C.D.t₃, C.D.comm23.symm.mul_pow, C.x₂_sq]

theorem comm_jz : C.D.F.j * z = z * C.D.F.j :=
  Q3.Q3CL.Thompson.commutes_of_mem_WSet C.D.c.hΩ C.D.c.hW _
    (C.x₃_sq ▸ W.pow_mem C.D.x₃_mem 2) z C.hd.hzW

end Ctx8F

structure HCtx (Ω : Set (Subgroup G)) (K K' W : Subgroup G)
    (S : Sylow 2 G) (R R' : Subgroup G) (z u : G) : Type where
  C : Ctx8F Ω K K' W S R R' z u
  a : G
  T₃ : Subgroup G
  ha2 : a * a = 1
  ha1 : a ≠ 1
  haR : R ≤ Subgroup.centralizer ({a} : Set G)
  haR' : R' ≤ Subgroup.centralizer ({a} : Set G)
  hT : IsSylow2In T₃ C.D.F.ρ₃.K
  hTN : T₃ ≤ Subgroup.normalizer (W : Set G)
  hTa : T₃ ≤ Subgroup.centralizer ({a} : Set G)
namespace HCtx
open CFSG.ClassicalInvolution.Asc77.S24B.HCtx
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (H : Asc77.S24B.HCtx Ω K K' W S R R' z u)

private def toHFrame : CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.HFrame Ω K K' W S R R' z u where
  C := H.C.toFrame
  a := H.a
  T₃ := H.T₃
  ha2 := H.ha2
  ha1 := H.ha1
  haR := H.haR
  haR' := H.haR'
  hT := H.hT
  hTN := H.hTN
  hTa := H.hTa

theorem comm_R {x : G} (hx : x ∈ R) : x * H.a = H.a * x :=
  Subgroup.mem_centralizer_singleton_iff.mp (H.haR hx)

theorem comm_R' {x : G} (hx : x ∈ R') : x * H.a = H.a * x :=
  Subgroup.mem_centralizer_singleton_iff.mp (H.haR' hx)

theorem x₃_mem_T : H.C.D.x₃ ∈ H.T₃ := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.HFrame.x₃_mem_T (toHFrame H)

theorem comm_W {w : G} (hw : w ∈ W) : w * H.a = H.a * w := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.HFrame.comm_W (toHFrame H) hw

theorem comm_z : z * H.a = H.a * z := H.comm_W H.C.hd.hzW

theorem comm_j : H.C.D.F.j * H.a = H.a * H.C.D.F.j :=
  H.comm_W (H.C.x₃_sq ▸ W.pow_mem H.C.D.x₃_mem 2)

theorem comm_r : H.C.D.F.ρ.r * H.a = H.a * H.C.D.F.ρ.r := H.comm_R H.C.r_mem_R

theorem comm_t : H.C.D.F.ρ'.r * H.a = H.a * H.C.D.F.ρ'.r := H.comm_R' H.C.t_mem_R'

theorem a_ne_z : H.a ≠ z := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.HFrame.a_ne_z (toHFrame H)

theorem a_ne_j : H.a ≠ H.C.D.F.j := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.HFrame.a_ne_j (toHFrame H)

theorem a_not_mem : H.a ∉ Subgroup.closure ({H.C.D.F.j, z} : Set G) := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.HFrame.a_not_mem (toHFrame H)

@[expose] def B : Subgroup G := Subgroup.closure ({H.C.D.F.j * H.a, H.C.D.F.j, z} : Set G)

theorem B_isElemAbelian : IsElemAbelian 2 H.B :=
  S24.B_isElemAbelian_of H.C.hjJ.sq H.C.hzK.sq H.ha2 H.C.comm_jz H.comm_j H.comm_z

theorem B_card : Nat.card ↥H.B = 8 :=
  S24.B_natCard_of H.C.hjJ.sq H.C.hzK.sq H.ha2 H.C.hjJ.ne_one H.C.hzK.ne_one H.C.z_ne_j.symm
    H.C.comm_jz H.comm_j H.comm_z H.a_not_mem

theorem ja_mem_B : H.C.D.F.j * H.a ∈ H.B := Subgroup.subset_closure (by simp)

theorem j_mem_B : H.C.D.F.j ∈ H.B := Subgroup.subset_closure (by simp)

theorem z_mem_B : z ∈ H.B := Subgroup.subset_closure (by simp)

theorem a_mem_B : H.a ∈ H.B := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.HFrame.a_mem_B (toHFrame H)
end HCtx
end S24B
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance.Bootstrap
namespace S24B
open CFSG.ClassicalInvolution.Asc77.S24B
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem le_exactCore {K₀ M V : Subgroup G} (hst : AscStand Ω K₀)
    (h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M)) (hM : M ∈ Ω)
    (hV : IsSylow2In V M) {c : G} (hc2 : c * c = 1)
    (hVc : V ≤ Subgroup.centralizer ({c} : Set G)) : V ≤ CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinLayer.exactCore c M := by
  have hc : IsPGroup 2 (Subgroup.zpowers c) := isPGroup_zpowers_of_sq_eq_one hc2
  have hcM : c ∈ trivialOnQuot M :=
    (CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinLayer.mem_trivialOnQuot_iff_exists_sylow hst.hyp h2 hc hM).mpr ⟨V, hV, hVc⟩
  exact ((CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinLayer.isSylow2In_exactCore_iff hc hcM).mpr ⟨hV, hVc⟩).1

theorem mem_tq {K₀ M V : Subgroup G} (hst : AscStand Ω K₀)
    (h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M)) (hM : M ∈ Ω)
    (hV : IsSylow2In V M) {c : G} (hc2 : c * c = 1)
    (hVc : V ≤ Subgroup.centralizer ({c} : Set G)) : M ∈ CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinLayer.tqMembers Ω c :=
  (CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinLayer.mem_tqMembers_iff_exists_sylow hst.hyp h2 (isPGroup_zpowers_of_sq_eq_one hc2)).mpr
    ⟨hM, V, hV, hVc⟩
namespace HCtx
open CFSG.ClassicalInvolution.Asc77.S24B.HCtx
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (H : Asc77.S24B.HCtx Ω K K' W S R R' z u)

@[expose] def rt : G := H.C.D.F.ρ.r * H.C.D.F.ρ'.r

@[expose] def Js : Subgroup G := conjSub H.rt H.C.D.F.ρ₃.K

@[expose] def Ts : Subgroup G := conjSub H.rt H.T₃

theorem comm_rt : H.rt * H.a = H.a * H.rt := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.HFrame.comm_rt (toHFrame H)

theorem Js_mem : H.Js ∈ Ω :=
  H.C.hs.stand.hyp.conjInvariant _ _ H.C.D.F.ρ₃.hK

theorem hjJs : IsUniqueInvolution H.Js H.C.D.F.j := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.HFrame.hjJs (toHFrame H)

theorem Ts_syl : IsSylow2In H.Ts H.Js := H.hT.conj H.rt

theorem Ts_le : H.Ts ≤ Subgroup.centralizer ({H.a} : Set G) := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.HFrame.Ts_le (toHFrame H)

theorem zx₃_mem_Ts : z * H.C.D.x₃⁻¹ ∈ H.Ts := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.HFrame.zx₃_mem_Ts (toHFrame H)

theorem Js_ne : H.Js ≠ H.C.D.F.ρ₃.K := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.HFrame.Js_ne (toHFrame H)

theorem za_sq : z * H.a * (z * H.a) = 1 := mul_mul_self H.C.hzK.sq H.ha2 H.comm_z

theorem ja_sq : H.C.D.F.j * H.a * (H.C.D.F.j * H.a) = 1 :=
  mul_mul_self H.C.hjJ.sq H.ha2 H.comm_j

theorem R_le_za : R ≤ Subgroup.centralizer ({z * H.a} : Set G) :=
  le_centralizer_mul ((H.C.hd.hR.2.1).trans (le_centralizer_of_unique H.C.hzK)) H.haR

theorem R'_le_za : R' ≤ Subgroup.centralizer ({z * H.a} : Set G) :=
  le_centralizer_mul ((H.C.hd.hR'.2.1).trans (le_centralizer_of_unique H.C.hzK')) H.haR'

theorem T_le_ja : H.T₃ ≤ Subgroup.centralizer ({H.C.D.F.j * H.a} : Set G) :=
  le_centralizer_mul (H.hT.1.trans (le_centralizer_of_unique H.C.hjJ)) H.hTa

theorem Ts_le_ja : H.Ts ≤ Subgroup.centralizer ({H.C.D.F.j * H.a} : Set G) :=
  le_centralizer_mul (H.Ts_syl.1.trans (le_centralizer_of_unique H.hjJs)) H.Ts_le
include H in

theorem hR'syl : IsSylow2In R' K' :=
  T7C.isSylow2In_of_mem_RSet_of_le H.C.hs.stand.hyp H.C.hs.hK'.1 H.C.hd.hR'.1
    H.C.hd.hR'.2.1
include H in

theorem K_tq (c : G) (hc2 : c * c = 1) (hc : R ≤ Subgroup.centralizer ({c} : Set G)) :
    K ∈ CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinLayer.tqMembers Ω c := mem_tq H.C.hs.stand H.C.hyp.std.1.quot2 H.C.hs.stand.mem H.C.hRsyl hc2 hc
include H in

theorem K'_tq (c : G) (hc2 : c * c = 1) (hc : R' ≤ Subgroup.centralizer ({c} : Set G)) :
    K' ∈ CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinLayer.tqMembers Ω c := mem_tq H.C.hs.stand H.C.hyp.std.1.quot2 H.C.hs.hK'.1 H.hR'syl hc2 hc

theorem J_tq (c : G) (hc2 : c * c = 1) (hc : H.T₃ ≤ Subgroup.centralizer ({c} : Set G)) :
    H.C.D.F.ρ₃.K ∈ CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinLayer.tqMembers Ω c := mem_tq H.C.hs.stand H.C.hyp.std.1.quot2 H.C.D.F.ρ₃.hK H.hT hc2 hc

theorem Js_tq (c : G) (hc2 : c * c = 1) (hc : H.Ts ≤ Subgroup.centralizer ({c} : Set G)) :
    H.Js ∈ CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinLayer.tqMembers Ω c := mem_tq H.C.hs.stand H.C.hyp.std.1.quot2 H.Js_mem H.Ts_syl hc2 hc

theorem j_mem_exact (c : G) (hc2 : c * c = 1) (hc : R ≤ Subgroup.centralizer ({c} : Set G))
    (hc' : R' ≤ Subgroup.centralizer ({c} : Set G)) :
    H.C.D.F.j ∈ CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinLayer.exactCore c K ⊔ CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinLayer.exactCore c K' := by
  rw [H.C.j_eq]
  exact Subgroup.mul_mem _
    (Subgroup.mem_sup_left (le_exactCore H.C.hs.stand H.C.hyp.std.1.quot2 H.C.hs.stand.mem H.C.hRsyl hc2 hc
      (R.inv_mem H.C.x₁_mem_R)))
    (Subgroup.mem_sup_right (le_exactCore H.C.hs.stand H.C.hyp.std.1.quot2 H.C.hs.hK'.1 H.hR'syl hc2 hc'
      H.C.x₂_mem_R'))

theorem z_mem_exact :
    z ∈ CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinLayer.exactCore (H.C.D.F.j * H.a) H.C.D.F.ρ₃.K ⊔ CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinLayer.exactCore (H.C.D.F.j *
        H.a) H.Js := by
  have e : H.C.D.x₃ * (z * H.C.D.x₃⁻¹) = z := by
    have hc : z * H.C.D.x₃⁻¹ = H.C.D.x₃⁻¹ * z :=
      Q3.Q3CL.Thompson.commutes_of_mem_WSet H.C.D.c.hΩ H.C.D.c.hW _ H.C.hd.hzW _
        (W.inv_mem H.C.D.x₃_mem)
    rw [hc]; group
  have h := Subgroup.mul_mem (CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinLayer.exactCore (H.C.D.F.j * H.a) H.C.D.F.ρ₃.K ⊔
      CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinLayer.exactCore (H.C.D.F.j * H.a) H.Js)
    (Subgroup.mem_sup_left (le_exactCore H.C.hs.stand H.C.hyp.std.1.quot2 H.C.D.F.ρ₃.hK H.hT H.ja_sq H.T_le_ja
      H.x₃_mem_T))
    (Subgroup.mem_sup_right (le_exactCore H.C.hs.stand H.C.hyp.std.1.quot2 H.Js_mem H.Ts_syl H.ja_sq H.Ts_le_ja
      H.zx₃_mem_Ts))
  rwa [e] at h
end HCtx
end S24B
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance.Bootstrap
namespace S24B
open CFSG.ClassicalInvolution.Asc77.S24B
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
namespace HCtx
open CFSG.ClassicalInvolution.Asc77.S24B.HCtx
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (H : Asc77.S24B.HCtx Ω K K' W S R R' z u)

theorem x₃_mul : H.C.D.x₃ * (z * H.C.D.x₃⁻¹) = z := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.HFrame.x₃_mul (toHFrame H)

theorem B_le {L : Subgroup G} (h1 : H.C.D.F.j * H.a ∈ L) (h2 : H.C.D.F.j ∈ L) (h3 : z ∈ L) :
    H.B ≤ L := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.HFrame.B_le (toHFrame H) h1 h2 h3

theorem closure_le_B {x y w : G} (hx : x ∈ H.B) (hy : y ∈ H.B) (hw : w ∈ H.B) :
    Subgroup.closure ({x, y, w} : Set G) ≤ H.B := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.HFrame.closure_le_B (toHFrame H) hx hy hw

theorem B_eq_zja : H.B = Subgroup.closure ({z, H.C.D.F.j, H.a} : Set G) := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.HFrame.B_eq_zja (toHFrame H)

theorem B_eq_zjza : H.B = Subgroup.closure ({z, H.C.D.F.j, z * H.a} : Set G) := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.HFrame.B_eq_zjza (toHFrame H)

theorem B_eq_jzja : H.B = Subgroup.closure ({H.C.D.F.j, z, H.C.D.F.j * H.a} : Set G) :=
  le_antisymm (H.B_le mem_closure₃ mem_closure₁ mem_closure₂)
    (H.closure_le_B H.j_mem_B H.z_mem_B H.ja_mem_B)

theorem hyp51At_z [h51v : Fact P24.Hyp51VertexP] [CoreLike G] : Hyp51At H.B z := by
  have hxy : H.C.D.x₁⁻¹ * H.C.D.x₂ = H.C.D.F.j := H.C.j_eq.symm
  refine h51v.out H.C.hs.stand H.C.hyp.std.1.quot2 H.C.hs.stand.mem H.C.hs.hK'.1 H.C.hzK
    H.C.hzK' H.B_isElemAbelian H.z_mem_B (K.inv_mem H.C.x₁_mem_K) H.C.x₂_mem_K'
    (by rw [hxy]; exact H.j_mem_B) (by rw [hxy]; exact H.C.hjJ.ne_one)
    (by rw [hxy]; exact H.C.z_ne_j.symm) H.a_mem_B H.ha1 H.a_ne_z
    (H.K_tq H.a H.ha2 H.haR).2 H.a_mem_B H.ha1 H.a_ne_z (H.K'_tq H.a H.ha2 H.haR').2

theorem hyp51At_j [h51v : Fact P24.Hyp51VertexP] [CoreLike G] : Hyp51At H.B H.C.D.F.j
    := by
  refine h51v.out H.C.hs.stand H.C.hyp.std.1.quot2 H.C.D.F.ρ₃.hK H.Js_mem H.C.hjJ H.hjJs
    H.B_isElemAbelian H.j_mem_B H.C.x₃_mem_J (H.Ts_syl.1 H.zx₃_mem_Ts)
    (by rw [H.x₃_mul]; exact H.z_mem_B) (by rw [H.x₃_mul]; exact H.C.hzK.ne_one)
    (by rw [H.x₃_mul]; exact H.C.z_ne_j) H.a_mem_B H.ha1 H.a_ne_j
    (H.J_tq H.a H.ha2 H.hTa).2 H.a_mem_B H.ha1 H.a_ne_j (H.Js_tq H.a H.ha2 H.Ts_le).2

theorem hyp51At_a [h51i : Fact (P24.Hyp51TwinInnerAt Ω)] [CoreLike G] : Hyp51At H.B H.a :=
  h51i.out
    H.C.hs.stand H.C.hyp.std.1.ih H.C.hyp.std.1.quot2 H.C.hs.stand.mem H.C.hs.hK'.1 H.C.hs.hne H.C.hzK H.C.hzK'
    (H.K_tq H.a H.ha2 H.haR) (H.K'_tq H.a H.ha2 H.haR') H.B_isElemAbelian H.z_mem_B H.j_mem_B
    H.a_mem_B H.B_eq_zja H.ha1 H.a_ne_z.symm H.C.hjJ.ne_one H.C.z_ne_j.symm H.C.hjJ.sq
    (H.j_mem_exact H.a H.ha2 H.haR H.haR')

theorem za_ne_one : z * H.a ≠ 1 := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.HFrame.za_ne_one (toHFrame H)

theorem ja_ne_one : H.C.D.F.j * H.a ≠ 1 := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.HFrame.ja_ne_one (toHFrame H)

theorem hyp51At_za [h51i : Fact (P24.Hyp51TwinInnerAt Ω)] [CoreLike G] : Hyp51At H.B (z *
    H.a) :=
  h51i.out
    H.C.hs.stand H.C.hyp.std.1.ih H.C.hyp.std.1.quot2 H.C.hs.stand.mem H.C.hs.hK'.1 H.C.hs.hne H.C.hzK H.C.hzK'
    (H.K_tq (z * H.a) H.za_sq H.R_le_za) (H.K'_tq (z * H.a) H.za_sq H.R'_le_za)
    H.B_isElemAbelian H.z_mem_B H.j_mem_B (H.B.mul_mem H.z_mem_B H.a_mem_B) H.B_eq_zjza
    H.za_ne_one (fun h => H.ha1 (left_eq_mul.mp h)) H.C.hjJ.ne_one H.C.z_ne_j.symm H.C.hjJ.sq
    (H.j_mem_exact (z * H.a) H.za_sq H.R_le_za H.R'_le_za)

theorem hyp51At_ja [h51i : Fact (P24.Hyp51TwinInnerAt Ω)] [CoreLike G] : Hyp51At H.B
    (H.C.D.F.j * H.a) :=
  h51i.out
    H.C.hs.stand H.C.hyp.std.1.ih H.C.hyp.std.1.quot2 H.C.D.F.ρ₃.hK H.Js_mem H.Js_ne H.C.hjJ H.hjJs
    (H.J_tq _ H.ja_sq H.T_le_ja) (H.Js_tq _ H.ja_sq H.Ts_le_ja) H.B_isElemAbelian H.j_mem_B
    H.z_mem_B H.ja_mem_B H.B_eq_jzja H.ja_ne_one (fun h => H.ha1 (left_eq_mul.mp h))
    H.C.hzK.ne_one H.C.z_ne_j H.C.hzK.sq H.z_mem_exact

theorem r_mem_normalizer_B : H.C.D.F.ρ.r ∈ Subgroup.normalizer (H.B : Set G) := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24B.HFrame.r_mem_normalizer_B (toHFrame H)

theorem hyp51 [Fact P24.Hyp51VertexP] [Fact (P24.Hyp51TwinInnerAt Ω)] [CoreLike G]
    : Hyp51 H.B := by
  refine hyp51_of_orbitReps H.B_isElemAbelian H.B_card
    (R := {z, H.C.D.F.j, H.a, z * H.a, H.C.D.F.j * H.a}) ?_ ?_
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h | h | h | h <;> rw [h]
    exacts [H.hyp51At_z, H.hyp51At_j, H.hyp51At_a, H.hyp51At_za, H.hyp51At_ja]
  · intro c hc hc1
    have hrN := H.r_mem_normalizer_B
    have hrj := H.C.r_conj_j
    have hra : H.C.D.F.ρ.r * H.a * H.C.D.F.ρ.r⁻¹ = H.a := by rw [H.comm_r]; group
    rcases T7K.mem_cases_of_commuting_involutions H.C.hjJ.sq H.C.hzK.sq H.ha2 H.C.comm_jz
        H.comm_j H.comm_z hc with h | h | h | h | h | h | h | h
    · exact absurd h hc1
    · exact ⟨z, by simp, 1, Subgroup.one_mem _, by rw [h]; group⟩
    · exact ⟨H.C.D.F.j, by simp, 1, Subgroup.one_mem _, by rw [h]; group⟩
    · exact ⟨H.C.D.F.j, by simp, H.C.D.F.ρ.r, hrN, by rw [h, hrj]⟩
    · exact ⟨H.a, by simp, 1, Subgroup.one_mem _, by rw [h]; group⟩
    · exact ⟨z * H.a, by simp, 1, Subgroup.one_mem _, by rw [h]; group⟩
    · exact ⟨H.C.D.F.j * H.a, by simp, 1, Subgroup.one_mem _, by rw [h]; group⟩
    · refine ⟨H.C.D.F.j * H.a, by simp, H.C.D.F.ρ.r, hrN, ?_⟩
      have e : H.C.D.F.ρ.r * (H.C.D.F.j * H.a) * H.C.D.F.ρ.r⁻¹ =
          (H.C.D.F.ρ.r * H.C.D.F.j * H.C.D.F.ρ.r⁻¹) * (H.C.D.F.ρ.r * H.a * H.C.D.F.ρ.r⁻¹) := by
        group
      rw [h, e, hrj, hra]
end HCtx
end S24B
end Asc77

end

end CFSG.ClassicalInvolution.Q8P
