module

public import CFSG.ClassicalInvolution.Asc77.AscS24BH1
public import CFSG.ClassicalInvolution.Asc77.AscS24BCyc2
public import CFSG.ClassicalInvolution.Asc77.WP3LayerSec

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Balance.Bootstrap

namespace S24B

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem le_centralizer_mul {X : Subgroup G} {b c : G} (hb : X ≤ Subgroup.centralizer ({b} : Set G))
    (hc : X ≤ Subgroup.centralizer ({c} : Set G)) :
    X ≤ Subgroup.centralizer ({b * c} : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 : x * b = b * x := Subgroup.mem_centralizer_singleton_iff.mp (hb hx)
  have h2 : x * c = c * x := Subgroup.mem_centralizer_singleton_iff.mp (hc hx)
  calc x * (b * c) = (x * b) * c := by group
    _ = b * (x * c) := by rw [h1]; group
    _ = b * c * x := by rw [h2]; group

omit [Finite G] [Fact p.Prime] in
theorem mul_mul_self {b c : G} (hb : b * b = 1) (hc : c * c = 1) (hbc : b * c = c * b) :
    b * c * (b * c) = 1 := by
  calc b * c * (b * c) = b * (c * b) * c := by group
    _ = b * (b * c) * c := by rw [hbc]
    _ = (b * b) * (c * c) := by group
    _ = 1 := by rw [hb, hc]; group

omit [Finite G] in
theorem le_centralizer_of_unique {M : Subgroup G} {b : G} (hb : IsUniqueInvolution M b) :
    M ≤ Subgroup.centralizer ({b} : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (e189_commute_of_mem hb hx).symm


theorem le_exactCore {K₀ M V : Subgroup G} (hst : AscStand p f Ω K₀) (hM : M ∈ Ω)
    (hV : IsSylow2In V M) {c : G} (hc2 : c * c = 1)
    (hVc : V ≤ Subgroup.centralizer ({c} : Set G)) : V ≤ exactCore c M := by
  have hc : IsPGroup 2 (Subgroup.zpowers c) := isPGroup_zpowers_of_sq_eq_one hc2
  have hcM : c ∈ trivialOnQuot M :=
    (mem_trivialOnQuot_iff_exists_sylow hst.odd hst.five hst.hyp hc hM).mpr ⟨V, hV, hVc⟩
  exact ((isSylow2In_exactCore_iff hst.hyp hc hM hcM).mpr ⟨hV, hVc⟩).1

theorem mem_tq {K₀ M V : Subgroup G} (hst : AscStand p f Ω K₀) (hM : M ∈ Ω)
    (hV : IsSylow2In V M) {c : G} (hc2 : c * c = 1)
    (hVc : V ≤ Subgroup.centralizer ({c} : Set G)) : M ∈ tqMembers Ω c :=
  (mem_tqMembers_iff_exists_sylow hst.odd hst.five hst.hyp (isPGroup_zpowers_of_sq_eq_one hc2)).mpr
    ⟨hM, V, hV, hVc⟩

namespace HCtx

variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (H : HCtx p f Ω K K' W S R R' z u)

@[expose] def rt : G := H.C.D.F.ρ.r * H.C.D.F.ρ'.r

@[expose] def Js : Subgroup G := conjSub H.rt H.C.D.F.ρ₃.K

@[expose] def Ts : Subgroup G := conjSub H.rt H.T₃

theorem comm_rt : H.rt * H.a = H.a * H.rt := by
  unfold rt
  rw [mul_assoc, H.comm_t, ← mul_assoc, H.comm_r, mul_assoc]

theorem rt_conj_j : H.rt * H.C.D.F.j * H.rt⁻¹ = H.C.D.F.j := by
  have hrz : H.C.D.F.ρ.r * z * H.C.D.F.ρ.r⁻¹ = z := by
    rw [(e189_commute_of_mem H.C.hzK H.C.r_mem_K).symm]; group
  have hzz : z * z = 1 := H.C.hzK.sq
  calc H.rt * H.C.D.F.j * H.rt⁻¹
      = H.C.D.F.ρ.r * (H.C.D.F.ρ'.r * H.C.D.F.j * H.C.D.F.ρ'.r⁻¹) * H.C.D.F.ρ.r⁻¹ := by
        unfold rt; group
    _ = (H.C.D.F.ρ.r * H.C.D.F.j * H.C.D.F.ρ.r⁻¹) * (H.C.D.F.ρ.r * z * H.C.D.F.ρ.r⁻¹) := by
        rw [H.C.t_conj_j]; group
    _ = H.C.D.F.j := by rw [H.C.r_conj_j, hrz, mul_assoc, hzz, mul_one]

theorem rt_conj_x₃ : H.rt * H.C.D.x₃ * H.rt⁻¹ = z * H.C.D.x₃⁻¹ := by
  have hc : H.C.D.x₃ * H.C.D.x₁ = H.C.D.x₁ * H.C.D.x₃ := H.C.D.comm13.eq.symm
  have h4 : H.C.D.x₃ ^ 4 = 1 := by rw [← H.C.orderOf_x₃]; exact pow_orderOf_eq_one _
  have e1 : H.rt * H.C.D.x₃ * H.rt⁻¹ =
      (H.C.D.F.ρ.r * H.C.D.x₃ * H.C.D.F.ρ.r⁻¹) * (H.C.D.F.ρ.r * H.C.D.x₂ * H.C.D.F.ρ.r⁻¹) := by
    have e : H.rt * H.C.D.x₃ * H.rt⁻¹ =
        H.C.D.F.ρ.r * (H.C.D.F.ρ'.r * H.C.D.x₃ * H.C.D.F.ρ'.r⁻¹) * H.C.D.F.ρ.r⁻¹ := by
      unfold rt; group
    rw [e, H.C.D.t₃]
    group
  rw [e1, H.C.D.r₃, H.C.D.r₂, H.C.x₂_eq]
  calc H.C.D.x₃ * H.C.D.x₁ * (H.C.D.x₁ * H.C.D.x₃ ^ 2)
      = (H.C.D.x₃ * H.C.D.x₁) * H.C.D.x₁ * H.C.D.x₃ ^ 2 := by group
    _ = (H.C.D.x₁ * H.C.D.x₃) * H.C.D.x₁ * H.C.D.x₃ ^ 2 := by rw [hc]
    _ = H.C.D.x₁ * (H.C.D.x₃ * H.C.D.x₁) * H.C.D.x₃ ^ 2 := by group
    _ = H.C.D.x₁ * (H.C.D.x₁ * H.C.D.x₃) * H.C.D.x₃ ^ 2 := by rw [hc]
    _ = (H.C.D.x₁ * H.C.D.x₁) * (H.C.D.x₃ ^ 4 * H.C.D.x₃⁻¹) := by group
    _ = z * H.C.D.x₃⁻¹ := by rw [← sq, H.C.x₁_sq, h4, one_mul]

theorem Js_mem : H.Js ∈ Ω :=
  H.C.hs.stand.hyp.conjInvariant _ _ H.C.D.F.ρ₃.hK

theorem hjJs : IsUniqueInvolution H.Js H.C.D.F.j := by
  have h := H.C.hjJ.conj H.rt
  rwa [H.rt_conj_j] at h

theorem Ts_syl : IsSylow2In H.Ts H.Js := H.hT.conj H.rt

theorem Ts_le : H.Ts ≤ Subgroup.centralizer ({H.a} : Set G) := by
  intro x hx
  rw [Ts, mem_conjSub_iff] at hx
  have h1 : H.rt⁻¹ * x * H.rt * H.a = H.a * (H.rt⁻¹ * x * H.rt) := H.comm_T hx
  have hr : H.rt * H.a = H.a * H.rt := H.comm_rt
  have hr' : H.rt⁻¹ * H.a = H.a * H.rt⁻¹ := by
    calc H.rt⁻¹ * H.a = H.rt⁻¹ * (H.a * H.rt) * H.rt⁻¹ := by group
      _ = H.rt⁻¹ * (H.rt * H.a) * H.rt⁻¹ := by rw [hr]
      _ = H.a * H.rt⁻¹ := by group
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc x * H.a = H.rt * (H.rt⁻¹ * x * H.rt) * (H.rt⁻¹ * H.a) := by group
    _ = H.rt * (H.rt⁻¹ * x * H.rt) * (H.a * H.rt⁻¹) := by rw [hr']
    _ = H.rt * ((H.rt⁻¹ * x * H.rt) * H.a) * H.rt⁻¹ := by group
    _ = H.rt * (H.a * (H.rt⁻¹ * x * H.rt)) * H.rt⁻¹ := by rw [h1]
    _ = (H.rt * H.a) * (H.rt⁻¹ * x * H.rt) * H.rt⁻¹ := by group
    _ = (H.a * H.rt) * (H.rt⁻¹ * x * H.rt) * H.rt⁻¹ := by rw [hr]
    _ = H.a * x := by group

theorem zx₃_mem_Ts : z * H.C.D.x₃⁻¹ ∈ H.Ts := by
  rw [← H.rt_conj_x₃]
  exact conj_mem_conjSub H.x₃_mem_T

theorem Js_ne : H.Js ≠ H.C.D.F.ρ₃.K := by
  intro h
  have h1 : z * H.C.D.x₃⁻¹ ∈ H.C.D.F.ρ₃.K := h ▸ H.Ts_syl.1 H.zx₃_mem_Ts
  have h2 : z ∈ H.C.D.F.ρ₃.K := by
    have h3 := Subgroup.mul_mem _ h1 H.C.x₃_mem_J
    have e : z * H.C.D.x₃⁻¹ * H.C.D.x₃ = z := by group
    rwa [e] at h3
  have h3 : z ∈ Subgroup.zpowers H.C.D.x₃ := H.C.J_inf_W ▸ ⟨h2, H.C.hd.hzW⟩
  rcases eq_one_or_eq_sq_of_mem_zpowers H.C.orderOf_x₃ h3 H.C.hzK.sq with h4 | h4
  · exact H.C.hzK.ne_one h4
  · exact H.C.z_ne_j (h4.trans H.C.x₃_sq)

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
  T7C.isSylow2In_of_mem_RSet_of_le H.C.hs.stand.odd H.C.hs.stand.hyp H.C.hs.hK'.1 H.C.hd.hR'.1
    H.C.hd.hR'.2.1

include H in
theorem K_tq (c : G) (hc2 : c * c = 1) (hc : R ≤ Subgroup.centralizer ({c} : Set G)) :
    K ∈ tqMembers Ω c := mem_tq H.C.hs.stand H.C.hs.stand.mem H.C.hRsyl hc2 hc

include H in
theorem K'_tq (c : G) (hc2 : c * c = 1) (hc : R' ≤ Subgroup.centralizer ({c} : Set G)) :
    K' ∈ tqMembers Ω c := mem_tq H.C.hs.stand H.C.hs.hK'.1 H.hR'syl hc2 hc

theorem J_tq (c : G) (hc2 : c * c = 1) (hc : H.T₃ ≤ Subgroup.centralizer ({c} : Set G)) :
    H.C.D.F.ρ₃.K ∈ tqMembers Ω c := mem_tq H.C.hs.stand H.C.D.F.ρ₃.hK H.hT hc2 hc

theorem Js_tq (c : G) (hc2 : c * c = 1) (hc : H.Ts ≤ Subgroup.centralizer ({c} : Set G)) :
    H.Js ∈ tqMembers Ω c := mem_tq H.C.hs.stand H.Js_mem H.Ts_syl hc2 hc

theorem j_mem_exact (c : G) (hc2 : c * c = 1) (hc : R ≤ Subgroup.centralizer ({c} : Set G))
    (hc' : R' ≤ Subgroup.centralizer ({c} : Set G)) :
    H.C.D.F.j ∈ exactCore c K ⊔ exactCore c K' := by
  rw [H.C.j_eq]
  exact Subgroup.mul_mem _
    (Subgroup.mem_sup_left (le_exactCore H.C.hs.stand H.C.hs.stand.mem H.C.hRsyl hc2 hc
      (R.inv_mem H.C.x₁_mem_R)))
    (Subgroup.mem_sup_right (le_exactCore H.C.hs.stand H.C.hs.hK'.1 H.hR'syl hc2 hc'
      H.C.x₂_mem_R'))

theorem z_mem_exact :
    z ∈ exactCore (H.C.D.F.j * H.a) H.C.D.F.ρ₃.K ⊔ exactCore (H.C.D.F.j * H.a) H.Js := by
  have e : H.C.D.x₃ * (z * H.C.D.x₃⁻¹) = z := by
    have hc : z * H.C.D.x₃⁻¹ = H.C.D.x₃⁻¹ * z :=
      Thompson.commutes_of_mem_WSet H.C.D.c.hp H.C.D.c.hq H.C.D.c.hΩ H.C.D.c.hW _ H.C.hd.hzW _
        (W.inv_mem H.C.D.x₃_mem)
    rw [hc]; group
  have h := Subgroup.mul_mem (exactCore (H.C.D.F.j * H.a) H.C.D.F.ρ₃.K ⊔
      exactCore (H.C.D.F.j * H.a) H.Js)
    (Subgroup.mem_sup_left (le_exactCore H.C.hs.stand H.C.D.F.ρ₃.hK H.hT H.ja_sq H.T_le_ja
      H.x₃_mem_T))
    (Subgroup.mem_sup_right (le_exactCore H.C.hs.stand H.Js_mem H.Ts_syl H.ja_sq H.Ts_le_ja
      H.zx₃_mem_Ts))
  rwa [e] at h

end HCtx

end S24B

end CFSG.ClassicalInvolution.Asc77
