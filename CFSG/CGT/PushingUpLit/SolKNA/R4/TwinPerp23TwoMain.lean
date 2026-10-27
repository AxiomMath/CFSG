module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp23TwoTrans
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinDiscThmE
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp23TwoAlg
public import CFSG.ClassicalInvolution.SmallCases.A7T22Main

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

namespace Perp23

namespace Two

section Main

theorem mem_centralizer_conj {G : Type*} [Group G] {a g y : G}
    (hy : y ∈ Subgroup.centralizer ({a} : Set G)) :
    g * y * g⁻¹ ∈ Subgroup.centralizer ({g * a * g⁻¹} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
  calc g * y * g⁻¹ * (g * a * g⁻¹) = g * (y * a) * g⁻¹ := by group
    _ = g * (a * y) * g⁻¹ := by rw [hy]
    _ = g * a * g⁻¹ * (g * y * g⁻¹) := by group


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem sup_centralizer_eq_top_of_thmE (hr : 4 ≤ r) (hE : TwinThmER r n)
    (h : PerpHypR r n Y R S t) (h2 : TwinPerp.TwoTwins R) {W : Subgroup Y}
    (hW : W ∈ WSet (CoreAssembly.conjClass (tightCore R))) (htW : t ∈ W)
    (hS4 : MuIsoS4 (CoreAssembly.conjClass (tightCore R)) W) {K' : Subgroup Y}
    (hK' : K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hne : K' ≠ tightCore R) {a : Y} (haK : a ∈ tightCore R ⊔ K') (haW : a ∈ W)
    (ha2 : a * a = 1) (ha1 : a ≠ 1) (hat : a ≠ t) :
    Subgroup.centralizer ({a} : Set Y) ⊔ Subgroup.centralizer ({t} : Set Y) = ⊤ := by
  classical
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  set K := tightCore R with hKdef
  obtain ⟨K'', hK'', hne'', ⟨D⟩⟩ := exists_twoFrame h h2 hW htW hS4
  have hpair : twinSet Ω K = {K, K''} := TwinPerp.twinSet_eq_pair h2 hK'' hne''
  have hK'eq : K' = K'' := by
    rw [hpair] at hK'
    rcases hK' with h1 | h1
    · exact absurd h1 hne
    · exact h1
  subst hK'eq
  have hΩ : HypOmegaGen Ω := h.core.hyp
  have hKΩ : K ∈ Ω := CoreAssembly.mem_conjClass_self _
  have hK'Ω : K' ∈ Ω := hK''.1
  have hz : IsUniqueInvolution K t := D.hzK
  have hz' : IsUniqueInvolution K' t := D.hzK'
  have hperp : KPerp Ω K = {K, K'} := h.perp.trans hpair
  have c : Q3CL.Thompson.Ctx Ω W := Q3CL.T8.ctxOf h.partIHypG hW
  have hquat : ∀ L ∈ Ω, ∃ P : Subgroup Y, IsSylow2In P L ∧
      Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2))) := by
    rintro _ ⟨g', rfl⟩
    refine ⟨conjSub g' ((S : Subgroup R).map R.subtype), h.core.datum.sylow_core.conj g', ⟨?_⟩⟩
    exact (Subgroup.equivMapOfInjective _ (MulAut.conj g').toMonoidHom
      (MulAut.conj g').injective).symm.trans
      ((Subgroup.equivMapOfInjective (S : Subgroup R) R.subtype R.subtype_injective).symm.trans
        h.core.quat.some)
  have h16 := WTool.sylow16_of_quat hr hΩ hquat
  have hwc := WTool.comm_of_mem_wSet hΩ hW
  set H := Subgroup.centralizer ({D.u} : Set Y) ⊔ Subgroup.centralizer ({t} : Set Y) with hH
  have hCu : Subgroup.centralizer ({D.u} : Set Y) ≤ H := le_sup_left
  have hCt : Subgroup.centralizer ({t} : Set Y) ≤ H := le_sup_right
  have hrH : D.F.ρ.r ∈ H :=
    hCt (Subgroup.mem_centralizer_singleton_iff.mpr D.r_t)
  have hr'H : D.F.ρ'.r ∈ H :=
    hCt (Subgroup.mem_centralizer_singleton_iff.mpr (D.hzK'.commute_of_mem D.r'_mem_K').symm)
  have hsH : D.F.ρ₃.r ∈ H :=
    hCu (Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp (D.s_u hwc)))
  have hWH : W ⊔ OCW W ≤ H := by
    refine sup_le (fun w hw => hCu ?_) (fun w hw => hCu ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (hwc w hw D.u D.u_mem_W)
    · have := Subgroup.mem_centralizer_iff.mp (Thompson.OCW_le_centralizer W hw) D.u D.u_mem_W
      exact Subgroup.mem_centralizer_singleton_iff.mpr this.symm
  have hMH : MGrp Ω W ≤ H := D.mgrp_le hΩ hW c hrH hr'H hsH hWH
  have htr := trans_of_mgrp hΩ h16 hKΩ hz hW htW hCt hMH (D.exists_conj_rep c)
  have hCtu : Subgroup.centralizer ({t * D.u} : Set Y) ≤ H := by
    intro y hy
    have h1 : D.F.ρ.r⁻¹ * y * D.F.ρ.r ∈ Subgroup.centralizer ({D.u} : Set Y) := by
      have h0 := mem_centralizer_conj (g := D.F.ρ.r⁻¹) hy
      have e : D.F.ρ.r⁻¹ * (t * D.u) * D.F.ρ.r⁻¹⁻¹ = D.u := by
        rw [← D.r_u hwc]; group
      rwa [e, inv_inv] at h0
    have e : y = D.F.ρ.r * (D.F.ρ.r⁻¹ * y * D.F.ρ.r) * D.F.ρ.r⁻¹ := by group
    rw [e]
    exact H.mul_mem (H.mul_mem hrH (hCu h1)) (H.inv_mem hrH)
  have hCu' : Subgroup.centralizer ({D.u} : Set Y) ≤
      Subgroup.centralizer ({t * D.u} : Set Y) ⊔ Subgroup.centralizer ({t} : Set Y) := by
    intro y hy
    have h1 : D.F.ρ.r * y * D.F.ρ.r⁻¹ ∈ Subgroup.centralizer ({t * D.u} : Set Y) := by
      have h0 := mem_centralizer_conj (g := D.F.ρ.r) hy
      rwa [D.r_u hwc] at h0
    have hrt : D.F.ρ.r⁻¹ ∈ Subgroup.centralizer ({t} : Set Y) :=
      Subgroup.inv_mem _ (Subgroup.mem_centralizer_singleton_iff.mpr D.r_t)
    have e : y = D.F.ρ.r⁻¹ * (D.F.ρ.r * y * D.F.ρ.r⁻¹) * D.F.ρ.r := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right hrt)
      (Subgroup.mem_sup_left h1)) (Subgroup.mem_sup_right
        (Subgroup.mem_centralizer_singleton_iff.mpr D.r_t))
  have hstd : StdCentW Ω K W H t := by
    refine ⟨hCt, ?_, ?_⟩
    · intro L hL J hJ z' hz'J hzz _
      exfalso
      have hJp : J ∈ KPerp Ω L := Set.mem_insert_of_mem _ hJ
      rw [A7T22.kPerp_eq_of_twin hΩ hKΩ hL, hperp] at hJp
      rcases hJp with rfl | rfl
      · exact hzz (hz'J.eq hz)
      · exact hzz (hz'J.eq hz')
    · intro L hL L' hL' hLL' R₁ R₂ hR₁ hR₂ hc x hx y hy ox oy hxyW
      have hLm : L ∈ ({K, K'} : Set (Subgroup Y)) := hpair ▸ hL
      have hL'm : L' ∈ ({K, K'} : Set (Subgroup Y)) := hpair ▸ hL'
      have hM : L ⊔ L' = K ⊔ K' := by
        rcases hLm with rfl | rfl <;> rcases hL'm with rfl | rfl
        · exact absurd rfl hLL'
        · rfl
        · exact sup_comm _ _
        · exact absurd rfl hLL'
      have hzL := isUniqueInvolution_of_mem_twinSet hz hL
      have hzL' := isUniqueInvolution_of_mem_twinSet hz hL'
      have hx2 : x * x = t := T7B.mul_self_eq_of_orderOf_four hzL (hR₁.1 hx) ox
      have hy2 : y * y = t := T7B.mul_self_eq_of_orderOf_four hzL' (hR₂.1 hy) oy
      have hxy : x * y = y * x := hc x hx y hy
      have hxy2 : (x * y) * (x * y) = 1 := by
        calc (x * y) * (x * y) = x * (y * x) * y := by group
          _ = x * (x * y) * y := by rw [← hxy]
          _ = (x * x) * (y * y) := by group
          _ = 1 := by rw [hx2, hy2]; exact hz.sq
      have hcard : Nat.card ↥(R₁ ⊓ R₂) ≤ 2 :=
        Sec6Gen.card_le_two_of_le_inf hΩ hL.1 hL'.1 hLL'.symm (hR₁.2.1.to_le inf_le_left)
          (inf_le_left.trans hR₁.1) (inf_le_right.trans hR₂.1)
      have hnot : x ∉ R₂ := by
        intro hxR₂
        have hle : Subgroup.zpowers x ≤ R₁ ⊓ R₂ := Subgroup.zpowers_le.mpr ⟨hx, hxR₂⟩
        have := Subgroup.card_le_of_le hle
        rw [Nat.card_zpowers, ox] at this
        omega
      have hxy1 : x * y ≠ 1 := fun h1 => hnot (by
        have : x = y⁻¹ := eq_inv_of_mul_eq_one_left h1
        rw [this]
        exact R₂.inv_mem hy)
      have hxyt : x * y ≠ t := fun h1 => hnot (by
        have hyx : y = x := by
          calc y = x⁻¹ * (x * y) := by group
            _ = x⁻¹ * t := by rw [h1]
            _ = x⁻¹ * (x * x) := by rw [hx2]
            _ = x := by group
        rw [← hyx]
        exact hy)
      have hxyK : x * y ∈ K ⊔ K' := by
        rw [← hM]
        exact (L ⊔ L').mul_mem (Subgroup.mem_sup_left (hR₁.1 hx))
          (Subgroup.mem_sup_right (hR₂.1 hy))
      rcases D.inv_cases hΩ hW hKΩ hK'' hne'' hxyK hxyW hxy2 hxy1 hxyt with h1 | h1
      · rw [h1]
        exact hCu
      · rw [h1]
        exact hCtu
  have hcent := centralizersSylowPairsW_of_stdCentW hΩ hz htW hstd
  have hWnorm : ∀ s ∈ (D.S₀ : Subgroup Y), conjSub s W = W := fun s hs =>
    mem_normalizer_iff_conjSub_eq.mp
      (WTool.le_normalizer_of_le_isPGroup hΩ h16 hW D.S₀.isPGroup' D.hWS hs)
  have hρ : IsSylow2In D.F.ρ.R K := by
    have := D.F.ρ.hRK
    rwa [D.hρK] at this
  have hρ' : IsSylow2In D.F.ρ'.R K' := by
    have := D.F.ρ'.hRK
    rwa [D.hρ'K] at this
  have hprinted : TwinThmEW.PrintedWT Ω K W :=
    ⟨D.S₀, D.F.ρ.R, hρ, D.hρS, hW, D.hWS, hWnorm, K', hK'', hne'', D.F.ρ'.R,
      mem_RSet_of_isSylow2In hK'Ω hρ', hρ'.1, D.hρ'S⟩
  have hHtop : H = ⊤ := hE Y R S t h.core K H W hKΩ hprinted ⟨htr, hcent⟩
  rcases D.inv_cases hΩ hW hKΩ hK'' hne'' haK haW ha2 ha1 hat with hau | hau
  · rw [hau]
    exact hHtop
  · rw [hau]
    refine top_le_iff.mp ?_
    rw [← hHtop]
    exact sup_le hCu' le_sup_right

end Main

end Two

end Perp23

end CFSG.CGT.PushingUpLit.SolKNA.R4
