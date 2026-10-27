module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25V3
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25AE5Sq

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25R.AE5X

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.ClassicalInvolution.Asc77.C5O
open CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Q3.AE (AEQ mkQ memBar)
open CFSG.ClassicalInvolution.Q3.TC.Thin (pSpan)
open CFSG.ClassicalInvolution.Q8P.Asc77.P25R.EndL (layerBarHullEquiv layerBarHullEquiv_mk
  mem_coreHull_of_mem_layerX layerX_le_centralizer conjSub_layerX_of_mem layerToHull le_layerX)
open scoped commutatorElement


section Layer

variable {G : Type} [Group G] [Finite G] [CoreLike G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ c : G}

structure AE5Layer (Ω : Set (Subgroup G)) (z c : G) where
  ε : G → AEQ 5
  mul : ∀ y₁ ∈ layerX Ω c, ∀ y₂ ∈ layerX Ω c, ε (y₁ * y₂) = ε y₁ * ε y₂
  ker : ∀ y ∈ layerX Ω c, (ε y = 1 ↔ y ∈ oddCoreIn (layerX Ω c))
  mem : ∀ y ∈ layerX Ω c, ε y ∈ TL4.aeModel 5
  surj : ∀ w ∈ TL4.aeModel 5, ∃ y ∈ layerX Ω c, ε y = w
  act : ∀ g ∈ Subgroup.centralizer ({c} : Set G),
    ∃ x : AEQ 5, ∀ y ∈ layerX Ω c, ε (g * y * g⁻¹) = x * ε y * x⁻¹
  lab : ∀ J ∈ tqMembers3 Ω c, ∃ (α : Finset (Fin 5)) (h : α.card = 4) (b : Bool),
    (∀ y ∈ layerX Ω c, y ∈ TwinADescent.coreAt c J → ε y ∈ memBar α h b) ∧
      (∀ w ∈ memBar α h b, ∃ y ∈ layerX Ω c, y ∈ TwinADescent.coreAt c J ∧ ε y = w)
  exc : ∀ d : G, d * z * d⁻¹ ∈ Subgroup.centralizer ({c} : Set G) → ∀ x : AEQ 5,
    (∀ y ∈ layerX Ω c, ε (d * z * d⁻¹ * y * (d * z * d⁻¹)⁻¹) = x * ε y * x⁻¹) →
    ∀ (α : Finset (Fin 5)) (h : α.card = 4) (b : Bool), ∀ w ∈ memBar α h b, w * w ≠ 1 →
      w * w * (w * w) = 1 → x * w * x⁻¹ = w →
        ∃ h ∈ Subgroup.centralizer ({c} : Set G), h * z * h⁻¹ = d * z * d⁻¹

theorem AE5Layer.of_lay (Λ : Lay Ω K K' W S R R' z t u₁ u₂ c) (hAE : LayerAE5 Ω c) :
    Nonempty (AE5Layer Ω z c) := by
  classical
  obtain ⟨I, hI⟩ := hAE
  have hS := layer_q8Section Λ.hyp Λ.hc2
  have htop : pSpan (TwinDisc.secFam Ω c) = ⊤ := hS.gen
  have hinj : Function.Injective I.φ := (MonoidHom.ker_eq_bot_iff _).1 hI
  obtain ⟨e, he⟩ : ∃ e : (↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) ≃*
      ↥(TL4.aeModel 5), ∀ (x : ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c))
      (hx : x ∈ pSpan (TwinDisc.secFam Ω c)), ((e x : ↥(TL4.aeModel 5)) : AEQ 5) = I.φ ⟨x, hx⟩ :=
    ⟨(Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop.symm)).trans
      ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr I.range_eq)), fun _ _ => rfl⟩
  obtain ⟨ε₀, hε₀⟩ : ∃ ε₀ : ↥(layerX Ω c) →* AEQ 5, ∀ y : ↥(layerX Ω c),
      ε₀ y = ((e (Λ.lbe (QuotientGroup.mk y)) : ↥(TL4.aeModel 5)) : AEQ 5) :=
    ⟨(TL4.aeModel 5).subtype.comp (e.toMonoidHom.comp (Λ.lbe.toMonoidHom.comp
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerX Ω c))))), fun _ => rfl⟩
  refine ⟨{ ε := fun y => if hy : y ∈ layerX Ω c then ε₀ ⟨y, hy⟩ else 1
            mul := ?_, ker := ?_, mem := ?_, surj := ?_, act := ?_, lab := ?_, exc := ?_ }⟩
  · intro y₁ h₁ y₂ h₂
    have h12 : y₁ * y₂ ∈ layerX Ω c := Subgroup.mul_mem _ h₁ h₂
    simp only [dif_pos h₁, dif_pos h₂, dif_pos h12]
    exact map_mul ε₀ ⟨y₁, h₁⟩ ⟨y₂, h₂⟩
  · intro y hy
    simp only [dif_pos hy]
    rw [hε₀, OneMemClass.coe_eq_one, MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff]
    exact mk_eq_one_iff (layerX Ω c) ⟨y, hy⟩
  · intro y hy
    simp only [dif_pos hy]
    rw [hε₀]
    exact (e _).2
  · intro w hw
    obtain ⟨b, hb⟩ := e.surjective ⟨w, hw⟩
    obtain ⟨b', hb'⟩ := Λ.lbe.surjective b
    obtain ⟨⟨y, hy⟩, hy'⟩ := QuotientGroup.mk_surjective b'
    refine ⟨y, hy, ?_⟩
    simp only [dif_pos hy]
    rw [hε₀, hy', hb', hb]
  · intro g hg
    have hb : conjSub g (layerX Ω c) = layerX Ω c := conjSub_layerX_of_mem Λ.hΩ hg
    obtain ⟨x, hx⟩ := AE5Sq.aut_eq_conj ((e.symm.trans (secAct Λ.hΩ Λ.hc2' ⟨g, hg⟩)).trans e)
    refine ⟨x, fun y hy => ?_⟩
    have hgy : g * y * g⁻¹ ∈ layerX Ω c := by
      have := Generic.conj_mem_conjSub (n := g) hy
      rwa [hb] at this
    simp only [dif_pos hy, dif_pos hgy]
    have h1 : (⟨g * y * g⁻¹, hgy⟩ : ↥(layerX Ω c)) = C25Y.conjOnSub (layerX Ω c) hb ⟨y, hy⟩ := rfl
    rw [hε₀, hε₀, h1, ← C25Y.layerAut_mk, Λ.lbe_layerAut hg hb]
    have := hx (e (Λ.lbe (QuotientGroup.mk ⟨y, hy⟩)))
    simpa using this
  · intro J hJ
    have hJ0 : secImg Ω c J ∈ TwinDisc.secFam Ω c := secImg_mem_secFam hJ
    obtain ⟨α, h, b, hlab⟩ := I.label _ hJ0
    refine ⟨α, h, b, ?_, ?_⟩
    · intro y hy hyJ
      simp only [dif_pos hy]
      rw [hε₀]
      have hC := layerX_le_centralizer Ω c hy
      have hY := mem_coreHull_of_mem_layerX Λ.hΩ Λ.hc2' Λ.h2 hy
      have hmem : (QuotientGroup.mk (⟨⟨y, hC⟩, hY⟩ : ↥(coreHull Ω c)) :
          ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) ∈ secImg Ω c J :=
        Subgroup.mem_map.mpr ⟨⟨⟨y, hC⟩, hY⟩,
          Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr hyJ), rfl⟩
      have hl : Λ.lbe (QuotientGroup.mk ⟨y, hy⟩) = QuotientGroup.mk ⟨⟨y, hC⟩, hY⟩ :=
        layerBarHullEquiv_mk Λ.hΩ Λ.hc2' Λ.h2 ⟨y, hy⟩
      have hps : (QuotientGroup.mk (⟨⟨y, hC⟩, hY⟩ : ↥(coreHull Ω c)) :
          ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) ∈
          pSpan (TwinDisc.secFam Ω c) := by
        rw [htop]; exact Subgroup.mem_top _
      rw [hl, he _ hps, ← hlab]
      exact ⟨⟨_, hps⟩, Subgroup.mem_subgroupOf.mpr hmem, rfl⟩
    · intro w hw
      rw [← hlab] at hw
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hw
      have hs' : (s : ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) ∈
          secImg Ω c J := Subgroup.mem_subgroupOf.mp hs
      obtain ⟨⟨⟨y, hC⟩, hY⟩, hy', hys⟩ := Subgroup.mem_map.mp hs'
      have hyJ : y ∈ TwinADescent.coreAt c J :=
        Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hy')
      have hyX : y ∈ layerX Ω c := by
        rw [layerX_eq_coreLayer Λ.hΩ Λ.hc2' Λ.h2]
        exact ⟨⟨y, hC⟩, hY, rfl⟩
      refine ⟨y, hyX, hyJ, ?_⟩
      simp only [dif_pos hyX]
      have hl : Λ.lbe (QuotientGroup.mk ⟨y, hyX⟩) = QuotientGroup.mk ⟨⟨y, hC⟩, hY⟩ :=
        layerBarHullEquiv_mk Λ.hΩ Λ.hc2' Λ.h2 ⟨y, hyX⟩ (hC := hC) (hY := hY)
      have hys' : (QuotientGroup.mk (⟨⟨y, hC⟩, hY⟩ : ↥(coreHull Ω c)) :
          ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) = ↑s := hys
      rw [hε₀, hl, hys', he _ s.2]
  · intro d hbC x hx α h b w hw hw2 hw4 hxw
    obtain ⟨L, hL, hLlab⟩ := I.label_surj α h b
    rw [← hLlab] at hw
    obtain ⟨s, hs, hsw⟩ := Subgroup.mem_map.mp hw
    have hsL : (s : ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) ∈ L :=
      Subgroup.mem_subgroupOf.mp hs
    have hes : ((e (s : ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) :
        ↥(TL4.aeModel 5)) : AEQ 5) = w := by
      rw [he _ s.2]; exact hsw
    have hs4' : s * s * (s * s) = 1 := by
      apply hinj
      rw [map_mul, map_mul, map_one, hsw]
      exact hw4
    have hs2' : s * s ≠ 1 := by
      intro h1
      apply hw2
      rw [← hsw, ← map_mul, h1, map_one]
    have hy4 : (s : ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) * s * s * s = 1 := by
      have := congrArg Subtype.val hs4'
      simpa [mul_assoc] using this
    have hy2 : (s : ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) * s ≠ 1 :=
      fun h1 => hs2' (Subtype.ext h1)
    have hb : conjSub (d * z * d⁻¹) (layerX Ω c) = layerX Ω c := conjSub_layerX_of_mem Λ.hΩ hbC
    have hfix : secAct Λ.hΩ Λ.hc2' ⟨d * z * d⁻¹, hbC⟩
        (s : ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) = s := by
      obtain ⟨b', hb'⟩ := Λ.lbe.surjective
        (s : ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c))
      obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk_surjective b'
      have hgy : d * z * d⁻¹ * y * (d * z * d⁻¹)⁻¹ ∈ layerX Ω c := by
        have := Generic.conj_mem_conjSub (n := d * z * d⁻¹) hy
        rwa [hb] at this
      have h1 := hx y hy
      simp only [dif_pos hy, dif_pos hgy] at h1
      rw [hε₀, hε₀] at h1
      apply e.injective
      apply Subtype.ext
      rw [← hb', ← Λ.lbe_layerAut hbC hb, C25Y.layerAut_mk]
      calc _ = ((e (Λ.lbe (QuotientGroup.mk ⟨d * z * d⁻¹ * y * (d * z * d⁻¹)⁻¹, hgy⟩)) :
              ↥(TL4.aeModel 5)) : AEQ 5) := rfl
        _ = x * ((e (Λ.lbe (QuotientGroup.mk ⟨y, hy⟩)) : ↥(TL4.aeModel 5)) : AEQ 5) * x⁻¹ := h1
        _ = x * w * x⁻¹ := by rw [hb', hes]
        _ = w := hxw
        _ = _ := by rw [hb', hes]
    obtain ⟨J, hJ, hJb⟩ := nc4_lift_sec Λ.hyp Λ.hΩ Λ.hc2' hbC hL hsL hy4 hy2 hfix
    obtain ⟨h', -, hh'⟩ := conj_of_member_sec Λ.hyp Λ.hc2 Λ.hc1 Λ.hcA Λ.hT Λ.hbad hJ hJb
    exact ⟨h', h'.2, hh'⟩

end Layer

end CFSG.ClassicalInvolution.Q8P.Asc77.P25R.AE5X
