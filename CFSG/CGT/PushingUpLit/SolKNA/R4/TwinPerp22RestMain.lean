module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp22RestLayer
public import CFSG.CGT.PushingUpLit.SolKNA.R4.NormalE2
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp22ZStar
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf17Exit

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Perp22Rest

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Inner
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
  CFSG.CGT.PushingUpLit.SolKNA.R4
open scoped commutatorElement

section Main


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem abelianO2R_of_three_twins (hr : 4 ≤ r) (hNo : NoQ16E4) (hList : SmallListR)
    (hO : NoDatumOtherR r) (h6 : ∀ m, TightLargeEdgeSR r m) (hM : Model163R r)
    (h : PerpHypR r n Y R S t)
    (hcard : (twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R)).ncard = 3)
    {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y}
    (d : A7T22.Hyp22G (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃)
    (htC : t ∈ Subgroup.centralizer ({u₁ * u₂} : Set Y))
    (htH : (⟨t, htC⟩ : ↥(Subgroup.centralizer ({u₁ * u₂} : Set Y))) ∈
      coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) :
    TightInO2 (QuotientGroup.mk'
      (classicalInvolutionOddCore ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)))
      (⟨⟨t, htC⟩, htH⟩ : ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)))) := by
  have hcent := inO2_cent_of_three_twins hr hNo hList hO h6 hM h hcard d htC
  have hc1 : u₁ * u₂ ≠ 1 := by
    intro h1
    have hu₂ : u₂ = u₁⁻¹ := eq_inv_of_mul_eq_one_right h1
    have hu₂K : u₂ ∈ K := hu₂ ▸ K.inv_mem d.hu₁.1
    have h4dvd : 4 ∣ orderOf u₂ := by rw [d.hu₂.2]
    exact d.hne (eq_of_mem_inf_of_four_dvd d.hyp d.hK'.1 d.mem d.hu₂.1 hu₂K h4dvd)
  have hc2' : IsPGroup 2 (Subgroup.zpowers (u₁ * u₂)) := isPGroup_zpowers_of_mul_self_eq_one d.sq_12 hc1
  haveI := TwinExitPf6.normal_coreHull d.hyp hc2'
  exact tightInO2_oddQuot_of_normal htH hcent

theorem hyp51B_of_three_twins (hr : 4 ≤ r) (hNo : NoQ16E4) (hList : SmallListR)
    (hO : NoDatumOtherR r) (h6 : ∀ m, TightLargeEdgeSR r m) (hM : Model163R r)
    (h : PerpHypR r n Y R S t)
    (hcard : (twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R)).ncard = 3)
    {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y}
    (d : A7T22.Hyp22G (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃) :
    Hyp51 (Subgroup.closure ({u₁ * u₂, t, u₂ * u₃} : Set Y)) := by
  refine ⟨d.isElemAbelian_B, d.natCard_B, fun c hc hc1 => ?_⟩
  have hzB : t ∈ Subgroup.closure ({u₁ * u₂, t, u₂ * u₃} : Set Y) := T7B.mem_closure_snd
  by_cases hcz : c = t
  · rw [hcz]
    exact Perp22.hyp51At_vertex_z d
  · obtain ⟨L, L', L₃, x, y, w, d', hxy⟩ := Perp22.exists_datum_of_mem_B d hc hc1 hcz
    subst hxy
    have hc2 : IsPGroup 2 (Subgroup.zpowers (x * y)) :=
      CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one d'.sq_12
    obtain ⟨htC, htH⟩ := Perp22.layer_mem d'
    exact TwinPerpV3.hyp51At_of_tightInO2 d.hyp hc2 d.isElemAbelian_B hc hzB hc1 d.hz.ne_one
      (Ne.symm hcz) htC htH (abelianO2R_of_three_twins hr hNo hList hO h6 hM h hcard d' htC htH)

theorem zStar_of_three_twins (hr : 4 ≤ r) (hNo : NoQ16E4) (hList : SmallListR)
    (hO : NoDatumOtherR r) (h6 : ∀ m, TightLargeEdgeSR r m) (hM : Model163R r)
    (h : PerpHypR r n Y R S t)
    (hcard : (twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R)).ncard = 3)
    {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y}
    (d : A7T22.Hyp22G (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃)
    (hμ : ¬ ∀ W ∈ WSet (CoreAssembly.conjClass (tightCore R)),
      MuIsoWylD4 (CoreAssembly.conjClass (tightCore R)) W) :
    t ∈ zStarOf (Subgroup.centralizer ({u₁ * u₂} : Set Y)) := by
  push Not at hμ
  obtain ⟨W, hW, hnW⟩ := hμ
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hΩ : HypOmegaGen Ω := d.hyp
  have hcomp := TwinPerpV3.dstarComp_subset_twinSet_of_not_wyl h.partIHypG d
    (h.kPerp_datum d.mem d.hz) hW hnW
  have hstar : ∀ J ∈ omegaStarNbr Ω K, J ∈ twinSet Ω K := fun J hJ =>
    hcomp J (Relation.ReflTransGen.single ⟨hJ.1, Or.inl hJ⟩)
  have hU : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core h.core.datum
  have hzK₃ : IsUniqueInvolution K₃ t := d.hzK₃
  have hstd : TwinStdR r n Y R S t :=
    ⟨h.core.card, h.core.simple, h.core.nonab, h.core.datum, h.core.quat, h.core.gen,
      h.core.oddFree, h.core.hyp, h.core.aEmpty, h.core.twin⟩
  obtain ⟨S₀, hstd₀⟩ := hstd.core
  have hRc₀ : tightCore (tightCore R) = tightCore R := TwinEdge.tightCore_idem R
  have hK₃Ω : K₃ ∈ CoreAssembly.conjClass (tightCore (tightCore R)) := by
    rw [hRc₀]; exact d.hK₃.1
  obtain ⟨S₃, hstd₃⟩ := exists_datum_atR hstd₀ hRc₀ hK₃Ω hzK₃
  have hRc₃ : tightCore K₃ = K₃ := TwinVtx.tightCore_eq_of_mem hRc₀ hK₃Ω
  set c : Y := u₁ * u₂ with hcdef
  have hc2 : c * c = 1 := d.sq_12
  have hc1 : c ≠ 1 := by
    intro h1
    have hu₂ : u₂ = u₁⁻¹ := eq_inv_of_mul_eq_one_right h1
    have hu₂K : u₂ ∈ K := hu₂ ▸ K.inv_mem d.hu₁.1
    have h4dvd : 4 ∣ orderOf u₂ := by rw [d.hu₂.2]
    exact d.hne (eq_of_mem_inf_of_four_dvd hΩ d.hK'.1 d.mem d.hu₂.1 hu₂K h4dvd)
  have t13 : K ≤ Balance.Bootstrap.trivialOnQuot K₃ :=
    A7T22.le_trivialOnQuot_of_twin hΩ d.mem d.hK₃.1 d.hK₃K.symm d.hz hzK₃
  have t23 : K' ≤ Balance.Bootstrap.trivialOnQuot K₃ :=
    A7T22.le_trivialOnQuot_of_twin hΩ d.hK'.1 d.hK₃.1 d.hK₃K'.symm d.hzK' hzK₃
  have hcq3 : c ∈ Balance.Bootstrap.trivialOnQuot K₃ :=
    Subgroup.mul_mem _ (t13 d.hu₁.1) (t23 d.hu₂.1)
  obtain ⟨htC, -⟩ := Perp22.layer_mem d
  have hcent := inO2_cent_of_three_twins hr hNo hList hO h6 hM h hcard d htC
  have h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass hstd₀.datum.twoGroup
  have hq := hstd₀.quat_sylow hRc₀
  have hA := h.aEmpty_all
  exact mem_zStarOf_of_inO2_of_star hr hΩ d.mem d.hz hstar h2 hq hA d.hK₃.1 hzK₃ hc2 hc1 hcq3 htC
    hcent

theorem threeTwinsExclR_of_model163R (hr : 4 ≤ r) (hNo : NoQ16E4) (hList : SmallListR)
    (hO : NoDatumOtherR r) (h6 : ∀ m, TightLargeEdgeSR r m) (hM : Model163R r)
    (hE : Perp22.ThmER r n) : Perp22.ThreeTwinsExclR r n := by
  intro Y _ _ R S t h hcard
  have h3 : ¬ TwinPerp.TwoTwins R := by
    intro h2
    obtain ⟨K', hK', hne⟩ := h.core.twin
    have := TwinPerp.twinSet_eq_pair h2 hK' hne
    rw [this] at hcard
    have hle : ({tightCore R, K'} : Set (Subgroup Y)).ncard ≤ 2 := by
      have e := Set.ncard_insert_le (tightCore R) ({K'} : Set (Subgroup Y))
      rw [Set.ncard_singleton] at e
      exact e
    omega
  have hall : ¬ ∀ W ∈ WSet (CoreAssembly.conjClass (tightCore R)),
      MuIsoWylD4 (CoreAssembly.conjClass (tightCore R)) W := by
    intro hall
    have := Perp22.ncard_twinSet_eq_four_of_wyl h h3 hall
    omega
  push Not at hall
  obtain ⟨W₀, hW₀, hnW⟩ := hall
  refine Perp22.false_of_not_wyl hE h h3 hW₀ hnW (fun {L L' L₃ x y w} d' => ?_)
    (fun {L L' L₃ x y w} d' => ?_)
  · exact hyp51B_of_three_twins hr hNo hList hO h6 hM h hcard d'
  · exact zStar_of_three_twins hr hNo hList hO h6 hM h hcard d' fun hall' => hnW (hall' W₀ hW₀)

end Main

end CFSG.CGT.PushingUpLit.SolKNA.R4.Perp22Rest
