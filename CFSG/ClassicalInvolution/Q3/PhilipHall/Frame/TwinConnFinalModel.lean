module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinConnTransportLift
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinIdentFinal
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520GlueD4Lie
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtxSecFrame
public import CFSG.ClassicalInvolution.Asc77.AscE18FromM
public import CFSG.ClassicalInvolution.Asc77.AscS24Alpha
public import CFSG.ClassicalInvolution.Asc77.AscT7AFinal
public import CFSG.ClassicalInvolution.Asc77.AscT7ASectD
public import CFSG.ClassicalInvolution.Asc77.AscT7CFinal
public import CFSG.ClassicalInvolution.Asc77.AscT7EFinal3
public import CFSG.ClassicalInvolution.Asc77.AscT7FJ
public import CFSG.ClassicalInvolution.Asc77.AscT7HC5
public import CFSG.ClassicalInvolution.Asc77.AscT7HFinal
public import CFSG.ClassicalInvolution.Asc77.AscT7QFinal
public import CFSG.ClassicalInvolution.Asc77.AscT7XFin
public import CFSG.ClassicalInvolution.Asc77.AscT7Y3
public import CFSG.ClassicalInvolution.Asc77.AscT8ThmEight
public import CFSG.ClassicalInvolution.Asc77.AscT8Y6
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.PairNormal
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameSec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinH1
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtxSecEdge
public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.CentQuotAEmpty
public import CFSG.ClassicalInvolution.Q3.Q3T7E9Comp
public import CFSG.ClassicalInvolution.Q3.Q3T7E9Main
public import CFSG.ClassicalInvolution.Q3.Q3T7LayerQ
public import CFSG.ClassicalInvolution.Q3.Q3T7P24A09
public import CFSG.ClassicalInvolution.Q3.Q3T7T2Main
public import CFSG.ClassicalInvolution.Q3.Q3T8Std8
public import CFSG.ClassicalInvolution.Q3.TL4OddConv
public import CFSG.ClassicalInvolution.SmallCases.A7Q1C
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S7E0
public import CFSG.Sporadic.Schreier.J4SNoCompCover

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520Aux

namespace TwinConnT


theorem model1520LieTarget_plus_four : Model1520LieTarget .POmegaPlus 4 :=
  fun _ _ _ X _ _ D i hi hk _ hL _ hLt =>
    model1520_of_lieSystem3_full X D i hi .POmegaPlus 4 (Or.inr ⟨rfl, rfl⟩) hk hL hLt


variable {G : Type} [Group G] [Finite G]

theorem isClassicalMember3On_conj_gen {X X' L : Subgroup G} {z : G} (c : G) (hX : conjSub c X = X')
    (h : TwinSecXg.IsClassicalMember3On X L z) :
    TwinSecXg.IsClassicalMember3On X' (conjSub c L) (c * z * c⁻¹) := by
  obtain ⟨hz, h'⟩ := h
  let φ : ↥X ≃* ↥X' :=
    (X.equivMapOfInjective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective).trans
      (MulEquiv.subgroupCongr hX)
  have hφ : ∀ x : X, ((φ x : X') : G) = c * (x : G) * c⁻¹ := fun x => rfl
  have hz' : c * z * c⁻¹ ∈ X' := by
    rw [← hX]
    exact conj_mem_conjSub hz
  refine ⟨hz', ?_⟩
  have h1 := TwinSecXg.isClassicalMember3_map_equiv φ h'
  have e1 : φ ⟨z, hz⟩ = ⟨c * z * c⁻¹, hz'⟩ := Subtype.ext (by rw [hφ])
  have e2 : (L.subgroupOf X).map φ.toMonoidHom = (conjSub c L).subgroupOf X' := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr (conj_mem_conjSub (Subgroup.mem_subgroupOf.mp hy))
    · intro hx
      have hxX' : (x : G) ∈ conjSub c X := hX ▸ x.2
      have hx' : c⁻¹ * (x : G) * c ∈ X := by
        rw [mem_conjSub_iff] at hxX'
        exact hxX'
      refine ⟨⟨c⁻¹ * (x : G) * c, hx'⟩, Subgroup.mem_subgroupOf.mpr ?_, Subtype.ext ?_⟩
      · have := Subgroup.mem_subgroupOf.mp hx
        rwa [mem_conjSub_iff] at this
      · show c * (c⁻¹ * (x : G) * c) * c⁻¹ = x
        group
  rw [e1, e2] at h1
  exact h1

theorem twin_mem_pi {K₀ K' : Subgroup G} {π : Set (Subgroup G)} {g : G} (hs : TwinGraphStd K₀)
    (hK' : K' ∈ twinSet (CoreAssembly.conjClass K₀) K₀)
    (hπ : π ∈ maxOrbs (nbrAdj (CoreAssembly.conjClass K₀)) K₀) (hH1 : NoCentralInv π)
    (hg : conjSub g K₀ ∈ π) : conjSub g K' ∈ π := by
  have hos := hs.orbitStd
  have hJΩ : conjSub g K₀ ∈ CoreAssembly.conjClass K₀ := ⟨g, rfl⟩
  have hπg : conjSub g '' π ∈ maxOrbs (nbrAdj (CoreAssembly.conjClass K₀)) (conjSub g K₀) :=
    isMaxOrb_conj hos.graph hπ g
  have hH1g : NoCentralInv (conjSub g '' π) := hH1.conj g
  have hV : conjSub g K' ∈ twinSet (CoreAssembly.conjClass K₀) (conjSub g K₀) :=
    twinSet_conj hs.hyp.conjInvariant hK' g
  have hK₀img : conjSub g⁻¹ (conjSub g K₀) ∈ conjSub g '' π := by
    rw [conjSub_inv_conjSub]
    exact hos.mem_conj_image_of_mem hπ hg
  have := hos.beta_subset_conj_image hJΩ hπg hK₀img (hos.twinSet_subset_beta hπg hH1g hV)
  obtain ⟨M, ⟨P, hP, rfl⟩, hM⟩ := this
  rw [conjSub_inv_conjSub] at hM
  rw [← hM]
  exact hP

theorem subgroupOf_mem_conjClass {J M X : Subgroup G} {a : G} (ha : a ∈ X) (h : conjSub a J = M) :
    M.subgroupOf X ∈ CoreAssembly.conjClass (J.subgroupOf X) :=
  ⟨⟨a, ha⟩, by
    show conjSub (⟨a, ha⟩ : ↥X) (J.subgroupOf X) = M.subgroupOf X
    rw [conjSub_subgroupOf, h]⟩

theorem model1520_of_twin_core {K₀ K' L : Subgroup G} {π : Set (Subgroup G)} {g t : G} {n : ℕ}
    (hCIT : CIT3Below n) (hn : Nat.card G ≤ n) (hZ : Subgroup.center G = ⊥)
    (hs : TwinGraphStd K₀) (hK' : K' ∈ twinSet (CoreAssembly.conjClass K₀) K₀) (hne : K' ≠ K₀)
    (hz : IsUniqueInvolution K₀ t)
    (hπ : π ∈ maxOrbs (nbrAdj (CoreAssembly.conjClass K₀)) K₀) (hH1 : NoCentralInv π)
    (hg : conjSub g K₀ ∈ π)
    (hθ : classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set G)) = ⊥)
    (hKL : K₀ ≤ L) (hL : TwinSecXg.IsClassicalMember3On (conjSub g (piGen π)) L t) :
    Model1520 (piGen π) (g * t * g⁻¹) := by
  have hos := hs.orbitStd
  have hK₀Ω : K₀ ∈ CoreAssembly.conjClass K₀ := CoreAssembly.mem_conjClass_self _
  have hJΩ : conjSub g K₀ ∈ CoreAssembly.conjClass K₀ := ⟨g, rfl⟩
  have hKgX : conjSub g K₀ ≤ piGen π := le_piGen hg
  have hw : IsUniqueInvolution (conjSub g K₀) (g * t * g⁻¹) := hz.conj g
  have hz' : IsUniqueInvolution K' t := TwinSecXg.isUniqueInvolution_of_mem_twinSet hz hK'
  have htX : g * t * g⁻¹ ∈ piGen π := hKgX hw.mem
  have hK'gπ : conjSub g K' ∈ π := twin_mem_pi hs hK' hπ hH1 hg
  have hK'gX : conjSub g K' ≤ piGen π := le_piGen hK'gπ
  have hlt : Nat.card (piGen π) < n := by
    have h1 := TwinSecXg.card_conj_lt hos hK₀Ω hπ hH1 hZ hz g
    have h2 : Nat.card (conjSub g (piGen π)) = Nat.card (piGen π) :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    omega
  have hO : classicalInvolutionOddCore ↥(piGen π) = ⊥ :=
    TwinSecXg.oddCore_eq_bot_of_normal (hos.piGen_normal hK₀Ω hπ hH1 hz)
      (hos.piGen_le_centralizer hπ hz) hθ
  have hcls : ∀ M ∈ π, M.subgroupOf (piGen π) ∈
      CoreAssembly.conjClass ((conjSub g K₀).subgroupOf (piGen π)) := by
    intro M hM
    obtain ⟨a, ha, hax⟩ := transitive_of_maxOrb hos.graph hπ (conjSub g K₀) hg M hM
    exact subgroupOf_mem_conjClass ha hax
  have hgen : (⨆ K ∈ CoreAssembly.conjClass ((conjSub g K₀).subgroupOf (piGen π)), K) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hle : piGen π ≤ (⨆ K ∈ CoreAssembly.conjClass ((conjSub g K₀).subgroupOf (piGen π)), K :
        Subgroup ↥(piGen π)).map (piGen π).subtype := by
      refine piGen_le fun M hM => ?_
      exact (Subgroup.map_subgroupOf_eq_of_le (le_piGen hM)).symm.le.trans
        (Subgroup.map_mono (le_iSup₂_of_le _ (hcls M hM) le_rfl))
    obtain ⟨y, hy, hyx⟩ := hle x.2
    have : y = x := Subtype.ext hyx
    rwa [this] at hy
  have hl : HasLifts (CoreAssembly.conjClass ((conjSub g K₀).subgroupOf (piGen π))) := by
    have hK₀img : K₀ ∈ conjSub g '' π := hos.mem_conj_image_of_mem hπ hg
    obtain ⟨P, hP, hPK⟩ := hK₀img
    have hK₀g' : conjSub g⁻¹ K₀ ∈ π := by
      rw [← hPK, conjSub_inv_conjSub]
      exact hP
    obtain ⟨a, ha, hax⟩ := transitive_of_maxOrb hos.graph hπ _ hK₀g' (conjSub g K₀) hg
    have hc : conjSub (a * g⁻¹) K₀ = conjSub g K₀ := by
      rw [conjSub_mul, hax]
    have hcX : conjSub (a * g⁻¹) (conjSub g (piGen π)) = piGen π := by
      rw [← conjSub_mul, show a * g⁻¹ * g = a by group]
      exact conjSub_eq_self_of_mem ha
    obtain ⟨hzc, hLc⟩ := isClassicalMember3On_conj_gen (a * g⁻¹) hcX hL
    have hct : a * g⁻¹ * t * (a * g⁻¹)⁻¹ = g * t * g⁻¹ := by
      have h1 := hz.conj (a * g⁻¹)
      rw [hc] at h1
      exact (hw.eq h1).symm
    have hzeq : (⟨a * g⁻¹ * t * (a * g⁻¹)⁻¹, hzc⟩ : ↥(piGen π)) = ⟨g * t * g⁻¹, htX⟩ :=
      Subtype.ext hct
    rw [hzeq] at hLc
    have hle : (conjSub g K₀).subgroupOf (piGen π) ≤ (conjSub (a * g⁻¹) L).subgroupOf (piGen π) := by
      intro x hx
      refine Subgroup.mem_subgroupOf.mpr ?_
      have := conjSub_mono (n := a * g⁻¹) hKL
      rw [hc] at this
      exact this (Subgroup.mem_subgroupOf.mp hx)
    exact hasLifts_conjClass (isUniqueInvolution_subgroupOf hw hKgX) hle hLc
  have hJ' : (conjSub g K').subgroupOf (piGen π) ∈
      twinSet (CoreAssembly.conjClass ((conjSub g K₀).subgroupOf (piGen π)))
        ((conjSub g K₀).subgroupOf (piGen π)) :=
    ⟨hcls _ hK'gπ, ⟨g * t * g⁻¹, htX⟩, isUniqueInvolution_subgroupOf hw hKgX,
      isUniqueInvolution_subgroupOf (hz'.conj g) hK'gX⟩
  have hne' : (conjSub g K').subgroupOf (piGen π) ≠ (conjSub g K₀).subgroupOf (piGen π) :=
    subgroupOf_ne_of_ne hKgX hK'gX (fun h => hne (Frame.conjSub_injective g h))
  have hΩX := hypOmegaGen_conjClass_section hs.hyp hJΩ hKgX
  have h2X : IsPGroup 2 ↥((conjSub g K₀).subgroupOf (piGen π)) :=
    (hs.two _ hJΩ).of_equiv (Subgroup.subgroupOfEquivOfLe hKgX).symm
  have hzJ := isUniqueInvolution_subgroupOf hw hKgX
  exact twinIdent_model1520_of_triality (G := G) (piGen π) (n := n) model1520LieTarget_plus_four
    hCIT hlt hO (J := (conjSub g K₀).subgroupOf (piGen π)) (z := ⟨g * t * g⁻¹, htX⟩) hΩX h2X
    hgen hl hzJ hJ' hne'

end TwinConnT

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
