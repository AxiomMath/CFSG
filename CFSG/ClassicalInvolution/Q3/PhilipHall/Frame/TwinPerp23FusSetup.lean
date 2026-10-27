module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23ExU16

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Fus

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

section Twins

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

structure LayerTwins (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (c : Y) (J J' Q Q' : Subgroup Y)
    (w : Y) : Prop where
  hc2 : c * c = 1
  hc1 : c ≠ 1
  hJ : J ∈ tqMembers3 (Om R) c
  hJ' : J' ∈ tqMembers3 (Om R) c
  hne : J ≠ J'
  hw : IsUniqueInvolution J w
  hw' : IsUniqueInvolution J' w
  hQ : IsSylow2In Q J
  hQ' : IsSylow2In Q' J'
  hQc : Q ≤ Subgroup.centralizer ({c} : Set Y)
  hQ'c : Q' ≤ Subgroup.centralizer ({c} : Set Y)
  hcomm : Commutes Q Q'

theorem layerTwins_both (hc : P23Cfg n Y R S t K' W u e g) :
    ∃ Q Q' : Subgroup Y,
      LayerTwins Y R u (conjSub g (tightCore R)) (conjSub g K') Q Q' (u * e) ∧
      LayerTwins Y R e (conjSub g (tightCore R)) (conjSub g K') Q Q' (u * e) := by
  classical
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hK'Ω : K' ∈ Om R := hc.std.hK'.1
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  have h2 : ∀ M ∈ Om R, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hC.datum.twoGroup)
  obtain ⟨R₁, R₁', b₁, b', hR₁, hR₁', hRD, hR'D, hcomm, hb₁R, hb'R', ob₁, ob', hub, hne_ue⟩ :=
    e_decomp hc
  have hNe := normalizer_le_centralizer_e hd
  have hR₁e : R₁ ≤ Subgroup.centralizer ({e} : Set Y) := hRD.2.trans hNe
  have hR₁'e : R₁' ≤ Subgroup.centralizer ({e} : Set Y) := hR'D.2.trans hNe
  have hR₁t : ∀ x ∈ R₁, x * t = t * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (le_centralizer_of_unique hz (hR₁.1 hx))
  have hR₁'t : ∀ x ∈ R₁', x * t = t * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (le_centralizer_of_unique hz' (hR₁'.1 hx))
  have hgcu := conj_cent_u hc hR₁e hR₁t
  have hgcu' := conj_cent_u hc hR₁'e hR₁'t
  have hgeg := geg_eq hc
  have hgcE : ∀ {T : Subgroup Y}, T ≤ Subgroup.centralizer ({e} : Set Y) →
      conjSub g T ≤ Subgroup.centralizer ({e} : Set Y) := by
    intro T hT x hx
    have hy : g⁻¹ * x * g ∈ T := mem_conjSub_iff.mp hx
    have hye : (g⁻¹ * x * g) * e = e * (g⁻¹ * x * g) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hT hy)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * e = x * (g * e * g⁻¹) := by rw [hgeg]
      _ = g * ((g⁻¹ * x * g) * e) * g⁻¹ := by group
      _ = g * (e * (g⁻¹ * x * g)) * g⁻¹ := by rw [hye]
      _ = (g * e * g⁻¹) * x := by group
      _ = e * x := by rw [hgeg]
  have hgce := hgcE hR₁e
  have hgce' := hgcE hR₁'e
  have hJ₁ : conjSub g (tightCore R) ∈ Om R := hΩ.conjInvariant g _ hK
  have hJ₂ : conjSub g K' ∈ Om R := hΩ.conjInvariant g _ hK'Ω
  have hR₃ : IsSylow2In (conjSub g R₁) (conjSub g (tightCore R)) := hR₁.conj g
  have hR₃' : IsSylow2In (conjSub g R₁') (conjSub g K') := hR₁'.conj g
  have hτ₁ : IsUniqueInvolution (conjSub g (tightCore R)) (u * e) := by
    rw [← hd.hgt]; exact hz.conj g
  have hτ₂ : IsUniqueInvolution (conjSub g K') (u * e) := by
    rw [← hd.hgt]; exact hz'.conj g
  have hne₂ : conjSub g (tightCore R) ≠ conjSub g K' := by
    intro he
    apply hc.std.hne
    have := congrArg (conjSub g⁻¹) he
    rw [conjSub_inv_conjSub, conjSub_inv_conjSub] at this
    exact this.symm
  have hcommg : Commutes (conjSub g R₁) (conjSub g R₁') := hcomm.conjSub g
  refine ⟨conjSub g R₁, conjSub g R₁', ⟨hd.hu2, hd.hu1, ⟨hJ₁, ?_⟩, ⟨hJ₂, ?_⟩, hne₂, hτ₁, hτ₂, hR₃, hR₃',
    hgcu, hgcu', hcommg⟩, ⟨hd.he2, hd.he1, ⟨hJ₁, ?_⟩, ⟨hJ₂, ?_⟩, hne₂, hτ₁, hτ₂, hR₃, hR₃', hgce,
    hgce', hcommg⟩⟩
  · exact TwinADescent3.mem_tq_of_sylCent hΩ h2 hJ₁ ⟨conjSub g R₁, hR₃, hgcu⟩
  · exact TwinADescent3.mem_tq_of_sylCent hΩ h2 hJ₂ ⟨conjSub g R₁', hR₃', hgcu'⟩
  · exact TwinADescent3.mem_tq_of_sylCent hΩ h2 hJ₁ ⟨conjSub g R₁, hR₃, hgce⟩
  · exact TwinADescent3.mem_tq_of_sylCent hΩ h2 hJ₂ ⟨conjSub g R₁', hR₃', hgce'⟩

end Twins

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Fus
