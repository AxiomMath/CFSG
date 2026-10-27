module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23ExU11

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement



open CFSG.ClassicalInvolution.Balance

section U28

open CFSG.ClassicalInvolution.Q8P.P24 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinLayer (tqMembers exactCore)

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem p23_innerHyp_u (hc : P23Cfg n Y R S t K' W u e g) :
    CFSG.ClassicalInvolution.Q8P.P24.TwinInnerHyp (Om R) (conjSub g (tightCore R)) (conjSub g K') (u * e)
      (g * u * g⁻¹) u (Subgroup.closure ({u * e, u, t} : Set Y)) := by
  classical
  set B := Subgroup.closure ({u * e, u, t} : Set Y) with hBdef
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
  have hBab := B_isElemAbelian hc
  obtain ⟨R₁, R₁', b₁, b', hR₁, hR₁', hRD, hR'D, hcomm, hb₁R, hb'R', ob₁, ob', hub, hne_ue⟩ :=
    e_decomp hc
  have hNe := normalizer_le_centralizer_e hd
  have hR₁e : R₁ ≤ Subgroup.centralizer ({e} : Set Y) := hRD.2.trans hNe
  have hR₁'e : R₁' ≤ Subgroup.centralizer ({e} : Set Y) := hR'D.2.trans hNe
  have hBm : ∀ {a : Y}, a ∈ ({u * e, u, t} : Set Y) → a ∈ B := fun h => Subgroup.subset_closure h
  have hueB : u * e ∈ B := hBm (by simp)
  have huB : u ∈ B := hBm (by simp)
  have htB : t ∈ B := hBm (by simp)
  have hguB := gug_mem_B hc
  have he1 := hd.he1
  have hu1 := hd.hu1
  have hut : u ≠ t := hd.huz
  have hR₁t : ∀ x ∈ R₁, x * t = t * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (le_centralizer_of_unique hz (hR₁.1 hx))
  have hR₁'t : ∀ x ∈ R₁', x * t = t * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (le_centralizer_of_unique hz' (hR₁'.1 hx))
  have hb₁K : b₁ ∈ tightCore R := hR₁.1 hb₁R
  have hb'K : b' ∈ K' := hR₁'.1 hb'R'
  have hgcu := conj_cent_u hc hR₁e hR₁t
  have hgcu' := conj_cent_u hc hR₁'e hR₁'t
  have hJ₁ : conjSub g (tightCore R) ∈ Om R := hΩ.conjInvariant g _ hK
  have hJ₂ : conjSub g K' ∈ Om R := hΩ.conjInvariant g _ hK'Ω
  have hR₃ : IsSylow2In (conjSub g R₁) (conjSub g (tightCore R)) := hR₁.conj g
  have hR₃' : IsSylow2In (conjSub g R₁') (conjSub g K') := hR₁'.conj g
  have hτ₁ : IsUniqueInvolution (conjSub g (tightCore R)) (u * e) := by
    rw [← hd.hgt]; exact hz.conj g
  have hτ₂ : IsUniqueInvolution (conjSub g K') (u * e) := by
    rw [← hd.hgt]; exact hz'.conj g
  have hgug : g * u * g⁻¹ = (g * b₁ * g⁻¹) * (g * b' * g⁻¹) := by
    rw [hub]; group
  have hgu1 : g * u * g⁻¹ ≠ 1 := fun h => hu1 (by
    calc u = g⁻¹ * (g * u * g⁻¹) * g := by group
      _ = g⁻¹ * 1 * g := by rw [h]
      _ = 1 := by group)
  have hgue : g * u * g⁻¹ ≠ u * e := by
    intro h
    apply hut
    rw [← hd.hgt] at h
    calc u = g⁻¹ * (g * u * g⁻¹) * g := by group
      _ = g⁻¹ * (g * t * g⁻¹) * g := by rw [h]
      _ = t := by group
  have hJ₁u : conjSub g (tightCore R) ∈ tqMembers3 (Om R) u :=
    ⟨hJ₁, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJ₁ ⟨conjSub g R₁, hR₃, hgcu⟩⟩
  have hJ₂u : conjSub g K' ∈ tqMembers3 (Om R) u :=
    ⟨hJ₂, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJ₂ ⟨conjSub g R₁', hR₃', hgcu'⟩⟩
  have hne₂ : conjSub g K' ≠ conjSub g (tightCore R) := by
    intro he
    apply hc.std.hne
    have := congrArg (conjSub g⁻¹) he
    rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this
  have hgg : (g * u * g⁻¹) * (g * u * g⁻¹) = 1 := by
    calc (g * u * g⁻¹) * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
      _ = 1 := by rw [hd.hu2]; group
  have hBu : B = Subgroup.closure ({u * e, g * u * g⁻¹, u} : Set Y) := by
    refine le_antisymm ((Subgroup.closure_le _).mpr ?_) ((Subgroup.closure_le _).mpr ?_)
    · intro a ha
      rcases ha with rfl | rfl | rfl
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
      · exact t_mem_closure_gug hc
    · intro a ha
      rcases ha with rfl | rfl | rfl
      · exact hueB
      · exact hguB
      · exact huB
  have hgb₁u : g * b₁ * g⁻¹ ∈ TwinLayer.exactCore u (conjSub g (tightCore R)) :=
    le_tightCore_of_isPGroup (le_inf hR₃.1 hgcu) hR₃.2.1 (conj_mem_conjSub hb₁R)
  have hgb'u : g * b' * g⁻¹ ∈ TwinLayer.exactCore u (conjSub g K') :=
    le_tightCore_of_isPGroup (le_inf hR₃'.1 hgcu') hR₃'.2.1 (conj_mem_conjSub hb'R')
  exact ⟨hJ₁, hJ₂, hne₂, hτ₁, hτ₂, hJ₁u, hJ₂u, hBab, hueB, hguB, huB, hBu, hu1,
    fun h => he1 (by simpa using h), hgu1, hgue, hgg,
    by rw [hgug]; exact Subgroup.mul_mem_sup hgb₁u hgb'u⟩

end U28

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
