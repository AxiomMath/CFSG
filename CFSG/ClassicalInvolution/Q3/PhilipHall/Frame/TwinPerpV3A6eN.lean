module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6eFrame
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6bMain
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescent3Fam

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6e

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE
open scoped commutatorElement


local notation "Ω[" R "]" => CoreAssembly.conjClass (tightCore R)

theorem conjSub_pCoreOf {Y : Type} [Group Y] (g : Y) (X : Subgroup Y) :
    conjSub g (pCoreOf 2 X) = pCoreOf 2 (conjSub g X) := by
  unfold conjSub
  exact (CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulAut.conj g) X).symm

theorem conjSub_rLayer_le {Y : Type} [Group Y] [Finite Y] {Ω : Set (Subgroup Y)} (hΩ : HypOmegaGen Ω)
    (c g : Y) : conjSub g (rLayer Ω c) ≤ rLayer Ω (g * c * g⁻¹) := by
  unfold rLayer
  show Subgroup.map (MulAut.conj g).toMonoidHom _ ≤ _
  rw [Subgroup.map_iSup]
  refine iSup_le fun R => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hR => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hRx => ?_
  have hR' : conjSub g R ∈ RSet Ω := Q3CL.Thompson.conjSub_mem_RSet hΩ hR g
  have hC : conjSub g R ≤ Subgroup.centralizer ({g * c * g⁻¹} : Set Y) := by
    intro x hx
    rw [mem_conjSub_iff] at hx
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hRx hx)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * (g * c * g⁻¹) = g * ((g⁻¹ * x * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
      _ = (g * c * g⁻¹) * x := by group
  exact le_iSup₂_of_le (conjSub g R) hR' (le_iSup_of_le hC le_rfl)

theorem conjSub_rLayer_eq {Y : Type} [Group Y] [Finite Y] {Ω : Set (Subgroup Y)} (hΩ : HypOmegaGen Ω)
    (c g : Y) : conjSub g (rLayer Ω c) = rLayer Ω (g * c * g⁻¹) := by
  refine le_antisymm (conjSub_rLayer_le hΩ c g) ?_
  have h := conjSub_mono (n := g) (conjSub_rLayer_le hΩ (g * c * g⁻¹) g⁻¹)
  rw [conjSub_conjSub_inv] at h
  have e : g⁻¹ * (g * c * g⁻¹) * g⁻¹⁻¹ = c := by group
  rw [e] at h
  exact h

namespace A6eCtx

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y} {a₁ a₂ a₃ a₄ y : Y}
  (C : A6eCtx n R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y)

include C in
theorem ae6E_inv_mem : ∀ J ∈ tqMembers3 Ω[R] (u₁ * u₂), ∀ s : Y, IsUniqueInvolution J s →
    s ∈ ae6E Ω[R] (u₁ * u₂) := by
  obtain ⟨hStd, hF, hα, h2g, -⟩ := C.H.ex
  have hd := hStd.datum
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := hd.hyp
  have hc2' : (u₁ * u₂) * (u₁ * u₂) = 1 := hd.sq_12
  have hc2 : IsPGroup 2 (Subgroup.zpowers (u₁ * u₂)) :=
    Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hc2'
  have hO := A6b.oddCoreOf_rLayer_eq_bot hStd hF hα h2g C.H.oddC
  have hS := TwinPerpV3.layer_q8Section hStd.perp hc2'
  obtain ⟨I⟩ := C.H.ae6
  obtain ⟨hmem3, hmem4⟩ := TwinPerpV3.v3_tq_members hStd hF
  have hz4 : IsUniqueInvolution K₄ t := TwinSecXg.isUniqueInvolution_of_mem_twinSet hd.hz hF.1
  obtain ⟨_, _, hU3⟩ := TwinDisc.isUniqueInvolution_secImg hΩ hc2 hmem3 hd.hzK₃
  obtain ⟨_, _, hU4⟩ := TwinDisc.isUniqueInvolution_secImg hΩ hc2 hmem4 hz4
  have hH : TL4.AECoverHyp I :=
    A6b.aeCoverHyp_of_twins (by norm_num) (by norm_num) hS I (TwinDisc.secImg_mem_secFam hmem3)
      (TwinDisc.secImg_mem_secFam hmem4) (Ne.symm (TwinPerpV3.v3_secImg_ne hStd hF)) hU3 hU4
  obtain ⟨hK₃Y, hK₄Y⟩ := A6b.members_le_rLayer hStd hF h2g
  have hYn : conjSub y (rLayer (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) =
      rLayer (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) :=
    TwinMu.Pf3.conjSub_rLayer hΩ C.fr.hc
  have htY : t ∈ rLayer (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) := hK₃Y hd.hzK₃.mem
  have hτY : y * t * y⁻¹ ∈ rLayer (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) := by
    have := conj_mem_conjSub (n := y) htY
    rwa [hYn] at this
  have hcY : u₁ * u₂ ∈ rLayer (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) := by
    have e : u₁ * u₂ = (y * t * y⁻¹) * (a₃ * a₄)⁻¹ := by
      rw [C.fr.hy, ← C.fr.hu]
      group
    have h := Subgroup.mul_mem _ hτY
      (Subgroup.inv_mem _ (Subgroup.mul_mem _ (hK₃Y C.fr.h₃.1) (hK₄Y C.fr.h₄.1)))
    rwa [← e] at h
  obtain ⟨-, -, -, hinv⟩ := A6b.layer_pCoreOf hΩ hc2 h2g hO hS I hH hcY hd.mul_ne_one
  exact hinv

include C in
theorem t_mem_E_conj (i : Y) {J : Subgroup Y} (hJ : J ∈ twinSet Ω[R] K)
    (hJC : J ≤ Subgroup.centralizer ({i * (u₁ * u₂) * i⁻¹} : Set Y)) :
    t ∈ pCoreOf 2 (rLayer Ω[R] (i * (u₁ * u₂) * i⁻¹)) := by
  have hStd := C.H.ex.1
  have hΩ : HypOmegaGen Ω[R] := (CoreData.of_S hStd.perp.core).hyp
  have h2g : ∀ J ∈ Ω[R], IsPGroup 2 ↥J := C.H.ex.2.2.2.1
  set J' := conjSub i⁻¹ J with hJ'
  have hJ'Ω : J' ∈ Ω[R] := hΩ.conjInvariant i⁻¹ J hJ.1
  have hJ'C : J' ≤ Subgroup.centralizer ({u₁ * u₂} : Set Y) := by
    intro x hx
    rw [hJ', mem_conjSub_iff] at hx
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hJC hx)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have e : i⁻¹⁻¹ * x * i⁻¹ = i * x * i⁻¹ := by group
    rw [e] at hx h1
    calc x * (u₁ * u₂) = i⁻¹ * ((i * x * i⁻¹) * (i * (u₁ * u₂) * i⁻¹)) * i := by group
      _ = i⁻¹ * ((i * (u₁ * u₂) * i⁻¹) * (i * x * i⁻¹)) * i := by rw [h1]
      _ = (u₁ * u₂) * x := by group
  have hq : J' ∈ tqMembers3 Ω[R] (u₁ * u₂) := by
    refine ⟨hJ'Ω, ?_⟩
    refine TwinADescent3.mem_tq_of_sylCent hΩ (fun M hM => (h2g M hM).to_quotient _) hJ'Ω
      ⟨J', ⟨le_rfl, h2g J' hJ'Ω, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩, hJ'C⟩
  have hs : IsUniqueInvolution J' (i⁻¹ * t * i⁻¹⁻¹) := (C.uniq hJ).conj i⁻¹
  have hE := C.ae6E_inv_mem J' hq _ hs
  have h1 := conj_mem_conjSub (n := i) hE
  have e : i * (i⁻¹ * t * i⁻¹⁻¹) * i⁻¹ = t := by group
  rw [e] at h1
  unfold ae6E at h1
  rw [conjSub_pCoreOf, conjSub_rLayer_eq hΩ] at h1
  exact h1

include C in
theorem fuse_mem_D {i : Y} (hi : i ∈ C.I) {J : Subgroup Y} (hJ : J ∈ twinSet Ω[R] K)
    (hJC : J ≤ Subgroup.centralizer ({i * (u₁ * u₂) * i⁻¹} : Set Y)) {y'' : Y}
    (hy'' : y'' ∈ Subgroup.centralizer ({i * (u₁ * u₂) * i⁻¹} : Set Y)) :
    y'' * t * y''⁻¹ ∈ C.D := by
  have hStd := C.H.ex.1
  have hΩ : HypOmegaGen Ω[R] := (CoreData.of_S hStd.perp.core).hyp
  have ht := C.t_mem_E_conj i hJ hJC
  have hyN : y'' ∈ Subgroup.normalizer
      (rLayer Ω[R] (i * (u₁ * u₂) * i⁻¹) : Set Y) :=
    mem_normalizer_iff_conjSub_eq.mpr (TwinMu.Pf3.conjSub_rLayer hΩ hy'')
  have h2 := TwinThin.pCoreOf_conj_mem hyN ht
  have h3 : pCoreOf 2 (rLayer Ω[R] (i * (u₁ * u₂) * i⁻¹)) ≤ C.D := by
    have e : pCoreOf 2 (rLayer Ω[R] (i * (u₁ * u₂) * i⁻¹)) = conjSub i (ae6E Ω[R] (u₁ * u₂)) := by
      unfold ae6E
      rw [conjSub_pCoreOf, conjSub_rLayer_eq hΩ]
    rw [e]
    rintro _ ⟨x, hx, rfl⟩
    exact C.P.conj_mem_D hi (ae6E_le_ae6D _ _ _ hx)
  exact h3 h2

end A6eCtx

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6e
