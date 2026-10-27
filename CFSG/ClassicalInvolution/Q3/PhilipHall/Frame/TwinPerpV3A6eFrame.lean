module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6eWt

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

namespace A6eCtx

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y} {a₁ a₂ a₃ a₄ y : Y}
  (C : A6eCtx n R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y)

include C in
theorem conj_W_mem {c : Y} (hc : c * t * c⁻¹ = t) :
    conjSub c W ∈ WSet Ω[R] ∧ t ∈ conjSub c W := by
  have hΩ : HypOmegaGen Ω[R] := (CoreData.of_S C.H.ex.1.perp.core).hyp
  have htW : t ∈ W := by
    have := C.H.ex.1.datum.sq₁
    rw [← this]
    exact W.mul_mem C.H.hu₁ C.H.hu₁
  refine ⟨Asc77.WSet.conj hΩ.conjInvariant C.H.hW c, ?_⟩
  have := conj_mem_conjSub (n := c) htW
  rwa [hc] at this

include C in
theorem frame_at {W' : Subgroup Y} (hW' : W' ∈ WSet Ω[R]) (htW' : t ∈ W') :
    ∃ b₁ b₂ b₃ b₄ y' : Y, Frame4 K K' K₃ K₄ W' t b₁ b₂ b₃ b₄ y' ∧
      y' ∈ Subgroup.centralizer ({b₁ * b₂} : Set Y) ∧ y' * t * y'⁻¹ ≠ t := by
  have hStd := C.H.ex.1
  have hF := C.H.ex.2.1
  have hd := hStd.datum
  have hP := (CoreData.of_S hStd.perp.core).partIHypG
  have hperp := kPerp_datum hStd.perp hd.mem hd.hz
  obtain ⟨b₁, b₂, b₃, b₄, y', h1, o1, h2, o2, h3, o3, h4, o4, -, -, -, -, -, -, hy, hyne,
    hb₁, hb₂, hb₃, hb₄, hyc, -⟩ :=
    exists_fuse_cent2W hP hd hperp hF.1 hF.2.1 hF.2.2.1 hF.2.2.2.1 hStd.wyl hW' htW'
  exact ⟨b₁, b₂, b₃, b₄, y', ⟨⟨h1, hb₁⟩, ⟨h2, hb₂⟩, ⟨h3, hb₃⟩, ⟨h4, hb₄⟩, o1, o2, o3, o4, hy⟩,
    hyc, hyne⟩

include C in
theorem rot_frame {W' : Subgroup Y} (hW' : W' ∈ WSet Ω[R]) (htW' : t ∈ W') :
    ∃ c₁ c₂ y'' : Y, c₁ ∈ K₃ ⊓ W' ∧ orderOf c₁ = 4 ∧ c₂ ∈ K₄ ⊓ W' ∧ orderOf c₂ = 4 ∧
      y'' ∈ Subgroup.centralizer ({c₁ * c₂} : Set Y) ∧ y'' * t * y''⁻¹ ∈ W' ∧
      y'' * t * y''⁻¹ ≠ t := by
  have hStd := C.H.ex.1
  have hF := C.H.ex.2.1
  have hd := hStd.datum
  have hP := (CoreData.of_S hStd.perp.core).partIHypG
  have h2g : ∀ J ∈ Ω[R], IsPGroup 2 ↥J := C.H.ex.2.2.2.1
  obtain ⟨b₁, b₂, b₃, b₄, y', fr', -, -⟩ := C.frame_at hW' htW'
  obtain ⟨-, -, -, -, -, hK₃K₄⟩ := C.twins_ne
  have hL₃ := C.hK₃t
  have hL₄ := C.hK₄t
  have hcomm : Commutes K₃ K₄ := fun x hx z hz => C.twin_comm hL₃ hL₄ hK₃K₄ x hx z hz
  have hsyl3 : IsSylow2In K₃ K₃ :=
    ⟨le_rfl, h2g K₃ hd.hK₃.1, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
  have hsyl4 : IsSylow2In K₄ K₄ :=
    ⟨le_rfl, h2g K₄ hF.1.1, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
  obtain ⟨L₃, w, hd''⟩ := hd.exists_datum_of_pair hL₃ hL₄ (Ne.symm hK₃K₄) hsyl3 hsyl4 hcomm
    fr'.h₃.1 fr'.h₄.1 fr'.o₃ fr'.o₄
  have htw3 : twinSet Ω[R] K₃ = twinSet Ω[R] K := twinSet_eq_of_mem_twinSet hd.hz hL₃
  have hL₃K : L₃ ∈ twinSet Ω[R] K := htw3 ▸ hd''.hK₃
  have hperp'' := kPerp_datum hStd.perp hd.hK₃.1 hd.hzK₃
  have key : ∀ L₄ : Subgroup Y, L₄ ∈ twinSet Ω[R] K → L₄ ≠ K₃ → L₄ ≠ K₄ → L₄ ≠ L₃ →
      ∃ c₁ c₂ y'' : Y, c₁ ∈ K₃ ⊓ W' ∧ orderOf c₁ = 4 ∧ c₂ ∈ K₄ ⊓ W' ∧ orderOf c₂ = 4 ∧
        y'' ∈ Subgroup.centralizer ({c₁ * c₂} : Set Y) ∧ y'' * t * y''⁻¹ ∈ W' ∧
        y'' * t * y''⁻¹ ≠ t := by
    intro L₄ hL₄K h41 h42 h43
    obtain ⟨a₁, a₂, a₃, a₄, y'', h1, o1, h2, o2, h3, o3, h4, o4, -, -, -, -, -, -, hy, hyne,
      hW₁, hW₂, hW₃, hW₄, hyc, -⟩ :=
      exists_fuse_cent2W hP hd'' hperp'' (htw3 ▸ hL₄K) h41 h42 h43 hStd.wyl hW' htW'
    refine ⟨a₁, a₂, y'', ⟨h1, hW₁⟩, o1, ⟨h2, hW₂⟩, o2, hyc, ?_, hyne⟩
    rw [hy]
    exact W'.mul_mem (W'.mul_mem (W'.mul_mem hW₁ hW₂) hW₃) hW₄
  rcases twinSet_four hStd hF L₃ hL₃K with h | h | h | h
  · exact key K' C.hK't C.twins_ne.2.2.2.1 C.twins_ne.2.2.2.2.1 (by
      rw [h]; exact C.twins_ne.1.symm)
  · exact key K C.hKt C.twins_ne.2.1 C.twins_ne.2.2.1 (by
      rw [h]; exact C.twins_ne.1)
  · exact absurd h hd''.hK₃K
  · exact absurd h hd''.hK₃K'

end A6eCtx

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6e
