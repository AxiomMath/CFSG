module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6fL2
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6dOdd

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6f

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
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6e
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE
open scoped commutatorElement


local notation "Ω[" R "]" => CoreAssembly.conjClass (tightCore R)

theorem conjSub_ae6L_le {Y : Type} [Group Y] {Ω : Set (Subgroup Y)} (hinv : ConjInvariant Ω)
    {t τ x c : Y} (ht : c * t * c⁻¹ = t) (hτ : c * τ * c⁻¹ = τ) (hx : c * x * c⁻¹ = x) :
    conjSub c (ae6L Ω t τ x) ≤ ae6L Ω t τ x := by
  unfold ae6L
  rw [conjSub_iSup₂]
  refine iSup₂_le fun J hJ => ?_
  have key : ∀ {s : Y}, c * s * c⁻¹ = s → J ∈ ae6Vc Ω s → conjSub c J ∈ ae6Vc Ω s := by
    intro s hs hJs
    refine ⟨hinv c J hJs.1, ?_⟩
    have := hJs.2.conj c
    rwa [hs] at this
  rcases hJ with (hJ | hJ) | hJ
  · exact le_iSup₂_of_le (f := fun J (_ : J ∈ ae6Vc Ω t ∪ ae6Vc Ω τ ∪ ae6Vc Ω x) => J)
      (conjSub c J) (Or.inl (Or.inl (key ht hJ))) le_rfl
  · exact le_iSup₂_of_le (f := fun J (_ : J ∈ ae6Vc Ω t ∪ ae6Vc Ω τ ∪ ae6Vc Ω x) => J)
      (conjSub c J) (Or.inl (Or.inr (key hτ hJ))) le_rfl
  · exact le_iSup₂_of_le (f := fun J (_ : J ∈ ae6Vc Ω t ∪ ae6Vc Ω τ ∪ ae6Vc Ω x) => J)
      (conjSub c J) (Or.inr (key hx hJ)) le_rfl

section Datum

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y} {a₁ a₂ a₃ a₄ y h : Y}
  (Z : LCtx n R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y h)

include Z in
theorem oddCoreOf_L_eq_bot : oddCoreOf (ae6L Ω[R] t (tauE t y) (xE t y h)) = ⊥ := by
  classical
  have hd := Z.C.H.ex.1.datum
  have hinv := conjInvariant_conjClass (tightCore R)
  set L : Subgroup Y := ae6L Ω[R] t (tauE t y) (xE t y h) with hLdef
  set N : Subgroup Y := oddCoreOf L with hN
  have hNodd : Odd (Nat.card N) := Balance.odd_card_oddCoreIn L
  have hNL : N ≤ L := oddCoreOf_le_self L
  have hNnormL : ∀ g ∈ L, ∀ x ∈ N, g * x * g⁻¹ ∈ N := fun g hg x hx =>
    Balance.conj_mem_oddCoreIn hg hx
  have hE2 : IsPGroup 2 ↥(e3 t y h) := A6d.isPGroup_two_of_sq_eq_one Z.hE.2
  have hNE : ∀ x ∈ N, ∀ e ∈ e3 t y h, x * e = e * x := fun x hx =>
    A6b.comm_of_odd_of_le_two hNodd hE2 le_rfl hx
      (fun q hq => (Subgroup.mem_normalizer_iff.mp (L_le_normalizer Z (hNL hx)) q).mp hq)
      (fun j hj n hn => hNnormL j (E3_le_L Z hj) n hn)
  have hxt : ∀ x ∈ N, x * t * x⁻¹ = t := fun x hx => by
    rw [hNE x hx t (t_mem_e3 t y h), mul_inv_cancel_right]
  have hP2 : IsPGroup 2 ↥(ae6P Ω[R] t) := isPGroup_ae6P Z.C
  have hNP : ∀ x ∈ N, ∀ p ∈ ae6P Ω[R] t, x * p = p * x := fun x hx =>
    A6b.comm_of_odd_of_le_two hNodd hP2 le_rfl hx
      (fun q hq => A6Hx.conj_mem_ae6P hinv (hxt x hx) hq)
      (fun j hj n hn => hNnormL j (ae6P_le_L_t Z hj) n hn)
  set Ct : Subgroup Y := Subgroup.centralizer ({t} : Set Y) with hCt
  set P : Subgroup Y := ae6P Ω[R] t with hP
  set C₁ : Subgroup Y := Ct ⊓ Subgroup.centralizer (P : Set Y) with hC₁
  have hNC₁ : N ≤ C₁ := by
    intro x hx
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr (hNE x hx t (t_mem_e3 t y h)),
      Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro p hp
    exact (hNP x hx p hp).symm
  have hC₁norm : ∀ g ∈ Ct, conjSub g C₁ = C₁ := by
    have hle : ∀ g ∈ Ct, conjSub g C₁ ≤ C₁ := by
      intro g hg c hc
      rw [mem_conjSub_iff] at hc
      have hgi : g⁻¹ ∈ Ct := Ct.inv_mem hg
      have hgit : g⁻¹ * t * g⁻¹⁻¹ = t := by
        have := Subgroup.mem_centralizer_singleton_iff.mp hgi
        rw [this, mul_inv_cancel_right]
      have hcCt : c ∈ Ct := by
        have : g * (g⁻¹ * c * g) * g⁻¹ ∈ Ct := Ct.mul_mem (Ct.mul_mem hg hc.1) hgi
        simpa [mul_assoc] using this
      refine ⟨hcCt, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro p hp
      have hp' : g⁻¹ * p * g ∈ P := by
        have := A6Hx.conj_mem_ae6P hinv hgit hp
        simpa using this
      have h1 := Subgroup.mem_centralizer_iff.mp hc.2 _ hp'
      calc p * c = g * ((g⁻¹ * p * g) * (g⁻¹ * c * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * c * g) * (g⁻¹ * p * g)) * g⁻¹ := by rw [h1]
        _ = c * p := by group
    intro g hg
    refine le_antisymm (hle g hg) ?_
    have h2 := conjSub_mono (n := g) (hle g⁻¹ (Ct.inv_mem hg))
    rwa [conjSub_conjSub_inv] at h2
  have hC₁L : ∀ c ∈ C₁, conjSub c L = L := by
    have hle : ∀ c ∈ C₁, conjSub c L ≤ L := by
      intro c hc
      have hc1 : c * t * c⁻¹ = t := by
        have := Subgroup.mem_centralizer_singleton_iff.mp hc.1
        rw [this, mul_inv_cancel_right]
      have hcP : ∀ p ∈ P, c * p * c⁻¹ = p := fun p hp => by
        have := Subgroup.mem_centralizer_iff.mp hc.2 p hp
        rw [← this, mul_inv_cancel_right]
      have hτP : tauE t y ∈ P := (A6Hx.t_tau_mem_ae6P Z.C.H Z.C.fr).2
      have hxP : xE t y h ∈ P := A6Hx.conj_mem_ae6P hinv
        (by have := Subgroup.mem_centralizer_singleton_iff.mp Z.hx.1; rw [this, mul_inv_cancel_right])
        hτP
      exact conjSub_ae6L_le hinv hc1 (hcP _ hτP) (hcP _ hxP)
    intro c hc
    refine le_antisymm (hle c hc) ?_
    have hci : c⁻¹ ∈ C₁ := C₁.inv_mem hc
    have h2 := conjSub_mono (n := c) (hle c⁻¹ hci)
    rwa [conjSub_conjSub_inv] at h2
  have hNnormC₁ : ∀ g ∈ C₁, conjSub g N = N := by
    intro g hg
    rw [hN, ← AscE184Sect.oddCoreOf_conjSub, hC₁L g hg]
  have hNn : C₁ ≤ Subgroup.normalizer (N : Set Y) := fun g hg =>
    Asc77.mem_normalizer_iff_conjSub_eq.mpr (hNnormC₁ g hg)
  have hNO : N ≤ oddCoreOf C₁ := Balance.le_oddCoreIn_of_normalizes hNC₁ hNn hNodd
  have hOle : oddCoreOf C₁ ≤ oddCoreOf Ct :=
    TwinDisc.oddCoreOf_le_of_normalizes inf_le_left hC₁norm
  have hOCt : oddCoreOf Ct = ⊥ := by
    show (classicalInvolutionOddCore ↥Ct).map Ct.subtype = ⊥
    rw [Z.C.H.oddC]
    exact Subgroup.map_bot _
  exact le_antisymm ((hNO.trans hOle).trans hOCt.le) bot_le

end Datum

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6f
