module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6fL1
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6dMain

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

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y} {a₁ a₂ a₃ a₄ y h : Y}
  (Z : LCtx n R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y h)

include Z in
theorem member_conj_of_inv_mem_E3 {J : Subgroup Y} (hJ : J ∈ Ω[R]) {c : Y}
    (hc : IsUniqueInvolution J c) (hcE : c ∈ e3 t y h) :
    ∃ ℓ ∈ ae6L Ω[R] t (tauE t y) (xE t y h), conjSub ℓ⁻¹ J ∈ ae6Vc Ω[R] t := by
  obtain ⟨ℓ, hℓ, hℓc⟩ := exists_conj_t_of_mem_E3 Z hcE hc.ne_one
  refine ⟨ℓ, hℓ, conjInvariant_conjClass (tightCore R) ℓ⁻¹ J hJ, ?_⟩
  have h1 := hc.conj ℓ⁻¹
  have e : ℓ⁻¹ * c * ℓ⁻¹⁻¹ = t := by rw [← hℓc]; group
  rwa [e] at h1

include Z in
theorem le_L_of_inv_mem_E3 {J : Subgroup Y} (hJ : J ∈ Ω[R]) {c : Y} (hc : IsUniqueInvolution J c)
    (hcE : c ∈ e3 t y h) : J ≤ ae6L Ω[R] t (tauE t y) (xE t y h) := by
  obtain ⟨ℓ, hℓ, hJ'⟩ := member_conj_of_inv_mem_E3 Z hJ hc hcE
  have h1 : conjSub ℓ⁻¹ J ≤ ae6L Ω[R] t (tauE t y) (xE t y h) :=
    (A6Hx.le_ae6P hJ'.1 hJ'.2).trans (ae6P_le_L_t Z)
  calc J = conjSub ℓ (conjSub ℓ⁻¹ J) := (conjSub_conjSub_inv ℓ J).symm
    _ ≤ conjSub ℓ (ae6L Ω[R] t (tauE t y) (xE t y h)) := conjSub_mono (n := ℓ) h1
    _ = ae6L Ω[R] t (tauE t y) (xE t y h) := conjSub_eq_self_of_mem hℓ

include Z in
theorem MGrp_le_L : MGrp Ω[R] W ≤ ae6L Ω[R] t (tauE t y) (xE t y h) := by
  have hΩ := A6d.hypOf Z.C.H
  have h2g := A6d.h2Of Z.C.H
  have hd := Z.C.H.ex.1.datum
  refine iSup₂_le fun R' hR' => ?_
  have hR'Ω : R' ∈ Ω[R] := by
    have := hR'.1
    rwa [rSet_eq_of_isPGroup h2g] at this
  obtain ⟨⟨zR, hzR⟩, -⟩ := hΩ.omega1 R' hR'Ω
  have hsyl : IsSylow2In R' R' := ⟨le_rfl, h2g R' hR'Ω, fun V' hV' _ h => le_antisymm hV' h⟩
  have hzW : zR ∈ W :=
    (Q3CL.Thompson.uniqueInvolution_mem_W hΩ Z.C.H.hW hR'Ω hR' hsyl hzR).2
  have htr : ∀ K₁ ∈ Ω[R], ∀ J ∈ Ω[R], ∃ x : Y, conjSub x K₁ = J := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact ⟨b * a⁻¹, by rw [conjSub_mul, conjSub_inv_conjSub]⟩
  obtain ⟨g, hg⟩ := htr K hd.mem R' hR'Ω
  have hzg : zR = g * t * g⁻¹ := by
    have := A6jB.isUniqueInvolution_conjSub hd.hz g
    rw [hg] at this
    exact hzR.eq this
  have hcases := A6Wt.mem_tG_W Z.C.H Z.C.fr hzW hzg.symm
  have hzE : zR ∈ e3 t y h := by
    rcases hcases with h' | h' | h'
    · rw [h']; exact t_mem_e3 t y h
    · rw [h']; exact tau_mem_e3 t y h
    · rw [h']; exact (e3 t y h).mul_mem (t_mem_e3 t y h) (tau_mem_e3 t y h)
  exact le_L_of_inv_mem_E3 Z hR'Ω hzR hzE

include Z in
theorem mem_KL_of_inv_mem_E3 {J : Subgroup Y} (hJ : J ∈ Ω[R]) {c : Y} (hc : IsUniqueInvolution J c)
    (hcE : c ∈ e3 t y h) : J ∈ ae6ConjIn (ae6L Ω[R] t (tauE t y) (xE t y h)) K := by
  obtain ⟨ℓ, hℓ, hJ'⟩ := member_conj_of_inv_mem_E3 Z hJ hc hcE
  obtain ⟨m, hm, hmK⟩ := A6jB.exists_M_conj_of_twin Z.C.H (ae6Vc_subset_twinSet Z.C hJ')
  refine ⟨ℓ * m, (ae6L Ω[R] t (tauE t y) (xE t y h)).mul_mem hℓ (MGrp_le_L Z hm), ?_⟩
  rw [conjSub_mul, hmK, conjSub_conjSub_inv]

include Z in
theorem K_le_L : K ≤ ae6L Ω[R] t (tauE t y) (xE t y h) :=
  (A6Hx.le_ae6P Z.C.H.ex.1.datum.mem Z.C.H.ex.1.datum.hz).trans (ae6P_le_L_t Z)

include Z in
theorem pSpan_KL :
    pSpan (ae6ConjIn (ae6L Ω[R] t (tauE t y) (xE t y h)) K) = ae6L Ω[R] t (tauE t y) (xE t y h) := by
  refine le_antisymm (A6d.pSpan_ae6ConjIn_le (K_le_L Z)) (iSup₂_le fun J hJ => ?_)
  have hc : ∃ c, IsUniqueInvolution J c ∧ c ∈ e3 t y h := by
    rcases hJ with (hJ | hJ) | hJ
    · exact ⟨t, hJ.2, t_mem_e3 t y h⟩
    · exact ⟨tauE t y, hJ.2, tau_mem_e3 t y h⟩
    · exact ⟨xE t y h, hJ.2, x_mem_e3 t y h⟩
  obtain ⟨c, hc, hcE⟩ := hc
  have hJΩ : J ∈ Ω[R] := by
    rcases hJ with (hJ | hJ) | hJ
    exacts [hJ.1, hJ.1, hJ.1]
  exact le_pSpan (mem_KL_of_inv_mem_E3 Z hJΩ hc hcE)

include Z in
theorem L_lt_top : ae6L Ω[R] t (tauE t y) (xE t y h) < ⊤ := by
  refine lt_top_iff_ne_top.mpr fun htop => ?_
  have hn : (e3 t y h).Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (htop ▸ L_le_normalizer Z))
  haveI := Z.C.H.ex.1.perp.core.simple
  have hbot := eq_bot_of_normal_isPGroup Z.C.H.ex.1.perp.core.nonab hn
    (A6d.isPGroup_two_of_sq_eq_one Z.hE.2)
  exact Z.C.H.ex.1.datum.hz.ne_one (by simpa [hbot] using t_mem_e3 t y h)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6f
