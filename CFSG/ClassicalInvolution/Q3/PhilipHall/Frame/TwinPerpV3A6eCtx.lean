module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6eIdent
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6eOrbit
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6Hx
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6Wt
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6Gen

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


local notation "Ω[" R "]" => CoreAssembly.conjClass (tightCore R)

structure A6eCtx (n : ℕ) {Y : Type} [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y) (K₄ W : Subgroup Y) (a₁ a₂ a₃ a₄ y : Y) where
  H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W
  fr : AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y
  P : E8Pkg (ae6I Ω[R] W (u₁ * u₂)) (ae6D Ω[R] W (u₁ * u₂))
  lab : E8Lab P (ae6ConjIn (ae6I Ω[R] W (u₁ * u₂)) K)
  hDsq : ∀ d ∈ ae6D Ω[R] W (u₁ * u₂), d * d = 1
  hE : IsElemAbelian2 (ae6E Ω[R] (u₁ * u₂)) 5 ∧ u₁ * u₂ ∈ ae6E Ω[R] (u₁ * u₂) ∧
    t ∈ ae6E Ω[R] (u₁ * u₂) ∧ y * t * y⁻¹ ∈ ae6E Ω[R] (u₁ * u₂)

theorem nonempty_ctx {n : ℕ} (hD : V3AE6D n) (hDN : V3AE6DNorm n) (hI : V3AE6I n) {Y : Type}
    [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y} {K K' K₃ : Subgroup Y}
    {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y} {a₁ a₂ a₃ a₄ y : Y}
    (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (fr : AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y) :
    Nonempty (A6eCtx n R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y) := by
  obtain ⟨hE1, hE2, hE3, hE4, -⟩ := hD Y R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y H fr
  obtain ⟨hDsq, -⟩ := hDN Y R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y H fr
  obtain ⟨-, A, hpI, hker, hcore⟩ := hI Y R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y H fr
  exact ⟨⟨H, fr, e8Pkg_of_aeIdent A hpI hker hcore, e8Lab_of_aeIdent A hpI hker hcore, hDsq,
    hE1, hE2, hE3, hE4⟩⟩

theorem ae6E_le_ae6D {Y : Type} [Group Y] (Ω : Set (Subgroup Y)) (W : Subgroup Y) (u : Y) :
    ae6E Ω u ≤ ae6D Ω W u := by
  unfold ae6D
  refine le_trans ?_ (le_iSup _ (1 : ↥(MGrp Ω W)))
  simp [conjSub_one]

namespace A6eCtx

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y} {a₁ a₂ a₃ a₄ y : Y}
  (C : A6eCtx n R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y)

abbrev I (_ : A6eCtx n R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y) : Subgroup Y :=
  ae6I Ω[R] W (u₁ * u₂)

abbrev D (_ : A6eCtx n R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y) : Subgroup Y :=
  ae6D Ω[R] W (u₁ * u₂)

include C in
theorem t_mem_D : t ∈ ae6D Ω[R] W (u₁ * u₂) := ae6E_le_ae6D _ _ _ C.hE.2.2.1

include C in
theorem tau_mem_D : y * t * y⁻¹ ∈ ae6D Ω[R] W (u₁ * u₂) := ae6E_le_ae6D _ _ _ C.hE.2.2.2

include C in
theorem u_mem_D : u₁ * u₂ ∈ ae6D Ω[R] W (u₁ * u₂) := ae6E_le_ae6D _ _ _ C.hE.2.1

end A6eCtx

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6e
