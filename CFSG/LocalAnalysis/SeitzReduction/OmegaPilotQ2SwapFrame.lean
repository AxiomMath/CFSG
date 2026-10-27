module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2SwapLift
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2SwapPair
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2SwapTriangle
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2Minus
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2PlusNbrMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Open
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus coordinateQuadMinus)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.SeitzQ2 (SwapParam SwapPairExclusion)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

section Frame

variable {P : Type*} [Group P]

@[expose] def triOverlap (X D : Subgroup P) (g h : P) : Subgroup P :=
  perfectCore (D.map (MulAut.conj g).toMonoidHom ⊓
    centralizer (X.map (MulAut.conj h).toMonoidHom : Set P))

@[expose] def SwapTriangleFrame (X D : Subgroup P) : Prop :=
  ∃ g : Fin 3 → P,
    (∀ a b : Fin 3, a ≠ b →
      X.map (MulAut.conj (g b)).toMonoidHom ≤ D.map (MulAut.conj (g a)).toMonoidHom) ∧
    (∀ a b : Fin 3, a < b → IsSimpleGroup (triOverlap X D (g a) (g b)) ∧
      center (triOverlap X D (g a) (g b)) = ⊥) ∧
    (∃ q : P, q ≠ 1 ∧ ∀ a b : Fin 3, a < b → q ∈ triOverlap X D (g a) (g b)) ∧
    triOverlap X D (g 0) (g 1) ⊔ triOverlap X D (g 0) (g 2) ⊔ triOverlap X D (g 1) (g 2) = ⊤

end Frame

section Triangle

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem false_of_swapTriangleFrame {P P' : Type} [Group P] [Finite P] [Group P']
    (hset : SeitzSetting G L) (hOut : Group.IsSolvable (Outer L)) (e : L ≃* P)
    (hP : SwapPairExclusion P) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) (e' : L ≃* P')
    {X D : Subgroup P'} (hF : SwapTriangleFrame X D) (Ψ : SwapParam t (modelToG e' D))
    (hinj : Function.Injective Ψ.Ψ) (hrange : Ψ.Ψ.range = centralizerPerfectCore (modelToG e' X)) :
    False := by
  obtain ⟨g, hXD, hS, ⟨q, hq1, hq⟩, hgen⟩ := hF
  have htC := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  set n : Fin 3 → G := fun a => ((e'.symm (g a) : L) : G) with hndef
  have hn : ∀ a, n a * t = t * n a := fun a =>
    (mem_centralizer_iff.1 htC _ (e'.symm (g a)).2)
  have hpar : ∀ a, ∃ P₀ : SwapParam t ((modelToG e' D).map (MulAut.conj (n a)).toMonoidHom),
      Function.Injective P₀.Ψ ∧ P₀.Ψ.range =
        centralizerPerfectCore ((modelToG e' X).map (MulAut.conj (n a)).toMonoidHom) := by
    intro a
    obtain ⟨P₀, h1, h2⟩ := E8Pilot.exists_swapParam_conj Ψ hinj (n a) (hn a)
    exact ⟨P₀, h1, by rw [h2, hrange, F4Pilot.map_centralizerPerfectCore]⟩
  obtain ⟨P₁, hinj₁, hrange₁⟩ := hpar 0
  obtain ⟨P₂, hinj₂, hrange₂⟩ := hpar 1
  obtain ⟨P₃, hinj₃, hrange₃⟩ := hpar 2
  have hXG : ∀ a, (modelToG e' X).map (MulAut.conj (n a)).toMonoidHom =
      modelToG e' (X.map (MulAut.conj (g a)).toMonoidHom) := fun a =>
    (UnitaryPilot.modelToG_map_conj e' X (g a)).symm
  have hDG : ∀ a, (modelToG e' D).map (MulAut.conj (n a)).toMonoidHom =
      modelToG e' (D.map (MulAut.conj (g a)).toMonoidHom) := fun a =>
    (UnitaryPilot.modelToG_map_conj e' D (g a)).symm
  have hov : ∀ a b, perfectCore ((modelToG e' D).map (MulAut.conj (n a)).toMonoidHom ⊓
      centralizer ((modelToG e' X).map (MulAut.conj (n b)).toMonoidHom : Set G)) =
      modelToG e' (triOverlap X D (g a) (g b)) := by
    intro a b
    rw [hXG, hDG, perfectCore_modelToG_inf_centralizer]
    rfl
  have hle : ∀ a b, a ≠ b → (modelToG e' X).map (MulAut.conj (n b)).toMonoidHom ≤
      (modelToG e' D).map (MulAut.conj (n a)).toMonoidHom := fun a b hab => by
    rw [hXG, hDG]
    exact UnitaryPilot.modelToG_mono e' (hXD a b hab)
  have hXL : ∀ a, (modelToG e' X).map (MulAut.conj (n a)).toMonoidHom ≤ L := fun a => by
    rw [hXG]
    exact UnitaryPilot.modelToG_le e' _
  have hsim : ∀ a b, a < b → IsSimpleGroup (perfectCore
      ((modelToG e' D).map (MulAut.conj (n a)).toMonoidHom ⊓
        centralizer ((modelToG e' X).map (MulAut.conj (n b)).toMonoidHom : Set G))) := by
    intro a b hab
    rw [hov]
    exact isSimpleGroup_modelToG e' (hS a b hab).1
  have hZ : ∀ a b, a < b → center (perfectCore
      ((modelToG e' D).map (MulAut.conj (n a)).toMonoidHom ⊓
        centralizer ((modelToG e' X).map (MulAut.conj (n b)).toMonoidHom : Set G))) = ⊥ := by
    intro a b hab
    rw [hov]
    exact F4Pilot.center_eq_bot_congr (UnitaryPilot.modelToGEquiv e' _) (hS a b hab).2
  have hqG : ∀ a b, a < b → ((e'.symm q : L) : G) ∈ perfectCore
      ((modelToG e' D).map (MulAut.conj (n a)).toMonoidHom ⊓
        centralizer ((modelToG e' X).map (MulAut.conj (n b)).toMonoidHom : Set G)) := by
    intro a b hab
    rw [hov]
    exact UnitaryPilot.symm_mem_modelToG e' (hq a b hab)
  have hq1G : ((e'.symm q : L) : G) ≠ 1 := fun h =>
    hq1 (e'.symm.injective (Subtype.ext (by rw [map_one]; exact h)))
  have hgenG : perfectCore ((modelToG e' D).map (MulAut.conj (n 0)).toMonoidHom ⊓
      centralizer ((modelToG e' X).map (MulAut.conj (n 1)).toMonoidHom : Set G)) ⊔
      perfectCore ((modelToG e' D).map (MulAut.conj (n 0)).toMonoidHom ⊓
        centralizer ((modelToG e' X).map (MulAut.conj (n 2)).toMonoidHom : Set G)) ⊔
      perfectCore ((modelToG e' D).map (MulAut.conj (n 1)).toMonoidHom ⊓
        centralizer ((modelToG e' X).map (MulAut.conj (n 2)).toMonoidHom : Set G)) = L := by
    rw [hov, hov, hov, ← UnitaryPilot.modelToG_sup, ← UnitaryPilot.modelToG_sup, hgen,
      UnitaryPilot.modelToG_top]
  have h01 : (0 : Fin 3) < 1 := by decide
  have h02 : (0 : Fin 3) < 2 := by decide
  have h12 : (1 : Fin 3) < 2 := by decide
  exact E8Pilot.false_of_swapParam_triangle hset hOut e hP ht hKt P₁ P₂ P₃ hinj₁ hinj₂ hinj₃
    hrange₁ hrange₂ hrange₃ (hXL 0) (hXL 1) (hXL 2) (hle 0 1 (by decide)) (hle 0 2 (by decide))
    (hle 1 0 (by decide)) (hle 1 2 (by decide)) (hle 2 0 (by decide)) (hle 2 1 (by decide))
    (hsim 0 1 h01) (hsim 0 2 h02) (hsim 1 2 h12) (hZ 0 1 h01) (hZ 0 2 h02) (hZ 1 2 h12)
    (hqG 0 1 h01) (hqG 0 2 h02) (hqG 1 2 h12) hq1G hgenG

end Triangle

section Rows

theorem omegaMinusTwoRowInput_swap_of_frame
    (hF : ∀ (n : ℕ) (hn : 6 ≤ n) (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K),
      (∀ s : K, s ^ 2 + b * s + c ≠ 0) → Nat.card K = 2 →
        SwapTriangleFrame (anisoTorus (K := K) (by omega : 1 ≤ n) b c)
          (anisoPerp (K := K) (by omega : 1 ≤ n) b c)) :
    OmegaMinusTwoRowInput .swap := by
  intro G _ _ L hset n hn K _ _ _ b c hirr hK2 e t ht hKt _ hN hr
  have htC := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hKc : Nat.card K = 2 ^ 1 := by rw [hK2, pow_one]
  obtain ⟨Ψ, hinj, hrange⟩ := exists_swapParam_anisoTorus hset hKc (by omega) hirr e htC ht hN hr
  exact false_of_swapTriangleFrame hset
    (isSolvable_outer_of_mulEquiv_minus (by omega) le_rfl hKc hirr e) e
    (swapPairExclusion_coordinateMinus_two hK2 (by omega) _ hirr) ht hKt e
    (hF n hn K b c hirr hK2) Ψ hinj hrange

theorem omegaPlusTwoRowInput_swap_of_frame
    (hF : ∀ (m : ℕ), 4 ≤ m → ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K)
      (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0), Nat.card K = 2 →
        SwapTriangleFrame (plusAnisoTorus m hirr) (plusAnisoPerp (K := K) m b c)) :
    OmegaPlusTwoRowInput .swap := by
  intro G _ _ L hset m hm K _ _ _ b c hirr hK2 e t ht hKt _ hN hr
  have htC := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hKc : Nat.card K = 2 ^ 1 := by rw [hK2, pow_one]
  obtain ⟨Ψ, hinj, hrange⟩ :=
    exists_swapParam_plusAnisoTorus hset hKc (by omega) hirr e htC ht hN hr
  exact false_of_swapTriangleFrame hset
    (isSolvable_outer_of_mulEquiv_plus (by omega) le_rfl hKc e) e
    (swapPairExclusion_coordinatePlus_two hK2 (by omega)) ht hKt _
    (hF m hm K b c hirr hK2) Ψ hinj hrange

end Rows

end CFSG.SeitzReduction.OmegaPilot
