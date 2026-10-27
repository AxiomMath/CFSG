module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusFourAniso

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank QuadraticMap
open CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadMinus
  coordinateQuadPlus minusIndexEquiv plusIndexEquiv regular_coordinateQuadMinus
  coordinateQuadPlus_apply)
open CFSG.SeitzReduction.UnitaryPilot (modelToG modelToGEquiv symm_mem_modelToG)
open CFSG.SeitzReduction.SymplecticPilot (liftParam)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (incl fieldAutT)

section Perp

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

omit [Finite K] [CharP K 2] in
theorem frameEntry_anisoPerpCoord (hn : 1 ≤ n) (t : Fin (n - 1) → Kˣ) (y : Fin (2 * (n - 1))) :
    frameEntry (minusFrameLeft hn) (minusFrameRight hn) t (anisoPerpCoord hn y) =
      frameEntry (plusFrameLeft (n - 1)) (plusFrameRight (n - 1)) t y := by
  obtain ⟨s, rfl⟩ := (plusIndexEquiv (n - 1)).surjective y
  rcases s with l | l
  · have h1 : anisoPerpCoord hn (plusIndexEquiv (n - 1) (.inl l)) = minusFrameLeft hn l := by
      simp [anisoPerpCoord, minusFrameLeft]
    rw [h1, (isHypFrame_minus K hn 0 0).frameEntry_left]
    exact ((isHypFrame_plus K (n - 1)).frameEntry_left t l).symm
  · have h1 : anisoPerpCoord hn (plusIndexEquiv (n - 1) (.inr l)) = minusFrameRight hn l := by
      simp [anisoPerpCoord, minusFrameRight]
    rw [h1, (isHypFrame_minus K hn 0 0).frameEntry_right]
    exact ((isHypFrame_plus K (n - 1)).frameEntry_right t l).symm

theorem anisoPerpEquiv_apply (hn : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (x : anisoPerp (K := K) (by omega : 1 ≤ n) b c)
    (G : orthDerived (coordinateQuadMinus n K (by omega) b c))
    (hG : (G : (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K)) ∈
      stabSub (anisoCoordLeft (by omega : 1 ≤ n)) (anisoCoordRight (by omega : 1 ≤ n)))
    (hxG : (x : matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) = projHom _ G)
    (w : Fin (2 * (n - 1)) → K) (y : Fin (2 * (n - 1))) :
    ((anisoPerpEquiv hn hirr x : orthDerived (coordinateQuadPlus (n - 1) K)) :
        (Fin (2 * (n - 1)) → K) ≃ₗ[K] (Fin (2 * (n - 1)) → K)) w y =
      (G : (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K))
        (Function.extend (anisoPerpCoord (by omega)) w 0) (anisoPerpCoord (by omega) y) := by
  have hsymm : ((stabDerived (coordinateQuadMinus n K (by omega) b c)
      (anisoCoordLeft (by omega)) (anisoCoordRight (by omega))).equivMapOfInjective
      (projHom _) (projHom_injective
        (isAnisoCoord_coordinateQuadMinus (K := K) (by omega : 1 ≤ n) hirr).exists_ne_zero)).symm
      x = ⟨G, hG⟩ :=
    (MulEquiv.symm_apply_eq _).mpr (Subtype.ext hxG)
  have e1 : anisoPerpEquiv hn hirr x =
      orthDerivedCongr (anisoPerpIsometry (by omega) b c)
        ((isAnisoCoord_coordinateQuadMinus (K := K) (by omega : 1 ≤ n) hirr).stabDerivedEquiv
          (regular_coordinateQuadMinus n K b c hn hirr).1 (regular_anisoPerp hn b c).1
          (regular_anisoPerp hn b c).2 ⟨G, hG⟩) := by
    rw [← hsymm]
    rfl
  rw [e1, orthDerivedCongr_apply]
  rfl

omit [Finite K] [CharP K 2] in
theorem minusFrameLin_mem_stabSub_aniso (hn : 1 ≤ n) (t : Fin (n - 1) → Kˣ) :
    frameLin (minusFrameLeft hn) (minusFrameRight hn) t ∈
      stabSub (K := K) (anisoCoordLeft hn) (anisoCoordRight hn) :=
  ⟨frameLin_single_of_forall_ne t (anisoCoordLeft_ne_minusFrameLeft hn)
      (anisoCoordLeft_ne_minusFrameRight hn),
    frameLin_single_of_forall_ne t (anisoCoordRight_ne_minusFrameLeft hn)
      (anisoCoordRight_ne_minusFrameRight hn)⟩

theorem frameHom_mem_anisoPerp (hn : 1 ≤ n) {b c : K} (t : Fin (n - 1) → Kˣ) :
    (isHypFrame_minus K hn b c).frameHom t ∈ anisoPerp hn b c :=
  minusFrameTorus_le_anisoPerp hn b c ⊤
    ((isHypFrame_minus K hn b c).frameHom_mem_frameTorusOf (Subgroup.mem_top t))

theorem anisoPerpEquiv_frameHom (hn : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (t : Fin (n - 1) → Kˣ) :
    ((anisoPerpEquiv hn hirr ⟨(isHypFrame_minus K (by omega) b c).frameHom t,
        frameHom_mem_anisoPerp (by omega) t⟩ : orthDerived (coordinateQuadPlus (n - 1) K)) :
        (Fin (2 * (n - 1)) → K) ≃ₗ[K] (Fin (2 * (n - 1)) → K)) =
      frameLin (plusFrameLeft (n - 1)) (plusFrameRight (n - 1)) t := by
  ext w x
  rw [anisoPerpEquiv_apply hn hirr _
    ⟨frameLin (minusFrameLeft (by omega)) (minusFrameRight (by omega)) t,
      (isHypFrame_minus K (by omega) b c).frameLin_mem_orthDerived t⟩
    (minusFrameLin_mem_stabSub_aniso (by omega) t) rfl w x]
  change frameLin (minusFrameLeft (by omega)) (minusFrameRight (by omega)) t
      (Function.extend (anisoPerpCoord (by omega)) w 0) (anisoPerpCoord (by omega) x) =
    frameLin (plusFrameLeft (n - 1)) (plusFrameRight (n - 1)) t w x
  rw [frameLin_apply, frameLin_apply, (anisoPerpCoord_injective _).extend_apply,
    frameEntry_anisoPerpCoord]

@[expose] noncomputable def anisoPerpModelEquiv (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    anisoPerp (K := K) (by omega : 1 ≤ n) b c ≃*
      matrixProjectiveDerived (coordinateQuadPlus (n - 1) K) :=
  (anisoPerpEquiv hn hirr).trans (MulEquiv.ofBijective (projHom _)
    ⟨projHom_injective (isHypCoord_coordinateQuadPlus (K := K)
      (⟨0, by omega⟩ : Fin (n - 1))).exists_ne_zero, projHom_surjective _⟩)

theorem anisoPerpModelEquiv_frameHom (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (t : Fin (n - 1) → Kˣ) :
    anisoPerpModelEquiv hn hirr ⟨(isHypFrame_minus K (by omega) b c).frameHom t,
        frameHom_mem_anisoPerp (by omega) t⟩ = (isHypFrame_plus K (n - 1)).frameHom t := by
  change projHom (coordinateQuadPlus (n - 1) K)
      (anisoPerpEquiv hn hirr ⟨_, frameHom_mem_anisoPerp (by omega) t⟩) =
    projHom (coordinateQuadPlus (n - 1) K)
      ⟨frameLin (plusFrameLeft (n - 1)) (plusFrameRight (n - 1)) t,
        (isHypFrame_plus K (n - 1)).frameLin_mem_orthDerived _⟩
  congr 1
  exact Subtype.ext (anisoPerpEquiv_frameHom hn hirr t)

omit [Finite K] [CharP K 2] in
theorem coordinateQuadPlus_comp_ringEquiv {k₀ : Type} [Field k₀] (φ : K ≃+* k₀) (m : ℕ)
    (v : Fin (2 * m) → K) :
    coordinateQuadPlus m k₀ (φ ∘ v) = φ (coordinateQuadPlus m K v) := by
  rw [coordinateQuadPlus_apply, coordinateQuadPlus_apply]
  simp only [Function.comp_apply, map_sum, map_mul]

omit [Finite K] [CharP K 2] in
@[expose] noncomputable def plusCongr {k₀ : Type} [Field k₀] (φ : K ≃+* k₀) (m : ℕ) :
    matrixProjectiveDerived (coordinateQuadPlus m K) ≃*
      matrixProjectiveDerived (coordinateQuadPlus m k₀) :=
  matrixProjectiveCongr φ (coordinateQuadPlus_comp_ringEquiv φ m)

theorem plusCongr_frameHom {k₀ : Type} [Field k₀] [Finite k₀] [CharP k₀ 2] (φ : K ≃+* k₀)
    (m : ℕ) (t : Fin m → Kˣ) :
    plusCongr φ m ((isHypFrame_plus K m).frameHom t) =
      (isHypFrame_plus k₀ m).frameHom (liftParam φ.toRingHom t) :=
  matrixProjectiveCongr_frameHom φ _ _ _ t

variable {G : Type} [Group G] {L : Subgroup G} {b c : K}

@[expose] noncomputable def anisoPerpFieldEquiv (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus (2 + 2) K (by omega) b c))
    {k₀ : Type} [Field k₀] (φ : K ≃+* k₀) :
    (((anisoPerp (K := K) (n := 2 + 2) (by omega) b c).map e.symm.toMonoidHom).map
        L.subtype : Subgroup G) ≃* matrixProjectiveDerived (coordinateQuadPlus (2 + 1) k₀) :=
  (modelToGEquiv e (anisoPerp (K := K) (n := 2 + 2) (by omega) b c)).symm.trans
    ((anisoPerpModelEquiv (n := 2 + 2) (by omega) hirr).trans (plusCongr φ (2 + 1)))

theorem anisoPerpFieldEquiv_frameHom (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus (2 + 2) K (by omega) b c))
    {k₀ : Type} [Field k₀] [Finite k₀] [CharP k₀ 2] (φ : K ≃+* k₀) (t : Fin (2 + 1) → Kˣ)
    (hmem : ((e.symm ((isHypFrame_minus K (n := 2 + 2) (by omega) b c).frameHom t) : L) : G) ∈
      ((anisoPerp (K := K) (n := 2 + 2) (by omega) b c).map e.symm.toMonoidHom).map
        L.subtype) :
    anisoPerpFieldEquiv hirr e φ ⟨_, hmem⟩ =
      (isHypFrame_plus k₀ (2 + 1)).frameHom (liftParam φ.toRingHom t) := by
  have h1 : (modelToGEquiv e (anisoPerp (K := K) (n := 2 + 2) _ b c)).symm ⟨_, hmem⟩ =
      ⟨(isHypFrame_minus K (n := 2 + 2) _ b c).frameHom t,
        frameHom_mem_anisoPerp (n := 2 + 2) (by omega) t⟩ := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  have h2 := anisoPerpModelEquiv_frameHom (n := 2 + 2) (by omega) hirr t
  have h3 := plusCongr_frameHom φ (2 + 1) t
  calc anisoPerpFieldEquiv hirr e φ ⟨_, hmem⟩
      = plusCongr φ (2 + 1) (anisoPerpModelEquiv (n := 2 + 2) (by omega) hirr
          ((modelToGEquiv e (anisoPerp (K := K) (n := 2 + 2) _ b c)).symm ⟨_, hmem⟩)) := rfl
    _ = _ := by rw [h1, h2, h3]

end Perp

section Inputs

@[expose] def OmegaMinusFourAnisoRowInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K),
      (∀ s : K, s ^ 2 + b * s + c ≠ 0) → Nat.card K = 2 ^ f → 2 ≤ f →
      ∀ (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus 4 K (by norm_num) b c)) (t : G),
        orderOf t = 2 → centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
        (∀ k : Fin (4 - 1), OmegaRowAt t (modelToG e (minusPairTorus (K := K) (by norm_num) b c k))
          (modelToG e (minusPairPerp (K := K) (by norm_num) b c k)) .field) →
        OmegaRowAt t (modelToG e (anisoTorus (K := K) (n := 4) (by norm_num) b c))
          (modelToG e (anisoPerp (K := K) (n := 4) (by norm_num) b c)) .field

end Inputs

section OfNormalized

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  {F : Type} [Field F] {r : ℕ} {hn : 1 ≤ r + 2} {b c : K}

@[expose] noncomputable def MinusAnisoFieldCover.ofNormalized
    {e : L ≃* matrixProjectiveDerived (coordinateQuadMinus (r + 2) K hn b c)} {ι : K →+* F}
    (π : anisoNeighbourCore e →* StatedOmega (StatedQuadPlus (r + 1) F))
    (hsurj : Function.Surjective π) (hker : π.ker ≤ center (anisoNeighbourCore e))
    (hT : ∀ t : Fin (r + 1) → Kˣ,
      ((e.symm ((isHypFrame_minus K hn b c).frameHom t) : L) : G) ∈ anisoNeighbourCore e)
    (hnorm : ∀ (t : Fin (r + 1) → Kˣ)
      (hmem : ((e.symm ((isHypFrame_minus K hn b c).frameHom t) : L) : G) ∈
        anisoNeighbourCore e),
      ((π ⟨_, hmem⟩ : StatedOmega (StatedQuadPlus (r + 1) F)) :
        GL (Fin (r + 1) ⊕ Fin (r + 1)) F) = diagOmega F (r + 1) (liftParam ι t)) :
    MinusAnisoFieldCover e ι where
  π := π
  surjective := hsurj
  ker_le := hker
  equivariant t hN x := by
    set y : anisoNeighbourCore e := ⟨_, hT t⟩
    have hconj : (anisoNeighbourCore e).normalizerMonoidHom ⟨_, hN⟩ x = y * x * y⁻¹ := by
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      rfl
    rw [hconj, map_mul, map_mul, map_inv]
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hnorm t (hT t)]

end OfNormalized

end CFSG.SeitzReduction.OmegaPilot
