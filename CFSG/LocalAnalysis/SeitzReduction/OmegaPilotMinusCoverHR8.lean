module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusCover
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusCoverHR8Model

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadMinus)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG modelToGEquiv symm_mem_modelToG)
open CFSG.SeitzReduction.SymplecticPilot (liftParam)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (incl)

section Equivariant

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  {F : Type} [Field F] {r : ℕ} {hn : 1 ≤ r + 2} {b c : K}

omit [Finite K] [CharP K 2] in
theorem minusNeighbourDiag_mul_mulSingle_inv (ι : K →+* F) (k : Fin (r + 1))
    (t : Fin (r + 1) → Kˣ) :
    minusNeighbourDiag ι k (t * (Pi.mulSingle k (t k))⁻¹) = minusNeighbourDiag ι k t := by
  rw [minusNeighbourDiag_apply, minusNeighbourDiag_apply]
  congr 3
  funext i
  rw [restrictParam_apply, restrictParam_apply, Pi.mul_apply, Pi.inv_apply,
    Pi.mulSingle_eq_of_ne (Fin.succAbove_ne k i), inv_one, mul_one]

theorem equivariant_of_normalized_minus
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus (r + 2) K hn b c)) (ι : K →+* F)
    (k : Fin (r + 1))
    (π : minusNeighbourCore e k →* StatedOmega (StatedQuadPlus (r + 1) F))
    (hD : modelToG e (minusPairPerp hn b c k) ≤ minusNeighbourCore e k)
    (hnorm : ∀ t : Fin (r + 1) → Kˣ, t k = 1 →
      ∀ hmem : ((e.symm ((isHypFrame_minus K hn b c).frameHom t) : L) : G) ∈
        minusNeighbourCore e k,
        ((π ⟨_, hmem⟩ : StatedOmega (StatedQuadPlus (r + 1) F)) :
          GL (Fin (r + 1) ⊕ Fin (r + 1)) F) = minusNeighbourDiag ι k t)
    (t : Fin (r + 1) → Kˣ)
    (hN : ((e.symm ((isHypFrame_minus K hn b c).frameHom t) : L) : G) ∈
      normalizer (minusNeighbourCore e k : Set G)) (x : minusNeighbourCore e k) :
    π ((minusNeighbourCore e k).normalizerMonoidHom ⟨_, hN⟩ x) =
      (StatedOmega (StatedQuadPlus (r + 1) F)).normalizerMonoidHom
        ⟨minusNeighbourDiag ι k t, minusNeighbourDiag_mem_normalizer ι k t⟩ (π x) := by
  set h := isHypFrame_minus K hn b c
  set c' : Fin (r + 1) → Kˣ := Pi.mulSingle k (t k) with hc'
  set t' : Fin (r + 1) → Kˣ := t * c'⁻¹ with ht'
  have ht'k : t' k = 1 := mul_mulSingle_inv_apply_self k t
  have htt : t = t' * c' := by rw [ht', inv_mul_cancel_right]
  set g' : G := ((e.symm (h.frameHom t') : L) : G) with hg'
  set gc : G := ((e.symm (h.frameHom c') : L) : G) with hgc
  have hgt : ((e.symm (h.frameHom t) : L) : G) = g' * gc := by
    rw [hg', hgc, ← Subgroup.coe_mul, ← map_mul, ← map_mul, ← htt]
  have hgcX : gc ∈ modelToG e (minusPairTorus hn b c k) :=
    symm_mem_modelToG e (frameHom_mulSingle_mem_minusPairTorus (n := r + 2) k (t k))
  have hcomm : ∀ y : minusNeighbourCore e k, (y : G) * gc = gc * y := fun y =>
    (mem_centralizer_iff.1 (F4Pilot.centralizerPerfectCore_le_centralizer _ y.2) gc hgcX).symm
  have hmem : g' ∈ minusNeighbourCore e k :=
    hD (symm_mem_modelToG e (frameHom_mem_minusPairPerp (n := r + 2) ht'k))
  have hval := hnorm t' ht'k hmem
  rw [minusNeighbourDiag_mul_mulSingle_inv] at hval
  set y : minusNeighbourCore e k := ⟨g', hmem⟩
  have hconj : (minusNeighbourCore e k).normalizerMonoidHom ⟨_, hN⟩ x = y * x * y⁻¹ := by
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    change ((e.symm (h.frameHom t) : L) : G) * x * ((e.symm (h.frameHom t) : L) : G)⁻¹ =
      g' * x * g'⁻¹
    rw [hgt, _root_.mul_inv_rev]
    calc g' * gc * ↑x * (gc⁻¹ * g'⁻¹) = g' * (gc * ↑x) * gc⁻¹ * g'⁻¹ := by group
      _ = g' * (↑x * gc) * gc⁻¹ * g'⁻¹ := by rw [hcomm x]
      _ = g' * ↑x * g'⁻¹ := by group
  rw [hconj, map_mul, map_mul, map_inv]
  apply Subtype.ext
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hval]

@[expose] noncomputable def MinusFieldCover.ofNormalized
    {e : L ≃* matrixProjectiveDerived (coordinateQuadMinus (r + 2) K hn b c)} {ι : K →+* F}
    {k : Fin (r + 1)} (π : minusNeighbourCore e k →* StatedOmega (StatedQuadPlus (r + 1) F))
    (hsurj : Function.Surjective π) (hker : π.ker ≤ center (minusNeighbourCore e k))
    (hD : modelToG e (minusPairPerp hn b c k) ≤ minusNeighbourCore e k)
    (hnorm : ∀ t : Fin (r + 1) → Kˣ, t k = 1 →
      ∀ hmem : ((e.symm ((isHypFrame_minus K hn b c).frameHom t) : L) : G) ∈
        minusNeighbourCore e k,
        ((π ⟨_, hmem⟩ : StatedOmega (StatedQuadPlus (r + 1) F)) :
          GL (Fin (r + 1) ⊕ Fin (r + 1)) F) = minusNeighbourDiag ι k t) :
    MinusFieldCover e ι k where
  π := π
  surjective := hsurj
  ker_le := hker
  equivariant t hN x := equivariant_of_normalized_minus e ι k π hD hnorm t hN x

end Equivariant

section Perp

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  {r : ℕ} {b c : K}

@[expose] noncomputable def minusPairPerpFieldEquiv (hr : 3 ≤ r)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus (r + 2) K (by omega) b c))
    (k : Fin (r + 1)) {k₀ : Type} [Field k₀] (φ : K ≃+* k₀) :
    (((minusPairPerp (K := K) (n := r + 2) (by omega) b c k).map e.symm.toMonoidHom).map
        L.subtype : Subgroup G) ≃*
      matrixProjectiveDerived (coordinateQuadMinus (r + 1) k₀ (by omega) (φ b) (φ c)) :=
  (modelToGEquiv e (minusPairPerp (K := K) (n := r + 2) (by omega) b c k)).symm.trans
    ((minusPairPerpModelEquiv (n := r + 2) (by omega) hirr k).trans
      (minusCongr φ (n := r + 1) (by omega) b c))

theorem minusPairPerpFieldEquiv_frameHom (hr : 3 ≤ r)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus (r + 2) K (by omega) b c))
    (k : Fin (r + 1)) {k₀ : Type} [Field k₀] [Finite k₀] [CharP k₀ 2] (φ : K ≃+* k₀)
    {t : Fin (r + 1) → Kˣ} (ht : t k = 1)
    (hmem : ((e.symm ((isHypFrame_minus K (n := r + 2) (by omega) b c).frameHom t) : L) : G) ∈
      ((minusPairPerp (K := K) (n := r + 2) (by omega) b c k).map e.symm.toMonoidHom).map
        L.subtype) :
    minusPairPerpFieldEquiv hr hirr e k φ ⟨_, hmem⟩ =
      (isHypFrame_minus k₀ (n := r + 1) (by omega) (φ b) (φ c)).frameHom
        (liftParam φ.toRingHom (restrictParam k t)) := by
  have h1 : (modelToGEquiv e (minusPairPerp (K := K) (n := r + 2) _ b c k)).symm
      ⟨_, hmem⟩ = ⟨(isHypFrame_minus K (n := r + 2) _ b c).frameHom t,
        frameHom_mem_minusPairPerp ht⟩ := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  have h2 := minusPairPerpModelEquiv_frameHom (n := r + 2) (by omega) hirr k ht
  have h2' : minusPairPerpModelEquiv (n := r + 2) (by omega) hirr k
      ⟨(isHypFrame_minus K (n := r + 2) (by omega) b c).frameHom t,
        frameHom_mem_minusPairPerp ht⟩ =
      (isHypFrame_minus K (n := r + 1) (by omega) b c).frameHom (restrictParam k t) := h2
  have h3 := minusCongr_frameHom φ (n := r + 1) (by omega) b c (restrictParam k t)
  calc minusPairPerpFieldEquiv hr hirr e k φ ⟨_, hmem⟩
      = minusCongr φ (n := r + 1) _ b c (minusPairPerpModelEquiv (n := r + 2)
          _ hirr k ((modelToGEquiv e
            (minusPairPerp (K := K) (n := r + 2) _ b c k)).symm ⟨_, hmem⟩)) := rfl
    _ = _ := by rw [h1, h2', h3]

end Perp

end CFSG.SeitzReduction.OmegaPilot
