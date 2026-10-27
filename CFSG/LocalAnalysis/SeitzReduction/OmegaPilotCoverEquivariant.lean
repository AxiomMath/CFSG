module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotFieldNormalize

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadPlus)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus plusIndexEquiv)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG symm_mem_modelToG)

section Frame

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

omit [Finite K] [CharP K 2] in
theorem frameLin_mem_stabSub {k : Fin n} {t : Fin n → Kˣ} (ht : t k = 1) :
    frameLin (plusFrameLeft n) (plusFrameRight n) t ∈
      stabSub (K := K) (plusIndexEquiv n (.inl k)) (plusIndexEquiv n (.inr k)) := by
  have h := isHypFrame_plus K n
  refine ⟨?_, ?_⟩
  · funext i
    rw [frameLin_apply]
    by_cases hi : i = plusFrameLeft n k
    · subst hi
      rw [h.frameEntry_left, ht]
      simp [plusFrameLeft]
    · have hi' : i ≠ plusIndexEquiv n (.inl k) := hi
      simp [hi']
  · funext i
    rw [frameLin_apply]
    by_cases hi : i = plusFrameRight n k
    · subst hi
      rw [h.frameEntry_right, ht]
      simp [plusFrameRight]
    · have hi' : i ≠ plusIndexEquiv n (.inr k) := hi
      simp [hi']

theorem frameHom_mem_pairPerp {k : Fin n} {t : Fin n → Kˣ} (ht : t k = 1) :
    (isHypFrame_plus K n).frameHom t ∈ pairPerp (K := K) k := by
  rw [IsHypFrame.frameHom_apply]
  exact ⟨⟨frameLin (plusFrameLeft n) (plusFrameRight n) t,
    (isHypFrame_plus K n).frameLin_mem_orthDerived t⟩,
    Subgroup.mem_subgroupOf.2 (frameLin_mem_stabSub ht), rfl⟩

theorem frameHom_mulSingle_mem_pairTorus (k : Fin n) (c : Kˣ) :
    (isHypFrame_plus K n).frameHom (Pi.mulSingle k c) ∈ pairTorus (K := K) k := by
  rw [← plusFrameTorus_rootParam]
  exact (isHypFrame_plus K n).frameHom_mem_frameTorusOf (mulSingle_mem_rootParam k c)

omit [Finite K] [CharP K 2] in
theorem mul_mulSingle_inv_apply_self (k : Fin n) (t : Fin n → Kˣ) :
    ((t * (Pi.mulSingle k (t k))⁻¹ : Fin n → Kˣ)) k = 1 := by
  simp

end Frame

section Equivariant

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  {F : Type} [Field F] {m : ℕ}

omit [Finite K] [CharP K 2] in
theorem neighbourDiag_mul_mulSingle_inv (ι : K →+* F) (k : Fin (m + 1)) (t : Fin (m + 1) → Kˣ) :
    neighbourDiag ι k (t * (Pi.mulSingle k (t k))⁻¹) = neighbourDiag ι k t := by
  rw [neighbourDiag_apply, neighbourDiag_apply]
  congr 2
  funext i
  rw [restrictParam_apply, restrictParam_apply, Pi.mul_apply, Pi.inv_apply,
    Pi.mulSingle_eq_of_ne (Fin.succAbove_ne k i), inv_one, mul_one]

theorem equivariant_of_normalized
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus (m + 1) K)) (ι : K →+* F)
    (k : Fin (m + 1)) (π : plusNeighbourCore e k →* StatedOmega (StatedQuadPlus m F))
    (hD : modelToG e (pairPerp (K := K) k) ≤ plusNeighbourCore e k)
    (hnorm : ∀ t : Fin (m + 1) → Kˣ, t k = 1 →
      ∀ hmem : ((e.symm ((isHypFrame_plus K (m + 1)).frameHom t) : L) : G) ∈
        plusNeighbourCore e k,
        ((π ⟨_, hmem⟩ : StatedOmega (StatedQuadPlus m F)) : GL (Fin m ⊕ Fin m) F) =
          neighbourDiag ι k t)
    (t : Fin (m + 1) → Kˣ)
    (hn : ((e.symm ((isHypFrame_plus K (m + 1)).frameHom t) : L) : G) ∈
      normalizer (plusNeighbourCore e k : Set G)) (x : plusNeighbourCore e k) :
    π ((plusNeighbourCore e k).normalizerMonoidHom ⟨_, hn⟩ x) =
      (StatedOmega (StatedQuadPlus m F)).normalizerMonoidHom
        ⟨neighbourDiag ι k t, neighbourDiag_mem_normalizer ι k t⟩ (π x) := by
  set h := isHypFrame_plus K (m + 1)
  set c : Fin (m + 1) → Kˣ := Pi.mulSingle k (t k) with hc
  set t' : Fin (m + 1) → Kˣ := t * c⁻¹ with ht'
  have ht'k : t' k = 1 := mul_mulSingle_inv_apply_self k t
  have htt : t = t' * c := by rw [ht', inv_mul_cancel_right]
  set g' : G := ((e.symm (h.frameHom t') : L) : G) with hg'
  set gc : G := ((e.symm (h.frameHom c) : L) : G) with hgc
  have hgt : ((e.symm (h.frameHom t) : L) : G) = g' * gc := by
    rw [hg', hgc, ← Subgroup.coe_mul, ← map_mul, ← map_mul, ← htt]
  have hgcX : gc ∈ modelToG e (pairTorus (K := K) k) :=
    symm_mem_modelToG e (frameHom_mulSingle_mem_pairTorus k (t k))
  have hcomm : ∀ y : plusNeighbourCore e k, (y : G) * gc = gc * y := fun y =>
    (mem_centralizer_iff.1 (F4Pilot.centralizerPerfectCore_le_centralizer _ y.2) gc hgcX).symm
  have hmem : g' ∈ plusNeighbourCore e k := hD (symm_mem_modelToG e (frameHom_mem_pairPerp ht'k))
  have hval := hnorm t' ht'k hmem
  rw [neighbourDiag_mul_mulSingle_inv] at hval
  set y : plusNeighbourCore e k := ⟨g', hmem⟩
  have hconj : (plusNeighbourCore e k).normalizerMonoidHom ⟨_, hn⟩ x = y * x * y⁻¹ := by
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

@[expose] noncomputable def PlusFieldCover.ofNormalized
    {e : L ≃* matrixProjectiveDerived (coordinateQuadPlus (m + 1) K)} {ι : K →+* F}
    {k : Fin (m + 1)} (π : plusNeighbourCore e k →* StatedOmega (StatedQuadPlus m F))
    (hsurj : Function.Surjective π) (hker : π.ker ≤ center (plusNeighbourCore e k))
    (hD : modelToG e (pairPerp (K := K) k) ≤ plusNeighbourCore e k)
    (hnorm : ∀ t : Fin (m + 1) → Kˣ, t k = 1 →
      ∀ hmem : ((e.symm ((isHypFrame_plus K (m + 1)).frameHom t) : L) : G) ∈
        plusNeighbourCore e k,
        ((π ⟨_, hmem⟩ : StatedOmega (StatedQuadPlus m F)) : GL (Fin m ⊕ Fin m) F) =
          neighbourDiag ι k t) :
    PlusFieldCover e ι k where
  π := π
  surjective := hsurj
  ker_le := hker
  equivariant t hn x := equivariant_of_normalized e ι k π hD hnorm t hn x

end Equivariant

end CFSG.SeitzReduction.OmegaPilot
