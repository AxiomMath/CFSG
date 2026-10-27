module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofFrameDLSubgroup

public section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG.LieType CFSG.LieType.Universal CFSG.Timmesfeld CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.WeakCT (spBlock blk exists_spMap spMap_comp_spBlock map_blk
  map_map_symm map_symm_map DoubleBondDiagram)
open scoped MatrixGroups

section Transport

variable {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {x : (Fin D.rank → ℤ) → F → K}
  {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
  {O : Steinberg.CommOrder (Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}

theorem weakCT_of_frame_dl_subgroup_equiv [Finite F] {F₀ : Type} [Field F₀] (e : F₀ ≃+* F)
    {t : StatedLieTag} {n p f : ℕ}
    (hCT : CurtisTits.CurtisTitsConclusion.{0} D t n p f) (hL : LeviConePresented D)
    (hE : Steinberg.ChevalleyExtras D F x C O) (hdiv : D.divisible = ∅)
    (hq : IsQuasisimple (StatedSp 2 F)) (h2 : (2 : F) ≠ 0)
    {adj : Fin D.rank → Fin D.rank → Prop} {a b : Fin D.rank}
    (hdiag : DoubleBondDiagram D.cartan adj a b)
    {H : Fin D.rank → Subgroup K} (hind : iSupIndep H)
    (hsq : ∀ k, Steinberg.weylElement x k 1 ^ 2 ∈ H k)
    {G : Type} [Group G] {U : Fin D.rank → Subgroup G}
    (hcomm : ∀ i j, i ≠ j → ¬ adj i j → ¬ adj j i → ∀ u ∈ U i, ∀ v ∈ U j, u * v = v * u)
    {ρ : Fin D.rank → SL(2, F₀) →* G} (hρ : ∀ k, (ρ k).range = U k)
    (hρa : Function.Injective (ρ a))
    (hψ : ∀ i j, adj i j → ¬ (i = a ∧ j = b) → ∃ ψ : SL(3, F₀) →* G,
      ψ.comp (blk F₀ 0) = ρ i ∧ ψ.comp (blk F₀ 1) = ρ j)
    (hψ4 : ∃ ψ : StatedSp 2 F₀ →* G, ψ.comp (spBlock F₀ 1) = ρ a ∧
      ψ.comp (spBlock F₀ 0) = ρ b) :
    ∃ Ψ : K →* G, Ψ.ker ≤ Subgroup.center K ∧ Ψ.range = ⨆ k, U k ∧
      IsQuasisimple ↥(⨆ k, U k) ∧
      LieModel (↥(⨆ k, U k) ⧸ Subgroup.center ↥(⨆ k, U k)) t n p f ∧
      ∀ k, (CurtisTits.rankOne D.rootGroup k).map Ψ = U k := by
  let φ₂ : SL(2, F) →* SL(2, F₀) := Matrix.SpecialLinearGroup.map e.symm.toRingHom
  let φ₃ : SL(3, F) →* SL(3, F₀) := Matrix.SpecialLinearGroup.map e.symm.toRingHom
  have hφ₂inj : Function.Injective φ₂ := fun A B h => by
    have := congrArg (Matrix.SpecialLinearGroup.map e.toRingHom) h
    rwa [map_symm_map, map_symm_map] at this
  have hφ₂surj : ∀ A : SL(2, F₀), ∃ B : SL(2, F), φ₂ B = A := fun A =>
    ⟨Matrix.SpecialLinearGroup.map e.toRingHom A, map_map_symm e A⟩
  obtain ⟨Φ, hΦ⟩ := exists_spMap (F := F) e.symm.toRingHom
  refine CFSG.ComponentClassification.CatLeafProof.weakCT_of_frame_dl_subgroup hCT hL hE hdiv hq
    h2 hdiag hind hsq hcomm (ρ := fun k => (ρ k).comp φ₂) (fun k => ?_) (hρa.comp hφ₂inj)
    (fun i j hij hne => ?_) ?_
  · rw [← hρ k]
    ext y
    constructor
    · rintro ⟨B, rfl⟩
      exact ⟨φ₂ B, rfl⟩
    · rintro ⟨A, rfl⟩
      obtain ⟨B, rfl⟩ := hφ₂surj A
      exact ⟨B, rfl⟩
  · obtain ⟨ψ', hψ0, hψ1⟩ := hψ i j hij hne
    refine ⟨ψ'.comp φ₃, ?_, ?_⟩
    · ext A
      show ψ' (φ₃ (blk F 0 A)) = ρ i (φ₂ A)
      rw [← hψ0, MonoidHom.comp_apply]
      exact congrArg ψ' (map_blk e.symm.toRingHom 0 A)
    · ext A
      show ψ' (φ₃ (blk F 1 A)) = ρ j (φ₂ A)
      rw [← hψ1, MonoidHom.comp_apply]
      exact congrArg ψ' (map_blk e.symm.toRingHom 1 A)
  · obtain ⟨ψ4, hψ41, hψ40⟩ := hψ4
    refine ⟨ψ4.comp Φ, ?_, ?_⟩
    · rw [MonoidHom.comp_assoc, spMap_comp_spBlock e.symm.toRingHom hΦ 1, ← MonoidHom.comp_assoc,
        hψ41]
    · rw [MonoidHom.comp_assoc, spMap_comp_spBlock e.symm.toRingHom hΦ 0, ← MonoidHom.comp_assoc,
        hψ40]

end Transport

end CFSG.ComponentClassification.CatLeafProof
