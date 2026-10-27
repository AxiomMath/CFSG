module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCoverBridge
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotFieldYModel

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup Matrix
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadMinus
  minusIndexEquiv coordinateQuadMinus_apply regular_coordinateQuadMinus)
open CFSG.SeitzReduction.SymplecticPilot (liftParam)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (incl incl_mk inclHom inclHom_val glIncl_val)
open CFSG.SeitzReduction.TwistedE6Pilot (isExtension_coordinateQuadMinus)
open CFSG.Adapters.RankTwoModelTransports (glCongr glCongr_coe glCongr_statedScalars)

section Frame

variable {K : Type} [Field K] {n : ℕ}

theorem minusFrameLin_mem_stabSub (hn : 1 ≤ n) (b c : K) {k : Fin (n - 1)}
    {t : Fin (n - 1) → Kˣ} (ht : t k = 1) :
    frameLin (minusFrameLeft hn) (minusFrameRight hn) t ∈
      stabSub (K := K) (minusIndexEquiv n hn (.inl k)) (minusIndexEquiv n hn (.inr (.inl k))) := by
  have h := isHypFrame_minus K hn b c
  refine ⟨?_, ?_⟩
  · funext i
    rw [frameLin_apply]
    by_cases hi : i = minusFrameLeft hn k
    · subst hi
      rw [h.frameEntry_left, ht]
      simp [minusFrameLeft]
    · have hi' : i ≠ minusIndexEquiv n hn (.inl k) := hi
      simp [hi']
  · funext i
    rw [frameLin_apply]
    by_cases hi : i = minusFrameRight hn k
    · subst hi
      rw [h.frameEntry_right, ht]
      simp [minusFrameRight]
    · have hi' : i ≠ minusIndexEquiv n hn (.inr (.inl k)) := hi
      simp [hi']

variable [Finite K] [CharP K 2]

theorem frameHom_mem_minusPairPerp {hn : 1 ≤ n} {b c : K} {k : Fin (n - 1)}
    {t : Fin (n - 1) → Kˣ} (ht : t k = 1) :
    (isHypFrame_minus K hn b c).frameHom t ∈ minusPairPerp hn b c k := by
  rw [IsHypFrame.frameHom_apply]
  exact ⟨⟨frameLin (minusFrameLeft hn) (minusFrameRight hn) t,
    (isHypFrame_minus K hn b c).frameLin_mem_orthDerived t⟩,
    Subgroup.mem_subgroupOf.2 (minusFrameLin_mem_stabSub hn b c ht), rfl⟩

theorem frameHom_mulSingle_mem_minusPairTorus {hn : 1 ≤ n} {b c : K} (k : Fin (n - 1))
    (x : Kˣ) :
    (isHypFrame_minus K hn b c).frameHom (Pi.mulSingle k x) ∈ minusPairTorus hn b c k := by
  rw [← minusFrameTorus_rootParam]
  exact (isHypFrame_minus K hn b c).frameHom_mem_frameTorusOf (mulSingle_mem_rootParam k x)

end Frame

section Perp

variable {K : Type} [Field K] {n : ℕ}

theorem frameEntry_minus_aniso {N : ℕ} (hN : 1 ≤ N) (t : Fin (N - 1) → Kˣ)
    (l : Fin 2) :
    frameEntry (minusFrameLeft hN) (minusFrameRight hN) t (minusIndexEquiv N hN (.inr (.inr l))) =
      1 :=
  frameEntry_of_forall_ne t (fun _ h => Sum.inr_ne_inl ((minusIndexEquiv N hN).injective h))
    (fun _ h => Sum.inr_ne_inl (Sum.inr_injective ((minusIndexEquiv N hN).injective h)))

theorem frameEntry_minusPerpCoord (hn : 2 ≤ n) (k : Fin (n - 1)) (t : Fin (n - 1) → Kˣ)
    (x : Fin (2 * (n - 1))) :
    frameEntry (minusFrameLeft (by omega : 1 ≤ n)) (minusFrameRight (by omega : 1 ≤ n)) t
        (minusPerpCoord hn k x) =
      frameEntry (minusFrameLeft (n := n - 1) (by omega))
        (minusFrameRight (n := n - 1) (by omega)) (fun l => t (avoid (by omega) k l)) x := by
  obtain ⟨σ, rfl⟩ := (minusIndexEquiv (n - 1) (by omega)).surjective x
  have hσ : minusPerpCoord hn k (minusIndexEquiv (n - 1) (by omega) σ) =
      minusIndexEquiv n (by omega)
        (Sum.map (avoid (by omega) k) (Sum.map (avoid (by omega) k) id) σ) := by
    simp [minusPerpCoord]
  rw [hσ]
  rcases σ with l | l | l
  · exact ((isHypFrame_minus K (by omega : 1 ≤ n) 0 0).frameEntry_left t _).trans
      ((isHypFrame_minus K (by omega : 1 ≤ n - 1) 0 0).frameEntry_left
        (fun l => t (avoid (by omega) k l)) l).symm
  · exact ((isHypFrame_minus K (by omega : 1 ≤ n) 0 0).frameEntry_right t _).trans
      ((isHypFrame_minus K (by omega : 1 ≤ n - 1) 0 0).frameEntry_right
        (fun l => t (avoid (by omega) k l)) l).symm
  · exact (frameEntry_minus_aniso (by omega : 1 ≤ n) t l).trans
      (frameEntry_minus_aniso (by omega : 1 ≤ n - 1) _ l).symm

variable [Finite K] [CharP K 2]

theorem minusPairPerpEquiv_frameHom (hn : 5 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : Fin (n - 1)) {t : Fin (n - 1) → Kˣ}
    (ht : t k = 1) :
    ((minusPairPerpEquiv hn hirr k ⟨(isHypFrame_minus K (by omega) b c).frameHom t,
        frameHom_mem_minusPairPerp ht⟩ :
      orthDerived (coordinateQuadMinus (n - 1) K (by omega) b c)) :
        (Fin (2 * (n - 1)) → K) ≃ₗ[K] (Fin (2 * (n - 1)) → K)) =
      frameLin (minusFrameLeft (n := n - 1) (by omega)) (minusFrameRight (n := n - 1) (by omega))
        (fun l => t (avoid (by omega) k l)) := by
  set h := isHypCoord_coordinateQuadMinus (K := K) (by omega : 1 ≤ n) b c k
  set y : stabDerived (coordinateQuadMinus n K (by omega) b c)
      (minusIndexEquiv n (by omega) (.inl k)) (minusIndexEquiv n (by omega) (.inr (.inl k))) :=
    ⟨⟨frameLin (minusFrameLeft (by omega)) (minusFrameRight (by omega)) t,
      (isHypFrame_minus K (by omega) b c).frameLin_mem_orthDerived t⟩,
      Subgroup.mem_subgroupOf.2 (minusFrameLin_mem_stabSub (by omega) b c ht)⟩ with hy
  have hsymm : ((stabDerived (coordinateQuadMinus n K (by omega) b c)
      (minusIndexEquiv n (by omega) (.inl k))
      (minusIndexEquiv n (by omega) (.inr (.inl k)))).equivMapOfInjective
        (projHom (coordinateQuadMinus n K (by omega) b c))
      (projHom_injective h.exists_ne_zero)).symm
        ⟨(isHypFrame_minus K (by omega) b c).frameHom t, frameHom_mem_minusPairPerp ht⟩ = y := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  have key : minusPairPerpEquiv hn hirr k
      ⟨(isHypFrame_minus K (by omega) b c).frameHom t, frameHom_mem_minusPairPerp ht⟩ =
      orthDerivedCongr (minusPerpIsometry (by omega) b c k)
        (h.stabDerivedEquiv (regular_coordinateQuadMinus n K b c (by omega) hirr).1
          (regular_minusPerp hn hirr k).1 (regular_minusPerp hn hirr k).2 y) := by
    rw [← hsymm]
    rfl
  rw [key]
  ext w x
  have hcoe : ((orthDerivedCongr (minusPerpIsometry (K := K) (by omega) b c k)
      (h.stabDerivedEquiv (regular_coordinateQuadMinus n K b c (by omega) hirr).1
        (regular_minusPerp hn hirr k).1 (regular_minusPerp hn hirr k).2 y) :
      orthDerived (coordinateQuadMinus (n - 1) K (by omega) b c)) :
        (Fin (2 * (n - 1)) → K) ≃ₗ[K] (Fin (2 * (n - 1)) → K)) =
      LinearEquiv.autCongr (minusPerpIsometry (K := K) (by omega) b c k).toLinearEquiv
        ((h.stabDerivedEquiv (regular_coordinateQuadMinus n K b c (by omega) hirr).1
          (regular_minusPerp hn hirr k).1 (regular_minusPerp hn hirr k).2 y :
            orthDerived ((coordinateQuadMinus n K (by omega) b c).comp
              (perpSub K (minusIndexEquiv n (by omega) (.inl k))
                (minusIndexEquiv n (by omega) (.inr (.inl k)))).subtype)) :
          perpSub K (minusIndexEquiv n (by omega) (.inl k))
              (minusIndexEquiv n (by omega) (.inr (.inl k))) ≃ₗ[K]
            perpSub K (minusIndexEquiv n (by omega) (.inl k))
              (minusIndexEquiv n (by omega) (.inr (.inl k)))) := rfl
  rw [hcoe, LinearEquiv.autCongr_apply_apply]
  change ((frameLin (minusFrameLeft (by omega)) (minusFrameRight (by omega)) t)
      (Function.extend (minusPerpCoord (by omega) k) w 0)) (minusPerpCoord (by omega) k x) =
    frameLin (minusFrameLeft (n := n - 1) (by omega)) (minusFrameRight (n := n - 1) (by omega))
      (fun l => t (avoid (by omega) k l)) w x
  rw [frameLin_apply, frameLin_apply, (minusPerpCoord_injective _ k).extend_apply,
    frameEntry_minusPerpCoord]

@[expose] noncomputable def minusPairPerpModelEquiv (hn : 5 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : Fin (n - 1)) :
    minusPairPerp (K := K) (by omega : 1 ≤ n) b c k ≃*
      matrixProjectiveDerived (coordinateQuadMinus (n - 1) K (by omega) b c) :=
  (minusPairPerpEquiv hn hirr k).trans (MulEquiv.ofBijective (projHom _)
    ⟨projHom_injective (isHypCoord_coordinateQuadMinus (K := K) (by omega : 1 ≤ n - 1) b c
      (⟨0, by omega⟩ : Fin (n - 1 - 1))).exists_ne_zero, projHom_surjective _⟩)

theorem minusPairPerpModelEquiv_frameHom (hn : 5 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : Fin (n - 1)) {t : Fin (n - 1) → Kˣ}
    (ht : t k = 1) :
    minusPairPerpModelEquiv hn hirr k ⟨(isHypFrame_minus K (by omega) b c).frameHom t,
        frameHom_mem_minusPairPerp ht⟩ =
      (isHypFrame_minus K (n := n - 1) (by omega) b c).frameHom
        (fun l => t (avoid (by omega) k l)) := by
  change projHom (coordinateQuadMinus (n - 1) K (by omega) b c)
      (minusPairPerpEquiv hn hirr k ⟨_, frameHom_mem_minusPairPerp ht⟩) =
    projHom (coordinateQuadMinus (n - 1) K (by omega) b c)
      ⟨frameLin (minusFrameLeft (n := n - 1) (by omega)) (minusFrameRight (n := n - 1) (by omega))
        (fun l => t (avoid (by omega) k l)),
        (isHypFrame_minus K (n := n - 1) (by omega) b c).frameLin_mem_orthDerived _⟩
  congr 1
  exact Subtype.ext (minusPairPerpEquiv_frameHom hn hirr k ht)

end Perp

section Congr

variable {K k : Type} [Field K] [Field k] {d : ℕ}

theorem map_matrixIsometries_glCongr (φ : K ≃+* k) {Q₁ : QuadraticForm K (Fin d → K)}
    {Q₂ : QuadraticForm k (Fin d → k)} (hQ : ∀ v, Q₂ (φ ∘ v) = φ (Q₁ v)) :
    (matrixIsometries Q₁).map (glCongr φ).toMonoidHom = matrixIsometries Q₂ := by
  ext B
  constructor
  · rintro ⟨A, hA, rfl⟩
    have hA' : A ∈ matrixIsometries Q₁ := hA
    rw [mem_matrixIsometries_iff] at hA'
    rw [mem_matrixIsometries_iff]
    intro w
    obtain ⟨v, rfl⟩ : ∃ v, φ ∘ v = w := ⟨φ.symm ∘ w, funext fun i => φ.apply_symm_apply _⟩
    rw [matrixLinearEquiv_apply, MulEquiv.coe_toMonoidHom,
      CFSG.ClassicalInvolution.Upgrade.glCongr_mulVec, hQ, hQ, ← matrixLinearEquiv_apply, hA']
  · intro hB
    refine ⟨(glCongr φ).symm B, ?_, (glCongr φ).apply_symm_apply B⟩
    show (glCongr φ).symm B ∈ matrixIsometries Q₁
    rw [mem_matrixIsometries_iff] at hB ⊢
    intro v
    apply φ.injective
    rw [← hQ, ← hQ, matrixLinearEquiv_apply, ← CFSG.ClassicalInvolution.Upgrade.glCongr_mulVec,
      MulEquiv.apply_symm_apply, ← matrixLinearEquiv_apply, hB]

theorem map_matrixDerived_glCongr (φ : K ≃+* k) {Q₁ : QuadraticForm K (Fin d → K)}
    {Q₂ : QuadraticForm k (Fin d → k)} (hQ : ∀ v, Q₂ (φ ∘ v) = φ (Q₁ v)) :
    (matrixDerived Q₁).map (glCongr φ).toMonoidHom = matrixDerived Q₂ := by
  rw [matrixDerived, matrixDerived, Subgroup.map_commutator, map_matrixIsometries_glCongr φ hQ]

theorem map_matrixScalars_glCongr (φ : K ≃+* k) (d : ℕ) :
    (matrixScalars d K).map (glCongr φ).toMonoidHom = matrixScalars d k :=
  glCongr_statedScalars φ

@[expose] noncomputable def matrixProjectiveCongr (φ : K ≃+* k) {Q₁ : QuadraticForm K (Fin d → K)}
    {Q₂ : QuadraticForm k (Fin d → k)} (hQ : ∀ v, Q₂ (φ ∘ v) = φ (Q₁ v)) :
    matrixProjectiveDerived Q₁ ≃* matrixProjectiveDerived Q₂ :=
  CFSG.RankThree.PartOne.KCOrthogonalDescent.quotientSubgroupOfEquiv (glCongr φ)
    (map_matrixDerived_glCongr φ hQ) (map_matrixScalars_glCongr φ d)

theorem matrixProjectiveCongr_mk (φ : K ≃+* k) {Q₁ : QuadraticForm K (Fin d → K)}
    {Q₂ : QuadraticForm k (Fin d → k)} (hQ : ∀ v, Q₂ (φ ∘ v) = φ (Q₁ v)) (A : matrixDerived Q₁)
    (B : matrixDerived Q₂) (hB : (B : GL (Fin d) k) = glCongr φ (A : GL (Fin d) K)) :
    matrixProjectiveCongr φ hQ (matrixProjectiveProjection Q₁ A) =
      matrixProjectiveProjection Q₂ B :=
  CFSG.RankThree.PartOne.KCOrthogonalDescent.quotientSubgroupOfEquiv_mk _ _ _ A B hB

theorem matrixProjectiveCongr_frameHom [Finite K] [CharP K 2] [Finite k] [CharP k 2]
    (φ : K ≃+* k) {Q₁ : QuadraticForm K (Fin d → K)} {Q₂ : QuadraticForm k (Fin d → k)}
    (hQ : ∀ v, Q₂ (φ ∘ v) = φ (Q₁ v)) {m : ℕ} {a b : Fin m → Fin d} (h₁ : IsHypFrame Q₁ a b)
    (h₂ : IsHypFrame Q₂ a b) (t : Fin m → Kˣ) :
    matrixProjectiveCongr φ hQ (h₁.frameHom t) = h₂.frameHom (liftParam φ.toRingHom t) := by
  rw [IsHypFrame.frameHom_apply, IsHypFrame.frameHom_apply]
  change matrixProjectiveCongr φ hQ (matrixProjectiveProjection Q₁ ((derivedEquiv Q₁).symm _)) =
    matrixProjectiveProjection Q₂ ((derivedEquiv Q₂).symm _)
  apply matrixProjectiveCongr_mk
  apply Units.ext
  ext i j
  rw [glCongr_coe, Matrix.map_apply, derivedEquiv_symm_frameLin_entry h₂,
    derivedEquiv_symm_frameLin_entry h₁]
  by_cases hij : i = j
  · simp only [hij, ↓reduceIte]
    exact frameEntry_liftParam φ.toRingHom a b t j
  · simp only [hij, ↓reduceIte, map_zero]

theorem coordinateQuadMinus_comp_ringEquiv (φ : K ≃+* k) {n : ℕ} (hn : 1 ≤ n) (b c : K)
    (v : Fin (2 * n) → K) :
    coordinateQuadMinus n k hn (φ b) (φ c) (φ ∘ v) = φ (coordinateQuadMinus n K hn b c v) := by
  rw [coordinateQuadMinus_apply, coordinateQuadMinus_apply]
  simp only [Function.comp_apply, map_add, map_mul, map_sum, map_pow]

@[expose] noncomputable def minusCongr (φ : K ≃+* k) {n : ℕ} (hn : 1 ≤ n) (b c : K) :
    matrixProjectiveDerived (coordinateQuadMinus n K hn b c) ≃*
      matrixProjectiveDerived (coordinateQuadMinus n k hn (φ b) (φ c)) :=
  matrixProjectiveCongr φ (coordinateQuadMinus_comp_ringEquiv φ hn b c)

theorem minusCongr_frameHom [Finite K] [CharP K 2] [Finite k] [CharP k 2] (φ : K ≃+* k) {n : ℕ}
    (hn : 1 ≤ n) (b c : K) (t : Fin (n - 1) → Kˣ) :
    minusCongr φ hn b c ((isHypFrame_minus K hn b c).frameHom t) =
      (isHypFrame_minus k hn (φ b) (φ c)).frameHom (liftParam φ.toRingHom t) :=
  matrixProjectiveCongr_frameHom φ _ _ _ t

end Congr

section Incl

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

theorem incl_frameHom_minus (k : Subfield F) [CharP k 2] (hn : 1 ≤ n) (b c : k)
    (s : Fin (n - 1) → kˣ) :
    incl k (isExtension_coordinateQuadMinus k hn b c) ((isHypFrame_minus k hn b c).frameHom s) =
      (isHypFrame_minus F hn (b : F) (c : F)).frameHom (liftParam k.subtype s) := by
  rw [IsHypFrame.frameHom_apply, IsHypFrame.frameHom_apply]
  change incl k _ (matrixProjectiveProjection _ ((derivedEquiv _).symm ⟨_, _⟩)) =
    matrixProjectiveProjection _ ((derivedEquiv _).symm ⟨_, _⟩)
  rw [incl_mk]
  congr 1
  apply Subtype.ext
  apply Units.ext
  ext i j
  rw [inclHom_val, glIncl_val, Matrix.map_apply,
    derivedEquiv_symm_frameLin_entry (isHypFrame_minus k hn b c),
    derivedEquiv_symm_frameLin_entry (isHypFrame_minus F hn (b : F) (c : F))]
  by_cases hij : i = j
  · simp only [hij, ↓reduceIte]
    exact (frameEntry_liftParam k.subtype _ _ s j).symm
  · simp only [hij, ↓reduceIte, map_zero]

end Incl

end CFSG.SeitzReduction.OmegaPilot
