module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCoverEquivariant
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotFieldNormalizeAut

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup Matrix
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadPlus)
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus plusIndexEquiv
  regular_coordinateQuadPlus)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
  (statedDerivedReindexEquiv statedDerivedReindexEquiv_symm_entry)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (incl incl_mk inclHom inclHom_val glIncl_val
  IsExtension)
open CFSG.SeitzReduction.SymplecticPilot (diagSpEntry diagSpEntry_inl diagSpEntry_inr)
open CFSG.Adapters.RankTwoModelTransports (glCongr glCongr_coe)
open CFSG.ClassicalInvolution.Upgrade (map_statedOmega)

section Matrix

variable {K : Type*} [Field K] {d : ℕ}

theorem derivedEquiv_symm_entry (Q : QuadraticForm K (Fin d → K)) (x : orthDerived Q)
    (a b : Fin d) :
    (((derivedEquiv Q).symm x : matrixDerived Q) : GL (Fin d) K).val a b =
      ((x : (Fin d → K) ≃ₗ[K] (Fin d → K)) (Pi.single b 1)) a := by
  set A := (derivedEquiv Q).symm x with hA
  have hx : derivedEquiv Q A = x := (derivedEquiv Q).apply_symm_apply x
  rw [← hx, coe_derivedEquiv]
  change (A : GL (Fin d) K).val a b = ((A : GL (Fin d) K).val *ᵥ Pi.single b 1) a
  rw [Matrix.mulVec_single_one]
  rfl

theorem derivedEquiv_symm_frameLin_entry {m : ℕ} [Finite K] [CharP K 2]
    {Q : QuadraticForm K (Fin d → K)} {a b : Fin m → Fin d} (h : IsHypFrame Q a b)
    (t : Fin m → Kˣ) (i j : Fin d) :
    (((derivedEquiv Q).symm ⟨frameLin a b t, h.frameLin_mem_orthDerived t⟩ : matrixDerived Q) :
      GL (Fin d) K).val i j = if i = j then ((frameEntry a b t i : Kˣ) : K) else 0 := by
  rw [derivedEquiv_symm_entry]
  change ((frameEntry a b t i : Kˣ) : K) * (Pi.single j (1 : K) : Fin d → K) i = _
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij]

end Matrix

section Stated

variable (F : Type) [Field F] [CharP F 2] (m : ℕ)

@[expose] noncomputable def statedDerivedPlusEquiv :
    StatedOmega (StatedQuadPlus m F) ≃* matrixDerived (coordinateQuadPlus m F) :=
  statedDerivedReindexEquiv (plusIndexEquiv m) (CFSG.LieType.Universal.Spin.quadPlus m F)
    (CFSG.LieType.Universal.Spin.coe_quadPlus m F)

omit [CharP F 2] in
theorem statedDerivedPlusEquiv_symm_entry (A : matrixDerived (coordinateQuadPlus m F))
    (i j : Fin m ⊕ Fin m) :
    (((statedDerivedPlusEquiv F m).symm A : StatedOmega (StatedQuadPlus m F)) :
      GL (Fin m ⊕ Fin m) F).val i j =
      (A : GL (Fin (2 * m)) F).val (plusIndexEquiv m i) (plusIndexEquiv m j) :=
  statedDerivedReindexEquiv_symm_entry _ _ _ A i j

@[expose] noncomputable def statedOmegaPlusEquiv (hm : 1 ≤ m) :
    StatedOmega (StatedQuadPlus m F) ≃* matrixProjectiveDerived (coordinateQuadPlus m F) :=
  (statedDerivedPlusEquiv F m).trans
    (MulEquiv.ofBijective (matrixProjectiveProjection (coordinateQuadPlus m F))
      ⟨fun x y hxy => by
        have hne := (isHypCoord_coordinateQuadPlus (K := F) (⟨0, by omega⟩ : Fin m)).exists_ne_zero
        have h1 : projHom (coordinateQuadPlus m F) (derivedEquiv _ x) =
            projHom (coordinateQuadPlus m F) (derivedEquiv _ y) := by
          change matrixProjectiveProjection _ ((derivedEquiv _).symm (derivedEquiv _ x)) =
            matrixProjectiveProjection _ ((derivedEquiv _).symm (derivedEquiv _ y))
          rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
          exact hxy
        exact (derivedEquiv _).injective (projHom_injective hne h1),
        matrixProjectiveProjection_surjective _⟩)

variable {F m}

theorem statedOmegaPlusEquiv_symm_frameHom [Finite F] (hm : 1 ≤ m) (u : Fin m → Fˣ) :
    (((statedOmegaPlusEquiv F m hm).symm ((isHypFrame_plus F m).frameHom u) :
      StatedOmega (StatedQuadPlus m F)) : GL (Fin m ⊕ Fin m) F) = diagOmega F m u := by
  set A := (derivedEquiv (coordinateQuadPlus m F)).symm
    ⟨frameLin (plusFrameLeft m) (plusFrameRight m) u,
      (isHypFrame_plus F m).frameLin_mem_orthDerived u⟩ with hA
  have hfr : (isHypFrame_plus F m).frameHom u = matrixProjectiveProjection _ A := rfl
  have hsymm : (statedOmegaPlusEquiv F m hm).symm (matrixProjectiveProjection _ A) =
      (statedDerivedPlusEquiv F m).symm A := by
    rw [MulEquiv.symm_apply_eq]
    simp only [statedOmegaPlusEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    rfl
  rw [hfr, hsymm]
  apply Units.ext
  ext a c
  have hent := statedDerivedPlusEquiv_symm_entry F m A a c
  have hA' := derivedEquiv_symm_frameLin_entry (isHypFrame_plus F m) u (plusIndexEquiv m a)
    (plusIndexEquiv m c)
  refine hent.trans (hA'.trans ?_)
  by_cases hac : a = c
  · subst hac
    simp only [↓reduceIte, diagOmega_apply_self]
    rcases a with l | l
    · rw [diagSpEntry_inl]
      exact congrArg Units.val ((isHypFrame_plus F m).frameEntry_left u l)
    · rw [diagSpEntry_inr]
      exact congrArg Units.val ((isHypFrame_plus F m).frameEntry_right u l)
  · simp only [(plusIndexEquiv m).injective.eq_iff, hac, ↓reduceIte, diagOmega_apply_ne u hac]

theorem statedOmegaPlusEquiv_diag [Finite F] (hm : 1 ≤ m) (u : Fin m → Fˣ)
    (hu : diagOmega F m u ∈ StatedOmega (StatedQuadPlus m F)) :
    statedOmegaPlusEquiv F m hm ⟨diagOmega F m u, hu⟩ = (isHypFrame_plus F m).frameHom u := by
  rw [← MulEquiv.eq_symm_apply]
  exact Subtype.ext (statedOmegaPlusEquiv_symm_frameHom hm u).symm

theorem diagOmega_mem_statedOmega_of_one_le [Finite F] (hm : 1 ≤ m) (u : Fin m → Fˣ) :
    diagOmega F m u ∈ StatedOmega (StatedQuadPlus m F) := by
  rw [← statedOmegaPlusEquiv_symm_frameHom hm u]
  exact Subtype.property _

end Stated

section Incl

open CFSG.SeitzReduction.SymplecticPilot (liftParam)

theorem frameEntry_liftParam {K F : Type} [Field K] [Field F] (ι : K →+* F) {ι' : Type*}
    [DecidableEq ι'] {m : ℕ} (a b : Fin m → ι') (t : Fin m → Kˣ) (i : ι') :
    ((frameEntry a b (liftParam ι t) i : Fˣ) : F) = ι ((frameEntry a b t i : Kˣ) : K) := by
  simp only [frameEntry, Units.coe_prod, map_prod]
  refine Finset.prod_congr rfl fun l _ => ?_
  unfold torusEntry
  split_ifs <;> simp [liftParam]

variable {F : Type} [Field F] [Finite F] [CharP F 2] {m : ℕ}

theorem incl_frameHom (k : Subfield F) [CharP k 2] (s : Fin m → kˣ) :
    incl k (CFSG.SeitzReduction.E7Pilot.isExtension_coordinateQuadPlus m k)
        ((isHypFrame_plus k m).frameHom s) =
      (isHypFrame_plus F m).frameHom (liftParam k.subtype s) := by
  rw [IsHypFrame.frameHom_apply, IsHypFrame.frameHom_apply]
  change incl k _ (matrixProjectiveProjection _ ((derivedEquiv _).symm ⟨_, _⟩)) =
    matrixProjectiveProjection _ ((derivedEquiv _).symm ⟨_, _⟩)
  rw [incl_mk]
  congr 1
  apply Subtype.ext
  apply Units.ext
  ext i j
  rw [inclHom_val, glIncl_val, Matrix.map_apply,
    derivedEquiv_symm_frameLin_entry (isHypFrame_plus k m),
    derivedEquiv_symm_frameLin_entry (isHypFrame_plus F m)]
  by_cases hij : i = j
  · simp only [hij, ↓reduceIte]
    exact (frameEntry_liftParam k.subtype _ _ s j).symm
  · simp only [hij, ↓reduceIte, map_zero]

end Incl

section Congr

open CFSG.SeitzReduction.SymplecticPilot (liftParam)

variable {K k : Type} [Field K] [Field k]

@[expose] noncomputable def statedOmegaPlusCongr (φ : K ≃+* k) (m : ℕ) :
    StatedOmega (StatedQuadPlus m K) ≃* StatedOmega (StatedQuadPlus m k) :=
  ((glCongr φ).subgroupMap _).trans (MulEquiv.subgroupCongr
    (map_statedOmega φ (CFSG.ClassicalInvolution.Upgrade.statedQuadPlus_comp φ)))

theorem coe_statedOmegaPlusCongr (φ : K ≃+* k) {m : ℕ} (x : StatedOmega (StatedQuadPlus m K)) :
    ((statedOmegaPlusCongr φ m x : StatedOmega (StatedQuadPlus m k)) : GL (Fin m ⊕ Fin m) k) =
      glCongr φ (x : GL (Fin m ⊕ Fin m) K) :=
  rfl

theorem glCongr_diagOmega (φ : K ≃+* k) {m : ℕ} (s : Fin m → Kˣ) :
    glCongr φ (diagOmega K m s) = diagOmega k m (liftParam φ.toRingHom s) := by
  apply Units.ext
  rw [glCongr_coe, diagOmega_coe, diagOmega_coe, Matrix.diagonal_map (map_zero φ)]
  congr 1
  funext a
  rcases a with l | l <;> simp [diagSpEntry, liftParam]

end Congr

section Perp

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

omit [Finite K] [CharP K 2] in
theorem frameEntry_plusPerpCoord (hn : 1 ≤ n) (k : Fin n) (t : Fin n → Kˣ)
    (x : Fin (2 * (n - 1))) :
    frameEntry (plusFrameLeft n) (plusFrameRight n) t (plusPerpCoord hn k x) =
      frameEntry (plusFrameLeft (n - 1)) (plusFrameRight (n - 1))
        (fun l => t (avoid (by omega) k l)) x := by
  obtain ⟨σ, rfl⟩ := (plusIndexEquiv (n - 1)).surjective x
  have hσ : plusPerpCoord hn k (plusIndexEquiv (n - 1) σ) =
      plusIndexEquiv n (Sum.map (avoid (by omega) k) (avoid (by omega) k) σ) := by
    simp [plusPerpCoord]
  rw [hσ]
  rcases σ with l | l
  · exact ((isHypFrame_plus K n).frameEntry_left t _).trans
      ((isHypFrame_plus K (n - 1)).frameEntry_left (fun l => t (avoid (by omega) k l)) l).symm
  · exact ((isHypFrame_plus K n).frameEntry_right t _).trans
      ((isHypFrame_plus K (n - 1)).frameEntry_right (fun l => t (avoid (by omega) k l)) l).symm

theorem pairPerpEquiv_frameHom (hn : 4 ≤ n) (k : Fin n) {t : Fin n → Kˣ} (ht : t k = 1) :
    ((pairPerpEquiv hn k ⟨(isHypFrame_plus K n).frameHom t, frameHom_mem_pairPerp ht⟩ :
      orthDerived (coordinateQuadPlus (n - 1) K)) :
        (Fin (2 * (n - 1)) → K) ≃ₗ[K] (Fin (2 * (n - 1)) → K)) =
      frameLin (plusFrameLeft (n - 1)) (plusFrameRight (n - 1))
        (fun l => t (avoid (by omega) k l)) := by
  set h := isHypCoord_coordinateQuadPlus (K := K) k
  set y : stabDerived (coordinateQuadPlus n K) (plusIndexEquiv n (.inl k))
      (plusIndexEquiv n (.inr k)) :=
    ⟨⟨frameLin (plusFrameLeft n) (plusFrameRight n) t,
      (isHypFrame_plus K n).frameLin_mem_orthDerived t⟩,
      Subgroup.mem_subgroupOf.2 (frameLin_mem_stabSub ht)⟩ with hy
  have hsymm : ((stabDerived (coordinateQuadPlus n K) (plusIndexEquiv n (.inl k))
      (plusIndexEquiv n (.inr k))).equivMapOfInjective (projHom (coordinateQuadPlus n K))
      (projHom_injective h.exists_ne_zero)).symm
        ⟨(isHypFrame_plus K n).frameHom t, frameHom_mem_pairPerp ht⟩ = y := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  have key : pairPerpEquiv hn k ⟨(isHypFrame_plus K n).frameHom t, frameHom_mem_pairPerp ht⟩ =
      orthDerivedCongr (plusPerpIsometry (by omega) k)
        (h.stabDerivedEquiv (regular_coordinateQuadPlus n K (by omega)).1
          (regular_plusPerp hn k).1 (regular_plusPerp hn k).2 y) := by
    rw [← hsymm]
    rfl
  rw [key]
  ext w x
  have hcoe : ((orthDerivedCongr (plusPerpIsometry (K := K) (by omega) k)
      (h.stabDerivedEquiv (regular_coordinateQuadPlus n K (by omega)).1
        (regular_plusPerp hn k).1 (regular_plusPerp hn k).2 y) :
      orthDerived (coordinateQuadPlus (n - 1) K)) :
        (Fin (2 * (n - 1)) → K) ≃ₗ[K] (Fin (2 * (n - 1)) → K)) =
      LinearEquiv.autCongr (plusPerpIsometry (K := K) (by omega) k).toLinearEquiv
        ((h.stabDerivedEquiv (regular_coordinateQuadPlus n K (by omega)).1
          (regular_plusPerp hn k).1 (regular_plusPerp hn k).2 y :
            orthDerived ((coordinateQuadPlus n K).comp
              (perpSub K (plusIndexEquiv n (.inl k)) (plusIndexEquiv n (.inr k))).subtype)) :
          perpSub K (plusIndexEquiv n (.inl k)) (plusIndexEquiv n (.inr k)) ≃ₗ[K]
            perpSub K (plusIndexEquiv n (.inl k)) (plusIndexEquiv n (.inr k))) := rfl
  rw [hcoe, LinearEquiv.autCongr_apply_apply]
  change ((frameLin (plusFrameLeft n) (plusFrameRight n) t)
      (Function.extend (plusPerpCoord (by omega) k) w 0)) (plusPerpCoord (by omega) k x) =
    frameLin (plusFrameLeft (n - 1)) (plusFrameRight (n - 1))
      (fun l => t (avoid (by omega) k l)) w x
  rw [frameLin_apply, frameLin_apply, (plusPerpCoord_injective _ k).extend_apply,
    frameEntry_plusPerpCoord]

@[expose] noncomputable def pairPerpModelEquiv (hn : 4 ≤ n) (k : Fin n) :
    pairPerp (K := K) k ≃* matrixProjectiveDerived (coordinateQuadPlus (n - 1) K) :=
  (pairPerpEquiv hn k).trans (MulEquiv.ofBijective (projHom _)
    ⟨projHom_injective (isHypCoord_coordinateQuadPlus (K := K)
      (⟨0, by omega⟩ : Fin (n - 1))).exists_ne_zero, projHom_surjective _⟩)

theorem pairPerpModelEquiv_frameHom (hn : 4 ≤ n) (k : Fin n) {t : Fin n → Kˣ} (ht : t k = 1) :
    pairPerpModelEquiv hn k ⟨(isHypFrame_plus K n).frameHom t, frameHom_mem_pairPerp ht⟩ =
      (isHypFrame_plus K (n - 1)).frameHom (fun l => t (avoid (by omega) k l)) := by
  change projHom (coordinateQuadPlus (n - 1) K)
      (pairPerpEquiv hn k ⟨_, frameHom_mem_pairPerp ht⟩) =
    projHom (coordinateQuadPlus (n - 1) K)
      ⟨frameLin (plusFrameLeft (n - 1)) (plusFrameRight (n - 1))
        (fun l => t (avoid (by omega) k l)),
        (isHypFrame_plus K (n - 1)).frameLin_mem_orthDerived _⟩
  congr 1
  exact Subtype.ext (pairPerpEquiv_frameHom hn k ht)

end Perp

end CFSG.SeitzReduction.OmegaPilot
