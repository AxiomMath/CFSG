module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166OmBlocks2Base
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusGen

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.OmegaPair

open Subgroup CFSG.Open
open CFSG.SeitzReduction.OmegaPilot
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus plusIndexEquiv)
open CFSG.ClassicalGroups.Orthogonal
open QuadraticMap

variable {K : Type} [Field K] [CharP K 2]

@[expose] noncomputable def rootSpacePoint (n : ℕ) (hn : 4 ≤ n) : Submodule K (Fin (2 * n) → K) where
  carrier := {y | y (plusFrameLeft n (zeroIdx n hn)) = 0 ∧
    y (plusFrameRight n (zeroIdx n hn)) = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro y z ⟨h1, h2⟩ ⟨g1, g2⟩
    exact ⟨by simp [h1, g1], by simp [h2, g2]⟩
  smul_mem' := by
    rintro c x ⟨h1, h2⟩
    exact ⟨by simp [Pi.smul_apply, h1], by simp [Pi.smul_apply, h2]⟩

theorem polar_frameE_rootSpacePoint (n : ℕ) (hn : 4 ≤ n) (y : rootSpacePoint (K := K) n hn) :
    polar (coordinateQuadPlus n K) (frameE n (zeroIdx n hn))
      ((y : rootSpacePoint n hn) : Fin (2 * n) → K) = 0 := by
  have h := isHypCoord_coordinateQuadPlus (K := K) (zeroIdx n hn)
  simp only [frameE, plusFrameLeft]
  rw [h.polar_left]
  exact y.2.2

theorem quad_frameE_zero (n : ℕ) (hn : 4 ≤ n) :
    coordinateQuadPlus n K (frameE n (zeroIdx n hn)) = 0 :=
  (isHypCoord_coordinateQuadPlus (K := K) (zeroIdx n hn)).map_left

@[expose] noncomputable def rootEltPoint (n : ℕ) (hn : 4 ≤ n)
    (y : rootSpacePoint (K := K) n hn) : orthDerived (coordinateQuadPlus n K) :=
  ⟨eichler (coordinateQuadPlus n K) (frameE n (zeroIdx n hn))
      ((y : rootSpacePoint n hn) : Fin (2 * n) → K),
    eichler_mem_orthDerived_plus (K := K) (n := n) (by omega) (frameE n (zeroIdx n hn))
      ((y : rootSpacePoint n hn) : Fin (2 * n) → K)⟩

@[expose] noncomputable def rootGroupHomPoint (n : ℕ) (hn : 4 ≤ n) :
    Multiplicative (rootSpacePoint (K := K) n hn) →*
      matrixProjectiveDerived (coordinateQuadPlus n K) where
  toFun y := projHom _ (rootEltPoint n hn y)
  map_one' := by
    have h1 : rootEltPoint n hn (1 : Multiplicative (rootSpacePoint (K := K) n hn)) = 1 := by
      apply Subtype.ext
      exact eichler_zero_right (coordinateQuadPlus n K) (frameE n (zeroIdx n hn))
    rw [h1, map_one]
  map_mul' y z := by
    have h1 : rootEltPoint n hn (y * z) = rootEltPoint n hn y * rootEltPoint n hn z := by
      apply Subtype.ext
      exact (eichler_mul (polar_frameE_rootSpacePoint (K := K) n hn y)
        (polar_frameE_rootSpacePoint (K := K) n hn z)).symm
    rw [h1, map_mul]

@[expose] noncomputable def rootGroupPoint (n : ℕ) (hn : 4 ≤ n) :
    Subgroup (matrixProjectiveDerived (coordinateQuadPlus n K)) :=
  (rootGroupHomPoint (K := K) n hn).range

theorem isPGroup_two_rootGroupPoint (n : ℕ) (hn : 4 ≤ n) :
    IsPGroup 2 (rootGroupPoint (K := K) n hn) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsquares : ∀ y : Multiplicative (rootSpacePoint (K := K) n hn), y ^ 2 = 1 := by
    intro y
    apply Multiplicative.toAdd.injective
    rw [pow_two]
    show Multiplicative.toAdd y + Multiplicative.toAdd y = 0
    have htwo : (2 : K) = 0 := CharTwo.two_eq_zero
    calc Multiplicative.toAdd y + Multiplicative.toAdd y
        = (1 + 1 : K) • Multiplicative.toAdd y := by rw [add_smul, one_smul]
      _ = (2 : K) • Multiplicative.toAdd y := by norm_num
      _ = 0 := by rw [htwo, zero_smul]
  refine IsPGroup.iff_orderOf.2 fun s => ?_
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.1 s.2
  let s' : rootGroupPoint (K := K) n hn :=
    ⟨rootGroupHomPoint (K := K) n hn y, by
      rw [rootGroupPoint]
      exact MonoidHom.mem_range.2 ⟨y, rfl⟩⟩
  have hs : s = s' := Subtype.ext hy.symm
  rw [hs]
  have hsq : s' ^ 2 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, Subgroup.coe_mk, _root_.sq, ← map_mul]
    rw [show y * y = 1 from by rw [← _root_.sq]; exact hsquares y, map_one]
  have hdvd : orderOf s' ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
  · exact ⟨0, by rw [h1]; simp⟩
  · exact ⟨1, by rw [h2]; simp⟩

section Action

variable [Finite K]

@[expose] noncomputable def torusActionPoint (n : ℕ) (hn : 4 ≤ n) (t : Fin n → Kˣ)
    (y : rootSpacePoint (K := K) n hn) : rootSpacePoint (K := K) n hn where
  val := (t (zeroIdx n hn) : K) •
    ((frameLin (plusFrameLeft n) (plusFrameRight n)) t)
      ((y : rootSpacePoint n hn) : Fin (2 * n) → K)
  property := by
    obtain ⟨h1, h2⟩ := y.2
    refine ⟨?_, ?_⟩
    · rw [Pi.smul_apply, frameLin_apply,
        IsHypFrame.frameEntry_left (plusFrame (K := K) n) t (zeroIdx n hn)]
      simp [h1]
    · rw [Pi.smul_apply, frameLin_apply,
        IsHypFrame.frameEntry_right (plusFrame (K := K) n) t (zeroIdx n hn)]
      simp [h2]

theorem frameLin_conj_rootEltPoint (n : ℕ) (hn : 4 ≤ n) (t : Fin n → Kˣ)
    (y : rootSpacePoint (K := K) n hn) :
    (⟨(frameLin (plusFrameLeft n) (plusFrameRight n)) t,
        (plusFrame (K := K) n).frameLin_mem_orthDerived t⟩ :
        orthDerived (coordinateQuadPlus n K)) * rootEltPoint n hn y *
      (⟨(frameLin (plusFrameLeft n) (plusFrameRight n)) t,
        (plusFrame (K := K) n).frameLin_mem_orthDerived t⟩ :
        orthDerived (coordinateQuadPlus n K))⁻¹ =
      rootEltPoint n hn (torusActionPoint n hn t y) := by
  apply Subtype.ext
  show (frameLin (plusFrameLeft n) (plusFrameRight n)) t *
      eichler (coordinateQuadPlus n K) (frameE n (zeroIdx n hn))
        ((y : rootSpacePoint n hn) : Fin (2 * n) → K) *
      ((frameLin (plusFrameLeft n) (plusFrameRight n)) t)⁻¹ =
    eichler (coordinateQuadPlus n K) (frameE n (zeroIdx n hn))
      (((t (zeroIdx n hn) : K) •
        ((frameLin (plusFrameLeft n) (plusFrameRight n)) t)
          ((y : rootSpacePoint n hn) : Fin (2 * n) → K)))
  rw [eichler_conj ((plusFrame (K := K) n).frameLin_mem_orthogonalGroup t)]
  have h1 : (frameLin (plusFrameLeft n) (plusFrameRight n)) t (frameE n (zeroIdx n hn)) =
      (t (zeroIdx n hn) : K) • frameE n (zeroIdx n hn) := by
    rw [frameE]
    exact IsHypFrame.frameLin_single_left (plusFrame (K := K) n) t (zeroIdx n hn)
  rw [h1, eichler_smul_left]

theorem frameHom_conj_rootGroupHomPoint (n : ℕ) (hn : 4 ≤ n) (t : Fin n → Kˣ)
    (y : rootSpacePoint (K := K) n hn) :
    (plusFrame (K := K) n).frameHom t * rootGroupHomPoint n hn y *
        ((plusFrame (K := K) n).frameHom t)⁻¹ =
      rootGroupHomPoint n hn (torusActionPoint n hn t y) := by
  have h := congrArg (projHom (coordinateQuadPlus n K)) (frameLin_conj_rootEltPoint n hn t y)
  simpa [IsHypFrame.frameHom_apply, rootGroupHomPoint, MonoidHom.comp_apply, map_mul, map_inv]
    using h

theorem qTorusHom_conj_rootGroupHomPoint (n q : ℕ) (hn : 4 ≤ n)
    (p : Fin n → rootsOfUnity q K) (y : rootSpacePoint (K := K) n hn) :
    qTorusHom (K := K) n q p * rootGroupHomPoint n hn y *
        (qTorusHom (K := K) n q p)⁻¹ =
      rootGroupHomPoint n hn
        (torusActionPoint n hn ((MonoidHom.compLeft (rootsOfUnity q K).subtype (Fin n)) p) y) := by
  change (plusFrame (K := K) n).frameHom ((MonoidHom.compLeft (rootsOfUnity q K).subtype (Fin n)) p) *
      rootGroupHomPoint n hn y * ((plusFrame (K := K) n).frameHom
        ((MonoidHom.compLeft (rootsOfUnity q K).subtype (Fin n)) p))⁻¹ = _
  rw [frameHom_conj_rootGroupHomPoint]

theorem qTorus_le_normalizer_rootGroupPoint (n q : ℕ) (hn : 4 ≤ n) :
    qTorus (K := K) n q ≤ Subgroup.normalizer (rootGroupPoint (K := K) n hn : Set _) := by
  rw [Subgroup.le_normalizer_iff]
  intro b hb s hs
  rw [qTorus_eq_range] at hb
  obtain ⟨p, hp⟩ := MonoidHom.mem_range.1 hb
  rw [rootGroupPoint] at hs
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.1 hs
  rw [← hp, ← hy]
  rw [qTorusHom_conj_rootGroupHomPoint (K := K) n q hn p y]
  exact MonoidHom.mem_range.2 ⟨_, rfl⟩

end Action

@[expose] noncomputable def rootEZ (n : ℕ) (hn : 4 ≤ n) (i : Fin n) (hi0 : i ≠ zeroIdx n hn) :
    rootSpacePoint (K := K) n hn where
  val := frameE n i
  property := by
    refine ⟨?_, ?_⟩
    · rw [frameE]
      exact Pi.single_eq_of_ne (fun h => hi0 ((plusFrameLeft_injective n h)).symm) 1
    · rw [frameE]
      exact Pi.single_eq_of_ne (fun h => Sum.inr_ne_inl ((plusIndexEquiv n).injective h)) 1

@[expose] noncomputable def rootFZ (n : ℕ) (hn : 4 ≤ n) (i : Fin n) (hi0 : i ≠ zeroIdx n hn) :
    rootSpacePoint (K := K) n hn where
  val := frameF n i
  property := by
    refine ⟨?_, ?_⟩
    · rw [frameF]
      exact Pi.single_eq_of_ne (fun h => Sum.inl_ne_inr ((plusIndexEquiv n).injective h)) 1
    · rw [frameF]
      exact Pi.single_eq_of_ne (fun h => hi0 ((plusFrameRight_injective n h)).symm) 1

theorem coe_torusAction_rootEZ (n : ℕ) (hn : 4 ≤ n) (t : Fin n → Kˣ) (i : Fin n)
    (hi0 : i ≠ zeroIdx n hn) :
    ((torusActionPoint n hn t (rootEZ (K := K) n hn i hi0) : rootSpacePoint (K := K) n hn) :
        Fin (2 * n) → K) =
      ((t (zeroIdx n hn) : K) * (t i : K)) • frameE n i := by
  simp only [torusActionPoint, rootEZ, frameE]
  rw [IsHypFrame.frameLin_single_left (plusFrame (K := K) n) t i, smul_smul]

theorem coe_torusAction_rootFZ (n : ℕ) (hn : 4 ≤ n) (t : Fin n → Kˣ) (i : Fin n)
    (hi0 : i ≠ zeroIdx n hn) :
    ((torusActionPoint n hn t (rootFZ (K := K) n hn i hi0) : rootSpacePoint (K := K) n hn) :
        Fin (2 * n) → K) =
      ((t (zeroIdx n hn) : K) * ((t i : K))⁻¹) • frameF n i := by
  simp only [torusActionPoint, rootFZ, frameF]
  rw [IsHypFrame.frameLin_single_right (plusFrame (K := K) n) t i, smul_smul]
  simp [Units.val_inv_eq_inv_val]

theorem eichler_coord_eq_point (n : ℕ) (hn : 4 ≤ n) {z₁ z₂ : Fin (2 * n) → K}
    (h₁ : z₁ ∈ rootSpacePoint (K := K) n hn) (h₂ : z₂ ∈ rootSpacePoint (K := K) n hn)
    (h : eichler (coordinateQuadPlus n K) (frameE n (zeroIdx n hn)) z₁ =
      eichler (coordinateQuadPlus n K) (frameE n (zeroIdx n hn)) z₂)
    {idx : Fin (2 * n)} (h_if : idx ≠ plusFrameRight n (zeroIdx n hn))
    (h_ie : idx ≠ plusFrameLeft n (zeroIdx n hn)) : z₁ idx = z₂ idx := by
  have hq := quad_frameE_zero (K := K) n hn
  have hp₁ := polar_frameE_rootSpacePoint (K := K) n hn ⟨z₁, h₁⟩
  have hp₂ := polar_frameE_rootSpacePoint (K := K) n hn ⟨z₂, h₂⟩
  have hc := congrFun (congrArg (fun (g : (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K)) =>
    g (frameF n (zeroIdx n hn))) h) idx
  rw [eichler_apply hq hp₁, eichler_apply hq hp₂] at hc
  have hf : (Pi.single (M := fun _ : Fin (2 * n) => K)
      (plusFrameRight n (zeroIdx n hn)) (1 : K)) idx = 0 :=
    Pi.single_eq_of_ne (M := fun _ : Fin (2 * n) => K) h_if 1
  have he : (Pi.single (M := fun _ : Fin (2 * n) => K)
      (plusFrameLeft n (zeroIdx n hn)) (1 : K)) idx = 0 :=
    Pi.single_eq_of_ne (M := fun _ : Fin (2 * n) => K) h_ie 1
  simp only [frameE, frameF, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, hf, he,
    mul_zero, add_zero, sub_zero, zero_add, smul_eq_mul] at hc
  have hpolar : polar (coordinateQuadPlus n K)
      (Pi.single (plusFrameRight n (zeroIdx n hn)) (1 : K))
      (Pi.single (plusFrameLeft n (zeroIdx n hn)) (1 : K)) = 1 := by
    have h := (isHypCoord_coordinateQuadPlus (K := K) (zeroIdx n hn)).polar_right
      (Pi.single (plusFrameLeft n (zeroIdx n hn)) (1 : K))
    simpa [plusFrameLeft, plusFrameRight] using h
  rw [hpolar, one_mul] at hc
  simpa using hc

section Centralizer

variable [Finite K]

@[expose] noncomputable def rootHomPoint (n : ℕ) (hn : 4 ≤ n)
    (y : rootSpacePoint (K := K) n hn) : matrixProjectiveDerived (coordinateQuadPlus n K) :=
  (projHom (coordinateQuadPlus n K)) (rootEltPoint n hn y)

theorem eichler_eq_of_rootGroupHom_eq_point (n : ℕ) (hn : 4 ≤ n)
    {y₁ y₂ : rootSpacePoint (K := K) n hn}
    (h : rootHomPoint (K := K) n hn y₁ = rootHomPoint (K := K) n hn y₂) :
    eichler (coordinateQuadPlus n K) (frameE n (zeroIdx n hn))
        ((y₁ : rootSpacePoint n hn) : Fin (2 * n) → K) =
      eichler (coordinateQuadPlus n K) (frameE n (zeroIdx n hn))
        ((y₂ : rootSpacePoint n hn) : Fin (2 * n) → K) := by
  have h' : rootEltPoint (K := K) n hn y₁ = rootEltPoint (K := K) n hn y₂ :=
    projHom_injective (isHypCoord_coordinateQuadPlus (K := K) (zeroIdx n hn)).exists_ne_zero h
  exact congrArg Subtype.val h'

theorem torus_mul_eq_one_of_mem_centralizer_point (n q : ℕ) (hn : 4 ≤ n)
    (p : Fin n → rootsOfUnity q K)
    {b : matrixProjectiveDerived (coordinateQuadPlus n K)}
    (hbC : b ∈ Subgroup.centralizer (rootGroupPoint (K := K) n hn : Set _))
    (hb : b = qTorusHom (K := K) n q p)
    (i : Fin n) (hi0 : i ≠ zeroIdx n hn) :
    ((MonoidHom.compLeft (rootsOfUnity q K).subtype (Fin n)) p (zeroIdx n hn) : K) *
      ((MonoidHom.compLeft (rootsOfUnity q K).subtype (Fin n)) p i : K) = 1 := by
  let t := (MonoidHom.compLeft (rootsOfUnity q K).subtype (Fin n)) p
  let s : matrixProjectiveDerived (coordinateQuadPlus n K) :=
    rootGroupHomPoint n hn (Multiplicative.ofAdd (rootEZ (K := K) n hn i hi0))
  have hs : s * b = b * s :=
    (Subgroup.mem_centralizer_iff.mp hbC) s
      (MonoidHom.mem_range.2 ⟨Multiplicative.ofAdd (rootEZ (K := K) n hn i hi0), rfl⟩)
  have hconj : b * s * b⁻¹ = s := by
    rw [← hs, mul_assoc, mul_inv_cancel, mul_one]
  rw [hb] at hconj
  dsimp only [s] at hconj
  have hroot : rootHomPoint (K := K) n hn
      (torusActionPoint n hn t (rootEZ (K := K) n hn i hi0)) =
      rootHomPoint (K := K) n hn (rootEZ (K := K) n hn i hi0) := by
    change rootGroupHomPoint n hn (Multiplicative.ofAdd
        (torusActionPoint n hn t (rootEZ (K := K) n hn i hi0))) =
      rootGroupHomPoint n hn (Multiplicative.ofAdd (rootEZ (K := K) n hn i hi0))
    change (qTorusHom (K := K) n q p) * rootGroupHomPoint n hn
        (rootEZ (K := K) n hn i hi0) *
        ((qTorusHom (K := K) n q p))⁻¹ =
      rootGroupHomPoint n hn (rootEZ (K := K) n hn i hi0) at hconj
    rw [qTorusHom_conj_rootGroupHomPoint (K := K) n q hn p (rootEZ (K := K) n hn i hi0)] at hconj
    exact hconj
  have heich := eichler_eq_of_rootGroupHom_eq_point n hn hroot
  have hcoord := eichler_coord_eq_point n hn
    (torusActionPoint n hn t (rootEZ (K := K) n hn i hi0)).2
    (rootEZ (K := K) n hn i hi0).2 heich
    (idx := plusFrameLeft n i)
    (fun h => Sum.inl_ne_inr ((plusIndexEquiv n).injective h))
    (fun h => hi0 ((plusFrameLeft_injective n h)))
  rw [coe_torusAction_rootEZ n hn t i hi0] at hcoord
  simpa [frameE, rootEZ, t] using hcoord

theorem torus_mul_inv_eq_one_of_mem_centralizer_point (n q : ℕ) (hn : 4 ≤ n)
    (p : Fin n → rootsOfUnity q K)
    {b : matrixProjectiveDerived (coordinateQuadPlus n K)}
    (hbC : b ∈ Subgroup.centralizer (rootGroupPoint (K := K) n hn : Set _))
    (hb : b = qTorusHom (K := K) n q p)
    (i : Fin n) (hi0 : i ≠ zeroIdx n hn) :
    ((MonoidHom.compLeft (rootsOfUnity q K).subtype (Fin n)) p (zeroIdx n hn) : K) *
      (((MonoidHom.compLeft (rootsOfUnity q K).subtype (Fin n)) p i : K))⁻¹ = 1 := by
  let t := (MonoidHom.compLeft (rootsOfUnity q K).subtype (Fin n)) p
  let s : matrixProjectiveDerived (coordinateQuadPlus n K) :=
    rootGroupHomPoint n hn (Multiplicative.ofAdd (rootFZ (K := K) n hn i hi0))
  have hs : s * b = b * s :=
    (Subgroup.mem_centralizer_iff.mp hbC) s
      (MonoidHom.mem_range.2 ⟨Multiplicative.ofAdd (rootFZ (K := K) n hn i hi0), rfl⟩)
  have hconj : b * s * b⁻¹ = s := by
    rw [← hs, mul_assoc, mul_inv_cancel, mul_one]
  rw [hb] at hconj
  dsimp only [s] at hconj
  have hroot : rootHomPoint (K := K) n hn
      (torusActionPoint n hn t (rootFZ (K := K) n hn i hi0)) =
      rootHomPoint (K := K) n hn (rootFZ (K := K) n hn i hi0) := by
    change rootGroupHomPoint n hn (Multiplicative.ofAdd
        (torusActionPoint n hn t (rootFZ (K := K) n hn i hi0))) =
      rootGroupHomPoint n hn (Multiplicative.ofAdd (rootFZ (K := K) n hn i hi0))
    change (qTorusHom (K := K) n q p) * rootGroupHomPoint n hn
        (rootFZ (K := K) n hn i hi0) *
        ((qTorusHom (K := K) n q p))⁻¹ =
      rootGroupHomPoint n hn (rootFZ (K := K) n hn i hi0) at hconj
    rw [qTorusHom_conj_rootGroupHomPoint (K := K) n q hn p (rootFZ (K := K) n hn i hi0)] at hconj
    exact hconj
  have heich := eichler_eq_of_rootGroupHom_eq_point n hn hroot
  have hcoord := eichler_coord_eq_point n hn
    (torusActionPoint n hn t (rootFZ (K := K) n hn i hi0)).2
    (rootFZ (K := K) n hn i hi0).2 heich
    (idx := plusFrameRight n i)
    (fun h => hi0 ((plusFrameRight_injective n h)))
    (fun h => Sum.inr_ne_inl ((plusIndexEquiv n).injective h))
  rw [coe_torusAction_rootFZ n hn t i hi0] at hcoord
  simpa [frameF, rootFZ, t] using hcoord

end Centralizer

theorem qTorus_inf_centralizer_rootGroupPoint_eq_bot [Finite K] (n q : ℕ) (hn : 4 ≤ n) :
    qTorus (K := K) n q ⊓
      Subgroup.centralizer (rootGroupPoint (K := K) n hn : Set _) = ⊥ := by
  rw [eq_bot_iff]
  intro b hb
  rw [Subgroup.mem_inf] at hb
  obtain ⟨hbB, hbC⟩ := hb
  rw [qTorus_eq_range] at hbB
  obtain ⟨p, hp⟩ := MonoidHom.mem_range.1 hbB
  let t := (MonoidHom.compLeft (rootsOfUnity q K).subtype (Fin n)) p
  have h0_1 : oneIdx n hn ≠ zeroIdx n hn := by simp [oneIdx, zeroIdx]
  have c1 := torus_mul_eq_one_of_mem_centralizer_point n q hn p hbC hp.symm (oneIdx n hn) h0_1
  have c2 := torus_mul_inv_eq_one_of_mem_centralizer_point n q hn p hbC hp.symm (oneIdx n hn) h0_1
  have c1' : (t (zeroIdx n hn) : K) * (t (oneIdx n hn) : K) = 1 := c1
  have c2' : (t (zeroIdx n hn) : K) * ((t (oneIdx n hn) : K))⁻¹ = 1 := c2
  have hpos : (-1 : K) = 1 := by
    have h2 : (1 : K) + 1 = 0 := by
      simpa [show (2 : K) = 1 + 1 by norm_num] using CharTwo.two_eq_zero (R := K)
    exact neg_eq_of_add_eq_zero_right h2
  have hu1 : t (zeroIdx n hn) = (t (oneIdx n hn))⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    apply Units.ext
    simpa using c1'
  have hc2u : t (zeroIdx n hn) * (t (oneIdx n hn))⁻¹ = 1 := by
    apply Units.ext
    simpa using c2'
  have hu2 : t (zeroIdx n hn) = t (oneIdx n hn) := by
    have h := eq_inv_of_mul_eq_one_left hc2u
    simpa using h
  have hinv : (t (oneIdx n hn))⁻¹ = t (oneIdx n hn) := hu1.symm.trans hu2
  have hsqU : t (oneIdx n hn) * t (oneIdx n hn) = 1 := by
    nth_rewrite 2 [← hinv]
    exact mul_inv_cancel (t (oneIdx n hn))
  have hsq : (t (oneIdx n hn) : K) * (t (oneIdx n hn) : K) = 1 := by
    simpa using congrArg Units.val hsqU
  have ht1K : (t (oneIdx n hn) : K) = 1 := by
    rcases mul_self_eq_one_iff.mp hsq with h | h
    · exact h
    · rw [h, hpos]
  have ht0K : (t (zeroIdx n hn) : K) = 1 := by
    have h : (t (zeroIdx n hn) : K) = ((t (oneIdx n hn) : K))⁻¹ := by
      simpa using congrArg Units.val hu1
    rw [h, ht1K, inv_one]
  have hti : ∀ i, i ≠ zeroIdx n hn → t i = 1 := by
    intro i hi0
    have hci := torus_mul_eq_one_of_mem_centralizer_point n q hn p hbC hp.symm i hi0
    have hci' : (t (zeroIdx n hn) : K) * (t i : K) = 1 := hci
    rw [ht0K, one_mul] at hci'
    exact Units.ext hci'
  have ht : t = 1 := by
    funext i
    by_cases hi0 : i = zeroIdx n hn
    · rw [hi0]
      exact Units.ext ht0K
    · exact hti i hi0
  rw [Subgroup.mem_bot, ← hp]
  change (plusFrame (K := K) n).frameHom t = 1
  rw [ht, map_one]

end CFSG.LocalAnalysis.GLTheoremA.Y10F.OmegaPair
