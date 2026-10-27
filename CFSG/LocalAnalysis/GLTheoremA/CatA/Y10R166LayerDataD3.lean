module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166OmBlocks2Base
public import CFSG.LieType.HighestRoot.CentTrialityThree
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightOrthPlusLevi
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusGen

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.OmegaPair

open Subgroup CFSG.Open
open CFSG.SeitzReduction.OmegaPilot
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus plusIndexEquiv
  regular_coordinateQuadPlus)
open CFSG.ClassicalGroups.Orthogonal
open QuadraticMap

variable {F : Type} [Field F] [Finite F] [CharP F 2] {m : ℕ}

section EichlerPlane

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem eichler_add_smul_pair {p q : V} (hp : Q p = 0) (hq : Q q = 0) (hpq : polar Q p q = 0)
    (a b a' b' : K) :
    eichler Q (a • p + b • q) (a' • p + b' • q) = eichler Q p ((a * b' - a' * b) • q) := by
  have hpq' : polar Q q p = 0 := by rw [polar_comm, hpq]
  have hQ1 : Q (a • p + b • q) = 0 := by
    rw [QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, hp, hq, polar_smul_left_eq,
      polar_smul_right_eq, hpq]
    ring
  have hQ2 : Q (a' • p + b' • q) = 0 := by
    rw [QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, hp, hq, polar_smul_left_eq,
      polar_smul_right_eq, hpq]
    ring
  have hQ3 : Q ((a * b' - a' * b) • q) = 0 := by
    rw [map_smul_eq_sq, hq]
    ring
  have hP1 : polar Q (a • p + b • q) (a' • p + b' • q) = 0 := by
    simp only [polar_add_left, polar_add_right, polar_smul_left_eq, polar_smul_right_eq,
      polar_self_eq_zero hp, polar_self_eq_zero hq, hpq, hpq', mul_zero, add_zero]
  have hP2 : polar Q p ((a * b' - a' * b) • q) = 0 := by
    rw [polar_smul_right_eq, hpq, mul_zero]
  refine LinearEquiv.ext fun x => ?_
  rw [eichler_apply hQ1 hP1, eichler_apply hp hP2]
  simp only [polar_add_left, polar_add_right, polar_smul_left_eq, polar_smul_right_eq,
    polar_self_eq_zero hp, polar_self_eq_zero hq, hpq, hpq', hQ2, hQ3, mul_zero, add_zero,
    sub_zero, zero_mul, add_smul, zero_smul, smul_add, smul_smul]
  module

end EichlerPlane

section Diagonal

variable [NeZero m]

noncomputable def torusParam (m : ℕ) [NeZero m] (ζ : Fˣ) : Fin m → Fˣ :=
  Pi.mulSingle (0 : Fin m) ζ * Pi.mulSingle (1 : Fin m) ζ

private noncomputable def torusParamTwo (m : ℕ) [NeZero m] (ζ : Fˣ) : Fin m → Fˣ :=
  Pi.mulSingle (2 : Fin m) ζ

theorem one_ne_zero_fin (hm : 4 ≤ m) : (1 : Fin m) ≠ 0 := by
  intro h
  have h2 : m = 1 := by simpa using congrArg Fin.val h
  omega

theorem two_ne_zero_fin (hm : 4 ≤ m) : (2 : Fin m) ≠ 0 := by
  intro h
  have h2 : 2 % m = 0 := by simpa using congrArg Fin.val h
  rw [Nat.mod_eq_of_lt (by omega)] at h2
  omega

theorem two_ne_one_fin (hm : 4 ≤ m) : (2 : Fin m) ≠ 1 := by
  intro h
  have h2 : 2 % m = 1 % m := by simpa using congrArg Fin.val h
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h2
  omega

theorem torusParam_apply (hm : 4 ≤ m) (ζ : Fˣ) (k : Fin m) :
    torusParam m ζ k = if k = 0 ∨ k = 1 then ζ else 1 := by
  by_cases h0 : k = 0
  · subst h0
    rw [if_pos (Or.inl rfl), torusParam, Pi.mul_apply, Pi.mulSingle_eq_same,
      Pi.mulSingle_eq_of_ne (Ne.symm (one_ne_zero_fin hm)), mul_one]
  by_cases h1 : k = 1
  · subst h1
    rw [if_pos (Or.inr rfl), torusParam, Pi.mul_apply, Pi.mulSingle_eq_same,
      Pi.mulSingle_eq_of_ne (one_ne_zero_fin hm), one_mul]
  · rw [if_neg (by tauto), torusParam, Pi.mul_apply,
      Pi.mulSingle_eq_of_ne (M := fun _ => Fˣ) h0, Pi.mulSingle_eq_of_ne (M := fun _ => Fˣ) h1,
      one_mul]

private theorem torusParam_apply_two (ζ : Fˣ) (k : Fin m) :
    torusParamTwo m ζ k = if k = 2 then ζ else 1 := by
  by_cases h2 : k = 2
  · subst h2
    rw [if_pos rfl, torusParamTwo, Pi.mulSingle_eq_same]
  · rw [if_neg h2, torusParamTwo, Pi.mulSingle_eq_of_ne (M := fun _ => Fˣ) h2]

theorem frameEntry_torusParam_ne (hm : 4 ≤ m) (h : IsHypFrame (coordinateQuadPlus m F)
    (plusFrameLeft m) (plusFrameRight m)) {ζ : Fˣ} (hζ1 : ζ ≠ 1) (hζinv : ζ⁻¹ ≠ ζ)
    {i : Fin (2 * m)} (hi0 : i ≠ plusFrameLeft m 0) (hi1 : i ≠ plusFrameLeft m 1) :
    frameEntry (plusFrameLeft m) (plusFrameRight m) (torusParam m ζ) i ≠ ζ := by
  by_cases hra : ∃ k, plusFrameLeft m k = i
  · obtain ⟨k, hk⟩ := hra
    subst hk
    rw [h.frameEntry_left, torusParam_apply hm]
    by_cases hk0 : k = 0
    · exact absurd (by rw [hk0]) hi0
    by_cases hk1 : k = 1
    · exact absurd (by rw [hk1]) hi1
    rw [if_neg (by tauto)]
    exact fun e => hζ1 e.symm
  · by_cases hrb : ∃ k, plusFrameRight m k = i
    · obtain ⟨k, hk⟩ := hrb
      subst hk
      rw [h.frameEntry_right, torusParam_apply hm]
      by_cases hk0 : k = 0
      · rw [if_pos (Or.inl hk0)]
        exact hζinv
      by_cases hk1 : k = 1
      · rw [if_pos (Or.inr hk1)]
        exact hζinv
      · rw [if_neg (by tauto)]
        exact fun e => hζ1 (by rw [← e, inv_one])
    · rw [frameEntry_of_forall_ne (t := torusParam m ζ)
        (fun k hk => hra ⟨k, hk.symm⟩) (fun k hk => hrb ⟨k, hk.symm⟩)]
      exact fun e => hζ1 e.symm

end Diagonal


section Frame

variable [NeZero m]

@[expose] noncomputable def framePair (k : Fin m) : HypPair (coordinateQuadPlus m F) :=
  (isHypCoord_coordinateQuadPlus (K := F) k).hypPair

private theorem framePair_e (k : Fin m) : (framePair (F := F) k).e = frameE m k := rfl

private theorem framePair_f (k : Fin m) : (framePair (F := F) k).f = frameF m k := rfl

private theorem frameE_apply_self (k : Fin m) : frameE (K := F) m k (plusFrameLeft m k) = 1 :=
  Pi.single_eq_same ..

private theorem frameE_apply_of_ne {k : Fin m} {i : Fin (2 * m)} (h : i ≠ plusFrameLeft m k) :
    frameE (K := F) m k i = 0 := Pi.single_eq_of_ne (M := fun _ => F) h 1

private theorem frameF_apply_self (k : Fin m) : frameF (K := F) m k (plusFrameRight m k) = 1 :=
  Pi.single_eq_same ..

private theorem frameF_apply_of_ne {k : Fin m} {i : Fin (2 * m)} (h : i ≠ plusFrameRight m k) :
    frameF (K := F) m k i = 0 := Pi.single_eq_of_ne (M := fun _ => F) h 1

private theorem frameLin_frameE (h : IsHypFrame (coordinateQuadPlus m F) (plusFrameLeft m)
    (plusFrameRight m)) (t : Fin m → Fˣ) (k : Fin m) :
    frameLin (plusFrameLeft m) (plusFrameRight m) t (frameE (K := F) m k) =
      ((t k : Fˣ) : F) • frameE (K := F) m k :=
  h.frameLin_single_left t k

private theorem frameLin_frameF (h : IsHypFrame (coordinateQuadPlus m F) (plusFrameLeft m)
    (plusFrameRight m)) (t : Fin m → Fˣ) (k : Fin m) :
    frameLin (plusFrameLeft m) (plusFrameRight m) t (frameF (K := F) m k) =
      (((t k)⁻¹ : Fˣ) : F) • frameF (K := F) m k :=
  h.frameLin_single_right t k

theorem framePair_orth (hm : 4 ≤ m) :
    (framePair (F := F) (m := m) 0).Orth (framePair (F := F) (m := m) 1) := by
  have h := isHypFrame_plus (K := F) m
  exact (isHypCoord_coordinateQuadPlus (K := F) (n := m) 0).orth
    (isHypCoord_coordinateQuadPlus (K := F) (n := m) 1)
    ⟨fun e => one_ne_zero_fin hm (h.left_injective e),
     h.left_ne_right 1 0,
     fun e => (h.left_ne_right 0 1) e.symm,
     fun e => one_ne_zero_fin hm (h.right_injective e)⟩

end Frame

section Eigenspace

variable {K : Type*} [Field K] {ι : Type*} [DecidableEq ι] {m : ℕ} {a b : Fin m → ι}

theorem apply_single_eq_zero_of_commute {t : Fin m → Kˣ} {g : (ι → K) ≃ₗ[K] (ι → K)}
    (hg : g * frameLin a b t = frameLin a b t * g) {i k : ι}
    (hik : frameEntry a b t i ≠ frameEntry a b t k) : (g (Pi.single k 1)) i = 0 := by
  have hsingle : frameLin a b t (Pi.single k 1) =
      ((frameEntry a b t k : Kˣ) : K) • Pi.single k 1 := by
    funext j
    rw [frameLin_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hjk : j = k
    · subst hjk
      simp
    · rw [Pi.single_eq_of_ne hjk]
      simp [Pi.single_eq_of_ne hjk]
  have h := congrFun (LinearEquiv.congr_fun hg (Pi.single k 1)) i
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hsingle, map_smul, frameLin_apply,
    Pi.smul_apply, smul_eq_mul] at h
  have hz : (((frameEntry a b t k : Kˣ) : K) - ((frameEntry a b t i : Kˣ) : K)) *
      (g (Pi.single k 1)) i = 0 := by
    rw [sub_mul, h, sub_self]
  have hne : (((frameEntry a b t k : Kˣ) : K) - ((frameEntry a b t i : Kˣ) : K)) ≠ 0 := by
    intro h0
    exact hik (Units.ext (sub_eq_zero.1 h0).symm)
  exact (mul_eq_zero.1 hz).resolve_left hne

end Eigenspace

section Eigenspaces

variable [NeZero m]

theorem frameEntry_torusParam_inv_ne (hm : 4 ≤ m)
    (h : IsHypFrame (coordinateQuadPlus m F) (plusFrameLeft m) (plusFrameRight m)) {ζ : Fˣ}
    (hζ1 : ζ ≠ 1) (hζinv : ζ⁻¹ ≠ ζ) {i : Fin (2 * m)}
    (hi0 : i ≠ plusFrameRight m 0) (hi1 : i ≠ plusFrameRight m 1) :
    frameEntry (plusFrameLeft m) (plusFrameRight m) (torusParam m ζ) i ≠ ζ⁻¹ := by
  have hζinv1 : ζ⁻¹ ≠ 1 := fun e => hζ1 (inv_eq_one.1 e)
  by_cases hra : ∃ k, plusFrameLeft m k = i
  · obtain ⟨k, hk⟩ := hra
    subst hk
    rw [h.frameEntry_left, torusParam_apply hm]
    by_cases hk0 : k = 0
    · rw [if_pos (Or.inl hk0)]
      exact hζinv.symm
    by_cases hk1 : k = 1
    · rw [if_pos (Or.inr hk1)]
      exact hζinv.symm
    · rw [if_neg (by tauto)]
      exact hζinv1.symm
  · by_cases hrb : ∃ k, plusFrameRight m k = i
    · obtain ⟨k, hk⟩ := hrb
      subst hk
      rw [h.frameEntry_right, torusParam_apply hm]
      by_cases hk0 : k = 0
      · exact absurd hk0 (fun e => hi0 (by rw [e]))
      by_cases hk1 : k = 1
      · exact absurd hk1 (fun e => hi1 (by rw [e]))
      · rw [if_neg (by tauto)]
        exact fun e => hζinv1 (by rw [← e, inv_one])
    · rw [frameEntry_of_forall_ne (t := torusParam m ζ)
        (fun k hk => hra ⟨k, hk.symm⟩) (fun k hk => hrb ⟨k, hk.symm⟩)]
      exact fun e => hζinv1 e.symm

theorem apply_frameE_eq_smul (hm : 4 ≤ m)
    (h : IsHypFrame (coordinateQuadPlus m F) (plusFrameLeft m) (plusFrameRight m)) {ζ : Fˣ}
    (hζ1 : ζ ≠ 1) (hζinv : ζ⁻¹ ≠ ζ) {g : (Fin (2 * m) → F) ≃ₗ[F] (Fin (2 * m) → F)}
    (hg : g * frameLin (plusFrameLeft m) (plusFrameRight m) (torusParam m ζ) =
      frameLin (plusFrameLeft m) (plusFrameRight m) (torusParam m ζ) * g)
    (k : Fin m) (hk : k = 0 ∨ k = 1) :
    g (frameE m k) = (g (frameE m k) (plusFrameLeft m 0)) • frameE m 0 +
      (g (frameE m k) (plusFrameLeft m 1)) • frameE m 1 := by
  have hne : plusFrameLeft m 1 ≠ plusFrameLeft m 0 :=
    fun e => one_ne_zero_fin hm (h.left_injective e)
  have hval : frameEntry (plusFrameLeft m) (plusFrameRight m) (torusParam m ζ)
      (plusFrameLeft m k) = ζ := by
    rw [h.frameEntry_left, torusParam_apply hm]
    rcases hk with rfl | rfl <;> simp
  funext i
  by_cases hi0 : i = plusFrameLeft m 0
  · subst hi0
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
      frameE_apply_self (k := 0), frameE_apply_of_ne (k := 1) (Ne.symm hne), mul_one, mul_zero,
      add_zero]
  by_cases hi1 : i = plusFrameLeft m 1
  · subst hi1
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
      frameE_apply_of_ne (k := 0) hne, frameE_apply_self (k := 1), mul_zero, mul_one, zero_add]
  · rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
      frameE_apply_of_ne (k := 0) hi0, frameE_apply_of_ne (k := 1) hi1, mul_zero, mul_zero,
      add_zero]
    exact apply_single_eq_zero_of_commute hg
      (by rw [hval]; exact frameEntry_torusParam_ne hm h hζ1 hζinv hi0 hi1)

theorem apply_frameF_eq_smul (hm : 4 ≤ m)
    (h : IsHypFrame (coordinateQuadPlus m F) (plusFrameLeft m) (plusFrameRight m)) {ζ : Fˣ}
    (hζ1 : ζ ≠ 1) (hζinv : ζ⁻¹ ≠ ζ) {g : (Fin (2 * m) → F) ≃ₗ[F] (Fin (2 * m) → F)}
    (hg : g * frameLin (plusFrameLeft m) (plusFrameRight m) (torusParam m ζ) =
      frameLin (plusFrameLeft m) (plusFrameRight m) (torusParam m ζ) * g)
    (k : Fin m) (hk : k = 0 ∨ k = 1) :
    g (frameF m k) = (g (frameF m k) (plusFrameRight m 0)) • frameF m 0 +
      (g (frameF m k) (plusFrameRight m 1)) • frameF m 1 := by
  have hne : plusFrameRight m 1 ≠ plusFrameRight m 0 :=
    fun e => one_ne_zero_fin hm (h.right_injective e)
  have hval : frameEntry (plusFrameLeft m) (plusFrameRight m) (torusParam m ζ)
      (plusFrameRight m k) = ζ⁻¹ := by
    rw [h.frameEntry_right, torusParam_apply hm]
    rcases hk with rfl | rfl <;> simp
  funext i
  by_cases hi0 : i = plusFrameRight m 0
  · subst hi0
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
      frameF_apply_self (k := 0), frameF_apply_of_ne (k := 1) (Ne.symm hne), mul_one, mul_zero,
      add_zero]
  by_cases hi1 : i = plusFrameRight m 1
  · subst hi1
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
      frameF_apply_of_ne (k := 0) hne, frameF_apply_self (k := 1), mul_zero, mul_one, zero_add]
  · rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
      frameF_apply_of_ne (k := 0) hi0, frameF_apply_of_ne (k := 1) hi1, mul_zero, mul_zero,
      add_zero]
    exact apply_single_eq_zero_of_commute hg
      (by rw [hval]; exact frameEntry_torusParam_inv_ne hm h hζ1 hζinv hi0 hi1)

end Eigenspaces


section LeviFix

variable [NeZero m]

noncomputable def planeE : Submodule F (Fin (2 * m) → F) :=
  Submodule.span F {frameE (K := F) m 0, frameE (K := F) m 1}

noncomputable def planeF' : Submodule F (Fin (2 * m) → F) :=
  Submodule.span F {frameF (K := F) m 0, frameF (K := F) m 1}

theorem polar_planes (horth : (framePair (F := F) (m := m) 0).Orth
    (framePair (F := F) (m := m) 1)) {a b γ δ : F} :
    polar (coordinateQuadPlus m F) (a • frameE (K := F) m 0 + b • frameE (K := F) m 1)
      (γ • frameF (K := F) m 0 + δ • frameF (K := F) m 1) = a * γ + b * δ := by
  have h00 : polar (coordinateQuadPlus m F) (frameE (K := F) m 0) (frameE (K := F) m 0) = 0 :=
    (framePair (F := F) (m := m) 0).polar_ee
  have h01 : polar (coordinateQuadPlus m F) (frameE (K := F) m 0) (frameE (K := F) m 1) = 0 :=
    horth.ee
  have h10 : polar (coordinateQuadPlus m F) (frameE (K := F) m 1) (frameE (K := F) m 0) = 0 := by
    rw [polar_comm]
    exact horth.ee
  have h11 : polar (coordinateQuadPlus m F) (frameE (K := F) m 1) (frameE (K := F) m 1) = 0 :=
    (framePair (F := F) (m := m) 1).polar_ee
  have hf0 : polar (coordinateQuadPlus m F) (frameE (K := F) m 0) (frameF (K := F) m 0) = 1 :=
    (framePair (F := F) (m := m) 0).polar_ef
  have hf1 : polar (coordinateQuadPlus m F) (frameE (K := F) m 0) (frameF (K := F) m 1) = 0 :=
    horth.ef
  have hf2 : polar (coordinateQuadPlus m F) (frameE (K := F) m 1) (frameF (K := F) m 0) = 0 := by
    rw [polar_comm]
    exact horth.fe
  have hf3 : polar (coordinateQuadPlus m F) (frameE (K := F) m 1) (frameF (K := F) m 1) = 1 :=
    (framePair (F := F) (m := m) 1).polar_ef
  simp only [polar_add_left, polar_add_right, polar_smul_left_eq, polar_smul_right_eq, h00, h01,
    h10, h11, hf0, hf1, hf2, hf3, mul_zero, mul_one, add_zero, zero_add]
  ring

end LeviFix


section RootGroup

variable [NeZero m]

theorem eichler_mem_leviFix_of_planes (hm : 4 ≤ m)
    (horth : (framePair (F := F) (m := m) 0).Orth (framePair (F := F) (m := m) 1))
    {a b γ δ : F} (hab : a * γ + b * δ = 0) :
    eichler (coordinateQuadPlus m F) (a • frameE (K := F) m 0 + b • frameE (K := F) m 1)
      (γ • frameF (K := F) m 0 + δ • frameF (K := F) m 1) ∈
      leviFix (orthDerived (coordinateQuadPlus m F)) (framePair (F := F) (m := m) 0)
        (framePair (F := F) (m := m) 1) := by
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus (K := F) (n := m) (by omega)
  have h00 : polar (coordinateQuadPlus m F) (frameE (K := F) m 0) (frameE (K := F) m 0) = 0 :=
    (framePair (F := F) (m := m) 0).polar_ee
  have h01 : polar (coordinateQuadPlus m F) (frameE (K := F) m 0) (frameE (K := F) m 1) = 0 :=
    horth.ee
  have h10 : polar (coordinateQuadPlus m F) (frameE (K := F) m 1) (frameE (K := F) m 0) = 0 := by
    rw [polar_comm]; exact horth.ee
  have h11 : polar (coordinateQuadPlus m F) (frameE (K := F) m 1) (frameE (K := F) m 1) = 0 :=
    (framePair (F := F) (m := m) 1).polar_ee
  have hf00 : polar (coordinateQuadPlus m F) (frameE (K := F) m 0) (frameF (K := F) m 0) = 1 :=
    (framePair (F := F) (m := m) 0).polar_ef
  have hf01 : polar (coordinateQuadPlus m F) (frameE (K := F) m 0) (frameF (K := F) m 1) = 0 :=
    horth.ef
  have hf10 : polar (coordinateQuadPlus m F) (frameE (K := F) m 1) (frameF (K := F) m 0) = 0 := by
    rw [polar_comm]; exact horth.fe
  have hf11 : polar (coordinateQuadPlus m F) (frameE (K := F) m 1) (frameF (K := F) m 1) = 1 :=
    (framePair (F := F) (m := m) 1).polar_ef
  have hff0 : polar (coordinateQuadPlus m F) (frameF (K := F) m 0) (frameF (K := F) m 0) = 0 :=
    (framePair (F := F) (m := m) 0).polar_ff
  have hff1 : polar (coordinateQuadPlus m F) (frameF (K := F) m 0) (frameF (K := F) m 1) = 0 :=
    horth.ff
  have hff2 : polar (coordinateQuadPlus m F) (frameF (K := F) m 1) (frameF (K := F) m 0) = 0 := by
    rw [polar_comm]; exact horth.ff
  have hff3 : polar (coordinateQuadPlus m F) (frameF (K := F) m 1) (frameF (K := F) m 1) = 0 :=
    (framePair (F := F) (m := m) 1).polar_ff
  have hfe00 : polar (coordinateQuadPlus m F) (frameF (K := F) m 0) (frameE (K := F) m 0) = 1 :=
    (framePair (F := F) (m := m) 0).polar_fe
  have hfe01 : polar (coordinateQuadPlus m F) (frameF (K := F) m 0) (frameE (K := F) m 1) = 0 :=
    horth.fe
  have hfe10 : polar (coordinateQuadPlus m F) (frameF (K := F) m 1) (frameE (K := F) m 0) = 0 := by
    rw [polar_comm]; exact horth.ef
  have hfe11 : polar (coordinateQuadPlus m F) (frameF (K := F) m 1) (frameE (K := F) m 1) = 1 :=
    (framePair (F := F) (m := m) 1).polar_fe
  have hQe0 : (coordinateQuadPlus m F) (frameE (K := F) m 0) = 0 :=
    (framePair (F := F) (m := m) 0).Q_e
  have hQe1 : (coordinateQuadPlus m F) (frameE (K := F) m 1) = 0 :=
    (framePair (F := F) (m := m) 1).Q_e
  have hQf0 : (coordinateQuadPlus m F) (frameF (K := F) m 0) = 0 :=
    (framePair (F := F) (m := m) 0).Q_f
  have hQf1 : (coordinateQuadPlus m F) (frameF (K := F) m 1) = 0 :=
    (framePair (F := F) (m := m) 1).Q_f
  have hQu : (coordinateQuadPlus m F) (a • frameE (K := F) m 0 + b • frameE (K := F) m 1) = 0 := by
    rw [QuadraticMap.map_add (coordinateQuadPlus m F), map_smul_eq_sq, map_smul_eq_sq, hQe0,
      hQe1, polar_smul_left_eq, polar_smul_right_eq, h01]
    ring
  have hQw : (coordinateQuadPlus m F) (γ • frameF (K := F) m 0 + δ • frameF (K := F) m 1) = 0 := by
    rw [QuadraticMap.map_add (coordinateQuadPlus m F), map_smul_eq_sq, map_smul_eq_sq, hQf0,
      hQf1, polar_smul_left_eq, polar_smul_right_eq, hff1]
    ring
  have huw : polar (coordinateQuadPlus m F) (a • frameE (K := F) m 0 + b • frameE (K := F) m 1)
      (γ • frameF (K := F) m 0 + δ • frameF (K := F) m 1) = 0 := by
    rw [polar_planes horth, hab]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hzero : γ * a + δ * b = 0 := by
    rw [mul_comm γ a, mul_comm δ b]
    exact hab
  have hE0 : eichler (coordinateQuadPlus m F) (a • frameE (K := F) m 0 + b • frameE (K := F) m 1)
      (γ • frameF (K := F) m 0 + δ • frameF (K := F) m 1) (frameE (K := F) m 0) =
      (1 - γ * a) • frameE (K := F) m 0 + (-(γ * b)) • frameE (K := F) m 1 := by
    rw [eichler_apply hQu huw]
    simp only [polar_add_right, polar_smul_right_eq, h00, h01, hf00, hf01, hQw, mul_zero, mul_one,
      add_zero, zero_mul]
    module
  have hE1 : eichler (coordinateQuadPlus m F) (a • frameE (K := F) m 0 + b • frameE (K := F) m 1)
      (γ • frameF (K := F) m 0 + δ • frameF (K := F) m 1) (frameE (K := F) m 1) =
      (-(δ * a)) • frameE (K := F) m 0 + (1 - δ * b) • frameE (K := F) m 1 := by
    rw [eichler_apply hQu huw]
    simp only [polar_add_right, polar_smul_right_eq, h10, h11, hf10, hf11, hQw, mul_zero, mul_one,
      add_zero, zero_mul]
    module
  have hF0 : eichler (coordinateQuadPlus m F) (a • frameE (K := F) m 0 + b • frameE (K := F) m 1)
      (γ • frameF (K := F) m 0 + δ • frameF (K := F) m 1) (frameF (K := F) m 0) =
      (1 + a * γ) • frameF (K := F) m 0 + (a * δ) • frameF (K := F) m 1 := by
    rw [eichler_apply hQu huw]
    simp only [polar_add_right, polar_smul_right_eq, hff0, hff1, hfe00, hfe01, hQw, mul_zero,
      mul_one, add_zero, zero_mul]
    module
  have hF1 : eichler (coordinateQuadPlus m F) (a • frameE (K := F) m 0 + b • frameE (K := F) m 1)
      (γ • frameF (K := F) m 0 + δ • frameF (K := F) m 1) (frameF (K := F) m 1) =
      (b * γ) • frameF (K := F) m 0 + (1 + b * δ) • frameF (K := F) m 1 := by
    rw [eichler_apply hQu huw]
    simp only [polar_add_right, polar_smul_right_eq, hff2, hff3, hfe10, hfe11, hQw, mul_zero,
      mul_one, add_zero, zero_mul]
    module
  have hE : eichler (coordinateQuadPlus m F) (a • frameE (K := F) m 0 + b • frameE (K := F) m 1)
      (γ • frameF (K := F) m 0 + δ • frameF (K := F) m 1) ∈
      TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadPlus m F) := eichler_mem_orthogonalGroup (coordinateQuadPlus m F) _ _
  refine mem_leviFix.mpr ⟨eichler_mem_orthDerived hQ hT _ _, ⟨⟨hE, ?_⟩, ?_⟩, ?_⟩
  ·
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have hconj := eichler_conj hE (frameE (K := F) m 0) (frameE (K := F) m 1)
    rw [hE0, hE1, eichler_add_smul_pair (Q := coordinateQuadPlus m F) (p := frameE (K := F) m 0)
      (q := frameE (K := F) m 1) hQe0 hQe1 h01] at hconj
    have hs : (1 - γ * a) * (1 - δ * b) - (-(δ * a)) * (-(γ * b)) = 1 := by
      rw [neg_mul_neg]
      linear_combination (norm := ring_nf) -hzero + (γ * a * δ * b) * h2
      simp [h2]
    rw [hs, one_smul] at hconj
    exact mul_inv_eq_iff_eq_mul.1 hconj
  ·
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have hconj := eichler_conj hE (frameF (K := F) m 0) (frameF (K := F) m 1)
    rw [hF0, hF1, eichler_add_smul_pair (Q := coordinateQuadPlus m F) (p := frameF (K := F) m 0)
      (q := frameF (K := F) m 1) hQf0 hQf1 hff1] at hconj
    have hs : (1 + a * γ) * (1 + b * δ) - (b * γ) * (a * δ) = 1 := by
      linear_combination (norm := ring_nf) hab + (a * γ * b * δ) * h2
      simp [h2]
    rw [hs, one_smul] at hconj
    exact mul_inv_eq_iff_eq_mul.1 hconj
  ·
    intro x hx
    have hx0 : polar (coordinateQuadPlus m F) (frameE (K := F) m 0) x = 0 := hx.1
    have hx1 : polar (coordinateQuadPlus m F) (frameF (K := F) m 0) x = 0 := hx.2.1
    have hx2 : polar (coordinateQuadPlus m F) (frameE (K := F) m 1) x = 0 := hx.2.2.1
    have hx3 : polar (coordinateQuadPlus m F) (frameF (K := F) m 1) x = 0 := hx.2.2.2
    rw [eichler_apply hQu huw]
    have h1 : polar (coordinateQuadPlus m F) x (a • frameE (K := F) m 0 + b • frameE (K := F) m 1)
        = 0 := by
      rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq,
        polar_comm (coordinateQuadPlus m F) x (frameE (K := F) m 0),
        polar_comm (coordinateQuadPlus m F) x (frameE (K := F) m 1), hx0, hx2, mul_zero, mul_zero,
        add_zero]
    have h3 : polar (coordinateQuadPlus m F) x (γ • frameF (K := F) m 0 + δ • frameF (K := F) m 1)
        = 0 := by
      rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq,
        polar_comm (coordinateQuadPlus m F) x (frameF (K := F) m 0),
        polar_comm (coordinateQuadPlus m F) x (frameF (K := F) m 1), hx1, hx3, mul_zero, mul_zero,
        add_zero]
    rw [h1, h3, hQw, mul_zero, add_zero]
    simp

end RootGroup


section Normal

variable [NeZero m]

theorem frameLin_mem_centralizer_leviFix (hm : 4 ≤ m) {t : Fin m → Fˣ} (ht : t 0 = t 1) :
    frameLin (plusFrameLeft m) (plusFrameRight m) t ∈
      Subgroup.centralizer ((leviFix (orthDerived (coordinateQuadPlus m F))
        (framePair (F := F) (m := m) 0) (framePair (F := F) (m := m) 1) :
        Subgroup ((Fin (2 * m) → F) ≃ₗ[F] (Fin (2 * m) → F))) :
        Set ((Fin (2 * m) → F) ≃ₗ[F] (Fin (2 * m) → F))) := by
  have h := isHypFrame_plus (K := F) m
  have horth := framePair_orth (F := F) hm
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus (K := F) (n := m) (by omega)
  have hE : ∀ u w : Fin (2 * m) → F, eichler (coordinateQuadPlus m F) u w ∈
      orthDerived (coordinateQuadPlus m F) := fun u w => eichler_mem_orthDerived hQ hT u w
  have hxO : frameLin (plusFrameLeft m) (plusFrameRight m) t ∈
      TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadPlus m F) :=
    h.frameLin_mem_orthogonalGroup t
  have hcomm : ∀ c : F, frameLin (plusFrameLeft m) (plusFrameRight m) t *
      eichler (coordinateQuadPlus m F) (frameE (K := F) m 0) (c • frameF (K := F) m 1) =
      eichler (coordinateQuadPlus m F) (frameE (K := F) m 0) (c • frameF (K := F) m 1) *
        frameLin (plusFrameLeft m) (plusFrameRight m) t := by
    intro c
    rw [← mul_inv_eq_iff_eq_mul, eichler_conj hxO, frameLin_frameE h t 0, map_smul,
      frameLin_frameF h t 1, eichler_smul_left]
    congr 1
    rw [Units.val_inv_eq_inv_val, ← ht]
    simp only [smul_smul]
    congr 1
    field_simp
  have hcomm' : ∀ c : F, frameLin (plusFrameLeft m) (plusFrameRight m) t *
      eichler (coordinateQuadPlus m F) (frameE (K := F) m 1) (c • frameF (K := F) m 0) =
      eichler (coordinateQuadPlus m F) (frameE (K := F) m 1) (c • frameF (K := F) m 0) *
        frameLin (plusFrameLeft m) (plusFrameRight m) t := by
    intro c
    rw [← mul_inv_eq_iff_eq_mul, eichler_conj hxO, frameLin_frameE h t 1, map_smul,
      frameLin_frameF h t 0, eichler_smul_left]
    congr 1
    rw [Units.val_inv_eq_inv_val, ← ht]
    simp only [smul_smul]
    congr 1
    field_simp
  set S : Set ((Fin (2 * m) → F) ≃ₗ[F] (Fin (2 * m) → F)) :=
    Set.range (fun s : F => eichler (coordinateQuadPlus m F) (framePair (F := F) (m := m) 0).e
      (s • (framePair (F := F) (m := m) 1).f)) ∪
      Set.range (fun s : F => eichler (coordinateQuadPlus m F) (framePair (F := F) (m := m) 1).e
        (s • (framePair (F := F) (m := m) 0).f)) with hS
  have hle : Subgroup.closure S ≤
      Subgroup.centralizer ({frameLin (plusFrameLeft m) (plusFrameRight m) t} :
        Set ((Fin (2 * m) → F) ≃ₗ[F] (Fin (2 * m) → F))) := by
    rw [Subgroup.closure_le]
    rintro g (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (hcomm c).symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (hcomm' c).symm
  refine Subgroup.mem_centralizer_iff.mpr (fun y hy => ?_)
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle ((leviFix_le_closure horth hE) hy))

theorem conj_mem_leviFix (hm : 4 ≤ m) {ζ : Fˣ} (hζ1 : ζ ≠ 1) (hζinv : ζ⁻¹ ≠ ζ)
    {g : (Fin (2 * m) → F) ≃ₗ[F] (Fin (2 * m) → F)}
    (hgΩ : g ∈ orthDerived (coordinateQuadPlus m F))
    (hg : g * frameLin (plusFrameLeft m) (plusFrameRight m) (torusParam m ζ) =
      frameLin (plusFrameLeft m) (plusFrameRight m) (torusParam m ζ) * g)
    {l : (Fin (2 * m) → F) ≃ₗ[F] (Fin (2 * m) → F)}
    (hl : l ∈ leviFix (orthDerived (coordinateQuadPlus m F)) (framePair (F := F) (m := m) 0)
      (framePair (F := F) (m := m) 1)) :
    g * l * g⁻¹ ∈ leviFix (orthDerived (coordinateQuadPlus m F)) (framePair (F := F) (m := m) 0)
      (framePair (F := F) (m := m) 1) := by
  have h := isHypFrame_plus (K := F) m
  have horth := framePair_orth (F := F) hm
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus (K := F) (n := m) (by omega)
  have hE : ∀ u w : Fin (2 * m) → F, eichler (coordinateQuadPlus m F) u w ∈
      orthDerived (coordinateQuadPlus m F) := fun u w => eichler_mem_orthDerived hQ hT u w
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadPlus m F) :=
    Subgroup.commutator_le_self _ hgΩ
  have hg1O : g⁻¹ ∈ TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadPlus m F) :=
    (TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadPlus m F)).inv_mem hgO
  have hge0 : g (frameE (K := F) m 0) = (g (frameE (K := F) m 0) (plusFrameLeft m 0)) •
      frameE (K := F) m 0 + (g (frameE (K := F) m 0) (plusFrameLeft m 1)) •
      frameE (K := F) m 1 :=
    apply_frameE_eq_smul hm h hζ1 hζinv hg 0 (Or.inl rfl)
  have hge1 : g (frameE (K := F) m 1) = (g (frameE (K := F) m 1) (plusFrameLeft m 0)) •
      frameE (K := F) m 0 + (g (frameE (K := F) m 1) (plusFrameLeft m 1)) •
      frameE (K := F) m 1 :=
    apply_frameE_eq_smul hm h hζ1 hζinv hg 1 (Or.inr rfl)
  have hgf0 : g (frameF (K := F) m 0) = (g (frameF (K := F) m 0) (plusFrameRight m 0)) •
      frameF (K := F) m 0 + (g (frameF (K := F) m 0) (plusFrameRight m 1)) •
      frameF (K := F) m 1 :=
    apply_frameF_eq_smul hm h hζ1 hζinv hg 0 (Or.inl rfl)
  have hgf1 : g (frameF (K := F) m 1) = (g (frameF (K := F) m 1) (plusFrameRight m 0)) •
      frameF (K := F) m 0 + (g (frameF (K := F) m 1) (plusFrameRight m 1)) •
      frameF (K := F) m 1 :=
    apply_frameF_eq_smul hm h hζ1 hζinv hg 1 (Or.inr rfl)
  have hgen1 : ∀ c : F, g * eichler (coordinateQuadPlus m F) (frameE (K := F) m 0)
      (c • frameF (K := F) m 1) * g⁻¹ ∈
      leviFix (orthDerived (coordinateQuadPlus m F)) (framePair (F := F) (m := m) 0)
        (framePair (F := F) (m := m) 1) := by
    intro c
    rw [eichler_conj hgO, hge0, map_smul, hgf1, smul_add, smul_smul, smul_smul]
    refine eichler_mem_leviFix_of_planes hm horth ?_
    have hp : polar (coordinateQuadPlus m F) (g (frameE (K := F) m 0))
        (g (frameF (K := F) m 1)) = 0 := by
      rw [polar_map_of_mem hgO]
      exact horth.ef
    rw [hge0, hgf1, polar_planes horth] at hp
    calc (g (frameE (K := F) m 0) (plusFrameLeft m 0)) *
          (c * (g (frameF (K := F) m 1) (plusFrameRight m 0))) +
          (g (frameE (K := F) m 0) (plusFrameLeft m 1)) *
          (c * (g (frameF (K := F) m 1) (plusFrameRight m 1))) =
        c * ((g (frameE (K := F) m 0) (plusFrameLeft m 0)) *
          (g (frameF (K := F) m 1) (plusFrameRight m 0)) +
          (g (frameE (K := F) m 0) (plusFrameLeft m 1)) *
          (g (frameF (K := F) m 1) (plusFrameRight m 1))) := by ring
      _ = 0 := by rw [hp]; ring
  have hgen2 : ∀ c : F, g * eichler (coordinateQuadPlus m F) (frameE (K := F) m 1)
      (c • frameF (K := F) m 0) * g⁻¹ ∈
      leviFix (orthDerived (coordinateQuadPlus m F)) (framePair (F := F) (m := m) 0)
        (framePair (F := F) (m := m) 1) := by
    intro c
    rw [eichler_conj hgO, hge1, map_smul, hgf0, smul_add, smul_smul, smul_smul]
    refine eichler_mem_leviFix_of_planes hm horth ?_
    have hp : polar (coordinateQuadPlus m F) (g (frameE (K := F) m 1))
        (g (frameF (K := F) m 0)) = 0 := by
      rw [polar_map_of_mem hgO, polar_comm]
      exact horth.fe
    rw [hge1, hgf0, polar_planes horth] at hp
    calc (g (frameE (K := F) m 1) (plusFrameLeft m 0)) *
          (c * (g (frameF (K := F) m 0) (plusFrameRight m 0))) +
          (g (frameE (K := F) m 1) (plusFrameLeft m 1)) *
          (c * (g (frameF (K := F) m 0) (plusFrameRight m 1))) =
        c * ((g (frameE (K := F) m 1) (plusFrameLeft m 0)) *
          (g (frameF (K := F) m 0) (plusFrameRight m 0)) +
          (g (frameE (K := F) m 1) (plusFrameLeft m 1)) *
          (g (frameF (K := F) m 0) (plusFrameRight m 1))) := by ring
      _ = 0 := by rw [hp]; ring
  set S : Set ((Fin (2 * m) → F) ≃ₗ[F] (Fin (2 * m) → F)) :=
    Set.range (fun s : F => eichler (coordinateQuadPlus m F) (framePair (F := F) (m := m) 0).e
      (s • (framePair (F := F) (m := m) 1).f)) ∪
      Set.range (fun s : F => eichler (coordinateQuadPlus m F) (framePair (F := F) (m := m) 1).e
        (s • (framePair (F := F) (m := m) 0).f)) with hS
  have hclos : Subgroup.closure S ≤ (leviFix (orthDerived (coordinateQuadPlus m F))
      (framePair (F := F) (m := m) 0) (framePair (F := F) (m := m) 1)).comap
        (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro x (⟨t, rfl⟩ | ⟨t, rfl⟩)
    · show (MulAut.conj g) (eichler (coordinateQuadPlus m F) (framePair (F := F) (m := m) 0).e
        (t • (framePair (F := F) (m := m) 1).f)) ∈
        leviFix (orthDerived (coordinateQuadPlus m F)) (framePair (F := F) (m := m) 0)
          (framePair (F := F) (m := m) 1)
      rw [MulAut.conj_apply]
      exact hgen1 t
    · show (MulAut.conj g) (eichler (coordinateQuadPlus m F) (framePair (F := F) (m := m) 1).e
        (t • (framePair (F := F) (m := m) 0).f)) ∈
        leviFix (orthDerived (coordinateQuadPlus m F)) (framePair (F := F) (m := m) 0)
          (framePair (F := F) (m := m) 1)
      rw [MulAut.conj_apply]
      exact hgen2 t
  have hl' : l ∈ Subgroup.closure S := leviFix_le_closure horth hE hl
  have hmem := hclos hl'
  rw [Subgroup.mem_comap] at hmem
  simpa [MulAut.conj_apply] using hmem

end Normal


section Order

variable [NeZero m]

theorem isQuasisimple_leviFix (hm : 4 ≤ m) (hF4 : 4 ≤ Nat.card F) :
    CFSG.IsQuasisimple ↥(leviFix (orthDerived (coordinateQuadPlus m F))
      (framePair (F := F) (m := m) 0) (framePair (F := F) (m := m) 1)) := by
  have horth := framePair_orth (F := F) hm
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus (K := F) (n := m) (by omega)
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (leviFixEquiv (framePair (F := F) (m := m) 0) (framePair (F := F) (m := m) 1) horth
      (fun u w => eichler_mem_orthDerived hQ hT u w)).symm
    (CFSG.LieType.HighestRoot.isQuasisimple_SL2_of_four_le (K := F) hF4)

end Order

end CFSG.LocalAnalysis.GLTheoremA.Y10F.OmegaPair
