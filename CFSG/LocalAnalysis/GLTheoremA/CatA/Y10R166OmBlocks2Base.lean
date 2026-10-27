module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualTypeAFix
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCoresForms

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

@[expose] noncomputable def frameE (n : ℕ) (k : Fin n) : Fin (2 * n) → K :=
  Pi.single (plusFrameLeft n k) 1

@[expose] noncomputable def frameF (n : ℕ) (k : Fin n) : Fin (2 * n) → K :=
  Pi.single (plusFrameRight n k) 1

@[expose] def zeroIdx (n : ℕ) (hn : 4 ≤ n) : Fin n := ⟨0, by omega⟩

@[expose] def twoIdx (n : ℕ) (hn : 4 ≤ n) : Fin n := ⟨2, by omega⟩

@[expose] def oneIdx (n : ℕ) (hn : 4 ≤ n) : Fin n := ⟨1, by omega⟩

@[expose] noncomputable def plusFrame (n : ℕ) :
    IsHypFrame (coordinateQuadPlus n K) (plusFrameLeft n) (plusFrameRight n) :=
  isHypFrame_plus K n

@[expose] noncomputable def rootSpace (n : ℕ) (hn : 4 ≤ n) : Submodule K (Fin (2 * n) → K) where
  carrier := {y | y (plusFrameLeft n (zeroIdx n hn)) = 0 ∧
    y (plusFrameRight n (zeroIdx n hn)) = 0 ∧
    y (plusFrameRight n (twoIdx n hn)) = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro y z ⟨h1, h2, h3⟩ ⟨g1, g2, g3⟩
    exact ⟨by simp [h1, g1], by simp [h2, g2], by simp [h3, g3]⟩
  smul_mem' := by
    rintro c x ⟨h1, h2, h3⟩
    exact ⟨by simp [Pi.smul_apply, h1], by simp [Pi.smul_apply, h2],
      by simp [Pi.smul_apply, h3]⟩

theorem polar_frameE_rootSpace (n : ℕ) (hn : 4 ≤ n) (y : rootSpace (K := K) n hn) :
    polar (coordinateQuadPlus n K) (frameE n (twoIdx n hn))
      ((y : rootSpace n hn) : Fin (2 * n) → K) = 0 := by
  have h := isHypCoord_coordinateQuadPlus (K := K) (twoIdx n hn)
  simp only [frameE, plusFrameLeft]
  rw [h.polar_left]
  obtain ⟨-, -, h3⟩ := y.2
  exact h3

@[expose] noncomputable def rootElt (n : ℕ) (hn : 4 ≤ n)
    (y : rootSpace (K := K) n hn) : orthDerived (coordinateQuadPlus n K) :=
  ⟨eichler (coordinateQuadPlus n K) (frameE n (twoIdx n hn))
      ((y : rootSpace n hn) : Fin (2 * n) → K),
    eichler_mem_orthDerived_plus (K := K) (n := n) (by omega) (frameE n (twoIdx n hn))
      ((y : rootSpace n hn) : Fin (2 * n) → K)⟩

@[expose] noncomputable def rootGroupHom (n : ℕ) (hn : 4 ≤ n) :
    Multiplicative (rootSpace (K := K) n hn) →*
      matrixProjectiveDerived (coordinateQuadPlus n K) where
  toFun y := projHom _ (rootElt n hn y)
  map_one' := by
    have h1 : rootElt n hn (1 : Multiplicative (rootSpace (K := K) n hn)) = 1 := by
      apply Subtype.ext
      exact eichler_zero_right (coordinateQuadPlus n K) (frameE n (twoIdx n hn))
    rw [h1, map_one]
  map_mul' y z := by
    have h1 : rootElt n hn (y * z) = rootElt n hn y * rootElt n hn z := by
      apply Subtype.ext
      exact (eichler_mul (polar_frameE_rootSpace (K := K) n hn y)
        (polar_frameE_rootSpace (K := K) n hn z)).symm
    rw [h1, map_mul]

section QTorsion

variable [Finite K]

@[expose] noncomputable def qTorus (n q : ℕ) :
    Subgroup (matrixProjectiveDerived (coordinateQuadPlus n K)) :=
  ((plusFrame n).frameHom.comp ((MonoidHom.compLeft (rootsOfUnity q K).subtype (Fin n)))).range

@[expose] noncomputable def qTorusHom (n q : ℕ) :
    (Fin n → rootsOfUnity q K) →* matrixProjectiveDerived (coordinateQuadPlus n K) :=
  (plusFrame n).frameHom.comp ((MonoidHom.compLeft (rootsOfUnity q K).subtype (Fin n)))

theorem qTorus_eq_range (n q : ℕ) :
    qTorus (K := K) n q = (qTorusHom (K := K) n q).range := rfl

theorem qTorusHom_injective (n q : ℕ) :
    Function.Injective (qTorusHom (K := K) n q) := by
  intro p p' h
  have h1 : (MonoidHom.compLeft (rootsOfUnity q K).subtype (Fin n)) p =
      (MonoidHom.compLeft (rootsOfUnity q K).subtype (Fin n)) p' :=
    (plusFrame (K := K) n).frameHom_injective h
  funext i
  exact Subtype.ext (congrFun h1 i)

theorem card_qTorus (n q : ℕ) (hq : q.Prime) (hdvd : q ∣ Nat.card K - 1) :
    Nat.card (qTorus (K := K) n q) = q ^ n := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  rw [qTorus_eq_range, MonoidHom.range_eq_map,
    Subgroup.card_map_of_injective (qTorusHom_injective n q)]
  rw [show Nat.card ↥(⊤ : Subgroup (Fin n → rootsOfUnity q K)) =
      Nat.card (Fin n → rootsOfUnity q K) from
    Nat.card_congr Subgroup.topEquiv.toEquiv]
  rw [Nat.card_pi]
  simp only [CFSG.LinearGroups.card_rootsOfUnity_of_dvd (K := K) (d := q) hdvd]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem isElemAbelian_top_pi_rootsOfUnity [Finite K] (n q : ℕ) (hdvd : q ∣ Nat.card K - 1) :
    IsElemAbelian q (⊤ : Subgroup (Fin n → rootsOfUnity q K)) := by
  have hcomm : IsMulCommutative ↥(⊤ : Subgroup (Fin n → rootsOfUnity q K)) :=
    IsMulCommutative.of_comm fun a b => Subtype.ext (mul_comm _ _)
  refine ⟨hcomm, fun x _ => ?_⟩
  funext i
  apply Subtype.ext
  exact (mem_rootsOfUnity q ((x i : rootsOfUnity q K) : Kˣ)).1 (x i).2

theorem isElemAbelian_qTorus (n q : ℕ) (hdvd : q ∣ Nat.card K - 1) :
    IsElemAbelian q (qTorus (K := K) n q) := by
  have hcomm : IsMulCommutative ↥(qTorus (K := K) n q) := by
    refine IsMulCommutative.of_comm fun a b => ?_
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    obtain ⟨p, hp⟩ := MonoidHom.mem_range.1 a.2
    obtain ⟨p', hp'⟩ := MonoidHom.mem_range.1 b.2
    rw [← hp, ← hp', ← map_mul, ← map_mul]
    exact congrArg (qTorusHom (K := K) n q) (mul_comm p p')
  refine ⟨hcomm, fun x hx => ?_⟩
  obtain ⟨p, hp⟩ := MonoidHom.mem_range.1 hx
  have hp' : qTorusHom (K := K) n q p = x := hp
  have hpq : p ^ q = 1 := by
    funext i
    apply Subtype.ext
    exact (mem_rootsOfUnity q ((p i : rootsOfUnity q K) : Kˣ)).1 (p i).2
  calc x ^ q = (qTorusHom (K := K) n q p) ^ q := by rw [← hp']
    _ = qTorusHom (K := K) n q (p ^ q) := (map_pow _ _ _).symm
    _ = 1 := by rw [hpq, map_one]

end QTorsion

section Element

variable [Finite K]

@[expose] noncomputable def qTorusElt (n : ℕ) (hn : 4 ≤ n) (ζ : Kˣ) :
    matrixProjectiveDerived (coordinateQuadPlus n K) :=
  (plusFrame n).frameHom (Pi.mulSingle (zeroIdx n hn) ζ)

@[expose] noncomputable def qTorusEltParam (n : ℕ) (hn : 4 ≤ n) {q : ℕ} {ζ : Kˣ}
    (hζq : ζ ^ q = 1) : Fin n → rootsOfUnity q K :=
  Pi.mulSingle (zeroIdx n hn) ⟨ζ, (mem_rootsOfUnity q ζ).2 hζq⟩

theorem qTorusElt_eq_hom (n : ℕ) (hn : 4 ≤ n) {q : ℕ} {ζ : Kˣ} (hζq : ζ ^ q = 1) :
    qTorusElt (K := K) n hn ζ = qTorusHom (K := K) n q (qTorusEltParam n hn hζq) := by
  rw [qTorusElt, qTorusHom, MonoidHom.comp_apply]
  congr 1
  funext i
  by_cases hi : i = zeroIdx n hn
  · simp [qTorusEltParam, MonoidHom.compLeft_apply, hi]
  · simp [qTorusEltParam, MonoidHom.compLeft_apply, hi]

theorem qTorusElt_mem_qTorus (n : ℕ) (hn : 4 ≤ n) {q : ℕ} {ζ : Kˣ} (hζq : ζ ^ q = 1) :
    qTorusElt (K := K) n hn ζ ∈ qTorus (K := K) n q := by
  rw [qTorusElt_eq_hom n hn hζq, qTorus]
  exact MonoidHom.mem_range.2 ⟨_, rfl⟩

theorem qTorusElt_mem_pairTorus (n : ℕ) (hn : 4 ≤ n) (ζ : Kˣ) :
    qTorusElt (K := K) n hn ζ ∈ pairTorus (K := K) (zeroIdx n hn) := by
  have hfr := frameTorusOf_rootParam (K := K) (Q := coordinateQuadPlus n K)
    (a := fun k => plusIndexEquiv n (.inl k)) (b := fun k => plusIndexEquiv n (.inr k))
    (k := zeroIdx n hn)
  rw [pairTorus, ← hfr, frameTorusOf]
  refine Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 ?_)
  refine ⟨Pi.mulSingle (zeroIdx n hn) ζ, ⟨ζ, rfl⟩, ?_⟩
  rfl

theorem qTorusElt_ne_one (n : ℕ) (hn : 4 ≤ n) {ζ : Kˣ} (hζ1 : ζ ≠ 1) :
    qTorusElt (K := K) n hn ζ ≠ 1 := by
  intro h
  let t : Fin n → Kˣ := fun i => if i = zeroIdx n hn then ζ else 1
  have hx : qTorusElt (K := K) n hn ζ = (plusFrame (K := K) n).frameHom t := by
    rw [qTorusElt]
    congr 1
    funext i
    by_cases hi : i = zeroIdx n hn <;> simp [t, hi]
  rw [hx] at h
  have h1 : t = 1 := (plusFrame (K := K) n).frameHom_injective (by simpa using h)
  have := congrFun h1 (zeroIdx n hn)
  simp [t] at this
  exact hζ1 this

end Element

section CoordAction

variable [Finite K]

theorem plusFrameLeft_injective (n : ℕ) :
    Function.Injective (plusFrameLeft (n := n)) := by
  intro i j h
  have h' := (plusIndexEquiv n).injective h
  simpa using h'

theorem plusFrameRight_injective (n : ℕ) :
    Function.Injective (plusFrameRight (n := n)) := by
  intro i j h
  have h' := (plusIndexEquiv n).injective h
  simpa using h'

end CoordAction

end CFSG.LocalAnalysis.GLTheoremA.Y10F.OmegaPair
