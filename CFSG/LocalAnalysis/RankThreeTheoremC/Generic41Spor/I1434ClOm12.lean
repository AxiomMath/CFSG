module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434ClSp6Aux
public import CFSG.Open.StatedDefs
import CFSG.Timmesfeld.Orders.ClassicalOmega
import CFSG.Assembly.Subnormal
import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.LieType.Steinberg.Classical.SpinFrame
import CFSG.LieType.Steinberg.Exceptional.E6E7
import CFSG.LieType.Steinberg.Families
import CFSG.LieType.Steinberg.G2
import CFSG.LieType.Universal.Spin.Generation
import CFSG.LieType.Universal.Spin.OddCT
import CFSG.LieType.Universal.Spin.PlusCT
import CFSG.LieType.Universal.Spin.Structure
import CFSG.LieType.Universal.SpinOmega
import CFSG.LieType.Universal.Unitary
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
import CFSG.LocalAnalysis.SectionRank.SporadicCover
import CFSG.Sporadic.M23.M23Group
import CFSG.Sporadic.Th.F2Spec
import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434.Cl

open CFSG.Open Matrix
open scoped commutatorElement

namespace Om12

abbrev OmI : Type := Fin (6 - 1) ⊕ Fin (6 - 1) ⊕ Fin 2

section Polar

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

theorem dot_alt_eq_zero (D : Matrix ι ι R) (hd : ∀ a, D a a = 0)
    (hs : ∀ a b, D a b + D b a = 0) (v : ι → R) : v ⬝ᵥ D *ᵥ v = 0 := by
  simp only [dotProduct, mulVec, Finset.mul_sum]
  rw [← Finset.sum_product']
  refine Finset.sum_involution (fun p _ => p.swap) (fun p _ => ?_) (fun p _ hp => ?_)
    (fun p hp => Finset.mem_univ _) (fun p _ => Prod.swap_swap p)
  · obtain ⟨a, b⟩ := p
    simp only [Prod.swap_prod_mk]
    have := hs a b
    calc v a * (D a b * v b) + v b * (D b a * v a) = v a * v b * (D a b + D b a) := by ring
      _ = 0 := by rw [this, mul_zero]
  · obtain ⟨a, b⟩ := p
    intro h
    simp only [Prod.swap_prod_mk, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    apply hp
    simp [hd]

theorem quad_eq_of_polar (P H : Matrix ι ι R) (hd : ∀ a, P a a = H a a)
    (hp : ∀ a b, P a b + P b a = H a b + H b a) (v : ι → R) : v ⬝ᵥ P *ᵥ v = v ⬝ᵥ H *ᵥ v := by
  have h := dot_alt_eq_zero (P - H) (fun a => by simp [hd]) (fun a b => by
    have := hp a b
    simp only [Matrix.sub_apply]
    linear_combination this) v
  rw [Matrix.sub_mulVec, dotProduct_sub, sub_eq_zero] at h
  exact h

@[expose] def PolarOK (H M : Matrix ι ι R) : Prop :=
  (∀ a, (Mᵀ * H * M) a a = H a a) ∧
    ∀ a b, (Mᵀ * H * M) a b + (Mᵀ * H * M) b a = H a b + H b a

theorem PolarOK.dot_eq {H M : Matrix ι ι R} (h : PolarOK H M) (v : ι → R) :
    (M *ᵥ v) ⬝ᵥ H *ᵥ (M *ᵥ v) = v ⬝ᵥ H *ᵥ v := by
  rw [← quad_eq_of_polar _ H h.1 h.2 v, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.mulVec_transpose, dotProduct_comm v, dotProduct_comm (M *ᵥ v),
    Matrix.dotProduct_mulVec]

theorem PolarOK.map {S : Type*} [CommRing S] (f : R →+* S) {H M : Matrix ι ι R}
    (h : PolarOK H M) : PolarOK (H.map f) (M.map f) := by
  have key : (M.map f)ᵀ * H.map f * M.map f = (Mᵀ * H * M).map f := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  unfold PolarOK
  rw [key]
  refine ⟨fun a => ?_, fun a b => ?_⟩
  · simp only [Matrix.map_apply]
    rw [h.1 a]
  · simp only [Matrix.map_apply]
    rw [← map_add, h.2 a b, map_add]

end Polar

@[expose] def Hq (R : Type*) [CommRing R] (b c : R) : Matrix OmI OmI R :=
  Matrix.of fun x y =>
    match x, y with
    | .inl i, .inr (.inl j) => if i = j then 1 else 0
    | .inr (.inr i), .inr (.inr j) =>
        if i = 0 ∧ j = 0 then 1 else if i = 0 ∧ j = 1 then b else if i = 1 ∧ j = 1 then c else 0
    | _, _ => 0

theorem quadMinus_eq_dot {K : Type} [Field K] (b c : K) (v : OmI → K) :
    StatedQuadMinus 6 K b c v = v ⬝ᵥ (Hq K b c) *ᵥ v := by
  simp only [StatedQuadMinus, dotProduct, Matrix.mulVec, Hq, Matrix.of_apply,
    Fintype.sum_sum_type]
  simp
  ring

theorem Hq_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (b c : R) :
    (Hq R b c).map f = Hq S (f b) (f c) := by
  ext x y
  rcases x with i | i | i <;> rcases y with j | j | j <;> simp [Hq, Matrix.map_apply] <;>
    split_ifs <;> simp

@[expose] def e12 : OmI ≃ Fin 12 :=
  (Equiv.sumCongr (Equiv.refl (Fin (6 - 1))) (finSumFinEquiv (m := 5) (n := 2))).trans
    (finSumFinEquiv (m := 5) (n := 5 + 2))

@[expose] def eBlk : OmI ≃ Fin 4 × Fin 3 :=
  e12.trans ((finProdFinEquiv (m := 3) (n := 4)).symm.trans (Equiv.prodComm (Fin 3) (Fin 4)))

@[expose] def lit (t : Fin 12 → Fin 12 → ZMod 2) : Matrix OmI OmI (ZMod 2) :=
  Matrix.of fun x y => t (e12 x) (e12 y)

@[expose] def tabP : Fin 12 → Fin 12 → ZMod 2 :=
  ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1],
  ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0],
  ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
  ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0],
  ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]]

@[expose] def tabPi : Fin 12 → Fin 12 → ZMod 2 :=
  ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
  ![0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0],
  ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
  ![0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0],
  ![0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0]]

@[expose] def tabT0 : Fin 12 → Fin 12 → ZMod 2 :=
  ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
  ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
  ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1],
  ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0]]

@[expose] def tabT1 : Fin 12 → Fin 12 → ZMod 2 :=
  ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0],
  ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0],
  ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
  ![0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0],
  ![0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

@[expose] def tabT2 : Fin 12 → Fin 12 → ZMod 2 :=
  ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0],
  ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0],
  ![0, 0, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0],
  ![0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

@[expose] def tabF0 : Fin 12 → Fin 12 → ZMod 2 :=
  ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
  ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
  ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0],
  ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
  ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1],
  ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1]]

@[expose] def tabF1 : Fin 12 → Fin 12 → ZMod 2 :=
  ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0],
  ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0],
  ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
  ![0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0],
  ![0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
  ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

@[expose] def tabF2 : Fin 12 → Fin 12 → ZMod 2 :=
  ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0],
  ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
  ![0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0],
  ![0, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0],
  ![0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

@[expose] def tabS01 : Fin 12 → Fin 12 → ZMod 2 :=
  ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1],
  ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0],
  ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1],
  ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
  ![0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 1],
  ![0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0]]

@[expose] def tabS02 : Fin 12 → Fin 12 → ZMod 2 :=
  ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1],
  ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1],
  ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
  ![0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0],
  ![0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0],
  ![0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0]]

@[expose] def t4 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 1, 0, 0; 1, 1, 0, 1; 0, 0, 0, 1; 0, 1, 1, 0]

@[expose] def bd {R : Type*} [CommRing R] (Y : Fin 3 → Matrix (Fin 4) (Fin 4) R) :
    Matrix OmI OmI R :=
  (Matrix.blockDiagonal Y).submatrix eBlk eBlk

@[expose] def PM : Matrix OmI OmI (ZMod 2) := lit tabP

@[expose] def PiM : Matrix OmI OmI (ZMod 2) := lit tabPi

@[expose] def TM : Fin 3 → Matrix OmI OmI (ZMod 2) := ![lit tabT0, lit tabT1, lit tabT2]

@[expose] def FM : Fin 3 → Matrix OmI OmI (ZMod 2) := ![lit tabF0, lit tabF1, lit tabF2]

@[expose] def SM01 : Matrix OmI OmI (ZMod 2) := lit tabS01

@[expose] def SM02 : Matrix OmI OmI (ZMod 2) := lit tabS02

theorem P_Pi : PM * PiM = 1 := by decide +kernel

theorem Pi_P : PiM * PM = 1 := by decide +kernel

theorem TM_pow_five : ∀ j, TM j * TM j * TM j * TM j * TM j = 1 := by decide +kernel

theorem TM_comm : ∀ i j, TM i * TM j = TM j * TM i := by decide +kernel

theorem FM_pow_four : ∀ j, FM j * FM j * FM j * FM j = 1 := by decide +kernel

theorem FM_TM_same : ∀ j, FM j * TM j = TM j * TM j * FM j := by decide +kernel

theorem FM_TM_other : ∀ i j, i ≠ j → FM i * TM j = TM j * FM i := by decide +kernel

theorem SM01_sq : SM01 * SM01 = 1 := by decide +kernel

theorem SM02_sq : SM02 * SM02 = 1 := by decide +kernel

theorem SM01_FM0 : SM01 * FM 0 = FM 1 * SM01 := by decide +kernel

theorem SM01_FM1 : SM01 * FM 1 = FM 0 * SM01 := by decide +kernel

theorem SM02_FM0 : SM02 * FM 0 = FM 2 * SM02 := by decide +kernel

theorem polar_TM : ∀ j, PolarOK (Hq (ZMod 2) 1 1) (TM j) := by
  unfold PolarOK
  decide +kernel

theorem polar_FM : ∀ j, PolarOK (Hq (ZMod 2) 1 1) (FM j) := by
  unfold PolarOK
  decide +kernel

theorem polar_SM01 : PolarOK (Hq (ZMod 2) 1 1) SM01 := by
  unfold PolarOK
  decide +kernel

theorem polar_SM02 : PolarOK (Hq (ZMod 2) 1 1) SM02 := by
  unfold PolarOK
  decide +kernel

theorem TM_bridge : ∀ j, TM j = PM * bd (Pi.mulSingle j t4) * PiM := by decide +kernel

theorem t4_pow_eq_one : ∀ a : Fin 5, t4 ^ (a : ℕ) = 1 → a = 0 := by decide +kernel

@[expose] def NM : Fin 5 → Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  ![0,
    !![1, 0, 1, 1; 0, 0, 1, 1; 1, 1, 0, 1; 1, 1, 1, 1],
    !![1, 0, 0, 1; 0, 0, 1, 0; 0, 1, 1, 1; 1, 0, 1, 0],
    !![0, 0, 0, 1; 0, 1, 1, 0; 0, 1, 0, 1; 1, 0, 1, 1],
    !![0, 0, 1, 1; 0, 1, 1, 1; 1, 1, 1, 1; 1, 1, 1, 0]]

theorem t4_sub_inv : ∀ a : Fin 5, a ≠ 0 →
    (t4 ^ (a : ℕ) - 1) * NM a = 1 ∧ NM a * (t4 ^ (a : ℕ) - 1) = 1 := by decide +kernel

section Blocks

variable {R : Type*} [CommRing R]

theorem bd_mul (Y Y' : Fin 3 → Matrix (Fin 4) (Fin 4) R) : bd (Y * Y') = bd Y * bd Y' := by
  unfold bd
  show (Matrix.blockDiagonal fun j => Y j * Y' j).submatrix eBlk eBlk = _
  rw [Matrix.blockDiagonal_mul, ← Matrix.submatrix_mul_equiv _ _ eBlk eBlk eBlk]

theorem bd_one : bd (1 : Fin 3 → Matrix (Fin 4) (Fin 4) R) = 1 := by
  unfold bd
  rw [Matrix.blockDiagonal_one]
  exact Matrix.submatrix_one_equiv eBlk

theorem bd_sub (Y Y' : Fin 3 → Matrix (Fin 4) (Fin 4) R) : bd (Y - Y') = bd Y - bd Y' := by
  unfold bd
  rw [Matrix.blockDiagonal_sub]
  ext x y
  simp [Matrix.submatrix_apply]

theorem bd_injective {Y Y' : Fin 3 → Matrix (Fin 4) (Fin 4) R} (h : bd Y = bd Y') : Y = Y' := by
  funext l
  ext r s
  have := congrFun (congrFun h (eBlk.symm (r, l))) (eBlk.symm (s, l))
  simpa [bd, Matrix.submatrix_apply] using this

theorem bd_apply (Y : Fin 3 → Matrix (Fin 4) (Fin 4) R) (r s : Fin 4) (l l' : Fin 3) :
    bd Y (eBlk.symm (r, l)) (eBlk.symm (s, l')) =
      if l = l' then Y l r s else 0 := by
  simp [bd, Matrix.submatrix_apply, Matrix.blockDiagonal_apply]

end Blocks

@[expose] def TG (j : Fin 3) : GL OmI (ZMod 2) :=
  ⟨TM j, TM j * TM j * TM j * TM j, by simpa [mul_assoc] using TM_pow_five j,
    by simpa [mul_assoc] using TM_pow_five j⟩

@[expose] def FG (j : Fin 3) : GL OmI (ZMod 2) :=
  ⟨FM j, FM j * FM j * FM j, by simpa [mul_assoc] using FM_pow_four j,
    by simpa [mul_assoc] using FM_pow_four j⟩

@[expose] def SG01 : GL OmI (ZMod 2) := ⟨SM01, SM01, SM01_sq, SM01_sq⟩

@[expose] def SG02 : GL OmI (ZMod 2) := ⟨SM02, SM02, SM02_sq, SM02_sq⟩

theorem TG_pow_five (j : Fin 3) : TG j ^ 5 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val]
  show TM j ^ 5 = 1
  simpa [pow_succ] using TM_pow_five j

theorem TG_comm (i j : Fin 3) : Commute (TG i) (TG j) := Units.ext (TM_comm i j)

theorem FG_TG_same (j : Fin 3) : FG j * TG j = TG j ^ 2 * FG j := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val]
  show FM j * TM j = TM j ^ 2 * FM j
  simpa [pow_two] using FM_TM_same j

theorem FG_TG_other {i j : Fin 3} (h : i ≠ j) : FG i * TG j = TG j * FG i :=
  Units.ext (FM_TM_other i j h)

theorem SG01_FG0 : SG01 * FG 0 = FG 1 * SG01 := Units.ext SM01_FM0

theorem SG01_FG1 : SG01 * FG 1 = FG 0 * SG01 := Units.ext SM01_FM1

theorem SG02_FG0 : SG02 * FG 0 = FG 2 * SG02 := Units.ext SM02_FM0

theorem TG_pow_val_add (j : Fin 3) (x y : ZMod 5) :
    TG j ^ (x + y).val = TG j ^ x.val * TG j ^ y.val := by
  rw [← pow_add, ZMod.val_add, ← pow_eq_pow_mod _ (TG_pow_five j)]

@[expose] def torZ (v : Fin 3 → ZMod 5) : GL OmI (ZMod 2) :=
  TG 0 ^ (v 0).val * TG 1 ^ (v 1).val * TG 2 ^ (v 2).val

theorem torZ_add (v w : Fin 3 → ZMod 5) : torZ (v + w) = torZ v * torZ w := by
  unfold torZ
  rw [survivor_mul_comm_three ((TG_comm 1 0).pow_pow _ _) ((TG_comm 2 0).pow_pow _ _)
    ((TG_comm 2 1).pow_pow _ _)]
  simp only [Pi.add_apply, TG_pow_val_add]

@[expose] noncomputable def torHomZ : Multiplicative (Fin 3 → ZMod 5) →* GL OmI (ZMod 2) :=
  MonoidHom.mk' (fun v => torZ (Multiplicative.toAdd v)) (fun v w => torZ_add _ _)

theorem frame_mul (X Y : Matrix OmI OmI (ZMod 2)) :
    PM * X * PiM * (PM * Y * PiM) = PM * (X * Y) * PiM := by
  calc PM * X * PiM * (PM * Y * PiM) = PM * X * (PiM * PM) * Y * PiM := by
        simp only [Matrix.mul_assoc]
    _ = PM * (X * Y) * PiM := by rw [Pi_P, Matrix.mul_one, Matrix.mul_assoc PM X Y]

theorem TG_pow_matrix (j : Fin 3) (n : ℕ) :
    ((TG j ^ n : GL OmI (ZMod 2)) : Matrix OmI OmI (ZMod 2)) =
      PM * bd (Pi.mulSingle j (t4 ^ n)) * PiM := by
  induction n with
  | zero =>
    rw [pow_zero, Units.val_one, pow_zero, Pi.mulSingle_one, bd_one, Matrix.mul_one, P_Pi]
  | succ n ih =>
    rw [pow_succ, Units.val_mul, ih, show ((TG j : GL OmI (ZMod 2)) : Matrix OmI OmI (ZMod 2)) =
      PM * bd (Pi.mulSingle j t4) * PiM from TM_bridge j, frame_mul, ← bd_mul,
      ← Pi.mulSingle_mul, pow_succ]

theorem torZ_matrix (v : Fin 3 → ZMod 5) :
    ((torZ v : GL OmI (ZMod 2)) : Matrix OmI OmI (ZMod 2)) =
      PM * bd (fun l => t4 ^ (v l).val) * PiM := by
  unfold torZ
  rw [Units.val_mul, Units.val_mul, TG_pow_matrix, TG_pow_matrix, TG_pow_matrix, frame_mul,
    ← bd_mul, frame_mul, ← bd_mul]
  congr 3
  funext l
  fin_cases l <;> simp [Pi.mulSingle_apply]

abbrev matZ (x : GL OmI (ZMod 2)) : Matrix OmI OmI (ZMod 2) := (x : Matrix OmI OmI (ZMod 2))

theorem frame_sub_one (Y : Fin 3 → Matrix (Fin 4) (Fin 4) (ZMod 2)) :
    PM * bd Y * PiM - 1 = PM * bd (Y - 1) * PiM := by
  rw [bd_sub, bd_one, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, P_Pi]

@[expose] def Ninv5 (x : ZMod 5) : Matrix (Fin 4) (Fin 4) (ZMod 2) := NM ⟨x.val, ZMod.val_lt x⟩

theorem sub_Ninv (x : ZMod 5) (hx : x ≠ 0) :
    (t4 ^ x.val - 1) * Ninv5 x = 1 ∧ Ninv5 x * (t4 ^ x.val - 1) = 1 :=
  t4_sub_inv ⟨x.val, ZMod.val_lt x⟩
    (fun h => hx ((ZMod.val_eq_zero x).1 (congrArg Fin.val h)))

theorem torZ_sub_one (v : Fin 3 → ZMod 5) :
    matZ (torZ v) - 1 = PM * bd ((fun l => t4 ^ (v l).val) - 1) * PiM := by
  show ((torZ v : GL OmI (ZMod 2)) : Matrix OmI OmI (ZMod 2)) - 1 = _
  rw [torZ_matrix, frame_sub_one]

theorem eq_zero_of_mulVec_torus (v : Fin 3 → ZMod 5) (hv : ∀ l, v l ≠ 0) (w : OmI → ZMod 2)
    (hw : (matZ (torZ v) - 1) *ᵥ w = 0) : w = 0 := by
  have hr : ((fun l => t4 ^ (v l).val) - 1) * (fun l => Ninv5 (v l)) = 1 := by
    funext l
    exact (sub_Ninv (v l) (hv l)).1
  have hl : (fun l => Ninv5 (v l)) * ((fun l => t4 ^ (v l).val) - 1) = 1 := by
    funext l
    exact (sub_Ninv (v l) (hv l)).2
  have h1 : (matZ (torZ v) - 1) * (PM * bd (fun l => Ninv5 (v l)) * PiM) = 1 := by
    rw [torZ_sub_one, frame_mul, ← bd_mul, hr, bd_one, Matrix.mul_one, P_Pi]
  have h2 : (PM * bd (fun l => Ninv5 (v l)) * PiM) * (matZ (torZ v) - 1) = 1 := by
    rw [torZ_sub_one, frame_mul, ← bd_mul, hl, bd_one, Matrix.mul_one, P_Pi]
  calc w = ((PM * bd (fun l => Ninv5 (v l)) * PiM) * (matZ (torZ v) - 1)) *ᵥ w := by
        rw [h2, Matrix.one_mulVec]
    _ = (PM * bd (fun l => Ninv5 (v l)) * PiM) *ᵥ ((matZ (torZ v) - 1) *ᵥ w) := by
        rw [Matrix.mulVec_mulVec]
    _ = 0 := by rw [hw, Matrix.mulVec_zero]

theorem eight_le_finrank_ker {v : Fin 3 → ZMod 5} {i j : Fin 3} (hij : i ≠ j) (hi : v i = 0)
    (hj : v j = 0) :
    8 ≤ Module.finrank (ZMod 2) (LinearMap.ker (Matrix.toLin' (matZ (torZ v) - 1))) := by
  let x : Fin 4 × Fin 2 → OmI := fun s => eBlk.symm (s.1, ![i, j] s.2)
  have hx : Function.Injective x := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h1 := eBlk.symm.injective h
    simp only [Prod.mk.injEq] at h1
    obtain ⟨h2, h3⟩ := h1
    subst h2
    fin_cases b <;> fin_cases b' <;> simp_all [hij, hij.symm]
  have hM := torZ_sub_one v
  have hmem : ∀ s, PM *ᵥ (Pi.single (x s) (1 : ZMod 2) : OmI → ZMod 2) ∈
      LinearMap.ker (Matrix.toLin' (matZ (torZ v) - 1)) := by
    intro s
    have hl : v (![i, j] s.2) = 0 := by
      obtain ⟨a, b⟩ := s
      fin_cases b <;> simp [hi, hj]
    have hu : PiM *ᵥ (PM *ᵥ (Pi.single (x s) (1 : ZMod 2) : OmI → ZMod 2)) =
        Pi.single (x s) 1 := by
      rw [Matrix.mulVec_mulVec, Pi_P, Matrix.one_mulVec]
    have hbd : bd ((fun l => t4 ^ (v l).val) - 1) *ᵥ
        (Pi.single (x s) (1 : ZMod 2) : OmI → ZMod 2) = 0 := by
      funext y
      obtain ⟨⟨r', l'⟩, rfl⟩ := eBlk.symm.surjective y
      rw [Matrix.mulVec_single_one, Matrix.col_apply]
      simp only [Pi.zero_apply, x]
      rw [bd_apply]
      split_ifs with h
      · subst h
        simp [hl]
      · rfl
    rw [LinearMap.mem_ker, Matrix.toLin'_apply, hM, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, hu, hbd, Matrix.mulVec_zero]
  have := survivor_card_le_finrank_ker (matZ (torZ v) - 1) PM PiM Pi_P x hx (fun s => by
    have h := hmem s
    rwa [LinearMap.mem_ker, Matrix.toLin'_apply] at h)
  simpa using this

theorem exactly_one_zero {v : Fin 3 → ZMod 5}
    (h : Module.finrank (ZMod 2) (LinearMap.ker (Matrix.toLin' (matZ (torZ v) - 1))) = 4) :
    (v 0 = 0 ∧ v 1 ≠ 0 ∧ v 2 ≠ 0) ∨ (v 0 ≠ 0 ∧ v 1 = 0 ∧ v 2 ≠ 0) ∨
      (v 0 ≠ 0 ∧ v 1 ≠ 0 ∧ v 2 = 0) := by
  by_cases h0 : v 0 = 0 <;> by_cases h1 : v 1 = 0 <;> by_cases h2 : v 2 = 0
  · have := eight_le_finrank_ker (v := v) (i := 0) (j := 1) (by decide) h0 h1
    omega
  · have := eight_le_finrank_ker (v := v) (i := 0) (j := 1) (by decide) h0 h1
    omega
  · have := eight_le_finrank_ker (v := v) (i := 0) (j := 2) (by decide) h0 h2
    omega
  · exact Or.inl ⟨h0, h1, h2⟩
  · have := eight_le_finrank_ker (v := v) (i := 1) (j := 2) (by decide) h1 h2
    omega
  · exact Or.inr (Or.inl ⟨h0, h1, h2⟩)
  · exact Or.inr (Or.inr ⟨h0, h1, h2⟩)
  · have hv : ∀ l, v l ≠ 0 := by
      intro l
      fin_cases l <;> assumption
    have hbot : LinearMap.ker (Matrix.toLin' (matZ (torZ v) - 1)) = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro w hw
      rw [Matrix.toLin'_apply] at hw
      exact eq_zero_of_mulVec_torus v hv w hw
    rw [hbot, finrank_bot] at h
    omega

theorem torZ_eq_one {v : Fin 3 → ZMod 5} (h : torZ v = 1) (l : Fin 3) : v l = 0 := by
  have h1 : PM * bd (fun l => t4 ^ (v l).val) * PiM = 1 := by
    rw [← torZ_matrix, h, Units.val_one]
  have h2 : bd (fun l => t4 ^ (v l).val) = bd (1 : Fin 3 → Matrix (Fin 4) (Fin 4) (ZMod 2)) := by
    rw [bd_one]
    calc bd (fun l => t4 ^ (v l).val) = PiM * (PM * bd (fun l => t4 ^ (v l).val) * PiM) * PM := by
          simp only [← Matrix.mul_assoc, Pi_P, Matrix.one_mul]
          rw [Matrix.mul_assoc _ PiM PM, Pi_P, Matrix.mul_one]
      _ = 1 := by rw [h1, Matrix.mul_one, Pi_P]
  have h3 := congrFun (bd_injective h2) l
  have h4 : t4 ^ (v l).val = 1 := h3
  have hlt : (v l).val < 5 := ZMod.val_lt (v l)
  have := t4_pow_eq_one ⟨(v l).val, hlt⟩ h4
  exact (ZMod.val_eq_zero (v l)).1 (congrArg Fin.val this)

theorem torHomZ_injective : Function.Injective torHomZ := by
  rw [injective_iff_map_eq_one]
  intro v hv
  funext l
  exact torZ_eq_one hv l

section FWorld

variable {F : Type} [Field F] [Fintype F]

noncomputable def psi2 (hF : Fintype.card F = 2) : ZMod 2 ≃+* F :=
  FiniteField.ringEquivOfCardEq (by rw [hF, ZMod.card])

theorem eq_zero_or_one (hF : Fintype.card F = 2) (x : F) : x = 0 ∨ x = 1 := by
  obtain ⟨y, rfl⟩ := (psi2 hF).surjective x
  have : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by decide
  rcases this y with rfl | rfl <;> simp

theorem coeffs_eq_one (hF : Fintype.card F = 2) {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    b = 1 ∧ c = 1 := by
  have h2 : (2 : F) = 0 := by
    have := map_ofNat (psi2 hF) 2
    rw [show ((2 : ZMod 2) : ZMod 2) = 0 from rfl, map_zero] at this
    exact this.symm
  have hc : c ≠ 0 := by simpa using hirr 0
  have hb : 1 + b + c ≠ 0 := by simpa using hirr 1
  have hc1 : c = 1 := (eq_zero_or_one hF c).resolve_left hc
  subst hc1
  refine ⟨(eq_zero_or_one hF b).resolve_left fun hb0 => hb ?_, rfl⟩
  rw [hb0]
  linear_combination h2

@[expose] noncomputable def phiGL (hF : Fintype.card F = 2) : GL OmI (ZMod 2) →* GL OmI F :=
  Matrix.GeneralLinearGroup.map (psi2 hF).toRingHom

theorem coe_phiGL (hF : Fintype.card F = 2) (x : GL OmI (ZMod 2)) :
    ((phiGL hF x : GL OmI F) : Matrix OmI OmI F) = (x : Matrix OmI OmI (ZMod 2)).map (psi2 hF) :=
  rfl

theorem phiGL_injective (hF : Fintype.card F = 2) : Function.Injective (phiGL hF) := by
  intro x y h
  apply Units.ext
  have := congrArg (fun z : GL OmI F => (z : Matrix OmI OmI F)) h
  simp only [coe_phiGL] at this
  exact Matrix.map_injective (psi2 hF).injective this

@[expose] def isoCore (F : Type) [Field F] : Subgroup (GL OmI F) :=
  Subgroup.closure {A : GL OmI F | ∀ v : OmI → F,
    StatedQuadMinus 6 F 1 1 ((A : Matrix OmI OmI F) *ᵥ v) = StatedQuadMinus 6 F 1 1 v}

theorem mem_isoCore (hF : Fintype.card F = 2) {M : Matrix OmI OmI (ZMod 2)}
    (hM : PolarOK (Hq (ZMod 2) 1 1) M) {x : GL OmI F}
    (hx : (x : Matrix OmI OmI F) = M.map (psi2 hF)) : x ∈ isoCore F := by
  apply Subgroup.subset_closure
  intro v
  rw [hx, quadMinus_eq_dot, quadMinus_eq_dot]
  have h1 : Hq F 1 1 = (Hq (ZMod 2) 1 1).map (psi2 hF) := by
    have := Hq_map (psi2 hF).toRingHom (1 : ZMod 2) 1
    simpa using this.symm
  rw [h1]
  exact (hM.map (psi2 hF).toRingHom).dot_eq v

@[expose] noncomputable def TF (hF : Fintype.card F = 2) (j : Fin 3) : GL OmI F :=
  phiGL hF (TG j)

@[expose] noncomputable def FF (hF : Fintype.card F = 2) (j : Fin 3) : GL OmI F :=
  phiGL hF (FG j)

@[expose] noncomputable def S01F (hF : Fintype.card F = 2) : GL OmI F := phiGL hF SG01

@[expose] noncomputable def S02F (hF : Fintype.card F = 2) : GL OmI F := phiGL hF SG02

theorem TF_mem_iso (hF : Fintype.card F = 2) (j : Fin 3) : TF hF j ∈ isoCore F :=
  mem_isoCore hF (polar_TM j) (by rw [TF, coe_phiGL]; rfl)

theorem FF_mem_iso (hF : Fintype.card F = 2) (j : Fin 3) : FF hF j ∈ isoCore F :=
  mem_isoCore hF (polar_FM j) (by rw [FF, coe_phiGL]; rfl)

theorem S01F_mem_iso (hF : Fintype.card F = 2) : S01F hF ∈ isoCore F :=
  mem_isoCore hF polar_SM01 (by rw [S01F, coe_phiGL]; rfl)

theorem S02F_mem_iso (hF : Fintype.card F = 2) : S02F hF ∈ isoCore F :=
  mem_isoCore hF polar_SM02 (by rw [S02F, coe_phiGL]; rfl)

theorem TF_pow_five (hF : Fintype.card F = 2) (j : Fin 3) : TF hF j ^ 5 = 1 := by
  rw [TF, ← map_pow, TG_pow_five, map_one]

theorem FF_TF_same (hF : Fintype.card F = 2) (j : Fin 3) :
    FF hF j * TF hF j * (FF hF j)⁻¹ = TF hF j ^ 2 := by
  rw [mul_inv_eq_iff_eq_mul]
  have := congrArg (phiGL hF) (FG_TG_same j)
  rwa [map_mul, map_mul, map_pow] at this

theorem FF_TF_other (hF : Fintype.card F = 2) {i j : Fin 3} (h : i ≠ j) :
    FF hF i * TF hF j * (FF hF i)⁻¹ = TF hF j := by
  rw [mul_inv_eq_iff_eq_mul]
  have := congrArg (phiGL hF) (FG_TG_other h)
  rwa [map_mul, map_mul] at this

theorem S01F_FF1 (hF : Fintype.card F = 2) : S01F hF * FF hF 1 * (S01F hF)⁻¹ = FF hF 0 := by
  rw [mul_inv_eq_iff_eq_mul]
  have := congrArg (phiGL hF) SG01_FG1
  rwa [map_mul, map_mul] at this

theorem S01F_FF0 (hF : Fintype.card F = 2) : S01F hF * FF hF 0 * (S01F hF)⁻¹ = FF hF 1 := by
  rw [mul_inv_eq_iff_eq_mul]
  have := congrArg (phiGL hF) SG01_FG0
  rwa [map_mul, map_mul] at this

theorem S02F_FF0 (hF : Fintype.card F = 2) : S02F hF * FF hF 0 * (S02F hF)⁻¹ = FF hF 2 := by
  rw [mul_inv_eq_iff_eq_mul]
  have := congrArg (phiGL hF) SG02_FG0
  rwa [map_mul, map_mul] at this

theorem TF_mem_omega (hF : Fintype.card F = 2) (j : Fin 3) :
    TF hF j ∈ StatedOmega (StatedQuadMinus 6 F 1 1) := by
  have h := Subgroup.commutator_mem_commutator (FF_mem_iso hF j) (TF_mem_iso hF j)
  have e : ⁅FF hF j, TF hF j⁆ = TF hF j := by
    rw [commutatorElement_def, FF_TF_same, pow_two, mul_inv_cancel_right]
  rw [e] at h
  exact h

@[expose] noncomputable def torGL (hF : Fintype.card F = 2) :
    Multiplicative (Fin 3 → ZMod 5) →* GL OmI F :=
  (phiGL hF).comp torHomZ

theorem torGL_apply (hF : Fintype.card F = 2) (v : Fin 3 → ZMod 5) :
    torGL hF (Multiplicative.ofAdd v) =
      TF hF 0 ^ (v 0).val * TF hF 1 ^ (v 1).val * TF hF 2 ^ (v 2).val := by
  show phiGL hF (torZ v) = _
  unfold torZ
  simp only [map_mul, map_pow]
  rfl

theorem torGL_mem (hF : Fintype.card F = 2) (u : Multiplicative (Fin 3 → ZMod 5)) :
    torGL hF u ∈ StatedOmega (StatedQuadMinus 6 F 1 1) := by
  have h := torGL_apply hF (Multiplicative.toAdd u)
  rw [show Multiplicative.ofAdd (Multiplicative.toAdd u) = u from rfl] at h
  rw [h]
  exact mul_mem (mul_mem (pow_mem (TF_mem_omega hF 0) _) (pow_mem (TF_mem_omega hF 1) _))
    (pow_mem (TF_mem_omega hF 2) _)

@[expose] noncomputable def torHom (hF : Fintype.card F = 2) :
    Multiplicative (Fin 3 → ZMod 5) →* ↥(StatedOmega (StatedQuadMinus 6 F 1 1)) :=
  (torGL hF).codRestrict _ (torGL_mem hF)

theorem torHom_injective (hF : Fintype.card F = 2) : Function.Injective (torHom hF) := by
  intro u w h
  have h1 : torGL hF u = torGL hF w := congrArg Subtype.val h
  exact torHomZ_injective ((phiGL_injective hF) h1)

theorem scalars_subgroupOf_eq_bot (hF : Fintype.card F = 2) (H : Subgroup (GL OmI F)) :
    (StatedScalars OmI F).subgroupOf H = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨u, hu⟩ := Subgroup.mem_subgroupOf.1 hx
  have hu1 : u = 1 := Units.ext ((eq_zero_or_one hF u).resolve_left u.ne_zero)
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hu, hu1, map_one]
  rfl

theorem natCard_proj_omega (hF : Fintype.card F = 2) :
    Nat.card (StatedProj (StatedOmega (StatedQuadMinus 6 F 1 1))) =
      Nat.card (StatedOmega (StatedQuadMinus 6 F 1 1)) := by
  have hbot := scalars_subgroupOf_eq_bot hF (StatedOmega (StatedQuadMinus 6 F 1 1))
  have h1 : Nat.card ((StatedScalars OmI F).subgroupOf
      (StatedOmega (StatedQuadMinus 6 F 1 1))) = 1 := by
    rw [hbot, Subgroup.card_bot]
  have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((StatedScalars OmI F).subgroupOf (StatedOmega (StatedQuadMinus 6 F 1 1)))
  rw [h1, mul_one] at hc
  exact hc.symm

theorem charP_two (hF : Fintype.card F = 2) : CharP F 2 :=
  charP_of_injective_ringHom (f := (psi2 hF).toRingHom) (psi2 hF).injective 2

theorem factorization_card_omega (hF : Fintype.card F = 2) :
    (Nat.card ↥(StatedOmega (StatedQuadMinus 6 F 1 1))).factorization 5 = 3 := by
  haveI : Finite F := Finite.of_fintype F
  haveI : CharP F 2 := charP_two hF
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hirr : ∀ s : F, s ^ 2 + 1 * s + 1 ≠ 0 := by
    intro s
    rcases eq_zero_or_one hF s with rfl | rfl
    · simp
    · intro h
      have : (1 : F) = 0 := by linear_combination h - h2
      exact one_ne_zero this
  have hcardF : Nat.card F = 2 := by rw [Nat.card_eq_fintype_card, hF]
  have h := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega_quadMinus (K := F)
    (n := 6) (by norm_num) hirr
  rw [hcardF, natCard_proj_omega hF] at h
  have hN : Nat.card ↥(StatedOmega (StatedQuadMinus 6 F 1 1)) =
      5 ^ 3 * (2 ^ 30 * 13 * (3 * 3 * 63 * 51 * 1023)) := by
    have : ((Nat.card ↥(StatedOmega (StatedQuadMinus 6 F 1 1)) : ℕ) : ℤ) =
        ((5 ^ 3 * (2 ^ 30 * 13 * (3 * 3 * 63 * 51 * 1023)) : ℕ) : ℤ) := by
      rw [h]
      decide +kernel
    exact_mod_cast this
  have h5 : Nat.factorization (2 ^ 30 * 13 * (3 * 3 * 63 * 51 * 1023)) 5 = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    norm_num
  rw [hN, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply, h5,
    Nat.Prime.factorization_pow (by norm_num : Nat.Prime 5)]
  simp

theorem FF_conj_TF_pow_same (hF : Fintype.card F = 2) (x : Fin 3) (n : ℕ) :
    FF hF x * TF hF x ^ n * (FF hF x)⁻¹ = TF hF x ^ (2 * n) := by
  have h : (MulAut.conj (FF hF x)) (TF hF x ^ n) = ((MulAut.conj (FF hF x)) (TF hF x)) ^ n :=
    map_pow _ _ _
  rw [MulAut.conj_apply, MulAut.conj_apply, FF_TF_same, ← pow_mul] at h
  exact h

theorem FF_conj_TF_pow_other (hF : Fintype.card F = 2) {x l : Fin 3} (hxl : x ≠ l) (n : ℕ) :
    FF hF x * TF hF l ^ n * (FF hF x)⁻¹ = TF hF l ^ n := by
  have h : (MulAut.conj (FF hF x)) (TF hF l ^ n) = ((MulAut.conj (FF hF x)) (TF hF l)) ^ n :=
    map_pow _ _ _
  rw [MulAut.conj_apply, MulAut.conj_apply, FF_TF_other hF hxl] at h
  exact h

theorem TF_pow_val_two_mul (hF : Fintype.card F = 2) (x : Fin 3) (a : ZMod 5) :
    TF hF x ^ (2 * a).val = TF hF x ^ (2 * a.val) := by
  have h : (2 * a).val = 2 * a.val % 5 := by
    rw [ZMod.val_mul]
    rfl
  rw [h, ← pow_eq_pow_mod _ (TF_pow_five hF x)]

theorem FF_conj_torGL (hF : Fintype.card F = 2) (x : Fin 3) (v : Fin 3 → ZMod 5) :
    FF hF x * torGL hF (Multiplicative.ofAdd v) * (FF hF x)⁻¹ =
      torGL hF (Multiplicative.ofAdd (Function.update v x (2 * v x))) := by
  rw [torGL_apply, torGL_apply, survivor_conj_mul_three]
  have hx : x = 0 ∨ x = 1 ∨ x = 2 := by
    fin_cases x <;> simp
  rcases hx with rfl | rfl | rfl
  · rw [FF_conj_TF_pow_same, FF_conj_TF_pow_other hF (by decide),
      FF_conj_TF_pow_other hF (by decide)]
    simp [Function.update_apply, TF_pow_val_two_mul]
  · rw [FF_conj_TF_pow_other hF (by decide), FF_conj_TF_pow_same,
      FF_conj_TF_pow_other hF (by decide)]
    simp [Function.update_apply, TF_pow_val_two_mul]
  · rw [FF_conj_TF_pow_other hF (by decide), FF_conj_TF_pow_other hF (by decide),
      FF_conj_TF_pow_same]
    simp [Function.update_apply, TF_pow_val_two_mul]

theorem FF_pow_conj_torGL (hF : Fintype.card F = 2) (x : Fin 3) (m : ℕ) (v : Fin 3 → ZMod 5) :
    FF hF x ^ m * torGL hF (Multiplicative.ofAdd v) * (FF hF x ^ m)⁻¹ =
      torGL hF (Multiplicative.ofAdd (Function.update v x (2 ^ m * v x))) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h : FF hF x ^ (m + 1) * torGL hF (Multiplicative.ofAdd v) * (FF hF x ^ (m + 1))⁻¹ =
        FF hF x * (FF hF x ^ m * torGL hF (Multiplicative.ofAdd v) * (FF hF x ^ m)⁻¹) *
          (FF hF x)⁻¹ := by
      rw [pow_succ']
      group
    have hu : Function.update (Function.update v x (2 ^ m * v x)) x
        (2 * Function.update v x (2 ^ m * v x) x) = Function.update v x (2 ^ (m + 1) * v x) := by
      rw [Function.update_idem, Function.update_self]
      congr 1
      ring
    rw [h, ih, FF_conj_torGL, hu]

theorem two_pow_injective : ∀ m m' : Fin 4, (2 : ZMod 5) ^ (m : ℕ) = 2 ^ (m' : ℕ) → m = m' := by
  decide

theorem four_lines (hF : Fintype.card F = 2) {i j k : Fin 3} (hij : i ≠ j) {S : GL OmI F}
    (hS : S ∈ isoCore F) (hSF : S * FF hF i * S⁻¹ = FF hF k)
    (g : ↥(StatedOmega (StatedQuadMinus 6 F 1 1))) {v : Fin 3 → ZMod 5} (hvk : v k = 0)
    (hvi : v i ≠ 0) (hvj : v j ≠ 0) :
    4 ≤ Set.ncard {B : Subgroup ↥(StatedOmega (StatedQuadMinus 6 F 1 1)) |
      ∃ g' : ↥(StatedOmega (StatedQuadMinus 6 F 1 1)),
        B = (Subgroup.zpowers (g * torHom hF (Multiplicative.ofAdd v) * g⁻¹)).map
            (MulAut.conj g').toMonoidHom ∧
          B ≤ (torHom hF).range.map (MulAut.conj g).toMonoidHom} := by
  have hmem : ∀ m : Fin 4, ⁅FF hF i ^ (m : ℕ), S⁆ ∈ StatedOmega (StatedQuadMinus 6 F 1 1) :=
    fun m => Subgroup.commutator_mem_commutator (pow_mem (FF_mem_iso hF i) _) hS
  refine survivor_lines_torus (torHom hF) (torHom_injective hF) g v
    (fun m => ⟨⁅FF hF i ^ (m : ℕ), S⁆, hmem m⟩)
    (fun m => Function.update v i (2 ^ (m : ℕ) * v i)) ?_ ?_
  · intro m
    apply Subtype.ext
    show ⁅FF hF i ^ (m : ℕ), S⁆ * torGL hF (Multiplicative.ofAdd v) * ⁅FF hF i ^ (m : ℕ), S⁆⁻¹ =
      torGL hF (Multiplicative.ofAdd (Function.update v i (2 ^ (m : ℕ) * v i)))
    have hSa : S * FF hF i ^ (m : ℕ) * S⁻¹ = FF hF k ^ (m : ℕ) := by
      have h := map_pow (MulAut.conj S) (FF hF i) (m : ℕ)
      rw [MulAut.conj_apply, MulAut.conj_apply, hSF] at h
      exact h
    have hcomm : ⁅FF hF i ^ (m : ℕ), S⁆ = FF hF i ^ (m : ℕ) * (FF hF k ^ (m : ℕ))⁻¹ := by
      rw [commutatorElement_def, ← hSa]
      group
    have hk : FF hF k ^ (m : ℕ) * torGL hF (Multiplicative.ofAdd v) * (FF hF k ^ (m : ℕ))⁻¹ =
        torGL hF (Multiplicative.ofAdd v) := by
      have hu : Function.update v k (2 ^ (m : ℕ) * v k) = v := by
        rw [hvk, mul_zero]
        exact Function.update_eq_self_iff.2 hvk.symm
      rw [FF_pow_conj_torGL, hu]
    have hk' : (FF hF k ^ (m : ℕ))⁻¹ * torGL hF (Multiplicative.ofAdd v) * FF hF k ^ (m : ℕ) =
        torGL hF (Multiplicative.ofAdd v) := by
      have h1 : FF hF k ^ (m : ℕ) * torGL hF (Multiplicative.ofAdd v) =
          torGL hF (Multiplicative.ofAdd v) * FF hF k ^ (m : ℕ) := by
        rwa [mul_inv_eq_iff_eq_mul] at hk
      calc (FF hF k ^ (m : ℕ))⁻¹ * torGL hF (Multiplicative.ofAdd v) * FF hF k ^ (m : ℕ)
          = (FF hF k ^ (m : ℕ))⁻¹ * (torGL hF (Multiplicative.ofAdd v) * FF hF k ^ (m : ℕ)) := by
            rw [mul_assoc]
        _ = (FF hF k ^ (m : ℕ))⁻¹ * (FF hF k ^ (m : ℕ) * torGL hF (Multiplicative.ofAdd v)) := by
            rw [h1]
        _ = torGL hF (Multiplicative.ofAdd v) := inv_mul_cancel_left _ _
    rw [hcomm]
    calc FF hF i ^ (m : ℕ) * (FF hF k ^ (m : ℕ))⁻¹ * torGL hF (Multiplicative.ofAdd v) *
          (FF hF i ^ (m : ℕ) * (FF hF k ^ (m : ℕ))⁻¹)⁻¹
        = FF hF i ^ (m : ℕ) * ((FF hF k ^ (m : ℕ))⁻¹ * torGL hF (Multiplicative.ofAdd v) *
            FF hF k ^ (m : ℕ)) * (FF hF i ^ (m : ℕ))⁻¹ := by group
      _ = FF hF i ^ (m : ℕ) * torGL hF (Multiplicative.ofAdd v) * (FF hF i ^ (m : ℕ))⁻¹ := by
          rw [hk']
      _ = _ := FF_pow_conj_torGL hF i m v
  · intro m m' n hn
    haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    have hj := congrFun hn j
    have hi := congrFun hn i
    simp only [Function.update_of_ne hij.symm] at hj
    simp only [Function.update_self] at hi
    have hn1 : n = 1 := mul_right_cancel₀ hvj (hj.trans (one_mul _).symm)
    rw [hn1, one_mul] at hi
    exact two_pow_injective m m' (mul_right_cancel₀ hvi hi)

abbrev matO (x : ↥(StatedOmega (StatedQuadMinus 6 F 1 1))) : Matrix OmI OmI F :=
  ((x : GL OmI F) : Matrix OmI OmI F)

theorem matO_torHom (hF : Fintype.card F = 2) (v : Fin 3 → ZMod 5) :
    matO (torHom hF (Multiplicative.ofAdd v)) = (matZ (torZ v)).map (psi2 hF) := rfl

theorem finrank_ker_conj_om (g A : ↥(StatedOmega (StatedQuadMinus 6 F 1 1))) :
    Module.finrank F (LinearMap.ker (Matrix.toLin' (matO (g⁻¹ * A * g) - 1))) =
      Module.finrank F (LinearMap.ker (Matrix.toLin' (matO A - 1))) := by
  have h := survivor_finrank_ker_conj (g : GL OmI F) (matO A - 1)
  have e : matO (g⁻¹ * A * g) - 1 = (((g : GL OmI F)⁻¹ : GL OmI F) : Matrix OmI OmI F) *
      (matO A - 1) * ((g : GL OmI F) : Matrix OmI OmI F) := by
    have h1 : (((g : GL OmI F)⁻¹ : GL OmI F) : Matrix OmI OmI F) *
        ((g : GL OmI F) : Matrix OmI OmI F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    symm
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1]
    rfl
  rw [e]
  exact h

end FWorld

end Om12

theorem domega12_lines {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 2) {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (Q : Sylow 5 ↥(StatedOmega (StatedQuadMinus 6 F b c)))
    (A : ↥(StatedOmega (StatedQuadMinus 6 F b c)))
    (hAQ : A ∈ (Q : Subgroup ↥(StatedOmega (StatedQuadMinus 6 F b c)))) (hA5 : A ^ 5 = 1)
    (hA1 : A ≠ 1)
    (hker : Module.finrank F (LinearMap.ker (Matrix.toLin'
      (((A : GL (Fin (6 - 1) ⊕ Fin (6 - 1) ⊕ Fin 2) F) :
        Matrix (Fin (6 - 1) ⊕ Fin (6 - 1) ⊕ Fin 2) (Fin (6 - 1) ⊕ Fin (6 - 1) ⊕ Fin 2) F) - 1))) =
        4) :
    4 ≤ Set.ncard {B : Subgroup ↥(StatedOmega (StatedQuadMinus 6 F b c)) |
      ∃ g : ↥(StatedOmega (StatedQuadMinus 6 F b c)),
        B = (Subgroup.zpowers A).map (MulAut.conj g).toMonoidHom ∧
          B ≤ (Q : Subgroup ↥(StatedOmega (StatedQuadMinus 6 F b c)))} := by
  obtain ⟨rfl, rfl⟩ := Om12.coeffs_eq_one hF hirr
  obtain ⟨g, v, hAeq, hQeq⟩ := survivor_exists_conj_torus (Om12.torHom hF)
    (Om12.torHom_injective hF) (Om12.factorization_card_omega hF) Q hAQ
  have hker' : Module.finrank (ZMod 2) (LinearMap.ker (Matrix.toLin'
      (Om12.matZ (Om12.torZ v) - 1))) = 4 := by
    have hv : Om12.torHom hF (Multiplicative.ofAdd v) = g⁻¹ * A * g := by
      rw [hAeq]
      group
    have h1 : Module.finrank F (LinearMap.ker (Matrix.toLin'
        (Om12.matO (Om12.torHom hF (Multiplicative.ofAdd v)) - 1))) = 4 := by
      rw [hv, Om12.finrank_ker_conj_om]
      exact hker
    have h2 : Om12.matO (Om12.torHom hF (Multiplicative.ofAdd v)) - 1 =
        (Om12.matZ (Om12.torZ v) - 1).map (Om12.psi2 hF) := by
      have := map_sub ((Om12.psi2 hF).toRingHom.mapMatrix) (Om12.matZ (Om12.torZ v)) 1
      rw [map_one] at this
      rw [Om12.matO_torHom]
      exact this.symm
    rw [h2, survivor_finrank_ker_map] at h1
    exact h1
  rw [hQeq, hAeq]
  rcases Om12.exactly_one_zero hker' with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  · exact Om12.four_lines hF (i := 1) (j := 2) (k := 0) (by decide) (Om12.S01F_mem_iso hF)
      (Om12.S01F_FF1 hF) g h0 h1 h2
  · exact Om12.four_lines hF (i := 0) (j := 2) (k := 1) (by decide) (Om12.S01F_mem_iso hF)
      (Om12.S01F_FF0 hF) g h1 h0 h2
  · exact Om12.four_lines hF (i := 0) (j := 1) (k := 2) (by decide) (Om12.S02F_mem_iso hF)
      (Om12.S02F_FF0 hF) g h2 h0 h1

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434.Cl
