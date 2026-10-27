module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddCl
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClDisp
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSLGraphBase
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSLSmallGraph3Basic
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FiveClTwoPart
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClOmegaSmallCount

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank Matrix
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.CatalogueBGraphForm (pureGraphAction)
open CFSG.ComponentClassification.CatFC

section Center

variable {K : Type} [Field K] [Finite K]

theorem u42_card_rootsOfUnity_dvd (k : ℕ) : Nat.card (rootsOfUnity k K) ∣ k := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := rootsOfUnity k K)
  rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
  refine orderOf_dvd_of_pow_eq_one (Subtype.ext ?_)
  have := (mem_rootsOfUnity k (g : Kˣ)).mp g.2
  simpa using this

theorem u42_card_rootsOfUnity_dvd_card (k : ℕ) : Nat.card (rootsOfUnity k K) ∣ Nat.card K - 1 := by
  rw [← Nat.card_units]
  exact Subgroup.card_subgroup_dvd_card _

theorem u42_card_center_sl_dvd {n : ℕ} (hn : 1 ≤ n) :
    Nat.card (center (SpecialLinearGroup (Fin n) K)) ∣ n := by
  rw [Nat.card_congr (SpecialLinearGroup.center_equiv_rootsOfUnity' (R := K)
    (⟨0, hn⟩ : Fin n)).toEquiv]
  have := u42_card_rootsOfUnity_dvd (K := K) (Fintype.card (Fin n))
  simpa using this

theorem u42_card_center_sl_dvd_card {n : ℕ} (hn : 1 ≤ n) :
    Nat.card (center (SpecialLinearGroup (Fin n) K)) ∣ Nat.card K - 1 := by
  rw [Nat.card_congr (SpecialLinearGroup.center_equiv_rootsOfUnity' (R := K)
    (⟨0, hn⟩ : Fin n)).toEquiv]
  exact u42_card_rootsOfUnity_dvd_card _

end Center

section Constraints

variable {n : ℕ} {K : Type} [Field K] [Finite K]

open CFSG.ComponentClassification.CatalogueBGraphForm (isometryGroup mem_isometryGroup)
open CFSG.ComponentClassification.CatalogueBGeneralLinear (specialLinearRange)
open CFSG.SeitzReduction.RankOne.ClTwoPart (card_fixed_dvd_card_mul_onQuotient)

theorem u42_pg_constraints (hn : 3 ≤ n) (A : GL (Fin n) K)
    {J : Subgroup ↥(fixedSubgroup (pureGraphAction n K A))}
    (hJ : U42Hyp (pureGraphAction n K A) J) :
    25920 ∣ Nat.card ↥(isometryGroup n K A⁻¹ ⊓ specialLinearRange n K) ∧
      Nat.card ↥(isometryGroup n K A⁻¹ ⊓ specialLinearRange n K) ∣
        Nat.card (center (SpecialLinearGroup (Fin n) K)) * 25920 := by
  have hout : pureGraphAction n K A ∉ inner (ProjectiveSpecialLinearGroup (Fin n) K) :=
    PSLSmallGraph3.pureGraph_not_inner hn A
  have hC := hJ.card_outer hout
  rw [pureGraphAction_eq_onQuotient A] at hC
  have hB : Nat.card ↥(fixedSubgroup (pgPsi A)) =
      Nat.card ↥(isometryGroup n K A⁻¹ ⊓ specialLinearRange n K) :=
    Nat.card_congr (pgFixEquiv A).toEquiv
  have h1 := card_fixed_onQuotient_dvd (center (SpecialLinearGroup (Fin n) K)) le_rfl (pgPsi A)
    (pgPsi_inv A)
  have h2 := card_fixed_dvd_card_mul_onQuotient (center (SpecialLinearGroup (Fin n) K))
    (pgPsi A) (pgPsi_inv A)
  rw [hC, hB] at h1 h2
  exact ⟨h1, h2⟩

theorem u42_pg_det_sq (R : GL (Fin n) K) (x : GL (Fin n) K) (hx : x ∈ isometryGroup n K R) :
    (Matrix.GeneralLinearGroup.det x) ^ 2 = 1 := by
  rw [mem_isometryGroup] at hx
  have h1 := congrArg Matrix.det hx
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h1
  have hR : (R : Matrix (Fin n) (Fin n) K).det ≠ 0 := (Matrix.GeneralLinearGroup.det R).ne_zero
  apply Units.ext
  have h2 : (x : Matrix (Fin n) (Fin n) K).det * (x : Matrix (Fin n) (Fin n) K).det = 1 := by
    apply mul_left_cancel₀ hR
    linear_combination h1
  simpa [pow_two] using h2

theorem u42_pg_index_dvd (R : GL (Fin n) K) :
    Nat.card ↥(isometryGroup n K R ⊓ specialLinearRange n K) ∣
        Nat.card ↥(isometryGroup n K R) ∧
      Nat.card ↥(isometryGroup n K R) ∣
        2 * Nat.card ↥(isometryGroup n K R ⊓ specialLinearRange n K) := by
  set I := isometryGroup n K R with hI
  let d : ↥I →* Kˣ := (Matrix.GeneralLinearGroup.det).comp I.subtype
  have hker : Nat.card d.ker = Nat.card ↥(I ⊓ specialLinearRange n K) := by
    have h1 : d.ker = (specialLinearRange n K).subgroupOf I := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf,
        CatalogueBGeneralLinear.specialLinearRange_eq_detKernel, MonoidHom.mem_ker]
      rfl
    rw [h1, CatFC.OmegaSmall.card_subgroupOf_eq_card_inf, inf_comm]
  have hrange : d.range ≤ rootsOfUnity 2 K := by
    rintro _ ⟨x, rfl⟩
    rw [mem_rootsOfUnity]
    exact u42_pg_det_sq R x x.2
  have hrd : Nat.card d.range ∣ 2 :=
    (Subgroup.card_dvd_of_le hrange).trans (u42_card_rootsOfUnity_dvd 2)
  have hcard := Subgroup.card_ker_mul_card_range d
  rw [hker] at hcard
  constructor
  · exact ⟨Nat.card d.range, hcard.symm⟩
  · rw [← hcard]
    rw [mul_comm 2]
    exact Nat.mul_dvd_mul_left _ hrd

end Constraints

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
