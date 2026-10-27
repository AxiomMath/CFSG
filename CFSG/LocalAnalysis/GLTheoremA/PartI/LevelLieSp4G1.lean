module

public import CFSG.Blueprint.SourceClassicalTransportLinear
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieSp4ETypeA
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.RankThree.PartOne.KC.OrthogonalReciprocal
public import CFSG.RankThree.PartOne.KC.PrimaryDecomposition
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.LevelLieSp4G

open Polynomial CFSG.Open CFSG.LocalAnalysis.GLTheoremA.LevelLieSp4E
open CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal

abbrev F8 : Type := GaloisField 2 3

noncomputable abbrev h0 (K : Type) [Field K] : K[X] := X ^ 2 + X + 1

theorem card_F8 : Nat.card F8 = 8 := by
  rw [GaloisField.card 2 3 (by norm_num)]
  norm_num

theorem no_root_F8 (x : F8) : x * x + x + 1 ≠ 0 := by
  classical
  haveI : Fintype F8 := Fintype.ofFinite F8
  exact no_root (by rw [← Nat.card_eq_fintype_card]; exact card_F8) x

theorem natDegree_h0 (K : Type) [Field K] : (h0 K).natDegree = 2 := by
  unfold h0
  compute_degree!

theorem monic_h0 (K : Type) [Field K] : (h0 K).Monic := by
  unfold h0
  monicity!

theorem coeff_h0 (K : Type) [Field K] (n : ℕ) :
    (h0 K).coeff n = if n = 0 ∨ n = 1 ∨ n = 2 then 1 else 0 := by
  unfold h0
  rcases Nat.lt_or_ge n 3 with hn | hn
  · interval_cases n <;> simp [coeff_X, coeff_one, coeff_X_pow]
  · have h2 : n ≠ 2 := by omega
    have h1 : n ≠ 1 := by omega
    have h0' : n ≠ 0 := by omega
    simp only [coeff_add, coeff_X_pow, coeff_X, coeff_one]
    simp [h0', h1, h2, Ne.symm h1]

theorem irreducible_h0_F8 : Irreducible (h0 F8) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [natDegree_h0]
    simp
  · intro x hx
    apply no_root_F8 x
    simpa [h0, IsRoot.def, sq] using hx

theorem reverse_h0 (K : Type) [Field K] : (h0 K).reverse = h0 K := by
  ext n
  rw [coeff_reverse, natDegree_h0, coeff_h0, coeff_h0]
  rcases Nat.lt_or_ge n 3 with hn | hn
  · interval_cases n <;> simp [revAt_le]
  · rw [revAt_eq_self_of_lt (by omega : 2 < n)]

theorem reciprocal_h0 (K : Type) [Field K] : reciprocalPolynomial (h0 K) = h0 K := by
  rw [reciprocalPolynomial, reverse_h0, coeff_h0]
  simp

theorem aeval_h0 {K V : Type} [Field K] [AddCommGroup V] [Module K V] (y : Module.End K V) :
    aeval y (h0 K) = y * y + y + 1 := by
  simp [h0, sq]

theorem minpoly_eq_h0 {V : Type} [AddCommGroup V] [Module F8 V] [Nontrivial V]
    (y : Module.End F8 V) (hy : y * y + y + 1 = 0) : minpoly F8 y = h0 F8 :=
  (minpoly.eq_of_irreducible_of_monic irreducible_h0_F8 (by rw [aeval_h0, hy])
    (monic_h0 F8)).symm

theorem primaryFactors_eq_h0 {V : Type} [AddCommGroup V] [Module F8 V] [FiniteDimensional F8 V]
    [Nontrivial V] (y : Module.End F8 V) (hy : y * y + y + 1 = 0) :
    primaryFactors y = {h0 F8} := by
  classical
  ext a
  rw [Finset.mem_singleton, mem_primaryFactors, minpoly_eq_h0 y hy]
  constructor
  · rintro ⟨hirr, hmon, hdvd⟩
    exact eq_of_monic_of_associated hmon (monic_h0 F8)
      (hirr.associated_of_dvd irreducible_h0_F8 hdvd)
  · rintro rfl
    exact ⟨irreducible_h0_F8, monic_h0 F8, dvd_rfl⟩

theorem ne_one_of_Pm {K : Type} [Field K] [CharP K 2] {A : ↥(StatedSp 2 K)}
    (hP : Pm (mat A) = 0) : A ≠ 1 := by
  rintro rfl
  rw [mat_one] at hP
  have h := congrFun (congrFun hP (Sum.inl 0)) (Sum.inl 0)
  simp only [Pm, Matrix.add_apply, Matrix.one_apply_eq, Matrix.mul_one, Matrix.zero_apply] at h
  have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  have h3 : (1 : K) + 1 + 1 = 1 := by rw [h2, zero_add]
  rw [h3] at h
  exact one_ne_zero h

theorem orderOf_proj_of_Pm (A : ↥(StatedSp 2 F8)) (hA3 : A ^ 3 = 1) (hP : Pm (mat A) = 0) :
    orderOf (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj 2 F8 A) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  apply orderOf_eq_prime
  · rw [← map_pow, hA3, map_one]
  · intro h1
    have hA : A ∈ CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spScalars 2 F8 := by
      rw [← CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.ker_proj]
      exact MonoidHom.mem_ker.2 h1
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spScalars,
      Subgroup.mem_subgroupOf, CFSG.Open.StatedScalars, MonoidHom.mem_range] at hA
    obtain ⟨c, hc⟩ := hA
    have hm : mat A = Matrix.scalar (Fin 2 ⊕ Fin 2) (c : F8) := by
      rw [mat, ← hc]
      rfl
    have h := congrFun (congrFun hP (Sum.inl 0)) (Sum.inl 0)
    rw [hm] at h
    simp [Pm, Matrix.scalar_apply, sq] at h
    exact no_root_F8 c h

end CFSG.LocalAnalysis.GLTheoremA.LevelLieSp4G
