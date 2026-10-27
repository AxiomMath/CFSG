module

public import CFSG.LieType.AlgebraicGroups.ToralRootCover
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.Lattice.SteinbergBIListMatrix

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups
open scoped Matrix

@[expose] def twE6D5 : Set (Fin Tag.E6.rank → ℤ) := {α | IsRoot Tag.E6 α ∧ α 0 = 0}

theorem twE6_root_coord_mem : ((rootFinset Tag.E6).filter
    (fun α => α 0 = -1 ∨ α 0 = 0 ∨ α 0 = 1)) = rootFinset Tag.E6 := by decide +kernel

theorem twE6_root_coord {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α) :
    α 0 = -1 ∨ α 0 = 0 ∨ α 0 = 1 := by
  have h : α ∈ (rootFinset Tag.E6).filter (fun α => α 0 = -1 ∨ α 0 = 0 ∨ α 0 = 1) := by
    rw [twE6_root_coord_mem]
    exact mem_rootFinset.2 hα
  exact (Finset.mem_filter.1 h).2

theorem twE6D5_ncard : twE6D5.ncard = 40 := by
  have h : ((rootFinset Tag.E6).filter (fun α => α 0 = 0)).card = 40 := by decide +kernel
  have h2 : twE6D5 = ↑((rootFinset Tag.E6).filter (fun α => α 0 = 0)) := by
    ext α
    simp only [Finset.coe_filter, Set.mem_setOf_eq, twE6D5]
    rw [mem_rootFinset]
  rw [h2, Set.ncard_coe_finset, h]

@[expose] def twE6omega1Tuple {K : Type} [Field K] (ζ : Kˣ) : Fin Tag.E6.rank → Kˣ :=
  fun i => if i = 0 then ζ else 1

theorem rootChar_twE6omega1Tuple {K : Type} [Field K] (ζ : Kˣ) (v : Fin Tag.E6.rank → ℤ) :
    rootChar (twE6omega1Tuple ζ) v = ζ ^ (v 0) := by
  rw [rootChar, Finset.prod_eq_single (0 : Fin Tag.E6.rank)]
  · simp [twE6omega1Tuple]
  · intro i _ hi
    simp [twE6omega1Tuple, hi]
  · intro h
    exact absurd (Finset.mem_univ (0 : Fin Tag.E6.rank)) h

theorem kernelRoots_omega1 {K : Type} [Field K] {q : ℕ} (hq : q.Prime) {ζ : Kˣ}
    (hζq : ζ ^ q = 1) (hζ1 : ζ ≠ 1) :
    kernelRoots (rootCharHom (twE6omega1Tuple ζ)) = twE6D5 := by
  have hone : ζ ^ (1 : ℕ) ≠ 1 := by simpa using hζ1
  ext γ
  rw [kernelRoots_rootCharHom]
  constructor
  · rintro ⟨hγ, hχ⟩
    refine ⟨hγ, ?_⟩
    rw [rootChar_twE6omega1Tuple] at hχ
    rcases twE6_root_coord hγ with h | h | h
    · rw [h] at hχ
      exact absurd (by simpa using hχ : ζ ^ (1 : ℕ) = 1) hone
    · exact h
    · rw [h] at hχ
      exact absurd (by simpa using hχ : ζ ^ (1 : ℕ) = 1) hone
  · rintro ⟨hγ, h0⟩
    exact ⟨hγ, by rw [rootChar_twE6omega1Tuple, h0, zpow_zero]⟩

end CFSG.LocalAnalysis.GLTheoremA.Y10F
