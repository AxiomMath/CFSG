module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieSp4G1
public import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks

public section

namespace CFSG.LocalAnalysis.GLTheoremA.LevelLieSp4G

open Polynomial CFSG.Open CFSG.LocalAnalysis.GLTheoremA.LevelLieSp4E
open CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.RankThree.Classical
open Matrix

theorem card_F8_eq_two_pow : Nat.card F8 = 2 ^ 3 := by
  rw [card_F8]
  norm_num

theorem orderOf_A_of_Pm (A : ↥(StatedSp 2 F8)) (hA3 : A ^ 3 = 1) (hP : Pm (mat A) = 0) :
    orderOf A = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact orderOf_eq_prime hA3 (ne_one_of_Pm hP)

theorem blocks_of_Pm (A : ↥(StatedSp 2 F8)) (hA3 : A ^ 3 = 1) (hP : Pm (mat A) = 0) :
    SpPrimaryBlocks 2 3 3 A (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj 2 F8 A) :=
  (symplectic_cross_prime_primary_centralizer_blocks (r := 2) (K := F8) (ℓ := 2) (f := 3)
    (p := 3) Nat.prime_two (by norm_num) card_F8_eq_two_pow Nat.prime_three (by norm_num)
    (by norm_num) (by norm_num) _ (orderOf_proj_of_Pm A hA3 hP)).2 A rfl
    (orderOf_A_of_Pm A hA3 hP)

theorem spEnd_quad (A : ↥(StatedSp 2 F8)) (hP : Pm (mat A) = 0) :
    spEnd A * spEnd A + spEnd A + 1 = 0 := by
  apply LinearMap.ext
  intro v
  have h : Pm (mat A) *ᵥ v = 0 := by rw [hP, Matrix.zero_mulVec]
  unfold Pm at h
  simpa [spEnd_apply, mat, Matrix.add_mulVec, Matrix.mulVec_mulVec, Matrix.one_mulVec] using h

theorem h0_mem_primaryFactors (A : ↥(StatedSp 2 F8)) (hP : Pm (mat A) = 0) :
    h0 F8 ∈ primaryFactors (spEnd A) := by
  rw [primaryFactors_eq_h0 (spEnd A) (spEnd_quad A hP)]
  exact Finset.mem_singleton_self _

theorem centralizer_le_spSupported (A : ↥(StatedSp 2 F8)) (hA3 : A ^ 3 = 1)
    (hP : Pm (mat A) = 0) :
    Subgroup.centralizer ({A} : Set ↥(StatedSp 2 F8)) ≤ spSupported A {h0 F8} := by
  have hsup := (blocks_of_Pm A hA3 hP).directProduct.2.2
  rw [← hsup]
  refine iSup_le fun O => ?_
  obtain ⟨h, hh, hO⟩ := O.2
  dsimp only at hO
  rw [Finset.mem_coe, primaryFactors_eq_h0 (spEnd A) (spEnd_quad A hP), Finset.mem_singleton] at hh
  subst hh
  rw [← hO, reciprocal_h0, Set.pair_eq_singleton]

theorem spSupported_le_centralizer (A : ↥(StatedSp 2 F8)) (O : Set (Polynomial F8)) :
    spSupported A O ≤ Subgroup.centralizer ({A} : Set ↥(StatedSp 2 F8)) := fun _ hg =>
  Subgroup.mem_centralizer_singleton_iff.2 (mem_spSupported.1 hg).1

theorem finrank_primaryComponent_h0 (A : ↥(StatedSp 2 F8)) (hP : Pm (mat A) = 0) :
    Module.finrank (AdjoinRoot (h0 F8)) (primaryComponent (spEnd A) (h0 F8)) = 2 := by
  haveI : Fact (Irreducible (h0 F8)) := ⟨irreducible_h0_F8⟩
  have htop : primaryComponent (spEnd A) (h0 F8) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    rw [mem_primaryComponent, aeval_h0, spEnd_quad A hP]
    rfl
  have h1 := finrank_primaryComponent (x := spEnd A) (a := h0 F8)
  have h4 : Module.finrank F8 (primaryComponent (spEnd A) (h0 F8)) = 4 := by
    rw [htop, finrank_top]
    simp [Module.finrank_pi]
  rw [natDegree_h0, h4] at h1
  omega

end CFSG.LocalAnalysis.GLTheoremA.LevelLieSp4G
