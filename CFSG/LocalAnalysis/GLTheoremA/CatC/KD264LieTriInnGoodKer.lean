module

public import CFSG.LieType.AlgebraicGroups.ToralRootCover
import CFSG.Blueprint.ChevalleyRootArtifact
import CFSG.RankThree.PartOne.KE.CTTorusFixed

public section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.TriInn

theorem eq_of_cube_roots {L : Type} [Field L] {x y : Lˣ} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hxy : x * y ≠ 1) : x = y := by
  have hx' : (x : L) ^ 3 = 1 := by
    have := congrArg Units.val hx
    simpa using this
  have hy' : (y : L) ^ 3 = 1 := by
    have := congrArg Units.val hy
    simpa using this
  have hxq : (x : L) ^ 2 + x + 1 = 0 := by
    have h : ((x : L) - 1) * ((x : L) ^ 2 + x + 1) = 0 := by linear_combination hx'
    rcases mul_eq_zero.1 h with h | h
    · exact absurd (Units.ext (sub_eq_zero.1 h)) hx1
    · exact h
  have hyq : (y : L) ^ 2 + y + 1 = 0 := by
    have h : ((y : L) - 1) * ((y : L) ^ 2 + y + 1) = 0 := by linear_combination hy'
    rcases mul_eq_zero.1 h with h | h
    · exact absurd (Units.ext (sub_eq_zero.1 h)) hy1
    · exact h
  have h : ((x : L) - y) * ((x : L) + y + 1) = 0 := by linear_combination hxq - hyq
  rcases mul_eq_zero.1 h with h | h
  · exact Units.ext (sub_eq_zero.1 h)
  · exfalso
    apply hxy
    apply Units.ext
    have hy2 : (y : L) = -1 - x := by linear_combination h
    simp only [Units.val_mul, Units.val_one]
    rw [hy2]
    linear_combination (-1 : L) * hxq


theorem exists_mem_kernelRoots_d4 {L : Type} [Field L] {a : Fin Tag.D4.rank → Lˣ}
    (ha : ∀ i, a i ^ 3 = 1) : ∃ γ, γ ∈ kernelRoots (rootCharHom a) := by
  have r0 : IsRoot Tag.D4 (Pi.single 0 1 : Fin Tag.D4.rank → ℤ) := isRoot_single _ 0
  have r1 : IsRoot Tag.D4 (Pi.single 1 1 : Fin Tag.D4.rank → ℤ) := isRoot_single _ 1
  have r2 : IsRoot Tag.D4 (Pi.single 2 1 : Fin Tag.D4.rank → ℤ) := isRoot_single _ 2
  have r20 : IsRoot Tag.D4 (Pi.single 2 1 + Pi.single 0 1 : Fin Tag.D4.rank → ℤ) := by
    rw [isRoot_iff_mem_artifactRoots]
    decide +kernel
  have r21 : IsRoot Tag.D4 (Pi.single 2 1 + Pi.single 1 1 : Fin Tag.D4.rank → ℤ) := by
    rw [isRoot_iff_mem_artifactRoots]
    decide +kernel
  have r201 : IsRoot Tag.D4
      (Pi.single 2 1 + Pi.single 0 1 + Pi.single 1 1 : Fin Tag.D4.rank → ℤ) := by
    rw [isRoot_iff_mem_artifactRoots]
    decide +kernel
  have hs : ∀ j : Fin Tag.D4.rank, rootChar a (Pi.single j 1) = a j :=
    fun j => CFSG.RankThree.PartOne.KE.CTTorus.rootChar_single a j
  have hk : ∀ γ, IsRoot Tag.D4 γ → rootChar a γ = 1 → γ ∈ kernelRoots (rootCharHom a) := by
    intro γ h1 h2
    rw [kernelRoots_rootCharHom]
    exact ⟨h1, h2⟩
  by_cases h0 : a 0 = 1
  · exact ⟨_, hk _ r0 (by rw [hs, h0])⟩
  by_cases h1 : a 1 = 1
  · exact ⟨_, hk _ r1 (by rw [hs, h1])⟩
  by_cases h2 : a 2 = 1
  · exact ⟨_, hk _ r2 (by rw [hs, h2])⟩
  by_cases h20 : a 2 * a 0 = 1
  · exact ⟨_, hk _ r20 (by rw [rootChar_add, hs, hs, h20])⟩
  by_cases h21 : a 2 * a 1 = 1
  · exact ⟨_, hk _ r21 (by rw [rootChar_add, hs, hs, h21])⟩
  have e0 : a 2 = a 0 := eq_of_cube_roots (ha 2) (ha 0) h2 h0 h20
  have e1 : a 2 = a 1 := eq_of_cube_roots (ha 2) (ha 1) h2 h1 h21
  refine ⟨_, hk _ r201 ?_⟩
  rw [rootChar_add, rootChar_add, hs, hs, hs, ← e0, ← e1]
  calc a 2 * a 2 * a 2 = a 2 ^ 3 := by rw [pow_three, mul_assoc]
    _ = 1 := ha 2

theorem nonempty_kernelComponent_d4 {L : Type} [Field L] {a : Fin Tag.D4.rank → Lˣ}
    (ha : ∀ i, a i ^ 3 = 1) : Nonempty (KernelComponent (rootCharHom a)) := by
  obtain ⟨γ, hγ⟩ := exists_mem_kernelRoots_d4 ha
  exact ⟨(Quotient.mk _ ⟨γ, hγ⟩ : KernelComponent (rootCharHom a))⟩

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.TriInn

end
