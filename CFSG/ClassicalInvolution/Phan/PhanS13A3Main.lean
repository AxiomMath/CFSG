module

public import CFSG.ClassicalInvolution.Phan.PhanS13A2Node
public import CFSG.ClassicalInvolution.Phan.PhanS11Adj
public import CFSG.ClassicalInvolution.Phan.PhanS13A1Alg

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open CFSG.LieType.Universal.Spin QuadraticMap CFSG.ClassicalInvolution.PhanB3.H
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.PhanB3
  CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlock)

section Main

variable {p f : ℕ} [Fact p.Prime]
  {hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2} {h2 : (2 : GaloisField p f) ≠ 0}
  {C : B2Coord hK (GaloisField p f) h2} {M : ModelB3 p f h2}
  {E : PhanFamilyB3 C (spinGroup (quadOdd 3 (GaloisField p f)))}
  [Algebra (GaloisField p f) (GaloisField p (2 * f))]
  {D : KDat (GaloisField p f) (GaloisField p (2 * f))}

theorem piDetOne_of_mem_R0 (S : Setup M E D) {g : spinGroup (quadOdd 3 (GaloisField p f))}
    (hg : g ∈ (E.ι 0).range) : PiDetOne D g := by
  obtain ⟨A, hA⟩ : spinAction (quadOdd 3 (GaloisField p f)) g ∈ (fr0 h2).La.range := by
    rw [← M.map_eq]
    exact ⟨g, S.mem_R0 hg, rfl⟩
  exact piDetOne_of_La0 D h2 A hA.symm

theorem piDetOne_of_mem_U1 (S : Setup M E D) {g : spinGroup (quadOdd 3 (GaloisField p f))}
    (hg : g ∈ (E.ι 1).range) : PiDetOne D g := by
  obtain ⟨hmap, -⟩ := U1_spec M.D S.h4
  have hmem : g ∈ (longBlock (GaloisField p f) 2 1).range.map M.D.θ := by
    have := hg
    rw [S.range 1] at this
    exact this
  obtain ⟨B, hB⟩ : spinAction (quadOdd 3 (GaloisField p f)) g ∈ (fr1 h2).La.range := by
    rw [← hmap]
    exact ⟨g, hmem, rfl⟩
  exact piDetOne_of_La1 D h2 B hB.symm

theorem piDetOne_of_mem_sup (S : Setup M E D) {g : spinGroup (quadOdd 3 (GaloisField p f))}
    (hg : g ∈ (E.ι 0).range ⊔ (E.ι 1).range) : PiDetOne D g := by
  have h : (E.ι 0).range ⊔ (E.ι 1).range ≤ piDetOneSubgroup D :=
    sup_le (fun u hu => (mem_piDetOneSubgroup D).2 (piDetOne_of_mem_R0 S hu))
      (fun u hu => (mem_piDetOneSubgroup D).2 (piDetOne_of_mem_U1 S hu))
  exact (mem_piDetOneSubgroup D).1 (h hg)

end Main

end CFSG.ClassicalInvolution.PhanB3.S
