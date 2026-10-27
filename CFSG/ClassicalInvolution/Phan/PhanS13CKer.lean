module

public import CFSG.ClassicalInvolution.Phan.PhanS11Adj
import CFSG.ClassicalInvolution.Phan.PhanB21Exists

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open CFSG.LieType.Universal.Spin QuadraticMap CFSG.ClassicalInvolution.PhanB3.H
  CFSG.ClassicalInvolution.PhanB3
open CFSG.ClassicalInvolution.Asc77.B3C (twShort)
open scoped MatrixGroups

section Sq

variable {F : Type} [Field F]

theorem mul_self_eq_one_of_spinAction_eq_one (h2 : (2 : F) ≠ 0) {z : spinGroup (quadOdd 3 F)}
    (hz : spinAction (quadOdd 3 F) z = 1) : z * z = 1 := by
  rcases eq_one_or_eq_neg_one_of_spinAction_eq_one_odd 3 F h2 z hz with h | h
  · exact Subtype.ext (by simp [h])
  · exact Subtype.ext (by simp [h])

end Sq

section Ker

variable {p f : ℕ} [Fact p.Prime]
  {hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2} {h2 : (2 : GaloisField p f) ≠ 0}
  {C : B2Coord hK (GaloisField p f) h2} {M : ModelB3 p f h2}
  {E : PhanFamilyB3 C (spinGroup (quadOdd 3 (GaloisField p f)))}
  [Algebra (GaloisField p f) (GaloisField p (2 * f))]
  {D : KDat (GaloisField p f) (GaloisField p (2 * f))}

theorem mem_torusSub_of_spinAction_eq_one (S : Setup M E D)
    {z : spinGroup (quadOdd 3 (GaloisField p f))}
    (hz : spinAction (quadOdd 3 (GaloisField p f)) z = 1) : z ∈ torusSub E := by
  have h2F : (2 : GaloisField p f) ≠ 0 := h2
  have hzz : z * z = 1 := mul_self_eq_one_of_spinAction_eq_one h2F hz
  have hfix : ∀ x ∈ (fr0 h2).span, spinAction (quadOdd 3 (GaloisField p f)) z x = x := by
    intro x _
    rw [hz]
    rfl
  obtain ⟨y, ⟨A, hAy⟩, hA⟩ := S.ord.fixW0 z hfix
  have hs : sInv E 2 ∈ (twShort h2).range.map M.D.θ := by
    have := sInv_mem_range (E := E) 2
    rw [S.range 2] at this
    exact this
  obtain ⟨y', ⟨B, hBy⟩, hB⟩ := hs
  subst hAy hBy
  have hψ : Function.Injective (fun A : SL(2, GaloisField p f) => M.D.θ (twShort h2 A)) :=
    M.D.θ_inj.comp (twShort_injective h2)
  have hAA : A * A = 1 := by
    apply hψ
    simp only [map_mul, map_one]
    rw [hA, hzz]
  have hBB : B * B = 1 := by
    apply hψ
    simp only [map_mul, map_one]
    rw [hB, sInv_mul_self]
  rcases SL2_eq_one_or_neg_one_of_mul_self h2F A hAA with hA1 | hA1
  · rw [← hA, hA1, map_one, map_one]
    exact one_mem _
  · rcases SL2_eq_one_or_neg_one_of_mul_self h2F B hBB with hB1 | hB1
    · exact absurd (by rw [← hB, hB1, map_one, map_one]) (sInv_ne_one S.good S.h2K 2)
    · have : z = sInv E 2 := by rw [← hA, hA1, ← hB, hB1]
      rw [this]
      exact sInv_mem_torusSub 2

end Ker

end CFSG.ClassicalInvolution.PhanB3.S
