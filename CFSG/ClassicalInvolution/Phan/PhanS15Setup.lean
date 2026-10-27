module

import CFSG.ClassicalInvolution.Phan.PhanS9A3Move
import CFSG.ClassicalInvolution.Phan.PhanS9A2Rot
import CFSG.ClassicalInvolution.Phan.PhanS9B3Move
import CFSG.ClassicalInvolution.Phan.PhanS9WMain
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Phan.PhanS11Adj
public import CFSG.ClassicalInvolution.Phan.PhanS9O5Span
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open CFSG.LieType.Universal.Spin QuadraticMap CFSG.ClassicalInvolution.PhanB3.H
  CFSG.ClassicalInvolution.PhanB3 CFSG.ClassicalInvolution.Phan CFSG.LieType.BorelTits

section SetupExists

variable {p f : ℕ} [Fact p.Prime]

theorem two_ne_zero_of_algebra {F K : Type} [Field F] [Field K] [Algebra F K]
    (h2 : (2 : F) ≠ 0) : (2 : K) ≠ 0 := by
  intro h
  apply h2
  have h' : algebraMap F K 2 = 0 := by
    rw [map_ofNat]
    exact h
  exact (map_eq_zero (algebraMap F K)).1 h'

theorem exists_setup (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hmod : p ^ f % 4 = 3)
    {hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2} {h2 : (2 : GaloisField p f) ≠ 0}
    {C : B2Coord hK (GaloisField p f) h2} (M : ModelB3 p f h2)
    (E : PhanFamilyB3 C (spinGroup (quadOdd 3 (GaloisField p f))))
    [Algebra (GaloisField p f) (GaloisField p (2 * f))]
    (hgood : GoodFamily E) (hrange : ∀ i, (E.ι i).range = M.U i) :
    ∃ D : KDat (GaloisField p f) (GaloisField p (2 * f)), Nonempty (Setup M E D) := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hF : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [hF]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have hn1 : ¬ IsSquare (-1 : GaloisField p f) := not_isSquare_neg_one hmod
  have h2K : (2 : GaloisField p (2 * f)) ≠ 0 := two_ne_zero_of_algebra h2
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by
    rw [hF]
    omega
  obtain ⟨D⟩ := exists_kdat (F := GaloisField p f) (K := GaloisField p (2 * f)) p f hF hK hp2 hn1
  refine ⟨D, ⟨⟨hgood, h2K, h4, hrange, ?_, ?_, ?_, ?_, ?_, hodd, hn1⟩⟩⟩
  · exact ⟨La0_fix_vE3 D h2, La0_mem_l0 D h2, La0_rotSL0_vXi D h2, La0_rotSL0_vE2 D h2,
      exists_rotSL0_of_fix_vXi D h2, exists_rotSL0_of_mapsTo_P h2, exists_La0_move D h2⟩
  · exact ⟨La1_fix_vXi D h2, La1_mem_l23 D h2, La1_rotSL1_vE2 D h2, La1_rotSL1_vE3 D h2,
      exists_rotSL1_of_fix_vE2 D h2, exists_rotSL1_of_mapsTo_Pp h2, exists_La1_move D h2⟩
  · intro c
    rw [unitaryInvolution_apply, D.tau_pow, hF]
  · exact ⟨fun hodd' h2K' hn1' {R} hR hdim {x y} hx hy hxR hyR =>
      exists_spin_move_ff D hodd' h2K' hn1' hR hdim hx hy hxR hyR⟩
  · exact ⟨fun g hg => fixP_le_theta h2 hn1 M.D g hg, fun g hg => fixW0_le_U2 h2 hn1 M.D g hg⟩

end SetupExists

end CFSG.ClassicalInvolution.PhanB3.S
