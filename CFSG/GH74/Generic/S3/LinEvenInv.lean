module

public import CFSG.GH74.KGroups.LinEvenAut
public import CFSG.GH74.Generic.S3.V1InnerLib

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GH74.KGroups.L3Eps (InvDataB4 invDataB4_of_equiv tInv tInv_mul_self tInv_ne_one exists_projectiveSL_equiv)

theorem exists_invDataB4_lin {K : Type} [Group K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h5 : 5 ≤ p ^ f) (hX : StatedClassicalModel K .PSL 3 p f) {w : K} (hw2 : w * w = 1) (hw1 : w ≠ 1) :
    ∃ S : Subgroup K, InvDataB4 (p ^ f) K w S := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_projectiveSL_equiv hX
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hodd : Odd (Nat.card F) := by rw [hF]; exact hpodd.pow
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  have h5' : 5 ≤ Nat.card F := by rw [hF]; exact h5
  have hex2 : e w * e w = 1 := by rw [← map_mul, hw2, map_one]
  have hex1 : e w ≠ 1 := fun h => hw1 (e.injective (h.trans (map_one e).symm))
  obtain ⟨g, hg⟩ := singleInv_projectiveSL h2 (e w) tInv hex2 hex1 tInv_mul_self (tInv_ne_one h2)
  let e' : K ≃* projectiveSL 3 F := e.trans (MulAut.conj g)
  have he' : e' w = tInv := by
    show MulAut.conj g (e w) = tInv
    rw [MulAut.conj_apply]
    exact hg
  exact ⟨_, invDataB4_of_equiv hF h2 (by omega) e' he'⟩

end CFSG.GH74.Generic.S3
