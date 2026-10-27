module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74F4
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74QDefs

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74

open CFSG Subgroup QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
  CFSG.ClassicalInvolution.Models.OrthogonalPairs
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K]

theorem card_centralizer_le_two_mul (h2 : (2 : K) ≠ 0) (x : spinGroup (quadOdd 3 K)) :
    Nat.card (centralizer ({x} : Set (spinGroup (quadOdd 3 K)))) ≤
      2 * Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 K) ⊓
        centralizer {spinAction (quadOdd 3 K) x} : Subgroup (VEnd K)) := by
  have : Finite (spinGroup (quadOdd 3 K)) :=
    CFSG.LieType.Steinberg.finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadOdd h2)
  have := finite_VEnd (K := K)
  set C := centralizer ({x} : Set (spinGroup (quadOdd 3 K))) with hC
  let ψ : C →* VEnd K := (spinAction (quadOdd 3 K)).comp C.subtype
  have hker : Nat.card ψ.ker ≤ 2 := by
    have hle : ψ.ker.map C.subtype ≤ (spinAction (quadOdd 3 K)).ker := by
      rintro _ ⟨g, hg, rfl⟩
      exact hg
    have hk : (spinAction (quadOdd 3 K)).ker = zpowers (spinZ K) := by
      rw [← center_spinGroup_quadOdd_eq_ker h2 (le_refl 3), center_spinGroup_quadOdd h2 (le_refl 3)]
    rw [← card_map_of_injective C.subtype_injective]
    calc Nat.card (ψ.ker.map C.subtype) ≤ Nat.card (spinAction (quadOdd 3 K)).ker :=
          card_le_of_le hle
      _ = 2 := by rw [hk, Nat.card_zpowers, orderOf_spinZ h2]
  have hrange : ψ.range ≤ (TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 K) ⊓
      centralizer {spinAction (quadOdd 3 K) x} : Subgroup (VEnd K)) := by
    rintro _ ⟨g, rfl⟩
    refine mem_inf.mpr ⟨TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr
      (map_spinAction _ _), mem_centralizer_singleton_iff.mpr ?_⟩
    have hg := mem_centralizer_singleton_iff.mp g.2
    show spinAction (quadOdd 3 K) (g : spinGroup (quadOdd 3 K)) * spinAction (quadOdd 3 K) x =
      spinAction (quadOdd 3 K) x * spinAction (quadOdd 3 K) (g : spinGroup (quadOdd 3 K))
    rw [← map_mul, ← map_mul, hg]
  calc Nat.card C = Nat.card ψ.ker * Nat.card ψ.range := (card_ker_mul_card_range ψ).symm
    _ ≤ 2 * Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 K) ⊓
        centralizer {spinAction (quadOdd 3 K) x} : Subgroup (VEnd K)) :=
      Nat.mul_le_mul hker (card_le_of_le hrange)

theorem f4Odd_holds : F4Odd := by
  intro K _ _ hodd c d hc hd
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  have h := Nat.mul_le_mul_left 2 (card_cen_xTwo_le h2 hc hd)
  have he : 2 * (2 * Nat.card K ^ 7 * (Nat.card K ^ 2 - 1)) =
      4 * Nat.card K ^ 7 * (Nat.card K ^ 2 - 1) := by ring
  rw [he] at h
  refine (card_centralizer_le_two_mul h2 _).trans ?_
  rw [spinAction_xTwo]
  exact h

end CFSG.ComponentClassification.HarrisLit.T1.S74
