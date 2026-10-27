module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14BlModelLevi
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2Torus
public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabG101Def

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.Quasithin (perfectCore le_perfectCore_of_perfect)
open CFSG.LieType.Steinberg.Sp (blockMat)

variable {K : Type} [Field K]

theorem closure_odd_eq_top_of_isSimpleGroup {M : Type*} [Group M] [IsSimpleGroup M] {y₀ : M}
    (hy₀ : y₀ ≠ 1) (hodd : Odd (orderOf y₀)) :
    closure {y : M | Odd (orderOf y)} = ⊤ := by
  have hconj : Group.conjugatesOfSet {y : M | Odd (orderOf y)} ⊆ {y : M | Odd (orderOf y)} := by
    intro x hx
    obtain ⟨a, ha, c, hc⟩ := Group.mem_conjugatesOfSet_iff.1 hx
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rwa [← hc.orderOf_eq]
  have hN : normalClosure {y : M | Odd (orderOf y)} = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (normalClosure {y : M | Odd (orderOf y)})
      with h | h
    · exfalso
      have h0 := subset_normalClosure (show y₀ ∈ {y : M | Odd (orderOf y)} from hodd)
      rw [h] at h0
      exact hy₀ ((Subgroup.mem_bot).1 h0)
    · exact h
  rw [eq_top_iff, ← hN]
  exact closure_mono hconj

section Transport

theorem spARep_one_eq_twoCentralElt {N : ℕ} (hN : 2 ≤ N) :
    (spARep N 1 : StatedSp N K) = twoCentralElt N ⟨0, by omega⟩ ⟨1, by omega⟩ 0 1 := by
  have hmat : (spARepMat N 1 : Matrix (Fin N) (Fin N) K) =
      twoCentralMat (⟨0, by omega⟩ : Fin N) ⟨1, by omega⟩ 0 1 := by
    ext m l
    rw [spARepMat_apply (by omega), twoCentralMat_apply]
    have hp0 : spAPar (⟨0, by omega⟩ : Fin N) = ⟨1, by omega⟩ :=
      Fin.ext (by rw [spAPar_val (j := 1) (by omega) (by simp)]; simp)
    have hp1 : spAPar (⟨1, by omega⟩ : Fin N) = ⟨0, by omega⟩ :=
      Fin.ext (by rw [spAPar_val (j := 1) (by omega) (by simp)]; simp)
    by_cases hl0 : l = ⟨0, by omega⟩
    · subst hl0
      rw [hp0]
      by_cases hm1 : m = ⟨1, by omega⟩
      · subst hm1
        simp [Fin.ext_iff]
      · have hm1' : (⟨1, by omega⟩ : Fin N) ≠ m := fun h => hm1 h.symm
        simp [hm1, hm1', Fin.ext_iff]
    · by_cases hl1 : l = ⟨1, by omega⟩
      · subst hl1
        rw [hp1]
        by_cases hm0 : m = ⟨0, by omega⟩
        · subst hm0
          simp [Fin.ext_iff]
        · have hm0' : (⟨0, by omega⟩ : Fin N) ≠ m := fun h => hm0 h.symm
          simp [hm0, hm0', Fin.ext_iff]
      · have hl : ¬ l.val < 2 * 1 := by
          intro h
          rcases Nat.lt_succ_iff_lt_or_eq.1 (show l.val < 1 + 1 by omega) with h' | h'
          · exact hl0 (Fin.ext (by simp at h' ⊢; omega))
          · exact hl1 (Fin.ext (by simpa using h'))
        have hl0' : (⟨0, by omega⟩ : Fin N) ≠ l := fun h => hl0 h.symm
        have hl1' : (⟨1, by omega⟩ : Fin N) ≠ l := fun h => hl1 h.symm
        simp [hl, hl0', hl1']
  rw [spARep, twoCentralElt]
  congr 1

variable [Finite K] [CharP K 2]

end Transport

section Final

variable [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem not_commute_nsElt_spARep_one {N : ℕ} (hN : 2 ≤ N) :
    nsElt (K := K) (⟨0, by omega⟩ : Fin N) * spARep N 1 ≠
      spARep N 1 * nsElt (⟨0, by omega⟩ : Fin N) := by
  intro h
  have e := congrFun (congrFun (congrArg (mat N K) h) (Sum.inr ⟨0, by omega⟩))
    (Sum.inr ⟨1, by omega⟩)
  rw [map_mul, map_mul, mat_spARep_eq, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.add_apply, Matrix.add_apply, add_right_inj] at e
  have h1 : (mat N K (nsElt (⟨0, by omega⟩ : Fin N)) * spANil K N 1) (Sum.inr ⟨0, by omega⟩)
      (Sum.inr ⟨1, by omega⟩) = -1 := by
    rw [Matrix.mul_apply, Fintype.sum_sum_type, Finset.sum_eq_single ⟨0, by omega⟩]
    · simp [mat_nsElt, blockMat, zThreeMat, spANil, spARepMat]
    · intro b _ hb
      have hb' :
          mat N K (nsElt (⟨0, by omega⟩ : Fin N)) (Sum.inr ⟨0, by omega⟩) (Sum.inl b) = 0 := by
        simp [mat_nsElt, blockMat, hb]
      rw [hb', zero_mul]
    · simp
  have h2 : (spANil K N 1 * mat N K (nsElt (⟨0, by omega⟩ : Fin N))) (Sum.inr ⟨0, by omega⟩)
      (Sum.inr ⟨1, by omega⟩) = 0 := by
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun t _ => by rcases t with t | t <;> simp [spANil]
  rw [h1, h2] at e
  exact one_ne_zero (neg_eq_zero.1 e)

end Final

end CFSG.SeitzReduction.SymplecticPilot
