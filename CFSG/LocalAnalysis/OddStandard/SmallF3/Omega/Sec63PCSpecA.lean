module

public import Certificates.Data.Asc82FbarCheck
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.SmallOddCore.LocalSpec

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.ComponentClassification.HarrisLit.P1 Certificates.Asc82Fbar

variable {n : ℕ}

theorem tp_mem_genOf_of_memT {cap m : ℕ} (hn : n < 2 ^ 32) {gs : List Table}
    (hg : ∀ g ∈ gs, permOK n g = true) (henum : enumOK n cap m gs = true) {x : Table}
    (hx : permOK n x = true) (h : memT n (mulClosureH n gs.toArray cap).1 x = true) :
    tp n x ∈ genOf n gs := by
  obtain ⟨-, hrep, -, -⟩ := enumOK_spec hn hg henum
  obtain ⟨k, hk, hxk⟩ := memT_spec (fun k hk => (hrep k hk).1) (rep_tp hx) h
  rw [hxk]
  exact (hrep k hk).2

theorem allInvConj_spec {cap m : ℕ} (hn : n < 2 ^ 32) {gs : List Table}
    (hg : ∀ g ∈ gs, permOK n g = true) (henum : enumOK n cap m gs = true) {b : Table}
    {bp : Equiv.Perm (Fin n)} (hb : Rep n b bp)
    (h : allInvConj n (mulClosureH n gs.toArray cap).1 b = true) :
    ∀ x ∈ genOf n gs, orderOf x = 2 → ∃ l ∈ genOf n gs, x = l * bp * l⁻¹ := by
  obtain ⟨-, hrep, hcov, -⟩ := enumOK_spec hn hg henum
  intro x hx hx2
  obtain ⟨k, hk, hxk⟩ := hcov x hx
  have hinv : involOK n (mulClosureH n gs.toArray cap).1[k]! = true :=
    involOK_of_orderOf hn hxk hx2
  simp only [allInvConj, Array.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  have h1 := h k hk
  rw [← getElem!_pos (mulClosureH n gs.toArray cap).1 k hk] at h1
  rcases h1 with h1 | h1
  · rw [h1] at hinv
    exact absurd hinv (by decide)
  · rw [Array.any_eq_true] at h1
    obtain ⟨j, hj, hjeq⟩ := h1
    rw [← getElem!_pos (mulClosureH n gs.toArray cap).1 j hj] at hjeq
    refine ⟨tablePerm n (mulClosureH n gs.toArray cap).1[j]!, (hrep j hj).2, ?_⟩
    have h2 := (tblEq_iff_eq (Rep.compT hxk (hrep j hj).1) (Rep.compT (hrep j hj).1 hb)).1 hjeq
    rw [eq_mul_inv_iff_mul_eq]
    exact h2

end CFSG.OddStandard.SmallF3.Omega
