module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSubflag

public section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearFlag

open Matrix

variable {K : Type*} [Field K] {n : ℕ}

@[expose] def borelOvergroupCuts (A : Subgroup (SpecialLinearGroup (Fin n) K)) : Set ℕ :=
  {i | ∃ (hi : 1 ≤ i) (hin : i < n), reflection n K i hi hin ∉ A}

theorem exists_isReducedWord (w : Equiv.Perm (Fin n)) : ∃ l : List ℕ, IsReducedWord w l := by
  obtain ⟨l, hl, hlen, hprod⟩ := exists_word_length_eq w
  obtain ⟨l', hl', hlen', hprod'⟩ := Nat.sInf_mem (s := {k | ∃ l : List ℕ, IsAdjWord n l ∧
    l.length = k ∧ adjWordProd n l = w}) ⟨_, l, hl, rfl, hprod⟩
  exact ⟨l', hl', hprod', hlen'⟩

theorem borel_overgroups (A : Subgroup (SpecialLinearGroup (Fin n) K))
    (hA : upperTriangular n K ≤ A) :
    A = flagStabilizer n K (borelOvergroupCuts A) ∧
      ∀ I : Set ℕ, (∀ i ∈ I, 1 ≤ i ∧ i < n) → A = flagStabilizer n K I →
        I = borelOvergroupCuts A := by
  classical
  set I := borelOvergroupCuts A with hIdef
  have hgen := (subflag_stabilizer_generation (K := K) (n := n) I).1
  have hmem := (subflag_stabilizer_generation (K := K) (n := n) I).2.2
  refine ⟨le_antisymm (fun g hg => ?_) ?_, fun J hJ hAJ => ?_⟩
  ·
    obtain ⟨w, hw⟩ := (triangular_bruhat (K := K) (n := n)).1 g
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := mem_bruhatCell.mp hw
    have hwA : signedPermutation n K w ∈ A := by
      have := mul_mem (mul_mem (inv_mem (hA hb₁)) hg) (inv_mem (hA hb₂))
      convert this using 1
      group
    obtain ⟨l, hl⟩ := exists_isReducedWord w
    have hletters := reduced_word_extraction A l w hA
      (fun b hb => mul_mem (mul_mem hwA (hA hb)) (inv_mem hwA)) hl
    set ρ := (l.map (reflElt n K)).prod with hρ
    have hρmem : ρ ∈ flagStabilizer n K I := by
      rw [hρ]
      refine Subgroup.list_prod_mem _ fun x hx => ?_
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
      obtain ⟨hj1, hjn⟩ := hl.1 j hj
      rw [reflElt_of_lt hj1 hjn]
      refine (hmem j hj1 hjn).mpr fun hjI => ?_
      obtain ⟨_, _, hnot⟩ := hjI
      exact hnot (hletters j hj hj1 hjn)
    have hρmono := isMonomial_prod_reflElt (K := K) (n := n) l
    rw [hl.2.1] at hρmono
    obtain ⟨D, hD, hwD⟩ := IsMonomial.exists_diagonal (M := signedPermutation n K w)
      (M' := ρ) (isMonomial_signedPermMatrix w) hρmono
    have hBI := upperTriangular_le_flagStabilizer (K := K) (n := n) I
    rw [hwD]
    exact mul_mem (mul_mem (hBI hb₁) (mul_mem hρmem (hBI hD))) (hBI hb₂)
  ·
    rw [hgen, Subgroup.closure_le]
    rintro g (hg | ⟨j, hj, hjn, hjI, rfl⟩)
    · exact hA hg
    · by_contra hnot
      exact hjI ⟨hj, hjn, hnot⟩
  ·
    ext i
    have hmemJ := (subflag_stabilizer_generation (K := K) (n := n) J).2.2
    constructor
    · intro hi
      obtain ⟨hi1, hin⟩ := hJ i hi
      refine ⟨hi1, hin, fun hrA => ?_⟩
      rw [hAJ] at hrA
      exact (hmemJ i hi1 hin).mp hrA hi
    · rintro ⟨hi1, hin, hrA⟩
      by_contra hiJ
      apply hrA
      rw [hAJ]
      exact (hmemJ i hi1 hin).mpr hiJ

end LinearFlag

end CFSG.LocalAnalysis.ComponentInitial
