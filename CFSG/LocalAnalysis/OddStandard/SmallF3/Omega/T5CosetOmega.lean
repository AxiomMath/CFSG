module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5SpinorInvol
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmegaConj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Det

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.ClassicalInvolution

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem t5_coset_omega (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hs : quadSign Q = -1) {s g : OGroup Q} (hss : s * s = 1) (hs3 : invDim s = 3)
    (hg2 : g * g = 1 ∨ g * g = piOrth Q) (hg : ∃ u ∈ omegaGroup hQ, g = u * s) :
    g * g = 1 ∧ ((invType g = invType s ∧ ∃ c ∈ omegaGroup hQ, c * s * c⁻¹ = g) ∨
      invDim g = 1 ∨ invDim g = 5) := by
  obtain ⟨u, hu, hgu⟩ := hg
  have hudet : QuadraticMap.orthogonalDet Q u = 1 := by
    have h := (mem_omegaGroup_iff hQ).mp hu
    rw [detSpinorNorm_apply hQ u] at h
    exact (Prod.ext_iff.mp h).1
  have hdetg : QuadraticMap.orthogonalDet Q g = -1 := by
    rw [hgu, map_mul (QuadraticMap.orthogonalDet Q) u s, hudet, one_mul,
      orthogonalDet_involution hss, hs3]
    decide
  have hgg : g * g = 1 := by
    rcases hg2 with h | h
    · exact h
    · exfalso
      have h1 : QuadraticMap.orthogonalDet Q g = 1 :=
        orthogonalDet_eq_one_of_mul_self_eq_piOrth (by rw [hdim]; decide) h
      rw [hdetg] at h1
      exact (by decide : (-1 : (ZMod 3)ˣ) ≠ 1) h1
  have hneg : (-1 : (ZMod 3)ˣ) ^ invDim g = -1 := by
    rw [← orthogonalDet_involution hgg, hdetg]
  have hodd : Odd (invDim g) := by
    rcases Nat.even_or_odd (invDim g) with he | ho
    · exfalso
      have h1 : (-1 : (ZMod 3)ˣ) ^ invDim g = 1 := he.neg_one_pow
      rw [hneg] at h1
      exact (by decide : (-1 : (ZMod 3)ˣ) ≠ 1) h1
    · exact ho
  have hle : invDim g ≤ 6 := by rw [← hdim]; exact invDim_le g
  have hcases : invDim g = 1 ∨ invDim g = 3 ∨ invDim g = 5 := by
    obtain ⟨k, hk⟩ := hodd
    omega
  refine ⟨hgg, ?_⟩
  rcases hcases with h1 | h3 | h5
  · exact Or.inr (Or.inl h1)
  · left
    have hd : detSpinorNorm hQ g = detSpinorNorm hQ s := by
      rw [hgu, map_mul (detSpinorNorm hQ) u s, (mem_omegaGroup_iff hQ).mp hu, one_mul]
    have hsign : invSign s = invSign g :=
      t5_invSign_eq_of_detSpinorNorm_eq hQ hss hgg hd.symm (by rw [hs3, h3])
    have htype : invType g = invType s := by
      simp only [invType]
      exact Prod.ext (by rw [h3, hs3]) hsign.symm
    obtain ⟨c, hc, hconj⟩ :=
      exists_mem_omegaGroup_conj hQ (by rw [hdim]; decide) hss hgg htype.symm
    exact ⟨htype, c, hc, hconj⟩
  · exact Or.inr (Or.inr h5)

end CFSG.OddStandard.SmallF3.Omega
