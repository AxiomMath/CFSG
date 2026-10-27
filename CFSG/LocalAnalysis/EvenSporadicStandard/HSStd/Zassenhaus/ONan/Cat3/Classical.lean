module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.Cat3.OrdersCl
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.Cat3.PSL2
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.Cat3.Pi3
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.Cat3.Blocks
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.Cat3.SmallTwo
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.Cat3.Unitary
public import CFSG.ClassicalGroups.Orthogonal.Simple
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Chevalley.RootCommutator
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Exceptional.E6E7
public import CFSG.LieType.Steinberg.Families
public import CFSG.LieType.Steinberg.G2
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.Open.PGLModelStated
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Th.F2Spec
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan.Cat3

open Subgroup CFSG.Blueprint CFSG.Open

theorem classical_cases {L : Type} [Group L] [Finite L] (h : Milestones.ClassicalRep L)
    (h3 : (Nat.card L).factorization 3 = 2) (hC : CentHyp L) : LieModel L .PSp 2 2 2 := by
  obtain ⟨t, n, p, f, hM⟩ := h
  rcases classical_config hM h3 with ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, rfl, hp3⟩
  ·
    obtain ⟨hadm, K, hK, hKf, hcard, ⟨e⟩⟩ := hM
    rcases hn with rfl | rfl | ⟨hn45, hp3, hmod⟩
    · exact (false_of_psl_two (CentHyp.of_mulEquiv e.symm hC)).elim
    · exact (false_of_psl_three (CentHyp.of_mulEquiv e.symm hC)).elim
    · have hp : p.Prime := hadm.1
      have hf : 1 ≤ f := hadm.2.1
      have hchar : ringChar K = p :=
        CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hp hf hcard
      have hchar3 : ringChar K ≠ 3 := by rw [hchar]; exact hp3
      have hC' : CentHyp (StatedProj (StatedSL n K)) := CentHyp.of_mulEquiv e.symm hC
      rcases hn45 with hn4 | hn5
      · subst n
        rcases card_eq_two_or_four_of_psl_four hchar3 hC' with h2 | h4
        · exact (false_of_psl_four_card_two h2 hC').elim
        · exfalso
          have hpf : p ^ f = 4 := hcard.symm.trans h4
          rw [hpf] at hmod
          norm_num at hmod
      · subst n
        rcases card_eq_two_or_four_of_psl_five hchar3 hC' with h2 | h4
        · exact (false_of_psl_five_card_two h2 hC').elim
        · exfalso
          have hpf : p ^ f = 4 := hcard.symm.trans h4
          rw [hpf] at hmod
          norm_num at hmod
  ·
    obtain ⟨hadm, K, hK, hKf, hcard, ⟨e⟩⟩ := hM
    rcases hn with rfl | ⟨hn45, hp3, hmod⟩
    · have hp : p.Prime := hadm.1
      exact (false_of_psu_three (K := K) (q := p ^ f) (Nat.one_le_pow _ _ hp.pos)
        (CentHyp.of_mulEquiv e.symm hC)).elim
    · have hC' : CentHyp (StatedProj (StatedSU n (p ^ f) K)) :=
        CentHyp.of_mulEquiv e.symm hC
      rcases hn45 with hn4 | hn5
      · subst n
        exact (false_of_psu_four (q := p ^ f) hcard hmod hC').elim
      · subst n
        exact (false_of_psu_five (q := p ^ f) hcard hmod hC').elim
  ·
    obtain ⟨hadm, K, hK, hKf, hcard, ⟨e⟩⟩ := hM
    have hp : p.Prime := hadm.1
    have hf : 1 ≤ f := hadm.2.1
    have hchar : ringChar K = p :=
      CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hp hf hcard
    have hchar3 : ringChar K ≠ 3 := by rw [hchar]; exact hp3
    have hC' : CentHyp (StatedProj (StatedSp 2 K)) := CentHyp.of_mulEquiv e.symm hC
    rcases card_eq_two_or_four_of_psp_four hchar3 hC' with h2 | h4
    · exfalso
      have hpf : p ^ f = 2 := hcard.symm.trans h2
      exact hadm.2.2.2 (by rw [hpf])
    · have hpf : p ^ f = 4 := hcard.symm.trans h4
      have hp2 : p = 2 := by
        apply Nat.prime_eq_prime_of_dvd_pow hp Nat.prime_two (m := 2)
        have h : p ∣ p ^ f := dvd_pow_self p (by omega)
        rw [hpf] at h
        simpa using h
      obtain rfl : p = 2 := hp2
      have hf2 : f = 2 := by
        have h : 2 ^ f = 2 ^ 2 := by norm_num at hpf ⊢; exact hpf
        exact Nat.pow_right_injective (by norm_num) h
      obtain rfl : f = 2 := hf2
      refine Or.inl ⟨by decide, ?_⟩
      exact ⟨hadm, K, hK, hKf, hcard, ⟨e⟩⟩

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan.Cat3
