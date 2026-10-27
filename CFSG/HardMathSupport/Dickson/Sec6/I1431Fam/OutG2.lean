module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.OutPsp
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.ExcCommon

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.KFacts
  CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.HardMathSupport.Dickson.Sec6.I923

section


section Core

variable {K : Type} [Field K] [Finite K]

theorem t6outg2_commutator_le_inner (hK3 : ringChar K ≠ 3) (hK4 : 4 ≤ Nat.card K) :
    commutator (MulAut (adjointGroup Tag.G2 K)) ≤ inner (adjointGroup Tag.G2 K) := by
  refine t6outpsp_commutator_le_of_eq_mul_comm _ (g2FieldHom K).range ?_ ?_
  · intro g
    obtain ⟨x, σ, rfl⟩ := (g2_automorphism_normal_form hK3 hK4).1 g
    exact ⟨_, ⟨x, rfl⟩, _, ⟨σ, rfl⟩, rfl⟩
  · rintro _ ⟨σ, rfl⟩ _ ⟨τ, rfl⟩
    rw [← map_mul, ← map_mul, CFSG.LocalAnalysis.ComponentInitial.ringAut_mul_comm K σ τ]

theorem t6outg2_innAutDerived_le_inner (hK3 : ringChar K ≠ 3) (hK4 : 4 ≤ Nat.card K) :
    innAutDerived (adjointGroup Tag.G2 K) ≤ inner (adjointGroup Tag.G2 K) :=
  sup_le le_rfl (t6outg2_commutator_le_inner hK3 hK4)

end Core

theorem outDerived3_g2Low : OutDerived3At FamG2Low := by
  intro P _ _ t n p f hadm ht hF hm τ hτ _
  obtain ⟨rfl, hp3⟩ := hF
  haveI : Fact p.Prime := ⟨hadm.1⟩
  have hf : 1 ≤ f := hadm.2.1
  have hU : UntwistedChevalleyModel P .G2 (p ^ f) := by
    rcases hm with ⟨ht', -⟩ | ⟨-, -, hE⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
    · exact absurd ht' (by decide)
    · exact hE.2
    · exact absurd ht' (by decide)
    · exact absurd ht' (by decide)
  obtain ⟨F, hFf, hFin, hFcard, ⟨θ⟩⟩ := exists_equiv_adjointGroup_of_untwisted hU
  have hchar : CharP F p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hadm.1 hf hFcard
  have hK3 : ringChar F ≠ 3 := by rw [ringChar.eq F p]; exact hp3
  have hK4 : 4 ≤ Nat.card F := by
    rw [hFcard]
    by_contra h
    have h3 : p ^ f = 3 := by have := hadm.2.2.2; omega
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hadm.1 Nat.prime_three).1
      (h3 ▸ dvd_pow_self p (by omega)))
  have h1 : MulAut.congr θ τ ∈ innAutDerived (adjointGroup Tag.G2 F) :=
    (mem_innAutDerived_congr θ).2 hτ
  exact (isInnerAut_congr θ τ).1 (t6outg2_innAutDerived_le_inner hK3 hK4 h1)

end

end CFSG.HardMathSupport.Dickson.Sec6.I1431
