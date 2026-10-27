module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.ExcCommon
public import CFSG.HardMathSupport.Dickson.Sec6.I1431LieAux.Rank

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.KFacts
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.LieType.Ree
open CFSG.HardMathSupport.Dickson.Sec6.I923
open scoped commutatorElement

set_option linter.unusedSectionVars false

theorem excres_commutator_le_ker {G A : Type*} [Group G] [Group A] (Θ : G →* A)
    (hA : ∀ a b : A, a * b = b * a) : commutator G ≤ Θ.ker := by
  rw [commutator_def, Subgroup.commutator_le]
  intro a _ b _
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm.2 (hA _ _)]

section F4


theorem excres_innAutDerived_le_inner_F4 {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) {K : Type}
    [Field K] (hK : Nat.card K = p ^ f) :
    innAutDerived (adjointGroup Tag.F4 K) ≤ inner (adjointGroup Tag.F4 K) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hp.pos f).ne')
  refine sup_le le_rfl ?_
  by_cases h2 : p = 2
  · subst h2
    haveI : CharP K ReeTag.F4.prime :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
    obtain ⟨-, -, ⟨Θ, -, -, hker⟩, -⟩ := even_F4_exact_automorphism_normal_form hf K hK
    exact (excres_commutator_le_ker Θ fun a b => mul_comm a b).trans hker.le
  · obtain ⟨-, Θ, -, -, hker, -⟩ :=
      odd_F4_and_nonexceptional_G2_automorphism_normal_form hp h2 hf K hK .F4 (Or.inl rfl)
    exact (excres_commutator_le_ker Θ fun a b =>
      CFSG.LocalAnalysis.ComponentInitial.ringAut_mul_comm K a b).trans hker.le

theorem outDerived3_f4 : OutDerived3At FamF4 := by
  intro P _ _ t n p f hadm ht hF hm τ hτ hτ3
  obtain rfl := hF
  have hf : 1 ≤ f := hadm.2.1
  have hU : UntwistedChevalleyModel P .F4 (p ^ f) := by
    rcases hm with ⟨ht', -⟩ | ⟨-, -, hE⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
    · exact absurd ht' (by decide)
    · exact hE.2
    · exact absurd ht' (by decide)
    · exact absurd ht' (by decide)
  obtain ⟨F, hFf, hFin, hFcard, ⟨θ⟩⟩ := exists_equiv_adjointGroup_of_untwisted hU
  have h1 : MulAut.congr θ τ ∈ innAutDerived (adjointGroup Tag.F4 F) :=
    (mem_innAutDerived_congr θ).2 hτ
  exact (isInnerAut_congr θ τ).1 (excres_innAutDerived_le_inner_F4 hadm.1 hf hFcard h1)

end F4

end CFSG.HardMathSupport.Dickson.Sec6.I1431
