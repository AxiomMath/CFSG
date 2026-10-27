module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431LieAux.Low
public import CFSG.RankThree.Chevalley.ExceptionalModelOrderThree

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.KFacts
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.Sec66T
open CFSG.Blueprint.Chevalley (TwistTag)
open CFSG.LieType.Chevalley (graphFixedRootGroup even_triality_exact_automorphism_normal_form
  odd_triality_exact_automorphism_normal_form)
open scoped commutatorElement

set_option linter.unusedSectionVars false

theorem t6outtrid4_commutator_le_ker {G A : Type*} [Group G] [Group A] (Θ : G →* A)
    (hA : ∀ a b : A, a * b = b * a) : commutator G ≤ Θ.ker := by
  rw [commutator_def, Subgroup.commutator_le]
  intro a _ b _
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm.2 (hA _ _)]

section Core


theorem t6outtrid4_commutator_le_range {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) :
    commutator (MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ≤
      (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range := by
  obtain ⟨Θ, hker, hcyc⟩ : ∃ Θ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →*
      (K ≃+* K), Θ.ker = (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range ∧ IsCyclic (K ≃+* K) := by
    by_cases h2 : p = 2
    · subst h2
      obtain ⟨-, -, ⟨Θ, -, -, hker, -⟩, hcyc, -⟩ :=
        even_triality_exact_automorphism_normal_form hf K hK σ hσ
      exact ⟨Θ, hker, hcyc⟩
    · obtain ⟨-, -, ⟨Θ, -, -, hker, -⟩, hcyc, -⟩ :=
        odd_triality_exact_automorphism_normal_form hp h2 hf K hK σ hσ
      exact ⟨Θ, hker, hcyc⟩
  rw [← hker]
  exact t6outtrid4_commutator_le_ker Θ fun a b => hcyc.isMulCommutative.is_comm.comm a b

theorem t6outtrid4_isInnerAut_of_mem_innAutDerived {P : Type} [Group P] {n p f : ℕ}
    (hm : LieModel P .trialityD4 n p f) {τ : MulAut P} (hτ : τ ∈ innAutDerived P) :
    IsInnerAut τ := by
  have hexc : ChevalleyExceptionalModel P .trialityD4 p f := by
    rcases hm with ⟨hcl, -⟩ | ⟨-, -, hexc⟩ | ⟨-, hree, -⟩ | ⟨-, h, -⟩
    · exact absurd hcl (by decide)
    · exact hexc
    · exact absurd hree (by decide)
    · exact absurd h (by decide)
  obtain ⟨hadm, hmod⟩ := hexc
  obtain ⟨K, _, _, σ₀, hK, hσ₀, ⟨e⟩⟩ :=
    CFSG.RankThree.Chevalley.exists_mulEquiv_graphFixedRootGroup_of_twisted_prime hadm.1 hadm.2.1
      hmod
  have hbij : Function.Bijective σ₀ := ⟨σ₀.injective, Finite.surjective_of_injective σ₀.injective⟩
  let σ : K ≃+* K := RingEquiv.ofBijective σ₀ hbij
  have hσ : ∀ c, σ c = c ^ (p ^ f) := hσ₀
  have hK3 : Nat.card K = (p ^ f) ^ 3 := hK
  let e' : graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≃* P := e
  have h1 : MulAut.congr e'.symm τ ∈
      innAutDerived (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    (mem_innAutDerived_congr e'.symm).2 hτ
  have h2 : MulAut.congr e'.symm τ ∈
      (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range :=
    sup_le le_rfl (t6outtrid4_commutator_le_range hadm.1 hadm.2.1 hK3 σ hσ) h1
  exact (isInnerAut_congr e'.symm τ).1 h2

end Core

section Final


theorem outDerived3_triD4Low : OutDerived3At FamTriD4Low := by
  intro P _ _ t n p f hadm ht hF hm τ hτ _
  obtain ⟨rfl, -⟩ := hF
  exact t6outtrid4_isInnerAut_of_mem_innAutDerived hm hτ

end Final

end CFSG.HardMathSupport.Dickson.Sec6.I1431
