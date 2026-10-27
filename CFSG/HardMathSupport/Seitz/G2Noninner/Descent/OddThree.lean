module

public import CFSG.HardMathSupport.Seitz.G2Noninner.Descent.Standard
import CFSG.RankThree.SteinbergBRThreeG2Noninner

public section

namespace CFSG.HardMathSupport.Seitz.G2Noninner

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Ree CFSG.RankThree.Chevalley CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartOne.SEITZ2

section Main


theorem fieldAutData_G2_three_at {f p : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 3 ^ f) (hp : p.Prime) (hpair : SubfieldPairG2At K) (hp5 : 5 ≤ p) :
    FieldAutData (adjointGroup .G2 K) p := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hchar : CharP K 3 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_three
      hf hK
  have : CharP K ReeTag.G2.prime := hchar
  have : NeZero (2 * f) := ⟨by omega⟩
  obtain ⟨-, hNF, ⟨Θ, -, -, hker⟩, -⟩ := G2_three_exact_automorphism_normal_form hf K hK
  have : Finite (Multiplicative (ZMod (2 * f))) := inferInstance
  have : IsCyclic (Multiplicative (ZMod (2 * f))) := inferInstance
  let Θ' : MulAut (adjointGroup .G2 K) →* Multiplicative (ZMod (2 * f)) := Θ
  have hker' : Θ'.ker = (MulAut.conj : adjointGroup .G2 K →* MulAut _).range := hker
  refine fieldAutData_G2_of_descent Nat.prime_three hf hK hp hpair hp5 ?_ ?_
  · intro E hE hEc
    exact exists_conj_mem_of_plane_of_hom hp Θ' hker' E hEc
  · intro α hα
    obtain ⟨hord, hout⟩ := hα
    let α' : MulAut (adjointGroup ReeTag.G2.tag K) := α
    have hord' : orderOf α' = p := hord
    have hout' : ∀ g : adjointGroup ReeTag.G2.tag K, α' ≠ MulAut.conj g := hout
    obtain ⟨⟨x, a⟩, hxa, -⟩ := hNF α'
    obtain ⟨-, -, ⟨σ, -, hσp, hσeq, -⟩, ⟨h, hh⟩, -⟩ :=
      CFSG.RankThree.three_G2_noninner_odd_prime_local_core_trivial hf hK hp (by omega) ⊤ le_top
        (⟨α', Subgroup.mem_top _⟩ : (⊤ : Subgroup (MulAut (adjointGroup ReeTag.G2.tag K))))
        (fun ⟨g, hg⟩ => hout' g hg.symm)
        (by rw [Subgroup.orderOf_mk]; exact hord') x a a.2 hxa
    have hfin : MulAut.conj h * α' * (MulAut.conj h)⁻¹ =
        entrywiseAdjointAut ReeTag.G2.tag σ := hh.trans hσeq
    exact ⟨h, σ, hσp, hfin⟩

theorem fieldAutData_G2_three (hpair : SubfieldPairG2Odd) {f p : ℕ} (hf : 1 ≤ f) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = 3 ^ f) (hp : p.Prime) (hp5 : 5 ≤ p) :
    FieldAutData (adjointGroup .G2 K) p :=
  fieldAutData_G2_three_at hf hK hp
    (hpair.at (by rw [ringChar_eq_of_card_pow Nat.prime_three hf hK]; norm_num)) hp5

end Main

end CFSG.HardMathSupport.Seitz.G2Noninner
