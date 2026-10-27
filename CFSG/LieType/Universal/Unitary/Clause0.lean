module

public import CFSG.LieType.Universal.Unitary.Model
public import CFSG.ClassicalGroups.Unitary.Simple

public section

namespace CFSG.LieType.Universal.Unitary

open CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p] {n : ℕ}

omit [CharP F p] in
theorem isQuasisimple_statedSU_of_card (hF : Nat.card F = (p ^ f) ^ 2) (hn : 3 ≤ n)
    (hnq : (n, p ^ f) ≠ (3, 2)) :
    IsQuasisimple (StatedSU n (p ^ f) F) ∧
      Subgroup.center (StatedSU n (p ^ f) F) =
        (StatedScalars (Fin n) F).subgroupOf (StatedSU n (p ^ f) F) :=
  isQuasisimple_statedSU (CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hF hn hnq)
    (CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F p f hF n hn hnq)

theorem isQuasisimple_SU (hF : Nat.card F = (p ^ f) ^ 2) (hn : 3 ≤ n)
    (hnq : (n, p ^ f) ≠ (3, 2)) : IsQuasisimple (SU (unitaryInvolution F p f) n) :=
  isQuasisimple_of_mulEquiv (equivStatedSU hF n).symm (isQuasisimple_statedSU_of_card hF hn hnq).1

theorem statedClassicalModel_center_quotient (hadm : StatedLieAdmissible .PSU n p f)
    (hF : Nat.card F = (p ^ f) ^ 2) :
    StatedClassicalModel
      (SU (unitaryInvolution F p f) n ⧸ Subgroup.center (SU (unitaryInvolution F p f) n))
      .PSU n p f :=
  ⟨hadm, F, inferInstance, inferInstance, hF,
    ⟨centerQuotientEquivStatedProj hF (isQuasisimple_statedSU_of_card hF hadm.2.2.1
      hadm.2.2.2).2⟩⟩

end CFSG.LieType.Universal.Unitary
