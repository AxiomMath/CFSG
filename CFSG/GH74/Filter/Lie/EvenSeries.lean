module

public import CFSG.GH74.Filter.Statements
public import Certificates.Certificate3953
public import CFSG.LocalAnalysis.SectionRank.Exceptional

public section

namespace CFSG.GH74.Filter.Lie

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.SectionRank

theorem witnessF4five_check : witnessF4five.check = true :=
  Certificates.certificate3953.1

theorem witnessE6five_check : witnessE6five.check = true :=
  Certificates.certificate3953.2.1

theorem witnessE7five_check : witnessE7five.check = true :=
  Certificates.certificate3953.2.2.1

theorem witnessE8five_check : witnessE8five.check = true :=
  Certificates.certificate3953.2.2.2

theorem not_gen4_of_untwistedModel_even
    {G : Type} [Group G] [Finite G] {τ : Tag} {f : ℕ}
    (W : SepWitness τ 5) (hW : W.check = true) (h : UntwistedChevalleyModel G τ (2 ^ f)) :
    ¬ Gen4 G := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_natCard_eq_pow hK
  exact not_gen4_of_mulEquiv e.symm (not_gen4_of_mulEquiv (adjointQuotientEquiv τ K).symm
    (SepWitness.not_gen4_adjointGroup hW le_rfl))

end CFSG.GH74.Filter.Lie

namespace CFSG.GH74.Filter

open CFSG.GH74.Filter.Lie
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.SectionRank

theorem t_F4_even :
    S_F4_even := fun _ _ _ _ h =>
  not_gen4_of_untwistedModel_even witnessF4five witnessF4five_check h.2

theorem t_E6_even :
    S_E6_even := fun _ _ _ _ h =>
  not_gen4_of_untwistedModel_even witnessE6five witnessE6five_check h.2

theorem t_E7_even :
    S_E7_even := fun _ _ _ _ h =>
  not_gen4_of_untwistedModel_even witnessE7five witnessE7five_check h.2

theorem t_E8_even :
    S_E8_even := fun _ _ _ _ h =>
  not_gen4_of_untwistedModel_even witnessE8five witnessE8five_check h.2

end CFSG.GH74.Filter
