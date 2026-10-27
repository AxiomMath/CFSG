module

public import CFSG.Open.LocalVocabulary

public section

open CFSG.Open

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse

theorem elementary_prime_cyclic {Ambient : Type groupUniverse} [Group Ambient] {prime : ℕ}
    (hprime : prime.Prime) (element : Ambient) (horder : orderOf element = prime) :
    IsElemAbelian prime (Subgroup.zpowers element) := by
  let : Fact prime.Prime := ⟨hprime⟩
  have hcard : Nat.card (Subgroup.zpowers element) = prime := (Nat.card_zpowers element).trans horder
  let : IsCyclic (Subgroup.zpowers element) := inferInstance
  constructor
  · infer_instance
  · intro member hmember
    have hpower : (⟨member, hmember⟩ : Subgroup.zpowers element) ^ prime = 1 :=
      hcard ▸ pow_card_eq_one'
    exact congrArg (fun entry : Subgroup.zpowers element => entry.val) hpower

end CFSG.LargeEvenClassification.Helpers
