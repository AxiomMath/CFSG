module

import all Certificates.Data.Census
public import Certificates.Data.Kernel.GilmanCensus.Twin

public section

namespace Certificates.GilmanCensusK

open Certificates.Census

theorem growA_lt (adj : List Nat) (B : Nat) : ∀ (f left c front : Nat), left < 2 ^ B →
    c < 2 ^ B → (growA adj f left c front).1 < 2 ^ B ∧ (growA adj f left c front).2 < 2 ^ B
  | 0, _, _, _, hl, hc => ⟨hl, hc⟩
  | f + 1, left, c, front, hl, hc => by
    simp only [growA]
    split
    · exact ⟨hl, hc⟩
    · have hnb : nbA adj front 0 &&& left < 2 ^ B := Nat.and_lt_two_pow _ hl
      exact growA_lt adj B f _ _ _ (Nat.xor_lt_two_pow hl hnb) (Nat.or_lt_two_pow hc hnb)

theorem compsA_lt (adj : List Nat) (B : Nat) : ∀ (f left : Nat), left < 2 ^ B →
    ∀ c ∈ compsA adj f left, c < 2 ^ B
  | 0, _, _ => by simp [compsA]
  | f + 1, left, hl => by
    intro c hc
    simp only [compsA] at hc
    split at hc
    · simp at hc
    · have h0 : left ^^^ (left &&& (left - 1)) < 2 ^ B :=
        Nat.xor_lt_two_pow hl (Nat.and_lt_two_pow _ (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hl))
      have hg := growA_lt adj B 128 (left ^^^ (left ^^^ (left &&& (left - 1))))
        (left ^^^ (left &&& (left - 1))) (left ^^^ (left &&& (left - 1)))
        (Nat.xor_lt_two_pow hl h0) h0
      rcases List.mem_cons.mp hc with hc | hc
      · rw [hc]
        exact hg.2
      · exact compsA_lt adj B f _ hg.1 c hc

end Certificates.GilmanCensusK

end
