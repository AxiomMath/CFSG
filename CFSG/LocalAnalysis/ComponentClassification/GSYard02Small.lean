module

public import CFSG.LocalAnalysis.ComponentClassification.GSYard02Basic

public section

namespace CFSG.ComponentClassification.Sol76.Sig.GSYard02

open CFSG Subgroup

variable {Q : Type} [Group Q]

theorem sylowFourJoined_of_card_sylow_eq_eight [Finite Q] (S : Sylow 2 Q)
    (hS : Nat.card (S : Subgroup Q) = 8) (hr : 3 ≤ Open.twoRank Q) : SylowFourJoined Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, -, hE, hcard⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 2) (H := ⊤) (k := 3) hr
  obtain ⟨P, hEP⟩ := (IsPGroup.of_card hcard : IsPGroup 2 E).exists_le_sylow
  have hP : Nat.card (P : Subgroup Q) = 2 ^ Nat.factorization (Nat.card Q) 2 :=
    Sylow.card_eq_multiplicity P
  have hS' : Nat.card (S : Subgroup Q) = 2 ^ Nat.factorization (Nat.card Q) 2 :=
    Sylow.card_eq_multiplicity S
  have hPS : Nat.card (P : Subgroup Q) = 8 := hP.trans (hS'.symm.trans hS)
  have hEP' : E = P := Subgroup.eq_of_le_of_card_ge hEP (by rw [hPS, hcard]; norm_num)
  refine sylowFourJoined_of_normal_elemAbelian P (A := E) ?_ (fun a ha => ?_) ?_
  · rw [hEP']
    exact Subgroup.le_normalizer
  · rw [← sq]
    exact hE.2 a ha
  · rw [hcard]
    norm_num

end CFSG.ComponentClassification.Sol76.Sig.GSYard02
