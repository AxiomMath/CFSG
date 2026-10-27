module

public import CFSG.LocalAnalysis.GL83PartI.I713.Alternating
public import CFSG.LocalAnalysis.GL83PartI.I713.SporadicAll

public section

namespace GL83.I713

open CFSG.Open CFSG.Blueprint

@[expose] def FamilyClause (P : (S : Type) → [Group S] → Prop) : Prop :=
  ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) → P S →
    OutClauseFor S

theorem outClauseFor_of_catalog_of_families
    (hcl : ∀ (t : StatedLieTag) (n p f : ℕ),
      FamilyClause fun S _ => StatedClassicalModel S t n p f)
    (hexc : ∀ (t : StatedLieTag) (p f : ℕ), t ∈ chevalleyExceptionalTags →
      FamilyClause fun S _ => ChevalleyExceptionalModel S t p f)
    (hree : ∀ (t : StatedLieTag) (p f : ℕ), t ∈ reeTitsTags →
      FamilyClause fun S _ => ReeTitsModel S t p f)
    (hsuz : ∀ p f : ℕ, FamilyClause fun S _ => SuzukiModel S p f)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hnonab : ∃ a b : S, a * b ≠ b * a)
    (hcat : Catalog S) : OutClauseFor S := by
  rcases hcat with ⟨p, -, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨t, n, p, f, hm⟩ | hx | hsp
  · exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab (e.injective (by rw [map_mul, map_mul, mul_comm]))
  · exact OutClauseFor.of_mulEquiv e (outClauseFor_alternating hn)
  · exact hcl t n p f S hnonab hm
  · rcases hx with ⟨t, p, f, ht, hm⟩ | ⟨t, p, f, ht, hm⟩ | ⟨p, f, hm⟩
    · exact hexc t p f ht S hnonab hm
    · exact hree t p f ht S hnonab hm
    · exact hsuz p f S hnonab hm
  · exact outClauseFor_sporadicRep hsp

end GL83.I713
