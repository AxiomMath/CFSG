module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713SSmall
public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.GL83PartI.I713.Alternating

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713S

open CFSG.Open CFSG.Blueprint

@[expose] def FamilyLift (P : (S : Type) → [Group S] → Prop) : Prop :=
  ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) → P S →
    LiftClause S

theorem liftClause_of_catalog_of_families
    (hcl : ∀ (t : StatedLieTag) (n p f : ℕ),
      FamilyLift fun S _ => StatedClassicalModel S t n p f)
    (hexc : ∀ (t : StatedLieTag) (p f : ℕ), t ∈ chevalleyExceptionalTags →
      FamilyLift fun S _ => ChevalleyExceptionalModel S t p f)
    (hree : ∀ (t : StatedLieTag) (p f : ℕ), t ∈ reeTitsTags →
      FamilyLift fun S _ => ReeTitsModel S t p f)
    (hsuz : ∀ p f : ℕ, FamilyLift fun S _ => SuzukiModel S p f)
    (hsp : FamilyLift fun S _ => NativeSporadic.SporadicRep S)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hnonab : ∃ a b : S, a * b ≠ b * a)
    (hcat : Catalog S) : LiftClause S := by
  rcases hcat with ⟨p, -, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨t, n, p, f, hm⟩ | hx | hsp'
  · exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab (e.injective (by rw [map_mul, map_mul, mul_comm]))
  · haveI : IsSimpleGroup (alternatingGroup (Fin n)) := e.symm.isSimpleGroup
    have hnonab' : ∃ a b : alternatingGroup (Fin n), a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := hnonab
      exact ⟨e a, e b, fun h => hab (e.injective (by simpa only [map_mul] using h))⟩
    exact LiftClause.of_mulEquiv e
      (liftClause_of_card_outer_le_four hnonab' (GL83.I713.card_outer_alternating_le_four hn))
  · exact hcl t n p f S hnonab hm
  · rcases hx with ⟨t, p, f, ht, hm⟩ | ⟨t, p, f, ht, hm⟩ | ⟨p, f, hm⟩
    · exact hexc t p f ht S hnonab hm
    · exact hree t p f ht S hnonab hm
    · exact hsuz p f S hnonab hm
  · exact hsp S hnonab hsp'

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713S
