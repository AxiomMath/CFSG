module

public import CFSG.Certificates.Kernel.Orders.Fi24p.Rels
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Fischer.TwentyFour

public section

namespace CFSG.KD.OrdFi24p

open TauCeti TauCeti.Sporadic

@[expose] def schreierLetters : Bool → List (Fin 12 × Bool) → List (ℕ × Bool)
  | _, [] => []
  | pos, (i, _) :: w =>
      if i.val = 0 then schreierLetters (!pos) w else (i.val - 1, pos) :: schreierLetters (!pos) w

theorem schreierLetters_eq (pos : Bool) (w : List (Fin 12 × Bool)) :
    ((fi24SchreierFactors pos w).foldr Relator.mul ((Relator.gen 0).pow 0)).toWord.map
      (fun l => (l.1.val, l.2)) = schreierLetters pos w := by
  induction w generalizing pos with
  | nil => simp [schreierLetters]
  | cons l w ih =>
    obtain ⟨i, s⟩ := l
    rw [fi24SchreierFactors_cons]
    by_cases h : i.val = 0
    · simp [h, schreierLetters, ih]
    · cases pos <;> simp [h, schreierLetters, ih, FreeGroup.invRev]

theorem relatorLetters_eq_flatMap : fi24PrimePresentation.relatorLetters =
    ((fi24SourcePairRelators ++ fi24AutomorphismAdditionalRelators).map Relator.toWord).flatMap
      fun w => [schreierLetters false w, schreierLetters true w] := by
  rw [fi24PrimePresentation_relatorLetters, fi24PrimeRelators_def]
  simp only [fi24SchreierRewrite_def]
  induction (fi24SourcePairRelators ++ fi24AutomorphismAdditionalRelators) with
  | nil => rfl
  | cons r l ih =>
    simp only [List.flatMap_cons, List.map_append, List.map_cons, List.map_nil, schreierLetters_eq, ih]

theorem rels_eq : fi24PrimePresentation.relatorLetters = rels := by
  rw [relatorLetters_eq_flatMap, fi24SourcePairRelators_def, fi24AutomorphismAdditionalRelators_def,
    fi24SourceEquationRelator_def, fi24SourceLongRelator_def, fi24SourceEquationWord_def,
    fi24SourceLongWord_def]
  simp only [List.map_append, List.map_map, List.map_cons, List.map_nil, Function.comp_def,
    toWord_coxeterRelator, fi24AutomorphismCoxeterMatrix_apply, fi24AutomorphismEdges_def, Relator.div,
    Relator.toWord_mul, Relator.toWord_inv, Relator.toWord_pow, Relator.toWord_gen]
  decide +kernel

end CFSG.KD.OrdFi24p

end
