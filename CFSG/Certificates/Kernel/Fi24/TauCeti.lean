module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Fischer.TwentyFour
public import CFSG.Certificates.Kernel.Fi24.Data.Fi24B

public section

namespace CFSG.KC.Fi24Top

open TauCeti TauCeti.Sporadic

@[expose] def lceEntry (w : List (ℕ × Bool)) : ℕ :=
  4 * w.length + 4096 * w.foldr (fun l acc => (2 * l.1 + if l.2 then 0 else 1) + 256 * acc) 0

theorem top_eq :
    fi24AutomorphismRelators.map (fun r => lceEntry (r.toWord.map fun l => (l.1.val, l.2))) =
      (List.range 80).map CFSG.KD.Fi24B.TOPT := by
  rw [fi24AutomorphismRelators_def, fi24AutomorphismAdditionalRelators_def, coxeterRelators_def,
    coxeterRelatorsOfList_def, fi24SourceEquationRelator_def, fi24SourceLongRelator_def,
    fi24SourceEquationWord_def, fi24SourceLongWord_def]
  simp only [List.map_append, List.map_map, List.map_cons, List.map_nil, Function.comp_def,
    toWord_coxeterRelator, fi24AutomorphismCoxeterMatrix_apply, fi24AutomorphismEdges_def,
    Relator.div, Relator.toWord_mul, Relator.toWord_inv, Relator.toWord_pow, Relator.toWord_gen]
  decide +kernel

end CFSG.KC.Fi24Top

end
