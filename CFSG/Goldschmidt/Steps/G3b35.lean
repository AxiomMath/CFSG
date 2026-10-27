module

public import CFSG.Goldschmidt.StatementsG
public import CFSG.Goldschmidt.Steps.G3b35JR

public section

namespace CFSG.Goldschmidt

open CFSG.Open CFSG.Walter G3b

theorem G35
    : S_G35 := by
  intro G _ _ L A Y hLn hLq hII hA hA1
  obtain ⟨hAL, hAab, hA2, hAmax, -⟩ := sstar_typeII_facts hLq hII hA hA1
  have hZ : Odd (Nat.card (Subgroup.center L)) := hII.1
  refine ⟨fun hYA => ?_, fun a ha ha1 hNY ⟨r, hr, hr2, hYr⟩ => ?_⟩
  · have hYA' : Y ≤ Subgroup.centralizer (A : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hYA
    rcases hII.2 with ⟨p, f, hp, hpodd, hf, h5, h8, ⟨e⟩⟩ | hJR
    · exact G35_one_L2 hLq e hpodd hf h5 h8 hAL hAab hA2 hAmax hYA'
    · exact G35_one_JR hLq hZ hJR hAL hAab hA2 hAmax hA1 hYA'
  · rcases hII.2 with ⟨p, f, hp, hpodd, hf, h5, h8, ⟨e⟩⟩ | hJR
    · exact G35_two_L2 hLq hZ e hpodd hf h5 h8 hAL hAab hA2 hAmax ha ha1 hNY hr hr2 hYr
    · have hYC := G35_two_JR hLq hZ hJR hAL hA2 ha ha1 hNY hr hr2 hYr
      exact ⟨hYC.trans le_sup_right, 1, Y.one_mem, hYC.trans le_sup_right⟩

end CFSG.Goldschmidt
