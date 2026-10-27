module

public import Certificates.Certificate24920
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.HypOnePrelude
public import CFSG.Sporadic.Schreier.RuOrbLFacts

public section

namespace CFSG.EvenSporadicStandard.RuStd

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.RuSchreier
open CFSG.EvenSporadicStandard.TwoRu.HypOne
open CFSG.Sporadic.Th (Rep)

theorem lGens_rep :
    ∀ l < lGens.size, Rep 4060 lGens[l]! (ruLGens.getD l 1) ∧
      Rep 4060 lGensInv[l]! (ruLGens.getD l 1)⁻¹ ∧ ruLGens.getD l 1 ∈ ruL := by
  intro l hl
  have hl3 : l < 3 := by simpa [lGens, ruLGensA_size] using hl
  refine ⟨?_, ?_, ?_⟩
  · rw [lGens, getElem!_map_tblOfArr (by rw [ruLGensA_size]; exact hl3)]
    exact rep_tblOfArr (rep_ruLGens l hl3)
  · rw [lGensInv, getElem!_map_tblOfArr (by simpa [ruLGensA_size] using hl3)]
    exact rep_tblOfArr (rep_ruLGensInv l hl3)
  · have := ruLGen_memL (l + 1)
    simpa [ruLGen] using this

theorem ruRepZ15_eq_commutator :
    ∃ g ∈ ruL, ∃ h ∈ ruL, g * h * g⁻¹ * h⁻¹ = ruRepZ 15 := by
  have hn : (4060 : ℕ) < 2 ^ 32 := by norm_num
  have hsz : lGens.size = 3 := by simp [lGens, ruLGensA_size]
  have hwg : ∀ z ∈ pairWordG, z ≠ 0 ∧ z.natAbs ≤ lGens.size := by rw [hsz]; decide
  have hwh : ∀ z ∈ pairWordH, z ≠ 0 ∧ z.natAbs ≤ lGens.size := by rw [hsz]; decide
  obtain ⟨g, hg, rg⟩ := rep_wordTables hn ruL lGens_rep hwg
  obtain ⟨h, hh, rh⟩ := rep_wordTables hn ruL lGens_rep hwh
  have hc := Certificates.certificate24920
  simp only [ruPairCheck, Bool.and_eq_true] at hc
  obtain ⟨⟨hgi, hhi⟩, heq⟩ := hc
  have r := Rep.compT (Rep.compT (Rep.compT rg rh) (Rep.inv_of_invOK rg hgi))
    (Rep.inv_of_invOK rh hhi)
  exact ⟨g, hg, h, hh, rep_unique r (rep_of_tblEq (rep_tblOfArr (rep_ruRepZ 15)) heq)⟩

end CFSG.EvenSporadicStandard.RuStd
