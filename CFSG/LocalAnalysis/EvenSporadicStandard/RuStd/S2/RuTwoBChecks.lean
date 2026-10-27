module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.FactsB1Comm
public import Certificates.Certificate24942

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.RuSchreier
open CFSG.Sporadic.Schreier CFSG.EvenSporadicStandard.TwoRu.HypOne
open CFSG.Sporadic.Th (Rep)

theorem ruTwoB_exists :
    (∃ g ∈ ruL, ∃ h ∈ ruL, orderOf (g * h * g⁻¹ * h⁻¹) = 5) ∧
      ∃ u ∈ ruL, orderOf u = 2 ∧ u ≠ ruA0 ∧
        ruL ≤ Subgroup.centralizer ({u} : Set (Equiv.Perm (Fin 4060))) := by
  have hn : (4060 : ℕ) < 2 ^ 32 := by norm_num
  have hsz : lGens.size = 3 := by simp [lGens, ruLGensA_size]
  have hwg : ∀ z ∈ twoBWordG, z ≠ 0 ∧ z.natAbs ≤ lGens.size := by rw [hsz]; decide
  have hwh : ∀ z ∈ twoBWordH, z ≠ 0 ∧ z.natAbs ≤ lGens.size := by rw [hsz]; decide
  have hwu : ∀ z ∈ twoBWordU, z ≠ 0 ∧ z.natAbs ≤ lGens.size := by rw [hsz]; decide
  obtain ⟨g, hg, rg⟩ := rep_wordTables hn ruL lGens_rep hwg
  obtain ⟨h, hh, rh⟩ := rep_wordTables hn ruL lGens_rep hwh
  obtain ⟨u, hu, ru⟩ := rep_wordTables hn ruL lGens_rep hwu
  have hc := Certificates.certificate24942
  simp only [ruTwoBCheck, Bool.and_eq_true, Bool.not_eq_true'] at hc
  obtain ⟨⟨⟨⟨⟨hgi, hhi⟩, hc5⟩, hu2⟩, hune⟩, hcomm⟩ := hc
  refine ⟨⟨g, hg, h, hh, ?_⟩, u, hu, ?_, ?_, ?_⟩
  · have rc : Rep 4060 twoBComm (g * h * g⁻¹ * h⁻¹) :=
      Rep.compT (Rep.compT (Rep.compT rg rh) (Rep.inv_of_invOK rg hgi))
        (Rep.inv_of_invOK rh hhi)
    exact (ordTest_iff perm_faithful rc (by norm_num)).1 hc5
  · exact (ordTest_iff perm_faithful ru (by norm_num)).1 hu2
  · intro heq
    have h0 : Rep 4060 (tblOfArr ruA0A) ruA0 := rep_tblOfArr rep_ruA0
    have ru' : Rep 4060 (twoBTab twoBWordU) u := ru
    have : tblEq 4060 (twoBTab twoBWordU) (tblOfArr ruA0A) = true := by
      rw [tblEq_iff]
      intro i hi
      rw [ru' i hi, h0 i hi, heq]
    rw [hune] at this
    exact Bool.false_ne_true this
  · have hk : ∀ k < lGens.size, u * ruLGens.getD k 1 = ruLGens.getD k 1 * u := by
      intro k hk
      have h1 : commT 4060 (twoBTab twoBWordU) lGens[k]! = true :=
        CFSG.Monster.B.Co2.allLt_spec hcomm hk
      exact (commT_iff ru (lGens_rep k hk).1).1 h1
    rw [ruL, Subgroup.closure_le]
    intro l hl
    simp only [Set.mem_ofPred_eq] at hl
    rw [ruLGens_eq] at hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    rcases hl with rfl | rfl | rfl
    · exact (hk 0 (by rw [hsz]; decide)).symm
    · exact (hk 1 (by rw [hsz]; decide)).symm
    · exact (hk 2 (by rw [hsz]; decide)).symm

end CFSG.EvenSporadicStandard.RuStd.S2
