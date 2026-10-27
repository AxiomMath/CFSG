module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTFinFour
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTFinCk
public import CFSG.Sporadic.Schreier.MathieuOddCoreM23
public import Certificates.Certificate55103

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Mathieu FinGlue FinFour
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

namespace FinM23

noncomputable def conjEquiv {G : Type} [Group G] [Finite G] (hc : center G = ⊥)
    (h : Nat.card (MulAut G) ≤ Nat.card G) : G ≃* MulAut G :=
  MulEquiv.ofBijective MulAut.conj ⟨conj_injective_of_center' hc, fun α => by
    have hα : α ∈ inner G := by
      rw [inner_eq_top_of_card_le hc h]
      exact mem_top α
    obtain ⟨g, hg⟩ := hα
    exact ⟨g, hg⟩⟩


theorem noFourPerfIn_m23 : NoFourPerfIn NativeSporadic.M23 := by
  have hn : (23 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m23Certificate := m23Certificate_check
  obtain ⟨hok, hsz, -⟩ := m23_oddcore_cover
  obtain ⟨hr1, hro1, hK1, hKc1, -⟩ := m23_rep_data1
  have hA : m23PermA ∈ m23Certificate.originalSubgroup := m23_gens_mem _ (by simp)
  have hB : m23PermB ∈ m23Certificate.originalSubgroup := m23_gens_mem _ (by simp)
  rw [m23InvReps_eq] at hok hsz
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  obtain ⟨hcov, hsize⟩ := exists_conj_of_repsOK hn m23Certificate hQ (pairTables_spec hn hA hB)
    1 (fun h hh => by simpa using hh) (m := 2) (by norm_num) [m23Rep1]
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact ⟨by simpa using hr1, hro1⟩) 4000 hok
  have hC : centralizerIn m23Certificate.originalSubgroup m23Rep1 =
      m23CentQ1.originalSubgroup := by
    refine centralizerIn_eq_of_le _ _ hK1 (c := 3795) ?_ ?_
    · rw [← hsz]
      exact hsize m23Rep1 (by simp)
    · rw [hKc1, m23Certificate_originalSubgroup, m23_card]
  rw [← m23Certificate_originalSubgroup]
  refine noFourPerfIn_of_reps (c := 1) (fun x hx => Or.inl hx) (mul_one 1)
    (fun x hx => by simpa using hx) [m23Rep1] Nat.prime_two Nat.prime_three (by norm_num)
    (a := 30) (b := 30) ?_ ?_
  · intro t ht htt ht1
    obtain ⟨r, hr, g, hg, rfl⟩ := hcov t (by simpa using ht)
      (orderOf_eq_prime (by rw [pow_two]; exact htt) ht1)
    exact ⟨r, hr, g, hg, rfl⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    have hK : m23Certificate.originalSubgroup ⊓ centralizer ({m23Rep1} : Set _) =
        m23CentQ1.originalSubgroup := hC
    rw [hK]
    set G := m23CentWords1.map (evalCodes [m23PermA, m23PermB]) with hG
    refine FinCk.centFourOK_spec hn (gens := G.map toTable) (gg := fun l => G[l]!)
      (fun l hl => ⟨?_, ?_⟩) (rep_toTable hn _) hKc1 Certificates.certificate55103
    · have hl' : l < G.length := by simpa using hl
      rw [getElem!_pos (G.map toTable) l hl, List.getElem_map, getElem!_pos G l hl']
      exact rep_toTable hn _
    · have hl' : l < G.length := by simpa using hl
      rw [m23CentQ1, certificate_originalSubgroup, getElem!_pos G l hl']
      exact subset_closure (List.getElem_mem hl')

end FinM23

theorem finCellB_m23
    {Y : Type} [Group Y]
    (hY : NativeSporadic.IsSporadic Y .M23) : FinCellB Y := by
  obtain ⟨e⟩ := hY
  have eA : MulAut Y ≃* ↥NativeSporadic.M23 :=
    (MulAut.congr (e : Y ≃* NativeSporadic.M23)).trans
      (FinM23.conjEquiv m23_center_eq_bot' m23_mulAut_card).symm
  exact finCellB_of (NoFourPerf.of_equiv eA (NoFourPerf.of_in FinM23.noFourPerfIn_m23))

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
