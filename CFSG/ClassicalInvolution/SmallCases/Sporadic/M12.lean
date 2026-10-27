module

public import CFSG.ClassicalInvolution.SmallCases.Sporadic.Cover
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12
public import Certificates.Certificate2193
public import Certificates.Certificate2200
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.M12Inputs
public import Certificates.Certificate9311
public import Certificates.Certificate2194
public meta import CFSG.ClassicalInvolution.SmallCases.Sporadic.Cover
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM12
public meta import CFSG.ClassicalInvolution.SmallCases.Sporadic.Basic
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreModel
public import CFSG.Sporadic.Schreier.MathieuOddCoreModel

public section

namespace CFSG.ClassicalInvolution

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
  CFSG.Sporadic.Th CFSG.Sporadic.Schreier.Native

theorem m12_U1_check :
    twoConstrainedCheck (enumerationTab m12CentQ1) (permClosureList m12UGens1 20) 5 = true := by
  exact Certificates.certificate9311.1

theorem m12_N2_check :
    indexTwoCheck m12Rep2 (enumerationTab m12CentQ2) (permClosureList m12NGens2 20) = true := by
  exact Certificates.certificate9311.2

theorem m12_cover_and_centralizers :
    (∀ u, (1 : Equiv.Perm (Fin 12))⁻¹ * u ∈ m12Certificate.originalSubgroup → orderOf u = 2 →
      ∃ d ∈ [(m12Rep1, m12CentQ1.originalSubgroup), (m12Rep2, m12CentQ2.originalSubgroup)],
        ∃ c ∈ m12Certificate.originalSubgroup, u = c * d.1 * c⁻¹) ∧
    ∀ d ∈ [(m12Rep1, m12CentQ1.originalSubgroup), (m12Rep2, m12CentQ2.originalSubgroup)],
      centralizerIn m12Certificate.originalSubgroup d.1 = d.2 := by
  have hn : (12 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m12Certificate := m12Certificate_check
  obtain ⟨hok, hsz, -⟩ := m12_oddcore_cover
  obtain ⟨hr1, hro1, hK1, hKc1, -⟩ := m12_rep_data1
  obtain ⟨hr2, hro2, hK2, hKc2, -⟩ := m12_rep_data2
  have hA : m12gA ∈ m12Certificate.originalSubgroup := m12_gens_mem _ (by simp)
  have hB : m12gB ∈ m12Certificate.originalSubgroup := m12_gens_mem _ (by simp)
  rw [m12InvReps_eq] at hok hsz
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  refine cover_and_centralizers_of_reps hn m12Certificate hQ (pairTables_spec hn hA hB) 1
    (fun h hh => by simpa using hh) _ ?_ 1000 hok ?_
  · intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact ⟨by simpa using hr1, hro1⟩
    · exact ⟨by simpa using hr2, hro2⟩
  · intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact ⟨hK1, by rw [hsz.1, hKc1, m12Certificate_originalSubgroup, m12_card]⟩
    · exact ⟨hK2, by rw [hsz.2, hKc2, m12Certificate_originalSubgroup, m12_card]⟩

theorem noNonsolvableClassical_M12 :
    NoNonsolvableClassical NativeSporadic.M12 := by
  obtain ⟨hcov, hcent⟩ := m12_cover_and_centralizers
  have hQ1 : ValidSchreier m12CentQ1 := (m12_oddcore_cent1).1
  have hQ2 : ValidSchreier m12CentQ2 := (m12_oddcore_cent2).1
  rw [← m12Certificate_originalSubgroup]
  refine noNonsolvableClassical_of_reps _ [m12Rep1, m12Rep2] ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (m12_rep_data1).1
    · exact (m12_rep_data2).1
  · intro u hu ho
    obtain ⟨d, hd, c, hc, hud⟩ := hcov u (by simpa using hu) ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact ⟨_, by simp, c, hc, hud⟩
    · exact ⟨_, by simp, c, hc, hud⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have h := hcent (m12Rep1, m12CentQ1.originalSubgroup) (by simp)
      unfold CentralizerGood
      rw [h]
      left
      exact exists_normal_pGroup_of_check _ (enumerationTab m12CentQ1) _
        (mem_enumerationTab_iff m12CentQ1 hQ1) 5 m12_U1_check
    · have h := hcent (m12Rep2, m12CentQ2.originalSubgroup) (by simp)
      unfold CentralizerGood
      rw [h]
      right
      exact exists_index_two_of_check m12Rep2 _ (enumerationTab m12CentQ2) _
        (mem_enumerationTab_iff m12CentQ2 hQ2) (enumerationTab_nodup m12CentQ2 hQ2) m12_N2_check

end CFSG.ClassicalInvolution
