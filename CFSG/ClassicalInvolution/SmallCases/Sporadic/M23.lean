module

public import CFSG.ClassicalInvolution.SmallCases.Sporadic.Cover
public import CFSG.Sporadic.Schreier.MathieuOddCoreM23
public import Certificates.Certificate2196
public import Certificates.Certificate2204
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.M23Inputs
public import Certificates.Certificate9313
public import Certificates.Certificate2197
public meta import CFSG.ClassicalInvolution.SmallCases.Sporadic.Cover
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM23
public import CFSG.Sporadic.Schreier.M23Check
public meta import CFSG.ClassicalInvolution.SmallCases.Sporadic.Basic
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreModel
public import CFSG.Sporadic.Schreier.MathieuOddCoreModel

public section

namespace CFSG.ClassicalInvolution

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
  CFSG.Sporadic.Th CFSG.Sporadic.Schreier.Native

theorem m23_U1_check :
    twoConstrainedCheck (enumerationTab m23CentQ1) (permClosureList m23UGens1 20) 4 = true := by
  exact Certificates.certificate9313

theorem m23_cover_and_centralizers :
    (∀ u, (1 : Equiv.Perm (Fin 23))⁻¹ * u ∈ m23Certificate.originalSubgroup → orderOf u = 2 →
      ∃ d ∈ [(m23Rep1, m23CentQ1.originalSubgroup)],
        ∃ c ∈ m23Certificate.originalSubgroup, u = c * d.1 * c⁻¹) ∧
    ∀ d ∈ [(m23Rep1, m23CentQ1.originalSubgroup)],
      centralizerIn m23Certificate.originalSubgroup d.1 = d.2 := by
  have hn : (23 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m23Certificate := m23Certificate_check
  obtain ⟨hok, hsz, -⟩ := m23_oddcore_cover
  obtain ⟨hr1, hro1, hK1, hKc1, -⟩ := m23_rep_data1
  have hA : m23PermA ∈ m23Certificate.originalSubgroup := m23_gens_mem _ (by simp)
  have hB : m23PermB ∈ m23Certificate.originalSubgroup := m23_gens_mem _ (by simp)
  rw [m23InvReps_eq] at hok hsz
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  refine cover_and_centralizers_of_reps hn m23Certificate hQ (pairTables_spec hn hA hB) 1
    (fun h hh => by simpa using hh) _ ?_ 4000 hok ?_
  · intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    subst hd
    exact ⟨by simpa using hr1, hro1⟩
  · intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    subst hd
    exact ⟨hK1, by rw [hsz, hKc1, m23Certificate_originalSubgroup, m23_card]⟩

theorem noNonsolvableClassical_M23 :
    NoNonsolvableClassical NativeSporadic.M23 := by
  obtain ⟨hcov, hcent⟩ := m23_cover_and_centralizers
  have hQ1 : ValidSchreier m23CentQ1 := (m23_oddcore_cent1).1
  rw [← m23Certificate_originalSubgroup]
  refine noNonsolvableClassical_of_reps _ [m23Rep1] ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact (m23_rep_data1).1
  · intro u hu ho
    obtain ⟨d, hd, c, hc, hud⟩ := hcov u (by simpa using hu) ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    subst hd
    exact ⟨_, by simp, c, hc, hud⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    have h := hcent (m23Rep1, m23CentQ1.originalSubgroup) (by simp)
    unfold CentralizerGood
    rw [h]
    left
    exact exists_normal_pGroup_of_check _ (enumerationTab m23CentQ1) _
      (mem_enumerationTab_iff m23CentQ1 hQ1) 4 m23_U1_check

end CFSG.ClassicalInvolution
