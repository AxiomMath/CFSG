module

public import CFSG.ClassicalInvolution.SmallCases.Sporadic.Cover
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22
public import Certificates.Certificate2195
public import Certificates.Certificate2202
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.M22Inputs
public import Certificates.Certificate9312
public import Certificates.Certificate3157
public meta import CFSG.ClassicalInvolution.SmallCases.Sporadic.Cover
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM22
public meta import CFSG.ClassicalInvolution.SmallCases.Sporadic.Basic
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreModel
public import CFSG.Sporadic.Schreier.MathieuOddCoreModel

public section

namespace CFSG.ClassicalInvolution

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
  CFSG.Sporadic.Th CFSG.Sporadic.Schreier.Native

theorem m22_U1_check :
    twoConstrainedCheck (enumerationTab m22CentQ1) (permClosureList m22UGens1 20) 6 = true := by
  exact Certificates.certificate9312

theorem m22_cover_and_centralizers :
    (∀ u, (1 : Equiv.Perm (Fin 22))⁻¹ * u ∈ m22Certificate.originalSubgroup → orderOf u = 2 →
      ∃ d ∈ [(m22Rep1, m22CentQ1.originalSubgroup)],
        ∃ c ∈ m22Certificate.originalSubgroup, u = c * d.1 * c⁻¹) ∧
    ∀ d ∈ [(m22Rep1, m22CentQ1.originalSubgroup)],
      centralizerIn m22Certificate.originalSubgroup d.1 = d.2 := by
  have hn : (22 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m22Certificate := m22Certificate_check
  obtain ⟨hok, hsz, -⟩ := m22_oddcore_cover
  obtain ⟨hr1, hro1, hK1, hKc1, -⟩ := m22_rep_data1
  have hA : m22gA ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  have hB : m22gB ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  rw [m22InvReps_eq] at hok hsz
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  refine cover_and_centralizers_of_reps hn m22Certificate hQ (pairTables_spec hn hA hB) 1
    (fun h hh => by simpa using hh) _ ?_ 2000 hok ?_
  · intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    subst hd
    exact ⟨by simpa using hr1, hro1⟩
  · intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    subst hd
    exact ⟨hK1, by rw [hsz, hKc1, m22Certificate_originalSubgroup, m22_card]⟩

theorem noNonsolvableClassical_M22 :
    NoNonsolvableClassical NativeSporadic.M22 := by
  obtain ⟨hcov, hcent⟩ := m22_cover_and_centralizers
  have hQ1 : ValidSchreier m22CentQ1 := (m22_oddcore_cent1).1
  rw [← m22Certificate_originalSubgroup]
  refine noNonsolvableClassical_of_reps _ [m22Rep1] ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact (m22_rep_data1).1
  · intro u hu ho
    obtain ⟨d, hd, c, hc, hud⟩ := hcov u (by simpa using hu) ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    subst hd
    exact ⟨_, by simp, c, hc, hud⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    have h := hcent (m22Rep1, m22CentQ1.originalSubgroup) (by simp)
    unfold CentralizerGood
    rw [h]
    left
    exact exists_normal_pGroup_of_check _ (enumerationTab m22CentQ1) _
      (mem_enumerationTab_iff m22CentQ1 hQ1) 6 m22_U1_check

end CFSG.ClassicalInvolution
