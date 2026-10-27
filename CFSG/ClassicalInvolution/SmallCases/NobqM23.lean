module

public import CFSG.ClassicalInvolution.SmallCases.NobqLists
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.M23
public import Certificates.Certificate2196
public import Certificates.Certificate2204
public import Certificates.Certificate9306
public import Certificates.Certificate2197
public meta import CFSG.ClassicalInvolution.SmallCases.NobqLists
public meta import CFSG.ClassicalInvolution.SmallCases.Sporadic.M23

public section

namespace CFSG.ClassicalInvolution.Nobq

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
  CFSG.Sporadic.Th CFSG.Sporadic.Schreier.Native CFSG.ClassicalInvolution

theorem m23_cqCheck :
    cqCheck m23Rep1 (enumerationTab m23CentQ1) = true := by
  exact Certificates.certificate9306

theorem noUniqueInvNormal_M23 :
    NoUniqueInvNormal NativeSporadic.M23 := by
  obtain ⟨hcov, hcent⟩ := m23_cover_and_centralizers
  have hQ1 : ValidSchreier m23CentQ1 := (m23_oddcore_cent1).1
  rw [← m23Certificate_originalSubgroup]
  refine noUniqueInvNormal_of_reps _ [m23Rep1] ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact (m23_rep_data1).1
  · intro u hu ho
    obtain ⟨d, hd, c, hc, hud⟩ := hcov u (by simpa using hu) ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    subst hd
    exact ⟨_, by simp, c, hc, hud⟩
  · intro r hr hrH N
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    have h := hcent (m23Rep1, m23CentQ1.originalSubgroup) (by simp)
    refine not_uniqueInvNormal_of_cqCheck _ m23Rep1 hrH (enumerationTab m23CentQ1) (fun g => ?_)
      m23_cqCheck N
    rw [mem_enumerationTab_iff m23CentQ1 hQ1]
    exact (Set.ext_iff.mp (congrArg (↑) h) g).symm

end CFSG.ClassicalInvolution.Nobq
