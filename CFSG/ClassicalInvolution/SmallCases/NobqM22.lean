module

public import CFSG.ClassicalInvolution.SmallCases.NobqLists
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.M22
public import Certificates.Certificate2195
public import Certificates.Certificate2202
public import Certificates.Certificate9305
public import Certificates.Certificate3157
public meta import CFSG.ClassicalInvolution.SmallCases.NobqLists
public meta import CFSG.ClassicalInvolution.SmallCases.Sporadic.M22

public section

namespace CFSG.ClassicalInvolution.Nobq

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
  CFSG.Sporadic.Th CFSG.Sporadic.Schreier.Native CFSG.ClassicalInvolution

theorem m22_cqCheck :
    cqCheck m22Rep1 (enumerationTab m22CentQ1) = true := by
  exact Certificates.certificate9305

theorem noUniqueInvNormal_M22 :
    NoUniqueInvNormal NativeSporadic.M22 := by
  obtain ⟨hcov, hcent⟩ := m22_cover_and_centralizers
  have hQ1 : ValidSchreier m22CentQ1 := (m22_oddcore_cent1).1
  rw [← m22Certificate_originalSubgroup]
  refine noUniqueInvNormal_of_reps _ [m22Rep1] ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact (m22_rep_data1).1
  · intro u hu ho
    obtain ⟨d, hd, c, hc, hud⟩ := hcov u (by simpa using hu) ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    subst hd
    exact ⟨_, by simp, c, hc, hud⟩
  · intro r hr hrH N
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    have h := hcent (m22Rep1, m22CentQ1.originalSubgroup) (by simp)
    refine not_uniqueInvNormal_of_cqCheck _ m22Rep1 hrH (enumerationTab m22CentQ1) (fun g => ?_)
      m22_cqCheck N
    rw [mem_enumerationTab_iff m22CentQ1 hQ1]
    exact (Set.ext_iff.mp (congrArg (↑) h) g).symm

end CFSG.ClassicalInvolution.Nobq
