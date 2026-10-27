module

public import CFSG.ClassicalInvolution.Q3.Q3SCriteria

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
  CFSG.Sporadic.Th CFSG.Sporadic.Schreier.Native CFSG.ClassicalInvolution

@[expose] def m22Wa : List ℤ :=
  [-2, -1, -2, -2, -2, -1, -2, -2, -1, -2, -1, -2, -2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2]
@[expose] def m22Wb : List ℤ :=
  [-2, -1, -2, -2, -2, -1, -2, -2, -1, -2, -1, -2, -2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2,
    -2, -1, -2, -2, -2, -1, -2, -2, -1, -2, -1, -2, -2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2,
    -2, -1, -2, -2, -2, -1, -2, -2, -2, -1, -2, -2, -2, -1, -2, -1, -2, -2, 1, 2, 2, 1, 2, 2,
    2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2, -2, -1, -2, -2, -2, -1, -2, -2, -2, -1, -2, -2, -2,
    -1, -2, -1, -2, -2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2]

@[expose] def m22Ga : Equiv.Perm (Fin 22) := tab (evalCodes [m22gA, m22gB] m22Wa)

@[expose] def m22Gb : Equiv.Perm (Fin 22) := tab (evalCodes [m22gA, m22gB] m22Wb)

theorem m22_witness :
    m22Ga * m22Rep1 = m22Rep1 * m22Ga ∧ m22Gb * m22Rep1 = m22Rep1 * m22Gb ∧
    m22Ga ^ 3 = 1 ∧ m22Gb ^ 3 = 1 ∧ (m22Ga * m22Gb) ^ 2 = 1 ∧
    m22Ga * m22Gb ≠ 1 ∧ m22Ga * m22Gb ≠ m22Rep1 := by
  decide +kernel

theorem m22G_mem (w : List ℤ) :
    tab (evalCodes [m22gA, m22gB] w) ∈ m22Certificate.originalSubgroup := by
  rw [tab_eq]
  exact evalCodes_mem _ m22_gens_mem _

theorem noWeakClassical3_M22 : NoWeakClassical3 NativeSporadic.M22 := by
  obtain ⟨hcov, hcent⟩ := m22_cover_and_centralizers
  obtain ⟨-, -, -, hK1, -⟩ := m22_rep_data1
  rw [← m22Certificate_originalSubgroup]
  refine noWeakClassical3_of_reps _ [m22Rep1] ?_ ?_
  · intro u hu ho
    obtain ⟨d, hd, c, hc, hud⟩ := hcov u (by simpa using hu) ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    subst hd
    exact ⟨_, by simp, c, hc, hud⟩
  · intro r hr hrep
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrep
    subst hrep
    have h1 : centralizerIn m22Certificate.originalSubgroup m22Rep1 =
        m22CentQ1.originalSubgroup := hcent (m22Rep1, m22CentQ1.originalSubgroup) (by simp)
    obtain ⟨c₁, c₂, hg₁, hg₂, ht, ht1, htz⟩ := m22_witness
    exact NoWeakClassical3At.of_ambient_witness _ hr (by rw [h1, hK1]; norm_num)
      (m22G_mem _) (m22G_mem _) c₁ c₂ hg₁ hg₂ ht ht1 htz

end CFSG.ClassicalInvolution.Q3
