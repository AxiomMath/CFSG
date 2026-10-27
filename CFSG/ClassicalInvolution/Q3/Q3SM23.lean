module

public import CFSG.ClassicalInvolution.Q3.Q3SCriteria

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
  CFSG.Sporadic.Th CFSG.Sporadic.Schreier.Native CFSG.ClassicalInvolution

@[expose] def m23Wa : List ℤ :=
  [-2, -1, -2, -1, -2, -1, -2, -2, -2, -1, -2, -1, -2, -2, -1, -2, -1, -2, -2, -1, -2, -2, -1,
    -2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, -2, -1, -2,
    -2, -2, -1, -2, -2, -1, -2, -2, -2, -1, -2, -1, -2, -1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1,
    2, 1, 2, 1, 2, 1, 2, 2, -2, -1, -2, -2, -2, -1, -2, -2, -1, -2, -2, -2, -1, -2, -1, -2, -1,
    2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2]
@[expose] def m23Wb : List ℤ :=
  [-2, -2, -2, -1, -2, -1, -2, -1, -2, -2, -1, -2, -2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2,
    2, -2, -1, -2, -2, -2, -1, -2, -2, -1, -2, -2, -2, -1, -2, -1, -2, -1, 2, 1, 2, 2, 1, 2, 1,
    2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, -2, -1, -2, -2, -2, -1, -2, -2, -1, -2, -2, -2, -1,
    -2, -1, -2, -1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, -2, -2, -2, -1,
    -2, -1, -2, -1, -2, -2, -1, -2, -2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 2]

@[expose] def m23Ga : Equiv.Perm (Fin 23) := tab (evalCodes [m23PermA, m23PermB] m23Wa)

@[expose] def m23Gb : Equiv.Perm (Fin 23) := tab (evalCodes [m23PermA, m23PermB] m23Wb)

theorem m23_witness :
    m23Ga * m23Rep1 = m23Rep1 * m23Ga ∧ m23Gb * m23Rep1 = m23Rep1 * m23Gb ∧
    m23Ga ^ 3 = 1 ∧ m23Gb ^ 3 = 1 ∧ (m23Ga * m23Gb) ^ 2 = 1 ∧
    m23Ga * m23Gb ≠ 1 ∧ m23Ga * m23Gb ≠ m23Rep1 := by
  decide +kernel

theorem m23G_mem (w : List ℤ) :
    tab (evalCodes [m23PermA, m23PermB] w) ∈ m23Certificate.originalSubgroup := by
  rw [tab_eq]
  exact evalCodes_mem _ m23_gens_mem _

theorem noWeakClassical3_M23 : NoWeakClassical3 NativeSporadic.M23 := by
  obtain ⟨hcov, hcent⟩ := m23_cover_and_centralizers
  obtain ⟨-, -, -, hK1, -⟩ := m23_rep_data1
  rw [← m23Certificate_originalSubgroup]
  refine noWeakClassical3_of_reps _ [m23Rep1] ?_ ?_
  · intro u hu ho
    obtain ⟨d, hd, c, hc, hud⟩ := hcov u (by simpa using hu) ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    subst hd
    exact ⟨_, by simp, c, hc, hud⟩
  · intro r hr hrep
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrep
    subst hrep
    have h1 : centralizerIn m23Certificate.originalSubgroup m23Rep1 =
        m23CentQ1.originalSubgroup := hcent (m23Rep1, m23CentQ1.originalSubgroup) (by simp)
    obtain ⟨c₁, c₂, hg₁, hg₂, ht, ht1, htz⟩ := m23_witness
    exact NoWeakClassical3At.of_ambient_witness _ hr (by rw [h1, hK1]; norm_num)
      (m23G_mem _) (m23G_mem _) c₁ c₂ hg₁ hg₂ ht ht1 htz

end CFSG.ClassicalInvolution.Q3
