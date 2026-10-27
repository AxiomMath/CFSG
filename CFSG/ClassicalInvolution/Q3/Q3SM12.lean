module

public import CFSG.ClassicalInvolution.Q3.Q3SCriteria

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
  CFSG.Sporadic.Th CFSG.Sporadic.Schreier.Native CFSG.ClassicalInvolution

@[expose] def m12W1a : List ℤ :=
  [-2, -1, -2, -2, -1, -2, -2, -1, -2, -1, -2, -2, -1, -2, -1, -2, -1, -2, -2, -1, -2, 1, 2, 1,
    2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, -2, -1, -2, -2, -1, -2, -2, -1,
    -2, -1, -2, -2, -1, -2, -1, -2, -1, -2, -2, -1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2,
    2, 1, 2, 2, 1, 2, 2, 1, 2]
@[expose] def m12W1b : List ℤ :=
  [-2, -1, -2, -2, -1, -2, -2, -1, -2, -1, -2, -2, -1, -2, -2, -1, 2, 1, 2, 1, 2, 1, 2, 1, 2,
    2, 1, 2, 2, 1, 2, 1, 2, 1, 2, -2, -1, -2, -1, -2, -1, -2, -2, -1, -2, -1, -2, -1, -2, -2,
    -1, -2, -2, -1, -2, -1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2]
@[expose] def m12W2a : List ℤ :=
  [-1, -2, -1, -2, -1, -2, -2, -1, -2, -2, -1, -2, -1, -2, -2, -1, 2, 2, 1, 2, 1, 2, 1, 2, 2,
    1, 2, 1, 2, 1, 2, 1, 2, 1, -1, -2, -1, -2, -1, -2, -2, -1, -2, -2, -1, -2, -1, -2, -2, -1,
    2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1]
@[expose] def m12W2b : List ℤ :=
  [-1, -2, -2, -1, -2, -1, -2, -2, -1, -2, -2, -1, -2, -1, -2, -2, -1, -2, -2, -1, -2, 1, 2, 2,
    1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, -1, -2, -2, -1, -2, -1, -2, -2, -1,
    -2, -2, -1, -2, -1, -2, -2, -1, -2, -2, -1, -2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2,
    1, 2, 2, 1, 2, 1, 2, -2, -1, -2, -1, -2, -1, -2, -2, -1, -2, -1, -2, -1, -2, -2, -1, -2,
    -1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, -2, -1, -2, -1, -2, -1, -2,
    -2, -1, -2, -1, -2, -1, -2, -2, -1, -2, -1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2,
    1, 2, 2, 1]

@[expose] def m12G1a : Equiv.Perm (Fin 12) :=
  tab (evalCodes [m12gA, m12gB] m12W1a)

@[expose] def m12G1b : Equiv.Perm (Fin 12) :=
  tab (evalCodes [m12gA, m12gB] m12W1b)

@[expose] def m12G2a : Equiv.Perm (Fin 12) :=
  tab (evalCodes [m12gA, m12gB] m12W2a)

@[expose] def m12G2b : Equiv.Perm (Fin 12) :=
  tab (evalCodes [m12gA, m12gB] m12W2b)


theorem m12_witness₁ :
    m12G1a * m12Rep1 = m12Rep1 * m12G1a ∧ m12G1b * m12Rep1 = m12Rep1 * m12G1b ∧
    m12G1a ^ 3 = 1 ∧ m12G1b ^ 3 = 1 ∧ (m12G1a * m12G1b) ^ 2 = 1 ∧ m12G1a * m12G1b ≠ 1 ∧
    m12G1a * m12G1b ≠ m12Rep1 := by
  decide +kernel

theorem m12_witness₂ :
    m12G2a * m12Rep2 = m12Rep2 * m12G2a ∧ m12G2b * m12Rep2 = m12Rep2 * m12G2b ∧
    m12G2a ^ 3 = 1 ∧ m12G2b ^ 3 = 1 ∧ (m12G2a * m12G2b) ^ 2 = 1 ∧ m12G2a * m12G2b ≠ 1 ∧
    m12G2a * m12G2b ≠ m12Rep2 := by
  decide +kernel

theorem m12G_mem (w : List ℤ) :
    tab (evalCodes [m12gA, m12gB] w) ∈ m12Certificate.originalSubgroup := by
  rw [tab_eq]
  exact evalCodes_mem _ m12_gens_mem _

theorem noWeakClassical3_M12 : NoWeakClassical3 NativeSporadic.M12 := by
  obtain ⟨hcov, hcent⟩ := m12_cover_and_centralizers
  obtain ⟨-, -, -, hK1, -⟩ := m12_rep_data1
  obtain ⟨-, -, -, hK2, -⟩ := m12_rep_data2
  rw [← m12Certificate_originalSubgroup]
  refine noWeakClassical3_of_reps _ [m12Rep1, m12Rep2] ?_ ?_
  · intro u hu ho
    obtain ⟨d, hd, c, hc, hud⟩ := hcov u (by simpa using hu) ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact ⟨_, by simp, c, hc, hud⟩
    · exact ⟨_, by simp, c, hc, hud⟩
  · intro r hr hrep
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrep
    rcases hrep with rfl | rfl
    · have h1 : centralizerIn m12Certificate.originalSubgroup m12Rep1 =
          m12CentQ1.originalSubgroup := hcent (m12Rep1, m12CentQ1.originalSubgroup) (by simp)
      obtain ⟨c₁, c₂, hg₁, hg₂, ht, ht1, htz⟩ := m12_witness₁
      exact NoWeakClassical3At.of_ambient_witness _ hr (by rw [h1, hK1]; norm_num)
        (m12G_mem _) (m12G_mem _) c₁ c₂ hg₁ hg₂ ht ht1 htz
    · have h1 : centralizerIn m12Certificate.originalSubgroup m12Rep2 =
          m12CentQ2.originalSubgroup := hcent (m12Rep2, m12CentQ2.originalSubgroup) (by simp)
      obtain ⟨c₁, c₂, hg₁, hg₂, ht, ht1, htz⟩ := m12_witness₂
      exact NoWeakClassical3At.of_ambient_witness _ hr (by rw [h1, hK2]; norm_num)
        (m12G_mem _) (m12G_mem _) c₁ c₂ hg₁ hg₂ ht ht1 htz

end CFSG.ClassicalInvolution.Q3
