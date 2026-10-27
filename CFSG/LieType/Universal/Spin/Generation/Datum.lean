module

public import CFSG.LieType.Universal.Spin.Generation.Frame
public import CFSG.LieType.Universal.Spin.Datum
public import CFSG.LieType.Universal.SpinClause0

public section

namespace CFSG.LieType.Universal.Spin

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

section Perp

variable {n : ℕ} {K : Type} [Field K]

theorem eq_zero_of_polar_plusFrame_vec (hn : 3 ≤ n) {v : Fin n ⊕ Fin n → K}
    (hv : ∀ k r, polar (quadPlus n K) v ((plusFrame n K hn).vec k r) = 0) : v = 0 := by
  funext x
  rcases x with k | k
  · have h := hv k false
    rwa [plusFrame_vec, plusVec_false, polar_quadPlus_single_inr] at h
  · have h := hv k true
    rwa [plusFrame_vec, plusVec_true, polar_quadPlus_single_inl] at h

theorem eq_smul_oddZ_of_polar_oddFrame_vec {v : Fin n ⊕ Fin n ⊕ Unit → K}
    (hv : ∀ k r, polar (quadOdd n K) v ((oddFrame n K).vec k r) = 0) :
    v = v (.inr (.inr ())) • (oddFrame n K).z := by
  funext x
  rcases x with k | k | ⟨⟩
  · have h := hv k false
    rw [oddFrame_vec, oddVec_false, polar_quadOdd_single_inr_inl] at h
    simp [oddZ, h]
  · have h := hv k true
    rw [oddFrame_vec, oddVec_true, polar_quadOdd_single_inl] at h
    simp [oddZ, h]
  · simp [oddZ]

end Perp

theorem plusDatum_iSup_eq_top (n : ℕ) (K : Type) [Field K] (hn : 3 ≤ n) :
    ⨆ γ ∈ RootSystem.roots (isFiniteType_cartanD n) ∅, plusRootGroup n K hn γ = ⊤ := by
  have := isPerfect_spinGroup_quadPlus (K := K) hn
  refine (plusFrame n K hn).eq_top_of_longRoot_mem_of_eq_zero ?_
    (fun v hv => eq_zero_of_polar_plusFrame_vec hn hv) (range_spinAction_quadPlus hn).le
  intro i j hij s t c
  obtain ⟨γ, hγ, h⟩ := exists_mem_rootsD_toStdD_eq n hij (boolSign_eq_one_or_eq_neg_one s)
    (boolSign_eq_one_or_eq_neg_one t)
  have hmem : (plusFrame n K hn).longRoot hij s t (.ofAdd c) ∈ plusRootGroup n K hn γ := by
    rw [plusRootGroup_eq hn hij s t h]
    exact ⟨_, rfl⟩
  exact Subgroup.mem_iSup_of_mem γ (Subgroup.mem_iSup_of_mem hγ hmem)

theorem oddDatum_iSup_eq_top (n : ℕ) (K : Type) [Field K] (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) :
    ⨆ γ ∈ RootSystem.roots (isFiniteType_cartanB n) ∅, oddRootGroup n K γ = ⊤ := by
  have := isPerfect_spinGroup_quadOdd h2 hn
  refine (oddFrame n K).eq_top_of_root_mem ?_ ?_
    (fun v hv => ⟨_, eq_smul_oddZ_of_polar_oddFrame_vec hv⟩) (range_spinAction_quadOdd h2 hn).le
  · intro i j hij s t c
    have hγ := ofStdB_mem_rootsB n (Or.inl ⟨i, j, boolSign s, boolSign t, hij,
      boolSign_eq_one_or_eq_neg_one s, boolSign_eq_one_or_eq_neg_one t, rfl⟩)
    have hmem : (oddFrame n K).longRoot hij s t (.ofAdd c) ∈
        oddRootGroup n K (ofStdB n (Pi.single i (boolSign s) + Pi.single j (boolSign t))) := by
      rw [oddRootGroup_eq_long hij s t (toStdB_ofStdB n _)]
      exact ⟨_, rfl⟩
    exact Subgroup.mem_iSup_of_mem _ (Subgroup.mem_iSup_of_mem hγ hmem)
  · intro i s c
    have hγ := ofStdB_mem_rootsB n (Or.inr ⟨i, boolSign s, boolSign_eq_one_or_eq_neg_one s, rfl⟩)
    have hmem : (oddFrame n K).shortRoot i s (.ofAdd c) ∈
        oddRootGroup n K (ofStdB n (Pi.single i (boolSign s))) := by
      rw [oddRootGroup_eq_short i s (toStdB_ofStdB n _)]
      exact ⟨_, rfl⟩
    exact Subgroup.mem_iSup_of_mem _ (Subgroup.mem_iSup_of_mem hγ hmem)

end CFSG.LieType.Universal.Spin
