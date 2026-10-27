module

public import CFSG.ClassicalGroups.Orthogonal.SiegelRT1CaseILemma32
public import CFSG.ClassicalGroups.Orthogonal.SiegelRT1Transversal

public section

namespace CFSG.ClassicalGroups.Orthogonal.SiegelRT1

open CFSG.ClassicalGroups.Alternating CFSG.HardMathSupport.Kantor79 QuadraticMap Module

section Generic

variable {K : Type*} [Field K] {N : Type*} [AddCommGroup N] [Module K N]

theorem CaseI.linearIndependent_pair_of_family {ι : Type*} {v : ι → N}
    (hv : LinearIndependent K v) {i j : ι} (hij : i ≠ j) : LinearIndependent K ![v i, v j] := by
  have h := hv.comp ![i, j] (by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all)
  convert h using 1
  ext x
  fin_cases x <;> rfl

end Generic

variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {N : Type*} [AddCommGroup N] [Module K N] [FiniteDimensional K N]
  {BN : LinearMap.BilinForm K N}
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {hBN : BN.IsAlt} {Qf : QuadraticForm K V} {ρ : Gsp BN →* (V ≃ₗ[K] V)}

theorem CaseI.axis_le_sup (hs : Setting hBN Qf ρ) {c c' : N} (hcc : BN c c' ≠ 0) {x : N}
    (hx : x ≠ 0) {l n p : K} (hl : l ≠ 0) (hn : n ≠ 0) (hp : p ≠ 0)
    (h₁ : axis hBN ρ x l ⊓ axis hBN ρ c n ≠ ⊥) (h₂ : axis hBN ρ x l ⊓ axis hBN ρ c' p ≠ ⊥) :
    axis hBN ρ x l ≤ axis hBN ρ c n ⊔ axis hBN ρ c' p := by
  have hc : c ≠ 0 := fun h => hcc (by rw [h, map_zero, LinearMap.zero_apply])
  have hc' : c' ≠ 0 := fun h => hcc (by rw [h, map_zero])
  obtain ⟨hAA', -⟩ := corollary_one_three hs.nondeg (hs.siegel c hc n hn) (hs.siegel c' hc' p hp)
    (CaseI.pow_four_ne_one hs hcc hn hp)
  obtain ⟨y, hyLA, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h₁
  obtain ⟨hyL, hyA⟩ := Submodule.mem_inf.mp hyLA
  obtain ⟨y', hy'A', hy'0, hyy', -⟩ :=
    exists_transversal_point (CaseI.finrank_axis hs hc' hp) hAA' hyA hy0
  have hL := eq_span_pair_of_transversal (axis_totallySingular hs c' p) hAA'
    (CaseI.finrank_axis hs hc' hp) (CaseI.finrank_axis hs hx hl) (axis_totallySingular hs x l) h₂
    hyL hyA hy0 hy'A' hy'0 hyy'
  rw [hL]
  exact Submodule.span_le.mpr (Set.insert_subset_iff.mpr ⟨Submodule.mem_sup_left hyA,
    Set.singleton_subset_iff.mpr (Submodule.mem_sup_right hy'A')⟩)

omit [Finite K] [CharP K 2] in
theorem exists_frame_of_five_le (hBN : BN.IsAlt) (hBNnd : BN.Nondegenerate)
    (h5 : 5 ≤ finrank K N) :
    ∃ a c c' c'' : N, BN c c' ≠ 0 ∧ BN a c = 0 ∧ BN a c' = 0 ∧ BN a c'' = 0 ∧ BN c'' c = 0 ∧
      BN c'' c' = 0 ∧ LinearIndependent K ![a, c] ∧ LinearIndependent K ![a, c'] ∧
      LinearIndependent K ![c'', c] ∧ LinearIndependent K ![c'', c'] ∧
      LinearIndependent K ![a, c''] := by
  obtain ⟨m, b, hb⟩ := hBN.exists_basis_toMatrix_eq_J hBNnd
  have hdim : finrank K N = m + m := by
    rw [finrank_eq_card_basis b, Fintype.card_sum, Fintype.card_fin]
  have hm : 3 ≤ m := by omega
  have hB : ∀ x y, BN (b x) (b y) = Matrix.J (Fin m) K x y := fun x y => by
    rw [← hb, LinearMap.BilinForm.toMatrix_apply]
  let i₀ : Fin m := ⟨0, by omega⟩
  let i₁ : Fin m := ⟨1, by omega⟩
  let i₂ : Fin m := ⟨2, by omega⟩
  have h01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  have h02 : i₀ ≠ i₂ := by simp [i₀, i₂, Fin.ext_iff]
  have h12 : i₁ ≠ i₂ := by simp [i₁, i₂, Fin.ext_iff]
  refine ⟨b (Sum.inl i₀), b (Sum.inl i₂), b (Sum.inr i₂), b (Sum.inl i₁), ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · simp [hB, Matrix.J]
  · simp [hB, Matrix.J]
  · simp [hB, Matrix.J, h02]
  · simp [hB, Matrix.J]
  · simp [hB, Matrix.J]
  · simp [hB, Matrix.J, h12]
  · exact CaseI.linearIndependent_pair_of_family b.linearIndependent (by simp [h02])
  · exact CaseI.linearIndependent_pair_of_family b.linearIndependent (by simp)
  · exact CaseI.linearIndependent_pair_of_family b.linearIndependent (by simp [h12])
  · exact CaseI.linearIndependent_pair_of_family b.linearIndependent (by simp)
  · exact CaseI.linearIndependent_pair_of_family b.linearIndependent (by simp [h01])

theorem false_of_caseI_of_five_le (hs : Setting hBN Qf ρ) (hI : CaseI hBN ρ)
    (h5 : 5 ≤ finrank K N) : False := by
  obtain ⟨a, c, c', c'', hcc, hac, hac', hac'', hc''c, hc''c', h1, h2, h3, h4, h5'⟩ :=
    exists_frame_of_five_le hBN hs.nondegN h5
  have ha : a ≠ 0 := by simpa using h5'.ne_zero (0 : Fin 2)
  have hc'' : c'' ≠ 0 := by simpa using h5'.ne_zero (1 : Fin 2)
  have hc : c ≠ 0 := by simpa using h1.ne_zero (1 : Fin 2)
  have hc' : c' ≠ 0 := by simpa using h2.ne_zero (1 : Fin 2)
  refine false_of_axis_eq hs h5' fun l m hl hm => ?_
  obtain ⟨hAA', hA'A, -⟩ := corollary_one_three hs.nondeg (hs.siegel c hc 1 one_ne_zero)
    (hs.siegel c' hc' 1 one_ne_zero) (CaseI.pow_four_ne_one hs hcc one_ne_zero one_ne_zero)
  exact eq_of_transversal_inf_ne_bot (axis_totallySingular hs c' 1) hAA' hA'A
    (CaseI.finrank_axis hs hc one_ne_zero) (CaseI.finrank_axis hs hc' one_ne_zero)
    (CaseI.finrank_axis hs ha hl) (CaseI.finrank_axis hs hc'' hm) (axis_totallySingular hs a l)
    (axis_totallySingular hs c'' m) (hI.inf_ne_bot_of_scalars h1 hac hl one_ne_zero)
    (hI.inf_ne_bot_of_scalars h2 hac' hl one_ne_zero)
    (hI.inf_ne_bot_of_scalars h3 hc''c hm one_ne_zero)
    (hI.inf_ne_bot_of_scalars h4 hc''c' hm one_ne_zero) (hI.inf_ne_bot_of_scalars h5' hac'' hl hm)

end CFSG.ClassicalGroups.Orthogonal.SiegelRT1
