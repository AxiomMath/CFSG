module

public import CFSG.ClassicalInvolution.Phan.PhanP7Rot

public section

namespace CFSG.ClassicalInvolution.PhanP

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Models.OrthogonalPairs QuadraticMap CFSG.ClassicalInvolution.PhanD4
  CFSG.LieType.Steinberg CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.ModelFacts.MF15
open scoped MatrixGroups Pointwise

section Matrix

variable {F : Type} [Field F]

theorem exists_decomp_of_not_FJ {ε : F} (hε' : ¬IsSquare (-ε)) {M : Matrix (Fin 2) (Fin 2) F}
    (hM : ¬FJ ε M) (X : Matrix (Fin 2) (Fin 2) F) :
    ∃ Y₁ Y₂ : Matrix (Fin 2) (Fin 2) F, FJ ε Y₁ ∧ FJ ε Y₂ ∧ X = Y₁ + M * Y₂ := by
  have hΔ : ε * (M 1 1 - M 0 0) ^ 2 + (M 1 0 + ε * M 0 1) ^ 2 ≠ 0 := by
    intro h
    by_cases h1 : M 1 1 - M 0 0 = 0
    · have h2 : M 1 0 + ε * M 0 1 = 0 := by
        rw [h1] at h
        simpa using h
      exact hM ⟨by linear_combination h1, by linear_combination h2⟩
    · refine hε' ⟨(M 1 0 + ε * M 0 1) / (M 1 1 - M 0 0), ?_⟩
      field_simp
      linear_combination -h
  obtain ⟨c, d, e1, e2⟩ : ∃ c d : F, c * (M 1 1 - M 0 0) - d * (M 1 0 + ε * M 0 1) =
      X 1 1 - X 0 0 ∧ c * (M 1 0 + ε * M 0 1) + d * ε * (M 1 1 - M 0 0) = X 1 0 + ε * X 0 1 := by
    refine ⟨((X 1 1 - X 0 0) * ε * (M 1 1 - M 0 0) + (X 1 0 + ε * X 0 1) * (M 1 0 + ε * M 0 1)) /
      (ε * (M 1 1 - M 0 0) ^ 2 + (M 1 0 + ε * M 0 1) ^ 2),
      ((M 1 1 - M 0 0) * (X 1 0 + ε * X 0 1) - (M 1 0 + ε * M 0 1) * (X 1 1 - X 0 0)) /
      (ε * (M 1 1 - M 0 0) ^ 2 + (M 1 0 + ε * M 0 1) ^ 2), ?_, ?_⟩ <;>
    · field_simp
      ring
  refine ⟨X - M * !![c, -d; ε * d, c], !![c, -d; ε * d, c], ⟨?_, ?_⟩, ⟨by simp, by simp⟩, by abel⟩
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination -e1
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination -e2

end Matrix

section Dec

variable {F K : Type} [Field F] [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {S : PhanFamilyD4 K p f (spinGroup (quadPlus 4 F))} {ε : F} {hε : ε ≠ 0} {h4 : (4 : F) ≠ 0}

theorem exists_decomp_span_of_mem_range_zero (hK : Nat.card K = (p ^ f) ^ 2) (hg : GoodFamily S)
    (hS : ModelSpec S ε hε h4) (hq : 5 ≤ p ^ f) (h2 : (2 : F) ≠ 0) (h2K : (2 : K) ≠ 0)
    (hε' : ¬IsSquare (-ε)) {ρ : spinGroup (quadPlus 4 F)} (hρ : ρ ∈ (S.ι 0).range)
    (hρT : ρ ∉ torusSub S) {x : Fin 4 ⊕ Fin 4 → F} (hx : x ∈ (frame0 (F := F)).span) :
    ∃ a ∈ planeA ε hε h4, ∃ a' ∈ planeA ε hε h4, x = a + spinAction (quadPlus 4 F) ρ a' := by
  have hmem : spinAction (quadPlus 4 F) ρ ∈ (frame0 (F := F)).La.range := by
    have : spinAction (quadPlus 4 F) ρ ∈ (S.ι 0).range.map (spinAction (quadPlus 4 F)) :=
      ⟨ρ, hρ, rfl⟩
    rw [hS.map_range 0] at this
    exact this
  obtain ⟨M, hM⟩ := hmem
  have hnFJ : ¬FJ ε (M : Matrix (Fin 2) (Fin 2) F) := by
    intro hFJ
    refine hρT (mem_torusSub_of_mem_range_zero hK hg hS hq h2 h2K hρ ?_)
    have hFJinv : FJ ε ((M⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) := by
      rw [Matrix.SpecialLinearGroup.coe_inv]
      exact hFJ.adjugate
    intro x
    rw [← hM]
    refine ⟨fun hx => ?_, fun hx => La_mem_planeA h2 hFJ hx⟩
    have := La_mem_planeA (hε := hε) (h4 := h4) h2 hFJinv hx
    rwa [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one] at this
  have hxx := (Frame.mem_span_iff (frame0 (F := F))).1 hx
  obtain ⟨Y₁, Y₂, h1, h1', hX⟩ := exists_decomp_of_not_FJ hε' hnFJ ((frame0 (F := F)).coords x)
  refine ⟨(frame0 (F := F)).incl Y₁, incl_mem_planeA_of_FJ ε hε h4 h1,
    (frame0 (F := F)).incl Y₂, incl_mem_planeA_of_FJ ε hε h4 h1', ?_⟩
  rw [← hM]
  show x = _ + (frame0 (F := F)).La M ((frame0 (F := F)).incl Y₂)
  rw [Frame.La_apply_incl, ← map_add, ← hX]
  exact hxx

theorem mem_torusSub_of_spinAction_eq_one (hg : GoodFamily S)
    (hS : ModelSpec S ε hε h4) (h2 : (2 : F) ≠ 0) (h2K : (2 : K) ≠ 0)
    {z : spinGroup (quadPlus 4 F)} (hz : spinAction (quadPlus 4 F) z = 1) : z ∈ torusSub S := by
  have hs : spinAction (quadPlus 4 F) (sInv S 2 * sInv S 3) = 1 := by
    rw [map_mul, spinAction_sInv hg hS h2 h2K 2, spinAction_sInv hg hS h2 h2K 3]
    show (frame2 (F := F)).La (-1) * (frame2 (F := F)).swap.La (-1) = 1
    rw [Frame.La_swap_neg_one, Frame.La_neg_one_mul_self]
  have hmem : sInv S 2 * sInv S 3 ∈ torusSub S :=
    mul_mem (tor_mem_torusSub S 2 _) (tor_mem_torusSub S 3 _)
  have hne : sInv S 2 * sInv S 3 ≠ 1 := hg.tor_negOne_mul_ne_one h2K (by decide)
  rcases eq_one_or_eq_neg_one_of_spinAction_eq_one 4 F z hz with h | h
  · have : z = 1 := Subtype.ext h
    rw [this]
    exact one_mem _
  · rcases eq_one_or_eq_neg_one_of_spinAction_eq_one 4 F _ hs with h' | h'
    · exact absurd (Subtype.ext h') hne
    · have : z = sInv S 2 * sInv S 3 := Subtype.ext (by rw [h, h'])
      rw [this]
      exact hmem

end Dec

end CFSG.ClassicalInvolution.PhanP
