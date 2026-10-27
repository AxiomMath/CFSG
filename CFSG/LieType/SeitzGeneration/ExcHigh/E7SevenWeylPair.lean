module

public import CFSG.RankThree.PartOne.KE.EDualStabilizer

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootSpace CFSG.RankThree.PartOne.KE
open CFSG.RankThree.E6 (charVal charVal_single)

variable {τ : Tag}

theorem int_eq_zero_of_add_sqrt_two_mul {a b : ℤ}
    (h : (a : ℝ) + Real.sqrt 2 * (b : ℝ) = 0) : a = 0 ∧ b = 0 := by
  by_cases hb : b = 0
  · subst hb
    simp only [Int.cast_zero, mul_zero, add_zero, Int.cast_eq_zero] at h
    exact ⟨h, rfl⟩
  · exfalso
    apply irrational_sqrt_two
    refine ⟨-(a : ℚ) / b, ?_⟩
    have hb' : (b : ℝ) ≠ 0 := Int.cast_ne_zero.2 hb
    push_cast
    field_simp
    linarith

theorem mem_closure_of_charVal_int
    (r : Fin τ.rank → ℤ) {w : WeylGroup τ} (hw : ∀ x, charVal r (w • x) = charVal r x) :
    w ∈ Subgroup.closure {s | ∃ α, IsRoot τ α ∧ charVal r α = 0 ∧ s = rootReflection α} := by
  have hmem : w ∈ dualWeylStabilizer r := hw
  have hfix : w ∈ weylStabilizer τ (dualVector r) :=
    weylAct_dualVector_eq fun v => mem_dualWeylStabilizer.1 ((dualWeylStabilizer r).inv_mem hmem) v
  rw [(exceptional_Lang_Weyl_chamber_point_stabilizers τ).2.2.2.2.2] at hfix
  refine Subgroup.closure_mono ?_ hfix
  rintro _ ⟨α, hα, h0, rfl⟩
  rw [inner_ofLattice_dualVector, Int.cast_eq_zero] at h0
  exact ⟨α, hα, h0, rfl⟩

theorem closure_rootReflection_eq_top :
    Subgroup.closure {s | ∃ α, IsRoot τ α ∧ s = rootReflection α} =
      (⊤ : Subgroup (WeylGroup τ)) := by
  rw [eq_top_iff, ← (coxeterSystem τ).subgroup_closure_range_simple, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  refine Subgroup.subset_closure ⟨Pi.single i 1, isRoot_single τ i, ?_⟩
  rw [rootReflection_eq_conj (w := 1) (j := i) (one_smul _ _), one_mul, inv_one, mul_one]

theorem inf_dualWeylStabilizer_le_closure_of_card
    {p : ℕ} [Fact p.Prime] (z₀ z₁ : Fin τ.rank → ZMod p)
    (hU : ¬ p ∣ Nat.card ↥(dualWeylStabilizer z₀ ⊓ dualWeylStabilizer z₁)) :
    dualWeylStabilizer z₀ ⊓ dualWeylStabilizer z₁ ≤
      Subgroup.closure {s | ∃ α ∈ rootKernel z₀ ∩ rootKernel z₁, s = rootReflection α} := by
  classical
  set U := dualWeylStabilizer z₀ ⊓ dualWeylStabilizer z₁ with hUdef
  have : Fintype U := Fintype.ofFinite _
  have hcard : (Fintype.card U : ZMod p) ≠ 0 := by
    intro h
    rw [ZMod.natCast_eq_zero_iff, ← Nat.card_eq_fintype_card] at h
    exact hU h
  have hz : ∀ z : Fin τ.rank → ZMod p, U ≤ dualWeylStabilizer z →
      ∀ α, charVal (avgColumn U (intLift z)) α = 0 → charVal z α = 0 := by
    intro z hUz α h
    have h' := charVal_avgColumn_cast hUz α
    rw [h, Int.cast_zero, eq_comm] at h'
    exact (mul_eq_zero.1 h').resolve_left hcard
  intro w hw
  have hwinv : w⁻¹ ∈ U := U.inv_mem hw
  have hfix : w ∈ weylStabilizer τ (dualVector (avgColumn U (intLift z₀)) +
      Real.sqrt 2 • dualVector (avgColumn U (intLift z₁))) := by
    rw [mem_weylStabilizer, map_add, map_smul,
      weylAct_dualVector_eq fun v => charVal_avgColumn_smul _ hwinv v,
      weylAct_dualVector_eq fun v => charVal_avgColumn_smul _ hwinv v]
  rw [(exceptional_Lang_Weyl_chamber_point_stabilizers τ).2.2.2.2.2] at hfix
  refine Subgroup.closure_mono ?_ hfix
  rintro _ ⟨α, hα, h0, rfl⟩
  rw [inner_add_right, real_inner_smul_right, inner_ofLattice_dualVector,
    inner_ofLattice_dualVector] at h0
  obtain ⟨h0', h1'⟩ := int_eq_zero_of_add_sqrt_two_mul h0
  exact ⟨α, ⟨⟨hα, hz z₀ inf_le_left α h0'⟩, ⟨hα, hz z₁ inf_le_right α h1'⟩⟩, rfl⟩

end CFSG.LieType.SeitzGeneration.ExcHigh

end
