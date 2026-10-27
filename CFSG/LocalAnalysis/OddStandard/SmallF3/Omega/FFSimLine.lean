module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFSimPair

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ff_span_inter_eq_line {u w₁ w₂ x : V} (hu : Q u ≠ 0) (h₁ : polar Q u w₁ = 0)
    (h₂ : polar Q u w₂ = 0) (hw : LinearIndependent (ZMod 3) ![w₁, w₂])
    (hx₁ : x ∈ Submodule.span (ZMod 3) {u, w₁}) (hx₂ : x ∈ Submodule.span (ZMod 3) {u, w₂}) :
    ∃ c : ZMod 3, x = c • u := by
  obtain ⟨a₁, b₁, hx₁⟩ := Submodule.mem_span_pair.mp hx₁
  obtain ⟨a₂, b₂, hx₂⟩ := Submodule.mem_span_pair.mp hx₂
  have hp₁ : polar Q u x = a₁ • (2 • Q u) := by
    rw [← hx₁, polar_add_right, polar_smul_right, polar_smul_right, polar_self, h₁,
      smul_zero, add_zero]
  have hp₂ : polar Q u x = a₂ • (2 • Q u) := by
    rw [← hx₂, polar_add_right, polar_smul_right, polar_smul_right, polar_self, h₂,
      smul_zero, add_zero]
  have hD : (2 : ZMod 3) * Q u ≠ 0 := mul_ne_zero (by decide) hu
  have ha : a₁ = a₂ := by
    apply mul_right_cancel₀ hD
    simpa [smul_eq_mul, nsmul_eq_mul] using hp₁.symm.trans hp₂
  have hb : b₁ • w₁ = b₂ • w₂ := by
    have h := hx₁.trans hx₂.symm
    rw [ha] at h
    exact add_left_cancel h
  have hz : b₁ • w₁ + (-b₂) • w₂ = 0 := by
    rw [neg_smul, ← sub_eq_add_neg, sub_eq_zero]
    exact hb
  have hb₁ : b₁ = 0 := ((LinearIndependent.pair_iff.mp hw) b₁ (-b₂) hz).1
  exact ⟨a₁, by rw [← hx₁, hb₁, zero_smul, add_zero]⟩

theorem ff_simAct_line (hQ : Q.Nondegenerate) (h5 : 5 ≤ Module.finrank (ZMod 3) V)
    (γ : simGroup Q)
    (hγ : ∀ t ∈ omegaGroup hQ, simAct Q γ t = t ∨ simAct Q γ t = piOrth Q * t)
    {u : V} (hu : Q u ≠ 0) : ∃ c : ZMod 3, (γ : V ≃ₗ[ZMod 3] V) u = c • u := by
  obtain ⟨w₁, w₂, hw₁, hw₂, hQw₁, hQw₂, hw⟩ :=
    ff_exists_orth_single_pair hQ (by omega) hu (d := Q u) hu
  exact ff_span_inter_eq_line hu hw₁ hw₂ hw
    (ff_simAct_pair hQ h5 γ hγ hu (hv := hQw₁) (huv := hw₁))
    (ff_simAct_pair hQ h5 γ hγ hu (hv := hQw₂) (huv := hw₂))

end CFSG.OddStandard.SmallF3.Omega
