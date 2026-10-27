module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import CFSG.LargeExtraspecial.A2ModSL

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.BGL

open scoped IntermediateField

variable {F : Type} [Field F] {σ : F ≃+* F}

theorem finite_ringAut [Finite F] : Finite (F ≃+* F) :=
  Finite.of_injective (fun e : F ≃+* F => (e : F → F)) DFunLike.coe_injective

theorem mem_fixedField_iff {x : F} :
    x ∈ FixedPoints.subfield (Subgroup.zpowers σ) F ↔ σ x = x := by
  constructor
  · intro h
    exact h ⟨σ, Subgroup.mem_zpowers σ⟩
  · intro h g
    have hle : Subgroup.zpowers σ ≤ MulAction.stabilizer (F ≃+* F) x :=
      (Subgroup.zpowers_le).mpr (by rw [MulAction.mem_stabilizer_iff]; exact h)
    exact hle g.2

theorem finrank_fixed_eq_orderOf [Finite F] :
    Module.finrank (FixedPoints.subfield (Subgroup.zpowers σ) F) F = orderOf σ := by
  have := finite_ringAut (F := F)
  let _ : Fintype (Subgroup.zpowers σ) := Fintype.ofFinite _
  rw [FixedPoints.finrank_eq_card, ← Nat.card_eq_fintype_card, Nat.card_zpowers]

theorem orderOf_prime_of_three (h3 : orderOf σ = 3) : (orderOf σ).Prime := h3 ▸ Nat.prime_three

theorem subring_eq_top_of_not_fixed [Finite F] (hr : (orderOf σ).Prime) {R : Subring F}
    (hR : ∀ x, σ x = x → x ∈ R) {t : F} (ht : t ∈ R) (hσt : σ t ≠ t) (s : F) : s ∈ R := by
  set K₀ := FixedPoints.subfield (Subgroup.zpowers σ) F
  have hfin : Module.finrank K₀ F = orderOf σ := finrank_fixed_eq_orderOf
  have : FiniteDimensional K₀ F := Module.finite_of_finrank_pos (by rw [hfin]; exact hr.pos)
  have hdvd : Module.finrank K₀ K₀⟮t⟯ ∣ orderOf σ := by
    have h := IntermediateField.finrank_dvd_of_le_right (K := K₀) (L := F) (F := K₀⟮t⟯)
      (E := ⊤) le_top
    rwa [IntermediateField.finrank_top', hfin] at h
  have htop : K₀⟮t⟯ = ⊤ := by
    rcases (Nat.dvd_prime hr).mp hdvd with h | h
    · exfalso
      rw [IntermediateField.finrank_eq_one_iff] at h
      have hmem : t ∈ K₀⟮t⟯ := IntermediateField.mem_adjoin_simple_self K₀ t
      rw [h, IntermediateField.mem_bot] at hmem
      obtain ⟨c, hc⟩ := hmem
      apply hσt
      rw [← hc]
      exact (mem_fixedField_iff).mp c.2
    · exact IntermediateField.eq_of_le_of_finrank_eq le_top
        (by rw [h, IntermediateField.finrank_top', hfin])
  let R' : Subalgebra K₀ F :=
    { R with algebraMap_mem' := fun c => hR _ ((mem_fixedField_iff).mp c.2) }
  have hle : Algebra.adjoin K₀ {t} ≤ R' :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr (show t ∈ R' from ht))
  have hs : s ∈ K₀⟮t⟯ := by rw [htop]; trivial
  rw [← IntermediateField.mem_toSubalgebra,
    IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (IsAlgebraic.of_finite K₀ t)]
    at hs
  exact hle hs

end CFSG.HardMathSupport.Solomon.Coordinator.BGL
