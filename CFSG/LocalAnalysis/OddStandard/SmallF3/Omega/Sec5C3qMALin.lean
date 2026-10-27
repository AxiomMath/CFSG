module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Frame

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem sec5c3qma_repr_eq_zero_of_comm (fr : NFrame Q (Fin 6) 1) {Z : Finset (Fin 6)}
    {g : OGroup Q} (hcomm : g * fr.signChange Z = fr.signChange Z * g) {i l : Fin 6}
    (hi : i ∈ Z) (hl : l ∉ Z) :
    fr.b.repr ((g : V ≃ₗ[ZMod 3] V) (fr.b i)) l = 0 := by
  have h1 : (g : V ≃ₗ[ZMod 3] V) (((fr.signChange Z : OGroup Q) : V ≃ₗ[ZMod 3] V) (fr.b i)) =
      ((fr.signChange Z : OGroup Q) : V ≃ₗ[ZMod 3] V) ((g : V ≃ₗ[ZMod 3] V) (fr.b i)) := by
    have := congrArg (fun e : OGroup Q => (e : V ≃ₗ[ZMod 3] V) (fr.b i)) hcomm
    simpa only [Subgroup.coe_mul, Submonoid.coe_mul, LinearEquiv.mul_apply] using this
  rw [fr.signChange_basis Z i, if_pos hi, map_neg] at h1
  have h2 := congrArg (fun v => fr.b.repr v l) h1
  simp only [map_neg, Finsupp.neg_apply, fr.repr_signChange, if_neg hl] at h2
  generalize fr.b.repr ((g : V ≃ₗ[ZMod 3] V) (fr.b i)) l = x at h2 ⊢
  revert x
  decide

theorem sec5c3qma_signChange_conj (fr : NFrame Q (Fin 6) 1) {Z J : Finset (Fin 6)}
    (hJ : ∀ i ∈ Z, ∀ j ∈ Z, (i ∈ J ↔ j ∈ J)) {g : OGroup Q}
    (hcomm : g * fr.signChange Z = fr.signChange Z * g)
    (hfix : ∀ j ∉ Z, (g : V ≃ₗ[ZMod 3] V) (fr.b j) = fr.b j) :
    fr.signChange J * g * (fr.signChange J)⁻¹ = g := by
  have hinv : (fr.signChange J)⁻¹ = fr.signChange J :=
    inv_eq_of_mul_eq_one_right (fr.signChange_mul_self J)
  rw [hinv]
  apply Subtype.ext
  apply fr.b.ext'
  intro i
  simp only [Subgroup.coe_mul, Submonoid.coe_mul, LinearEquiv.mul_apply]
  rw [fr.signChange_basis J i]
  by_cases hiZ : i ∈ Z
  · have hkey : ((fr.signChange J : OGroup Q) : V ≃ₗ[ZMod 3] V)
        ((g : V ≃ₗ[ZMod 3] V) (fr.b i)) =
        if i ∈ J then -((g : V ≃ₗ[ZMod 3] V) (fr.b i)) else (g : V ≃ₗ[ZMod 3] V) (fr.b i) := by
      apply fr.b.ext_elem
      intro l
      rw [fr.repr_signChange]
      by_cases hl : l ∈ Z
      · by_cases hiJ : i ∈ J
        · have hlJ : l ∈ J := (hJ i hiZ l hl).mp hiJ
          simp [hiJ, hlJ]
        · have hlJ : l ∉ J := fun h => hiJ ((hJ i hiZ l hl).mpr h)
          simp [hiJ, hlJ]
      · have h0 := sec5c3qma_repr_eq_zero_of_comm fr hcomm hiZ hl
        by_cases hiJ : i ∈ J <;> simp [hiJ, h0]
    by_cases hiJ : i ∈ J
    · rw [if_pos hiJ, map_neg, map_neg, hkey, if_pos hiJ, neg_neg]
    · rw [if_neg hiJ, hkey, if_neg hiJ]
  · by_cases hiJ : i ∈ J
    · rw [if_pos hiJ, map_neg, map_neg, hfix i hiZ, fr.signChange_basis J i, if_pos hiJ, neg_neg]
    · rw [if_neg hiJ, hfix i hiZ, fr.signChange_basis J i, if_neg hiJ]

end CFSG.OddStandard.SmallF3.Omega
