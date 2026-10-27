module

public import Mathlib.LinearAlgebra.SpecialLinearGroup

public section

namespace CFSG.LinearAlgebra.RootGroupSL

variable {k E V : Type} [Field k] [Field E] [Algebra k E] [AddCommGroup V] [Module k V]

private lemma mul_apply (g h : SpecialLinearGroup k V) (v : V) : (g * h) v = g (h v) := rfl

private lemma inv_apply (g : SpecialLinearGroup k V) (v : V) :
    g⁻¹ v = (g : V ≃ₗ[k] V).symm v := rfl

private lemma apply_inv_apply (g : SpecialLinearGroup k V) (v : V) : g (g⁻¹ v) = v := by
  rw [inv_apply]
  exact LinearEquiv.apply_symm_apply (g : V ≃ₗ[k] V) v

private lemma apply_inv_eq_iff (g : SpecialLinearGroup k V) (u v : V) :
    g⁻¹ v = u ↔ v = g u := by
  rw [inv_apply]
  exact (g : V ≃ₗ[k] V).symm_apply_eq

private lemma one_apply (v : V) : (1 : SpecialLinearGroup k V) v = v := rfl

private lemma apply_add (g : SpecialLinearGroup k V) (v w : V) : g (v + w) = g v + g w :=
  map_add (g : V →ₗ[k] V) v w

@[expose] def datumQ (ι : E →ₗ[k] V) (π : V →ₗ[k] E) :
    Subgroup (SpecialLinearGroup k V) where
  carrier := {g | (∀ t, g (ι t) = ι t) ∧ (∀ v, π v = 0 → g v - v ∈ LinearMap.range ι) ∧
    ∀ v, π (g v - v) = 0}
  mul_mem' := by
    rintro g h ⟨hg1, hg2, hg3⟩ ⟨hh1, hh2, hh3⟩
    refine ⟨?_, ?_, ?_⟩
    · intro t
      rw [mul_apply, hh1 t, hg1 t]
    · intro v hv
      have hπ : π (h v) = 0 := by
        have h1 : h v = (h v - v) + v := by abel
        rw [h1, map_add, hh3 v, hv, add_zero]
      have h1 : g (h v) - h v ∈ LinearMap.range ι := hg2 (h v) hπ
      have h2 : h v - v ∈ LinearMap.range ι := hh2 v hv
      have heq : g (h v) - v = (g (h v) - h v) + (h v - v) := by abel
      rw [mul_apply, heq]
      exact Submodule.add_mem (LinearMap.range ι) h1 h2
    · intro v
      have heq : g (h v) - v = (g (h v) - h v) + (h v - v) := by abel
      rw [mul_apply, heq, map_add, hg3 (h v), hh3 v, add_zero]
  one_mem' := by
    refine ⟨?_, ?_, ?_⟩
    · intro t
      exact one_apply (ι t)
    · intro v hv
      rw [one_apply, sub_self]
      exact Submodule.zero_mem (LinearMap.range ι)
    · intro v
      rw [one_apply, sub_self, map_zero]
  inv_mem' := by
    rintro g ⟨hg1, hg2, hg3⟩
    refine ⟨?_, ?_, ?_⟩
    · intro t
      exact (apply_inv_eq_iff g (ι t) (ι t)).mpr (hg1 t).symm
    · intro v hv
      have hsub : π (v - g⁻¹ v) = 0 := by
        simpa [apply_inv_apply g v] using hg3 (g⁻¹ v)
      have hpu : π (g⁻¹ v) = 0 := by
        have h1 : g⁻¹ v = v - (v - g⁻¹ v) := by abel
        rw [h1, map_sub, hv, hsub, sub_zero]
      have hmem : v - g⁻¹ v ∈ LinearMap.range ι := by
        simpa [apply_inv_apply g v] using hg2 (g⁻¹ v) hpu
      simpa [neg_sub] using Submodule.neg_mem (LinearMap.range ι) hmem
    · intro v
      have h : g⁻¹ v - v = -(g (g⁻¹ v) - g⁻¹ v) := by
        rw [apply_inv_apply g v, neg_sub]
      rw [h, map_neg, hg3 (g⁻¹ v), neg_zero]

@[expose] def datumQ0 (ι : E →ₗ[k] V) (π : V →ₗ[k] E) :
    Subgroup (SpecialLinearGroup k V) where
  carrier := {g | (∀ v, g v - v ∈ LinearMap.range ι) ∧ ∀ v, π v = 0 → g v = v}
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    refine ⟨?_, ?_⟩
    · intro v
      have h1 : g (h v) - h v ∈ LinearMap.range ι := hg1 (h v)
      have h2 : h v - v ∈ LinearMap.range ι := hh1 v
      have heq : g (h v) - v = (g (h v) - h v) + (h v - v) := by abel
      rw [mul_apply, heq]
      exact Submodule.add_mem (LinearMap.range ι) h1 h2
    · intro v hv
      rw [mul_apply, hh2 v hv, hg2 v hv]
  one_mem' := by
    refine ⟨?_, ?_⟩
    · intro v
      rw [one_apply, sub_self]
      exact Submodule.zero_mem (LinearMap.range ι)
    · intro v hv
      exact one_apply v
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    refine ⟨?_, ?_⟩
    · intro v
      have hmem : v - g⁻¹ v ∈ LinearMap.range ι := by
        simpa [apply_inv_apply g v] using hg1 (g⁻¹ v)
      simpa [neg_sub] using Submodule.neg_mem (LinearMap.range ι) hmem
    · intro v hv
      exact (apply_inv_eq_iff g v v).mpr (hg2 v hv).symm

@[expose] def datumU1 (ι : E →ₗ[k] V) : Subgroup (SpecialLinearGroup k V) where
  carrier := {g | (∀ v, g v - v ∈ LinearMap.range ι) ∧ ∀ t, g (ι t) = ι t}
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    refine ⟨?_, ?_⟩
    · intro v
      have h1 : g (h v) - h v ∈ LinearMap.range ι := hg1 (h v)
      have h2 : h v - v ∈ LinearMap.range ι := hh1 v
      have heq : g (h v) - v = (g (h v) - h v) + (h v - v) := by abel
      rw [mul_apply, heq]
      exact Submodule.add_mem (LinearMap.range ι) h1 h2
    · intro t
      rw [mul_apply, hh2 t, hg2 t]
  one_mem' := by
    refine ⟨?_, ?_⟩
    · intro v
      rw [one_apply, sub_self]
      exact Submodule.zero_mem (LinearMap.range ι)
    · intro t
      exact one_apply (ι t)
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    refine ⟨?_, ?_⟩
    · intro v
      have hmem : v - g⁻¹ v ∈ LinearMap.range ι := by
        simpa [apply_inv_apply g v] using hg1 (g⁻¹ v)
      simpa [neg_sub] using Submodule.neg_mem (LinearMap.range ι) hmem
    · intro t
      exact (apply_inv_eq_iff g (ι t) (ι t)).mpr (hg2 t).symm

@[expose] def datumU2 (π : V →ₗ[k] E) : Subgroup (SpecialLinearGroup k V) where
  carrier := {g | (∀ v, π (g v - v) = 0) ∧ ∀ v, π v = 0 → g v = v}
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    refine ⟨?_, ?_⟩
    · intro v
      have heq : g (h v) - v = (g (h v) - h v) + (h v - v) := by abel
      rw [mul_apply, heq, map_add, hg1 (h v), hh1 v, add_zero]
    · intro v hv
      rw [mul_apply, hh2 v hv, hg2 v hv]
  one_mem' := by
    refine ⟨?_, ?_⟩
    · intro v
      rw [one_apply, sub_self, map_zero]
    · intro v hv
      exact one_apply v
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    refine ⟨?_, ?_⟩
    · intro v
      have h : g⁻¹ v - v = -(g (g⁻¹ v) - g⁻¹ v) := by
        rw [apply_inv_apply g v, neg_sub]
      rw [h, map_neg, hg1 (g⁻¹ v), neg_zero]
    · intro v hv
      exact (apply_inv_eq_iff g v v).mpr (hg2 v hv).symm

theorem datumQ0_le_datumQ (ι : E →ₗ[k] V) (π : V →ₗ[k] E) (h : ∀ t, π (ι t) = 0) :
    datumQ0 ι π ≤ datumQ ι π := by
  intro g hg
  obtain ⟨hg1, hg2⟩ := hg
  refine ⟨?_, ?_, ?_⟩
  · intro t
    exact hg2 (ι t) (h t)
  · intro v hv
    exact hg1 v
  · intro v
    obtain ⟨t, ht⟩ := hg1 v
    rw [← ht, h t]

theorem datumQ0_commute_datumQ (ι : E →ₗ[k] V) (π : V →ₗ[k] E) {q z : SpecialLinearGroup k V}
    (hq : q ∈ datumQ ι π) (hz : z ∈ datumQ0 ι π) : q * z = z * q := by
  obtain ⟨hq1, hq2, hq3⟩ := hq
  obtain ⟨hz1, hz2⟩ := hz
  apply SpecialLinearGroup.ext
  intro v
  rw [mul_apply, mul_apply]
  set w : V := z v - v with hw
  have hwW : w ∈ LinearMap.range ι := hz1 v
  obtain ⟨t, ht⟩ := hwW
  have hqw : q w = w := by rw [← ht, hq1 t]
  have hzv : z v = v + w := by rw [hw]; abel
  have hqzv : q (z v) = q v + w := by
    rw [hzv, apply_add, hqw]
  have hker : π (q v - v) = 0 := hq3 v
  have hzq : z (q v) = (q v - v) + (v + w) := by
    have h1 : q v = (q v - v) + v := by abel
    calc z (q v) = z ((q v - v) + v) := congrArg z h1
      _ = z (q v - v) + z v := by rw [apply_add]
      _ = (q v - v) + (v + w) := by rw [hz2 (q v - v) hker, hzv]
  rw [hqzv, hzq]
  abel

end CFSG.LinearAlgebra.RootGroupSL
