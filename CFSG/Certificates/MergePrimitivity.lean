module

public import CFSG.Certificates.InvariantMerge
public import Mathlib.GroupTheory.GroupAction.Primitive

public section

namespace CFSG.Certificates

open scoped Pointwise

variable {n m : ℕ}

theorem stabilizer_orbit_merge_primitivity (S : Fin m → Equiv.Perm (Fin n))
    [htrans : MulAction.IsPretransitive (Subgroup.closure (Set.range S)) (Fin n)]
    (b : Fin n) (H : Subgroup (Equiv.Perm (Fin n))) (hHP : H ≤ Subgroup.closure (Set.range S))
    (hHb : ∀ h ∈ H, h b = b) {J : Type*} (xs : J → Fin n)
    (hcover : ∀ x, x ≠ b → ∃ j, ∃ h ∈ H, h (xs j) = x)
    (hmerge : ∀ j, ∃ L, ValidInvariantMerge S b (xs j) L) :
    MulAction.IsPreprimitive (Subgroup.closure (Set.range S)) (Fin n) := by
  set P := Subgroup.closure (Set.range S)
  have hsmul : ∀ (g : P) (y : Fin n), g • y = (g : Equiv.Perm (Fin n)) y := fun _ _ => rfl
  refine MulAction.IsPreprimitive.of_isTrivialBlock_base b fun {B} hbB hB => ?_
  by_cases hsub : B.Subsingleton
  · exact Or.inl hsub
  right
  obtain ⟨x, hxB, hxb⟩ : ∃ x ∈ B, x ≠ b := by
    by_contra! h
    exact hsub fun u hu v hv => (h u hu).trans (h v hv).symm
  obtain ⟨j, h, hH, rfl⟩ := hcover x hxb
  have hjB : xs j ∈ B := by
    have hhP : h⁻¹ ∈ P := hHP (inv_mem hH)
    have heq : (⟨h⁻¹, hhP⟩ : P) • B = (1 : P) • B := by
      refine hB.smul_eq_smul_of_nonempty ⟨b, ?_, by rw [one_smul]; exact hbB⟩
      refine Set.mem_smul_set.2 ⟨b, hbB, ?_⟩
      rw [hsmul]
      exact hHb _ (inv_mem hH)
    rw [one_smul] at heq
    rw [← heq]
    refine Set.mem_smul_set.2 ⟨h (xs j), hxB, ?_⟩
    rw [hsmul]
    simp
  let R : Fin n → Fin n → Prop := fun u v => ∃ g : P, u ∈ g • B ∧ v ∈ g • B
  have hR : Equivalence R := by
    refine ⟨fun u => ?_, fun ⟨g, hu, hv⟩ => ⟨g, hv, hu⟩, fun ⟨g, hu, hv⟩ ⟨g', hv', hw⟩ => ?_⟩
    · obtain ⟨g, hg⟩ := MulAction.exists_smul_eq P b u
      exact ⟨g, Set.mem_smul_set.2 ⟨b, hbB, hg⟩, Set.mem_smul_set.2 ⟨b, hbB, hg⟩⟩
    · have heq : g • B = g' • B := hB.smul_eq_smul_of_nonempty ⟨_, hv, hv'⟩
      exact ⟨g, hu, heq ▸ hw⟩
  have hinv : ∀ p ∈ P, ∀ u v, R u v → R (p u) (p v) := by
    rintro p hp u v ⟨g, hu, hv⟩
    obtain ⟨u', hu', rfl⟩ := Set.mem_smul_set.1 hu
    obtain ⟨v', hv', rfl⟩ := Set.mem_smul_set.1 hv
    refine ⟨⟨p, hp⟩ * g, Set.mem_smul_set.2 ⟨u', hu', ?_⟩, Set.mem_smul_set.2 ⟨v', hv', ?_⟩⟩ <;>
      rw [mul_smul] <;> rfl
  obtain ⟨L, hL⟩ := hmerge j
  have huniv := invariant_merge_soundness S b (xs j) L hL R hR hinv
    ⟨1, by rw [one_smul]; exact hbB, by rw [one_smul]; exact hjB⟩
  refine Set.eq_univ_of_forall fun y => ?_
  obtain ⟨g, hb, hy⟩ := huniv b y
  have heq : g • B = (1 : P) • B :=
    hB.smul_eq_smul_of_nonempty ⟨b, hb, by rw [one_smul]; exact hbB⟩
  rw [heq, one_smul] at hy
  exact hy

end CFSG.Certificates
