module

public import Mathlib.LinearAlgebra.Projectivization.Cardinality
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open Module

private lemma finrank_comap_mkQ {K : Type*} [Field K] {X : Type*} [AddCommGroup X]
    [Module K X] [FiniteDimensional K X] (p : Submodule K X)
    (q : Submodule K (X ⧸ p)) :
    finrank K (Submodule.comap p.mkQ q) = finrank K q + finrank K p := by
  classical
  let q' : Submodule K X := Submodule.comap p.mkQ q
  let f : q' →ₗ[K] X ⧸ p := p.mkQ.domRestrict q'
  have hker : LinearMap.ker f = Submodule.comap q'.subtype p := by
    ext x
    simp [f, q', Submodule.mem_comap]
  have hrange : LinearMap.range f = q := by
    apply le_antisymm
    · rintro y ⟨x, rfl⟩
      exact x.2
    · intro y hy
      obtain ⟨x, rfl⟩ := p.mkQ_surjective y
      exact ⟨⟨x, hy⟩, rfl⟩
  have h := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange, hker] at h
  have hfin : finrank K (Submodule.comap q'.subtype p) = finrank K p :=
    (Submodule.comapSubtypeEquivOfLe (Submodule.le_comap_mkQ p q)).finrank_eq
  rw [hfin] at h
  exact h.symm

section Count

variable {K : Type*} [Field K] [Fintype K] {W : Type*} [AddCommGroup W] [Module K W]

theorem card_submodule_between_eq_geom_sum {U X : Submodule K W} [FiniteDimensional K X]
    (hUX : U ≤ X) :
    Nat.card {M : Submodule K W // U ≤ M ∧ M ≤ X ∧ finrank K M = finrank K U + 1} =
      ∑ i ∈ Finset.range (finrank K X - finrank K U), Fintype.card K ^ i := by
  classical
  let U' : Submodule K X := U.comap X.subtype
  have hU' : finrank K U' = finrank K U :=
    (Submodule.comapSubtypeEquivOfLe hUX).finrank_eq
  let e₁ : {M : Submodule K W // U ≤ M ∧ M ≤ X ∧ finrank K M = finrank K U + 1} ≃
      {M : Submodule K X // U' ≤ M ∧ finrank K M = finrank K U' + 1} :=
    { toFun := fun M =>
        ⟨M.1.comap X.subtype, by
          refine ⟨Submodule.comap_mono M.2.1, ?_⟩
          rw [(Submodule.comapSubtypeEquivOfLe M.2.2.1).finrank_eq, M.2.2.2, hU']⟩
      invFun := fun M =>
        ⟨M.1.map X.subtype, by
          refine ⟨?_, Submodule.map_subtype_le X M.1, ?_⟩
          · have hUmap : Submodule.map X.subtype U' = U := by
              rw [Submodule.map_comap_subtype, inf_eq_right.mpr hUX]
            rw [← hUmap]
            exact Submodule.map_mono M.2.1
          · rw [Submodule.finrank_map_subtype_eq, M.2.2, hU']⟩
      left_inv := fun M => by
        apply Subtype.ext
        simp only [Subtype.coe_mk]
        rw [Submodule.map_comap_subtype, inf_eq_right.mpr M.2.2.1]
      right_inv := fun M => by
        apply Subtype.ext
        simp only [Subtype.coe_mk]
        rw [Submodule.comap_map_eq_of_injective (f := X.subtype) (by exact Subtype.val_injective)] }
  let e₂ : {M : Submodule K X // U' ≤ M ∧ finrank K M = finrank K U' + 1} ≃
      {q : Submodule K (X ⧸ U') // finrank K q = 1} :=
    { toFun := fun M =>
        ⟨M.1.map U'.mkQ, by
          have h := finrank_comap_mkQ (p := U') (q := M.1.map U'.mkQ)
          rw [Submodule.comap_map_eq_self (f := U'.mkQ) (p := M.1)
            (by rw [Submodule.ker_mkQ]; exact M.2.1)] at h
          omega⟩
      invFun := fun q =>
        ⟨q.1.comap U'.mkQ, by
          refine ⟨Submodule.le_comap_mkQ U' q.1, ?_⟩
          have h := finrank_comap_mkQ (p := U') (q := q.1)
          rw [q.2] at h
          omega⟩
      left_inv := fun M => by
        apply Subtype.ext
        exact Submodule.comap_map_eq_self (f := U'.mkQ) (p := M.1)
          (by rw [Submodule.ker_mkQ]; exact M.2.1)
      right_inv := fun q => by
        apply Subtype.ext
        exact Submodule.map_comap_eq_of_surjective (f := U'.mkQ) U'.mkQ_surjective q.1 }
  have hcard : Nat.card {M : Submodule K W //
      U ≤ M ∧ M ≤ X ∧ finrank K M = finrank K U + 1} =
      Nat.card {q : Submodule K (X ⧸ U') // finrank K q = 1} :=
    Nat.card_congr (e₁.trans e₂)
  have hproj : Nat.card {q : Submodule K (X ⧸ U') // finrank K q = 1} =
      Nat.card (Projectivization K (X ⧸ U')) :=
    Nat.card_congr (Projectivization.equivSubmodule K (X ⧸ U')).symm
  have hdim : finrank K (X ⧸ U') = finrank K X - finrank K U := by
    rw [Submodule.finrank_quotient, hU']
  rw [hcard, hproj]
  have h := Projectivization.card_of_finrank (k := K) (V := X ⧸ U')
    (n := finrank K X - finrank K U) hdim
  rw [Nat.card_eq_fintype_card (α := K)] at h
  exact h

theorem card_submodule_between_two {U X : Submodule K W} [FiniteDimensional K X]
    (hUX : U ≤ X) (hd : finrank K X = finrank K U + 2) :
    Nat.card {M : Submodule K W // U ≤ M ∧ M ≤ X ∧ finrank K M = finrank K U + 1} =
      Fintype.card K + 1 := by
  have h2 : finrank K U + 2 - finrank K U = 2 := by omega
  rw [card_submodule_between_eq_geom_sum hUX, hd, h2]
  exact geom_sum_two

end Count

end CFSG.Geometry.GeneralizedQuadrangles

end
