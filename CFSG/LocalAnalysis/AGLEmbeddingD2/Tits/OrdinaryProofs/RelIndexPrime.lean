module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.GroupTheory.Index

public section

namespace CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs

variable {G : Type*} [Group G]

theorem eq_or_eq_of_relIndex_prime {R S P : Subgroup G} (hRS : R ≤ S) (hSP : S ≤ P)
    (hp : (R.relIndex P).Prime) : S = R ∨ S = P := by
  have h : R.relIndex S * S.relIndex P = R.relIndex P := Subgroup.relIndex_mul_relIndex R S P hRS hSP
  rcases (Nat.dvd_prime hp).1 (Dvd.intro _ h) with h1 | h1
  · exact Or.inl (le_antisymm (Subgroup.relIndex_eq_one.mp h1) hRS)
  · have hx : S.relIndex P = 1 := by
      rw [h1] at h
      exact Nat.eq_of_mul_eq_mul_left hp.pos (h.trans (mul_one _).symm)
    exact Or.inr (le_antisymm hSP (Subgroup.relIndex_eq_one.mp hx))

theorem relIndex_sup_eq_three_of_mul {R P : Subgroup G} (hP : Nat.card P = 3)
    (hinf : P ⊓ R = ⊥) (hPR : ∀ x ∈ P ⊔ R, ∃ p ∈ P, ∃ r ∈ R, x = p * r) :
    R.relIndex (P ⊔ R) = 3 := by
  have hbij : Function.Bijective
      (fun p : P => (((⟨p.1, Subgroup.mem_sup_left p.2⟩ : ↥(P ⊔ R : Subgroup G))) :
        ↥(P ⊔ R : Subgroup G) ⧸ R.subgroupOf (P ⊔ R))) := by
    constructor
    · rintro ⟨p, hp⟩ ⟨p', hp'⟩ h
      dsimp only at h
      have h2 := QuotientGroup.eq.mp h
      rw [Subgroup.mem_subgroupOf] at h2
      have hmem : p⁻¹ * p' ∈ P ⊓ R :=
        ⟨P.mul_mem (P.inv_mem hp) hp', by simpa using h2⟩
      rw [hinf, Subgroup.mem_bot] at hmem
      have hpp : p = p' := inv_mul_eq_one.mp hmem
      subst hpp
      rfl
    · intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨p, hp, r, hr, hx⟩ := hPR x.1 x.2
      refine ⟨⟨p, hp⟩, ?_⟩
      dsimp only
      apply QuotientGroup.eq.mpr
      rw [Subgroup.mem_subgroupOf]
      simpa [hx] using hr
  have hcard : Nat.card (↥(P ⊔ R : Subgroup G) ⧸ R.subgroupOf (P ⊔ R)) = Nat.card P :=
    (Nat.card_congr (Equiv.ofBijective _ hbij)).symm
  unfold Subgroup.relIndex Subgroup.index
  rw [hcard, hP]

end CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs
