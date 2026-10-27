module

public import TauCeti.GroupTheory.SemidirectProduct

public section

namespace CFSG.GroupTheory

theorem ker_sup_eq_of_normalizer
    {X Y : Type*} [Group X] [Group Y]
    (f : X →* Y) (P Q : Subgroup X)
    (hnorm : Q ≤ Subgroup.normalizer (P : Set X))
    (himg : P.map f ⊓ Q.map f = ⊥) :
    (P ⊔ Q) ⊓ f.ker = (P ⊓ f.ker) ⊔ (Q ⊓ f.ker) := by
  refine le_antisymm ?_
    (sup_le (inf_le_inf_right f.ker le_sup_left) (inf_le_inf_right f.ker le_sup_right))
  intro x hx
  obtain ⟨hx_sup, hx_ker⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨p, hp, q, hq, hxpq⟩ :=
    (TauCeti.Subgroup.mem_sup_of_right_le_normalizer_left
      (H := P) (K := Q) hnorm).1 hx_sup
  have hxker : f x = 1 := MonoidHom.mem_ker.mp hx_ker
  rw [hxpq] at hxker ⊢
  rw [map_mul] at hxker
  have hpP : f p ∈ P.map f := ⟨p, hp, rfl⟩
  have hqQ : f q ∈ Q.map f := ⟨q, hq, rfl⟩
  have hpinv : f p = (f q)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]
    exact hxker
  have hpQ : f p ∈ Q.map f := by
    rw [hpinv]
    exact Subgroup.inv_mem _ hqQ
  have hfp1 : f p = 1 := by
    have hbot : f p ∈ (⊥ : Subgroup Y) := by
      rw [← himg]
      exact Subgroup.mem_inf.mpr ⟨hpP, hpQ⟩
    exact Subgroup.mem_bot.mp hbot
  have hfq1 : f q = 1 := by
    rw [hfp1, one_mul] at hxker
    exact hxker
  exact Subgroup.mul_mem_sup
    (Subgroup.mem_inf.mpr ⟨hp, MonoidHom.mem_ker.mpr hfp1⟩)
    (Subgroup.mem_inf.mpr ⟨hq, MonoidHom.mem_ker.mpr hfq1⟩)

end CFSG.GroupTheory

end
