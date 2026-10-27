module

public import CFSG.ClassicalInvolution.Q3.TL4ExitDichA
public import CFSG.ClassicalInvolution.Q3.TL4S3DichB

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77

namespace MF163

variable {X : Type} [Group X] [Finite X]

theorem Concl163Syl.of_conj {R : Subgroup X} {S : Sylow 2 R} {z : X} (hD : TightDatum R S z)
    (h : Concl163Syl R S z) {M : Subgroup X} (hM : M ∈ CoreAssembly.conjClass (tightCore R))
    {a : X} (ha : IsUniqueInvolution M a) {P : Subgroup X} (hP : IsSylow2In P M)
    {β : MulAut X} (hβ2 : β * β = 1) (hβP : ∀ x ∈ P, β x = x) :
    β = 1 ∨ β = MulAut.conj a := by
  obtain ⟨g, rfl⟩ := hM
  obtain ⟨x, -, hx⟩ :=
    Asc77.exists_conjSub_eq_of_isSylow2In hD.sylow_core (S3Dich.isSylow2In_conj g hP)
  obtain ⟨c, hcS⟩ : ∃ c : X, conjSub c ((S : Subgroup R).map R.subtype) = P :=
    ⟨g * x, by rw [conjSub_mul, hx, conjSub_conjSub_inv]⟩
  have hmem : ∀ s ∈ (S : Subgroup R).map R.subtype, c * s * c⁻¹ ∈ P := fun s hs =>
    hcS ▸ conj_mem_conjSub hs
  let β' : MulAut X := (MulAut.conj c)⁻¹ * β * MulAut.conj c
  have hβ : β = MulAut.conj c * β' * (MulAut.conj c)⁻¹ := by
    simp only [β']
    group
  have hβ'2 : β' * β' = 1 := by
    calc β' * β' = (MulAut.conj c)⁻¹ * (β * β) * MulAut.conj c := by
          simp only [β']
          group
      _ = 1 := by rw [hβ2, mul_one, inv_mul_cancel]
  have hβ'S : ∀ s ∈ (S : Subgroup R).map R.subtype, β' s = s := fun s hs => by
    simp only [β', MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply, hβP _ (hmem s hs)]
    group
  have hza : c * z * c⁻¹ = a := by
    have hz2 : z * z = 1 := by rw [← pow_two, ← hD.order, pow_orderOf_eq_one]
    have h1 : c * z * c⁻¹ * (c * z * c⁻¹) = 1 := by
      rw [show c * z * c⁻¹ * (c * z * c⁻¹) = c * (z * z) * c⁻¹ by group, hz2, mul_one,
        mul_inv_cancel]
    refine (ha.unique _ (hP.1 (hmem z hD.mem)) h1).resolve_left fun h2 => ?_
    have := hD.order
    rw [conj_eq_one_iff.mp h2, orderOf_one] at this
    exact absurd this (by norm_num)
  rcases h β' hβ'2 hβ'S with h1 | h1
  · left
    rw [hβ, h1, mul_one, mul_inv_cancel]
  · right
    rw [hβ, h1, ← hza, map_mul, map_mul, map_inv]

end MF163

end CFSG.ClassicalInvolution.Q3.TL4
