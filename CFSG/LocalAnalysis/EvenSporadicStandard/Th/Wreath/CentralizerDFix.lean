module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SylowEndSchur
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.W5

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup SylowEnd

@[expose] def Efix {G : Type} [Group G] (D : Subgroup G) (t : G) : Subgroup G where
  carrier := {c | c ∈ centralizer (D : Set G) ∧ c⁻¹ * (t * c * t⁻¹) ∈ D}
  one_mem' := ⟨Subgroup.one_mem _, by simp⟩
  mul_mem' := by
    rintro a b ⟨haC, haD⟩ ⟨hbC, hbD⟩
    have hbe : b⁻¹ * (a⁻¹ * (t * a * t⁻¹)) * b = a⁻¹ * (t * a * t⁻¹) := by
      have hcomm : b * (a⁻¹ * (t * a * t⁻¹)) = (a⁻¹ * (t * a * t⁻¹)) * b :=
        (mem_centralizer_iff.1 hbC _ haD).symm
      calc b⁻¹ * (a⁻¹ * (t * a * t⁻¹)) * b =
          b⁻¹ * ((a⁻¹ * (t * a * t⁻¹)) * b) := by group
        _ = b⁻¹ * (b * (a⁻¹ * (t * a * t⁻¹))) := by rw [← hcomm]
        _ = a⁻¹ * (t * a * t⁻¹) := by group
    refine ⟨(centralizer (D : Set G)).mul_mem haC hbC, ?_⟩
    have heq : (a * b)⁻¹ * (t * (a * b) * t⁻¹) =
        (a⁻¹ * (t * a * t⁻¹)) * (b⁻¹ * (t * b * t⁻¹)) := by
      calc (a * b)⁻¹ * (t * (a * b) * t⁻¹)
          = b⁻¹ * (a⁻¹ * (t * a * t⁻¹)) * (t * b * t⁻¹) := by group
        _ = (b⁻¹ * (a⁻¹ * (t * a * t⁻¹)) * b) * (b⁻¹ * (t * b * t⁻¹)) := by group
        _ = (a⁻¹ * (t * a * t⁻¹)) * (b⁻¹ * (t * b * t⁻¹)) := by rw [hbe]
    rw [heq]
    exact D.mul_mem haD hbD
  inv_mem' := by
    rintro a ⟨haC, haD⟩
    refine ⟨(centralizer (D : Set G)).inv_mem haC, ?_⟩
    have hcomm : a * (a⁻¹ * (t * a * t⁻¹)) = (a⁻¹ * (t * a * t⁻¹)) * a :=
      (mem_centralizer_iff.1 haC _ haD).symm
    have hcomm_inv : a * (a⁻¹ * (t * a * t⁻¹))⁻¹ = (a⁻¹ * (t * a * t⁻¹))⁻¹ * a := by
      symm
      calc (a⁻¹ * (t * a * t⁻¹))⁻¹ * a
          = (a⁻¹ * (t * a * t⁻¹))⁻¹ * (a * (a⁻¹ * (t * a * t⁻¹))) *
              (a⁻¹ * (t * a * t⁻¹))⁻¹ := by group
        _ = (a⁻¹ * (t * a * t⁻¹))⁻¹ * ((a⁻¹ * (t * a * t⁻¹)) * a) *
              (a⁻¹ * (t * a * t⁻¹))⁻¹ := by rw [hcomm]
        _ = a * (a⁻¹ * (t * a * t⁻¹))⁻¹ := by group
    have hcalc : (a⁻¹)⁻¹ * (t * a⁻¹ * t⁻¹) = (a⁻¹ * (t * a * t⁻¹))⁻¹ := by
      calc (a⁻¹)⁻¹ * (t * a⁻¹ * t⁻¹)
          = a * (t * a⁻¹ * t⁻¹) := by group
        _ = a * ((a⁻¹ * (t * a * t⁻¹))⁻¹ * a⁻¹) := by group
        _ = (a * (a⁻¹ * (t * a * t⁻¹))⁻¹) * a⁻¹ := by group
        _ = ((a⁻¹ * (t * a * t⁻¹))⁻¹ * a) * a⁻¹ := by rw [hcomm_inv]
        _ = (a⁻¹ * (t * a * t⁻¹))⁻¹ := by group
    rw [hcalc]
    exact D.inv_mem haD

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B Aa D : Subgroup G}
  {z b : G}

theorem ThCyc.t_sq (H : ThCyc G L R t) : t * t = 1 := by simpa [sq] using H.sq_t

theorem ThCyc.t_inv (H : ThCyc G L R t) : t⁻¹ = t := inv_eq_of_mul_eq_one_right H.t_sq

theorem ThCyc.t_conj_efix (H : ThCyc G L R t) {c : G} :
    t * (c⁻¹ * (t * c * t⁻¹)) * t⁻¹ = (c⁻¹ * (t * c * t⁻¹))⁻¹ := by
  have ht : t * t = 1 := H.t_sq
  have htinv : t⁻¹ = t := H.t_inv
  have h2 : t * (t * c * t⁻¹) * t⁻¹ = c := by
    calc t * (t * c * t⁻¹) * t⁻¹ = (t * t) * c * (t⁻¹ * t⁻¹) := by group
      _ = c := by rw [htinv]; simp only [ht, one_mul, mul_one]
  calc t * (c⁻¹ * (t * c * t⁻¹)) * t⁻¹
      = (t * c⁻¹ * t⁻¹) * (t * (t * c * t⁻¹) * t⁻¹) := by group
    _ = (t * c⁻¹ * t⁻¹) * c := by rw [h2]
    _ = (t * c * t⁻¹)⁻¹ * c := by group
    _ = (c⁻¹ * (t * c * t⁻¹))⁻¹ := by group

end CFSG.EvenSporadicStandard.ThStd
