module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec4L45_conj_eq_mul_of_conj_eq {t z d e : G}
    (h : e⁻¹ * (t * z) * e = d⁻¹ * t * d) :
    (d * e⁻¹)⁻¹ * t * (d * e⁻¹) = t * z := by
  have h1 := congrArg (fun x => e * x * e⁻¹) h
  have hl1 : e * (e⁻¹ * (t * z) * e) * e⁻¹ = t * z := by group
  have hr1 : e * (d⁻¹ * t * d) * e⁻¹ = (d * e⁻¹)⁻¹ * t * (d * e⁻¹) := by group
  rw [hl1, hr1] at h1
  exact h1.symm

theorem sec4L45_eq_conj_of_conj_eq {t z h l l' : G}
    (hAs : l' * (h⁻¹ * z * h) * l'⁻¹ = l * (h⁻¹ * t * h) * l⁻¹) :
    z = (h * l'⁻¹ * l * h⁻¹) * t * (h * l'⁻¹ * l * h⁻¹)⁻¹ := by
  have h1 := congrArg (fun x => l'⁻¹ * x * l') hAs
  have h2 : h⁻¹ * z * h = l'⁻¹ * l * (h⁻¹ * t * h) * l⁻¹ * l' := by
    have hL' : l'⁻¹ * (l' * (h⁻¹ * z * h) * l'⁻¹) * l' = h⁻¹ * z * h := by group
    have hR' : l'⁻¹ * (l * (h⁻¹ * t * h) * l⁻¹) * l' =
        l'⁻¹ * l * (h⁻¹ * t * h) * l⁻¹ * l' := by group
    rw [hL', hR'] at h1
    exact h1
  have h3 := congrArg (fun x => h * x * h⁻¹) h2
  have hL'' : h * (h⁻¹ * z * h) * h⁻¹ = z := by group
  have hR'' : h * (l'⁻¹ * l * (h⁻¹ * t * h) * l⁻¹ * l') * h⁻¹ =
      (h * l'⁻¹ * l * h⁻¹) * t * (h * l'⁻¹ * l * h⁻¹)⁻¹ := by group
  rw [hL'', hR''] at h3
  exact h3

end CFSG.OddStandard.SmallF3.Omega
