module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltSixAut
public import Certificates.Certificate23600

public section

namespace CFSG.ComponentClassification.GSThmB.A10E1

open Equiv Equiv.Perm Subgroup


theorem mem_range_conjNormal_of_commute_swap (α : MulAut (alternatingGroup (Fin 6)))
    {i j : Fin 6} (hij : i ≠ j)
    (hα : α * MulAut.conjNormal (swap i j) = MulAut.conjNormal (swap i j) * α) :
    ∃ τ : Perm (Fin 6), α = MulAut.conjNormal τ := by
  obtain ⟨π, hπ⟩ := isConj_iff.mp (isConj_swap hij (show (4 : Fin 6) ≠ 5 by decide))
  set β := MulAut.conjNormal π * α * (MulAut.conjNormal π)⁻¹ with hβ
  have hcomm : β * MulAut.conjNormal (swap 4 5) = MulAut.conjNormal (swap 4 5) * β := by
    rw [← hπ, map_mul, map_mul, map_inv, hβ]
    calc MulAut.conjNormal π * α * (MulAut.conjNormal π)⁻¹ *
          (MulAut.conjNormal π * MulAut.conjNormal (swap i j) * (MulAut.conjNormal π)⁻¹) =
        MulAut.conjNormal π * (α * MulAut.conjNormal (swap i j)) * (MulAut.conjNormal π)⁻¹ := by
          group
      _ = MulAut.conjNormal π * (MulAut.conjNormal (swap i j) * α) *
          (MulAut.conjNormal π)⁻¹ := by rw [hα]
      _ = MulAut.conjNormal π * MulAut.conjNormal (swap i j) * (MulAut.conjNormal π)⁻¹ *
          (MulAut.conjNormal π * α * (MulAut.conjNormal π)⁻¹) := by group
  obtain ⟨τ, -, hτ⟩ := RankTwoAlt.exists_perm_of_commute_swap45 β fun x =>
    congrArg (fun γ : MulAut (alternatingGroup (Fin 6)) => γ x) hcomm
  have hβτ : β = MulAut.conjNormal τ := by
    ext x
    rw [hτ x, MulAut.conjNormal_apply]
  refine ⟨π⁻¹ * τ * π, ?_⟩
  rw [map_mul, map_mul, map_inv, ← hβτ, hβ]
  group

theorem mem_range_conjNormal_of_commute_odd
    (α : MulAut (alternatingGroup (Fin 6))) {σ q : Perm (Fin 6)} (hσ : σ * σ = 1)
    (hσs : sign σ = -1) (hqs : sign q = 1) (hq4 : q ^ 4 = 1) (hq2 : q ^ 2 ≠ 1)
    (hσq : σ * q = q * σ) (h1 : α * MulAut.conjNormal σ = MulAut.conjNormal σ * α)
    (h2 : α * MulAut.conjNormal (q ^ 2) = MulAut.conjNormal (q ^ 2) * α) :
    ∃ τ : Perm (Fin 6), α = MulAut.conjNormal τ := by
  rcases Certificates.certificate23600 σ q hσ hσs hqs hq4 hq2 hσq with
    ⟨i, j, hij, rfl⟩ | ⟨i, j, hij, hsw⟩
  · exact mem_range_conjNormal_of_commute_swap α hij h1
  · refine mem_range_conjNormal_of_commute_swap α hij ?_
    rw [← hsw, map_mul]
    calc α * (MulAut.conjNormal σ * MulAut.conjNormal (q ^ 2)) =
        (α * MulAut.conjNormal σ) * MulAut.conjNormal (q ^ 2) := by group
      _ = MulAut.conjNormal σ * (α * MulAut.conjNormal (q ^ 2)) := by rw [h1]; group
      _ = MulAut.conjNormal σ * MulAut.conjNormal (q ^ 2) * α := by rw [h2]; group

end CFSG.ComponentClassification.GSThmB.A10E1
