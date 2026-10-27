module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeTenSL3Inner

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open Matrix
open CFSG.LocalAnalysis.AGL81TheoremCD.Section12 (ThreeTenTorusExclusion)

theorem d_le_sup_centralizer_of_threeTenHyp {H : Type} [Group H] [Finite H]
    {I D P Y : Subgroup H} {p d : ℕ} (hhyp : ThreeTenHyp I D P Y p d)
    (e : ↥I ≃* SpecialLinearGroup (Fin 3) (ZMod p))
    (htor : ThreeTenTorusExclusion p d) :
    D ≤ I ⊔ Subgroup.centralizer (I : Set H) := by
  intro δ hδ
  obtain ⟨t, ht⟩ := exists_conj_of_threeTenHyp hhyp e htor hδ
  have hmem : (t : H)⁻¹ * δ ∈ Subgroup.centralizer (I : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx' : δ * x * δ⁻¹ = (t : H) * x * (t : H)⁻¹ := by
      simpa using ht ⟨x, hx⟩
    calc x * ((t : H)⁻¹ * δ)
        = x * (t : H)⁻¹ * δ := by group
      _ = (t : H)⁻¹ * (δ * x * δ⁻¹) * δ := by rw [hx']; group
      _ = ((t : H)⁻¹ * δ) * x := by group
  have hδ_eq : δ = (t : H) * ((t : H)⁻¹ * δ) := by group
  rw [hδ_eq]
  exact Subgroup.mul_mem_sup t.2 hmem

end CFSG.LocalAnalysis.AGL81I.Section3
