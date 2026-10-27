module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P6Fix

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P6

open Subgroup CFSG.Open

variable {G : Type*} [Group G]

theorem mem_conj_of_conjA {V E : Subgroup G} {t h s : G} (ht2 : t * t = 1)
    (hEc : ∀ e ∈ E, e * t = t * e) (hEV : E ≤ V) (htV : t ∉ V)
    (heps : ∀ e ∈ E, ∃ v ∈ V, v * t * v⁻¹ = t * e) (hh : h ∈ normalizer (V : Set G))
    (hD : zpowers s ⊔ (V ⊓ centralizer ({s} : Set G)) =
      (E ⊔ zpowers t).map (MulAut.conj h).toMonoidHom) :
    ∃ h' ∈ normalizer (V : Set G), h' * t * h'⁻¹ = s := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hn : ∀ p ∈ E, t * p * t⁻¹ ∈ E := fun p hp => by
    rw [← hEc p hp]
    simpa [mul_assoc] using hp
  have hs : s ∈ (E ⊔ zpowers t).map (MulAut.conj h).toMonoidHom :=
    hD ▸ mem_sup_left (mem_zpowers s)
  obtain ⟨a, ha, hasr⟩ := Subgroup.mem_map.1 hs
  have hasr' : h * a * h⁻¹ = s := by simpa [MulAut.conj_apply] using hasr
  rcases (mem_sup_zpowers_iff ht2 hn).1 ha with haE | haE
  · exfalso
    have hsV : s ∈ V := by
      rw [← hasr']
      exact (mem_normalizer_iff.1 hh a).1 (hEV haE)
    have hAV : (E ⊔ zpowers t).map (MulAut.conj h).toMonoidHom ≤ V := by
      rw [← hD]
      exact sup_le (zpowers_le.2 hsV) inf_le_left
    have htA : h * t * h⁻¹ ∈ (E ⊔ zpowers t).map (MulAut.conj h).toMonoidHom :=
      Subgroup.mem_map.2 ⟨t, mem_sup_right (mem_zpowers t), by simp [MulAut.conj_apply]⟩
    exact htV ((mem_normalizer_iff.1 hh t).2 (hAV htA))
  · obtain ⟨v, hv, hvt⟩ := heps (a * t) haE
    refine ⟨h * v, mul_mem hh (le_normalizer hv), ?_⟩
    have hat : a = t * (a * t) := by
      have := hEc (a * t) haE
      calc a = a * (t * t) := by rw [ht2, mul_one]
        _ = (a * t) * t := by group
        _ = t * (a * t) := by rw [this]
    rw [← hasr', hat]
    calc h * v * t * (h * v)⁻¹ = h * (v * t * v⁻¹) * h⁻¹ := by group
      _ = h * (t * (a * t)) * h⁻¹ := by rw [hvt]

end CFSG.LocalAnalysis.EvenBN.Tits.N.P6
