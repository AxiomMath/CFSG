module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.ClassicalGroups.UnitaryFlag.GramForm

public section

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup Equiv CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

universe u v

theorem exists_norm_one_orderOf_of_dvd {ℓ f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) {p : ℕ} [Fact p.Prime] (hp : p ∣ ℓ ^ f + 1) :
    ∃ ζ : Kˣ, h.norm (ζ : K) = 1 ∧ orderOf ζ = p := by
  have := h.finite
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := (Units.map h.normHom).ker) p
    (by rw [(unitary_field_norm h).2.2.1]; exact hp)
  exact ⟨x, h.mem_ker_normUnits.mp x.2, by rw [orderOf_coe, hx]⟩

end CFSG.LocalAnalysis.GorensteinLyons
