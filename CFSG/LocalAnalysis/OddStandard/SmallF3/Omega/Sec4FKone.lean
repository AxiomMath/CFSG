module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FCent
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FCyc
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4MClaim
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FAct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G} {A B : Subgroup G}
  {φ : (Fin 7 → ZMod 2) → G}

theorem Sec4FSetup.kcases (h : Sec4FSetup t L S z A B φ) {y : G}
    (hy : ∃ g : G, y = g⁻¹ * t * g) (hyN : y ∈ normalizer (A : Set G)) :
    (∃ p : Option (Fin 7), y = sec4MPt t φ p) ∨
      ∃ a b : Option (Fin 7), a ≠ b ∧ Sec4MRealizes t φ y (Equiv.swap a b) := by
  obtain ⟨σ, hσ⟩ := h.exists_realizes hyN
  have hy2 : y * y = 1 := by
    obtain ⟨g, rfl⟩ := hy
    calc g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [h.t_sq]; group
  have hσ2 : σ * σ = 1 := h.realizes_sq hy2 hσ
  rcases sec4M_perm_trichotomy σ hσ2 with rfl | ⟨a, b, hab, rfl⟩ | ⟨x, y', hx, hy', hyx, hyx'⟩
  · left
    have hcent : y ∈ centralizer (A : Set G) := h.mem_centralizer_iff_realizes_one.mpr hσ
    have hyA : y ∈ A := h.cent_two_elt hcent ⟨1, by simpa [pow_two] using hy2⟩
    exact h.exists_pt_of_conj hy hyA
  · right
    exact ⟨a, b, hab, hσ⟩
  · exact (h.false_of_two_cycles hy hσ hx hy' hyx hyx').elim

end CFSG.OddStandard.SmallF3.Omega
