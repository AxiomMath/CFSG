module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A7NatFusion

public section
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.SteinbergCB

section Weak

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}
  {ψ : V ≃* Multiplicative (evenWeight 7)}

theorem A7NatPre.weight_four_of_mem_conjugate_F4 (h331 : Stmt3_3_1_F4) (hyp : Hyp1223 G T L V)
    (h : A7NatPre T L V ψ)
    (wt26 : ∀ v : V, (hammingNorm (vec ψ v) = 2 ∨ hammingNorm (vec ψ v) = 6) →
      centralizer ({(v : G)} : Set G) ≤ normalizer (L : Set G))
    (g : G) (hg : CFSG.conjugate V g ≠ V) (v : V) (hv : (v : G) ∈ CFSG.conjugate V g)
    (hv1 : v ≠ 1) : hammingNorm (vec ψ v) = 4 := by
  have hwt := weight_of_mem_evenWeight _ (vec_mem ψ v) (by rwa [ne_eq, vec_eq_zero_iff])
  rcases hwt with h2 | h4 | h6
  rotate_left
  · exact h4
  all_goals
    exfalso
    rw [mem_conjugate_iff_mem] at hv
    set u : V := ⟨g * v * g⁻¹, hv⟩ with hu
    obtain ⟨l, hl, hlu⟩ := h.exists_conj_of_conj_F4 h331 hyp (u := v) (w := u) (g := g) rfl
    have hc : l⁻¹ * g ∈ centralizer ({(v : G)} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      have h1 : g * (v : G) * g⁻¹ = l * v * l⁻¹ := hlu
      calc l⁻¹ * g * v = l⁻¹ * (g * v * g⁻¹) * g := by group
        _ = l⁻¹ * (l * v * l⁻¹) * g := by rw [h1]
        _ = v * (l⁻¹ * g) := by group
    have hcM := wt26 v (by first | exact Or.inl ‹_› | exact Or.inr ‹_›) hc
    have hgM : g ∈ normalizer (L : Set G) := by
      have h2 := mul_mem ((le_normalizer : L ≤ normalizer (L : Set G)) hl) hcM
      rwa [mul_inv_cancel_left] at h2
    rcases h.TI g hgM with hVg | hVg
    · exact hg hVg
    · have hmem : (v : G) ∈ V ⊓ CFSG.conjugate V g := by
        refine ⟨v.2, ?_⟩
        show (v : G) ∈ CFSG.conjugate V g
        rw [mem_conjugate_iff_mem]
        exact hv
      rw [hVg, mem_bot] at hmem
      exact hv1 (Subtype.ext hmem)

end Weak

end CFSG.Quasithin.H13.A7
