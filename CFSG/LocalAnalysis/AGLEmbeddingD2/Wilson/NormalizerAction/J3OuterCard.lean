module

public import CFSG.Sporadic.SmallOddCore.J3

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic

section Main


set_option linter.unusedSectionVars false

set_option maxRecDepth 20000 in
theorem card_centralizer_outer_involution {t : Equiv.Perm (Fin 6156)}
    (ht : t ∈ j3R) (ht2 : orderOf t = 2) (htP : t ∉ j3P) :
    Nat.card (j3P ⊓ centralizer ({t} : Set (Equiv.Perm (Fin 6156))) :
      Subgroup (Equiv.Perm (Fin 6156))) = 2448 := by
  obtain ⟨-, -, -, hrows, hcover, -⟩ := ctuc_j3_all_involution_fixed_subgroups_odd_core_trivial
  obtain ⟨r, hr, g, hg, htr⟩ := hcover t ht ht2
  obtain ⟨-, -, hout, hC, hcard, -⟩ := hrows r hr
  have hro : r.outer = true := by
    by_contra hro
    apply htP
    have hin : tp 6156 r.rep ∈ j3P := by
      by_contra hn
      exact hro (hout.2 hn)
    rw [htr]
    exact j3P.mul_mem (j3P.mul_mem hg hin) (j3P.inv_mem hg)
  have key : r.centOrder = 2448 := by
    have hr' := hr
    simp only [j3Rows, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with h0 | h1
    · rw [h0] at hro
      simp at hro
    · rw [h1]
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : Equiv.Perm (Fin 6156), t₀ = tp 6156 r.rep := ⟨_, rfl⟩
  rw [← ht₀] at htr hC hcard
  rw [key] at hcard
  have hconj : (j3P ⊓ centralizer ({t₀} : Set (Equiv.Perm (Fin 6156))) :
      Subgroup (Equiv.Perm (Fin 6156))).map (MulAut.conj g).toMonoidHom =
      j3P ⊓ centralizer ({t} : Set (Equiv.Perm (Fin 6156))) := by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_inf, mem_centralizer_singleton_iff,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨x, ⟨hxP, hxt⟩, rfl⟩
      refine ⟨j3P.mul_mem (j3P.mul_mem hg hxP) (j3P.inv_mem hg), ?_⟩
      rw [htr]
      calc g * x * g⁻¹ * (g * t₀ * g⁻¹) = g * (x * t₀) * g⁻¹ := by group
        _ = g * (t₀ * x) * g⁻¹ := by rw [hxt]
        _ = g * t₀ * g⁻¹ * (g * x * g⁻¹) := by group
    · rintro ⟨hyP, hyt⟩
      refine ⟨g⁻¹ * y * g, ⟨j3P.mul_mem (j3P.mul_mem (j3P.inv_mem hg) hyP) hg, ?_⟩, by group⟩
      have : t₀ = g⁻¹ * t * g := by rw [htr]; group
      rw [this]
      calc g⁻¹ * y * g * (g⁻¹ * t * g) = g⁻¹ * (y * t) * g := by group
        _ = g⁻¹ * (t * y) * g := by rw [hyt]
        _ = g⁻¹ * t * g * (g⁻¹ * y * g) := by group
  rw [← hconj, Subgroup.card_map_of_injective (MulAut.conj g).injective, hcard]

end Main

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
