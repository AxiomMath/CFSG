module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8L1Norm
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8L1Swap

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

section Uni

variable {A : Type} [Group A] [Finite A]

omit [Finite A] in
theorem exists_four_le_of_quot {J : Subgroup A} (hZ : center ↥J = ⊥)
    (hU : ∃ U : Subgroup (↥J ⧸ center ↥J), IVK.IsFourSubgroup U) :
    ∃ U : Subgroup A, U ≤ J ∧ IVK.IsFourSubgroup U := by
  obtain ⟨U, hU⟩ := hU
  let eJ : ↥J ≃* (↥J ⧸ center ↥J) :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  let f : (↥J ⧸ center ↥J) →* A := J.subtype.comp eJ.symm.toMonoidHom
  have hf : Function.Injective f := J.subtype_injective.comp eJ.symm.injective
  obtain ⟨hc, hs⟩ := IVK.isFourSubgroup_props hU
  refine ⟨U.map f, ?_, IVK.isFourSubgroup_of ?_ ?_ ?_⟩
  · rintro _ ⟨u, -, rfl⟩
    exact (eJ.symm u).2
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hc a ha b hb]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, hs a ha, map_one]
  · rw [Subgroup.card_map_of_injective hf]
    exact hU.2

end Uni

theorem cellAbs_of_uniform {F : (Y : Type) → [Group Y] → Prop}
    (hrank : ∀ (Y : Type) [Group Y] [Finite Y], F Y →
      ∀ E : Subgroup (MulAut Y), IsElementaryAbelian 2 ↥E → Nat.card ↥E ≤ 8)
    (hfour : ∀ (Y : Type) [Group Y] [Finite Y], F Y → ∃ U : Subgroup Y, IVK.IsFourSubgroup U)
    (hcard : ∀ (Y : Type) [Group Y] [Finite Y], F Y → ¬ (Nat.card Y) ^ 2 ∣ Nat.factorial 11) :
    CellAbs F := by
  intro A _ _ zb Sb Vb J hfr hJ _ hY
  exfalso
  by_cases hsw : Sb ≤ normalizer (J : Set A)
  · obtain ⟨E, hE, hE16⟩ := exists_elemAbelian_aut_of_normalizes hfr hJ hsw
    have := hrank _ hY E hE
    omega
  · obtain ⟨s, -, hsN⟩ := Set.not_subset.mp hsw
    have hs : cs s J ≠ J := fun h => hsN (cs_eq_iff_mem_normalizer.mp h)
    by_cases hZ : center ↥J = ⊥
    · obtain ⟨U, hUJ, hU⟩ := exists_four_le_of_quot hZ (hfour _ hY)
      exact hs (hfr.comp_unique_of_four hJ hUJ hU _ (isComponent_cs hJ s))
    · exact hcard _ hY (swap_card_sq hfr hJ hZ hsw)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L1
