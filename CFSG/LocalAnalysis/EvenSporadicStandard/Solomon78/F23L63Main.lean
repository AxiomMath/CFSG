module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.F23L63Transport
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi23Setting

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Sporadic.Fi23 CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.Solomon78.F23L63

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

set_option linter.unusedSectionVars false

theorem exists_embedding {G Y : Type} [Group G] [Group Y] {L : Subgroup G} (ψ : ↥L ≃* Y) :
    ∃ φ : Y →* G, Function.Injective φ ∧ φ.range = L ∧ ∀ y, φ y = ((ψ.symm y : ↥L) : G) := by
  refine ⟨L.subtype.comp ψ.symm.toMonoidHom, L.subtype_injective.comp ψ.symm.injective, ?_,
    fun y => rfl⟩
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective _ ψ.symm.surjective,
    Subgroup.map_top, Subgroup.range_subtype]

theorem exists_equiv_conj {G Y : Type} [Group G] [Group Y] {L : Subgroup G} (ψ : ↥L ≃* Y)
    (c : Y) : ∃ ψ' : ↥L ≃* Y, ∀ x, ψ' x = c⁻¹ * ψ x * c :=
  ⟨ψ.trans (MulAut.conj c⁻¹), fun x => by simp⟩

section Main


theorem fi23Lemma63_proved : Fi23Lemma63 := by
  intro G _ L hL
  obtain ⟨e⟩ := hL
  let ψ : ↥L ≃* J := e.trans CFSG.Sporadic.Fi23.fi23EquivJ
  obtain ⟨φ₀, hφ₀, hr₀, hφ₀ψ⟩ := @exists_embedding G J _ (inferInstance) L ψ
  refine ⟨?_, ?_, ?_⟩
  · intro A A' hA hA' h1 h2 c1 c2
    exact conj_of_embedding φ₀ hφ₀ hr₀ hA hA' h1 h2 c1 c2
  · have hu : φ₀ d ∈ L := hr₀ ▸ ⟨d, rfl⟩
    refine ⟨φ₀ d, hu, ?_, ?_⟩
    · rw [orderOf_injective φ₀ hφ₀ d]
      exact CFSG.Sporadic.Fi23.orderOf_d
    · rw [@CFSG.EvenSporadicStandard.Induction.fi23_card_inf_centralizer_eq G J _ (inferInstance)
        L ψ (φ₀ d) hu]
      have : ψ ⟨φ₀ d, hu⟩ = d := by
        have h : (⟨φ₀ d, hu⟩ : ↥L) = ψ.symm d := Subtype.ext (hφ₀ψ d)
        rw [h]
        exact ψ.apply_symm_apply d
      rw [this]
      exact CFSG.Sporadic.Fi23.card_centralizer_d
  · intro u hu
    obtain ⟨huL, hu2, hcard⟩ := hu
    have h1 : orderOf (ψ ⟨u, huL⟩) = 2 := by
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hu2]
    have h2 : Nat.card ↥(centralizer ({ψ ⟨u, huL⟩} : Set J)) = 129123503308800 := by
      rw [← @CFSG.EvenSporadicStandard.Induction.fi23_card_inf_centralizer_eq G J _
        (inferInstance) L ψ u huL]
      exact hcard
    obtain ⟨c, hc⟩ := isConj_iff.1
      (CFSG.EvenSporadicStandard.Induction.fi23J_isConj_d_of_card h1 h2)
    obtain ⟨ψ', hψ'⟩ := @exists_equiv_conj G J _ (inferInstance) L ψ c
    have hψ'u : ψ' ⟨u, huL⟩ = d := by
      rw [hψ', ← hc]
      group
    obtain ⟨φ, hφ, hr, hφψ'⟩ := @exists_embedding G J _ (inferInstance) L ψ'
    have hφd : φ d = u := by
      have : ψ'.symm d = ⟨u, huL⟩ := ψ'.symm_apply_eq.2 hψ'u.symm
      rw [hφψ' d, this]
    exact frame_of_embedding φ hφ hr hφd

end Main

end CFSG.EvenSporadicStandard.Solomon78
