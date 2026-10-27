module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Ctx

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def fzN2 (t x₁ x₂ : G) : Subgroup G :=
  normalizer ((ctxW t x₁ x₂ : Subgroup G) : Set G)

structure IsFzT2 (t x₁ x₂ : G) (S T₂ : Subgroup G) : Prop where
  le_N2 : T₂ ≤ fzN2 t x₁ x₂
  isPGroup : IsPGroup 2 T₂
  odd_relIndex : ¬ 2 ∣ T₂.relIndex (fzN2 t x₁ x₂)
  S_le : S ≤ T₂

@[expose] def fzR (t x₁ x₂ : G) : Subgroup G := CFSG.Open.pCoreOf 2 (fzN2 t x₁ x₂)

@[expose] def fzQ (t x₁ x₂ rho : G) : Subgroup G :=
  ctxW t x₁ x₂ ⊔ ⁅fzR t x₁ x₂, zpowers rho⁆

@[expose] def fzP (t x₁ x₂ rho : G) : Subgroup G := ⁅fzQ t x₁ x₂ rho, zpowers rho⁆

@[expose] def FzSylow (T : Subgroup G) : Prop := IsPGroup 2 T ∧ ¬ 2 ∣ T.index

variable [Finite G]

theorem exists_isFzT2 {t x₁ x₂ : G} {S : Subgroup G} (hS : IsPGroup 2 S)
    (hSN : S ≤ fzN2 t x₁ x₂) : ∃ T₂ : Subgroup G, IsFzT2 t x₁ x₂ S T₂ := by
  have hS' : IsPGroup 2 (S.subgroupOf (fzN2 t x₁ x₂)) := hS.comap_subtype
  obtain ⟨Q, hQ⟩ := hS'.exists_le_sylow
  refine ⟨(Q : Subgroup (fzN2 t x₁ x₂)).map (fzN2 t x₁ x₂).subtype, ⟨?_, ?_, ?_, ?_⟩⟩
  · rintro _ ⟨q, -, rfl⟩
    exact q.2
  · exact Q.isPGroup'.map _
  · have hrel : ((Q : Subgroup (fzN2 t x₁ x₂)).map (fzN2 t x₁ x₂).subtype).relIndex
        (fzN2 t x₁ x₂) = (Q : Subgroup (fzN2 t x₁ x₂)).index := by
      have h := Subgroup.relIndex_map_map_of_injective
        (f := (fzN2 t x₁ x₂).subtype) (Q : Subgroup (fzN2 t x₁ x₂)) ⊤
        (fzN2 t x₁ x₂).subtype_injective
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
      rw [h, Subgroup.relIndex_top_right]
    rw [hrel]
    exact Q.not_dvd_index
  · intro g hg
    refine ⟨⟨g, hSN hg⟩, hQ ?_, rfl⟩
    exact hg

theorem fz_S_le_N2 {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}
    (h : Ctx t L S x₁ x₂ lam rho tau) : S ≤ fzN2 t x₁ x₂ := by
  intro g hg
  rw [fzN2, mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    exact h.normal_W.2 g hg k hk
  · intro hk
    have h' := h.normal_W.2 g⁻¹ (S.inv_mem hg) _ hk
    simpa [mul_assoc] using h'

end CFSG.OddStandard.SmallF3.FritzII
