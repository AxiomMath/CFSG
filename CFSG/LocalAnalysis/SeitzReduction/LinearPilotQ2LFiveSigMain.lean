module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSigCore
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSigLevi

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial LinearFlag Matrix

theorem lFiveGraphLeviNormInput_of_fieldModule
    (h : LFiveWOneFieldModuleInput) :
    LFiveGraphLeviNormInput := by
  intro G _ _ L hset K _ _ hK e t ht hKt c W₁ hW₁c hW₁2 hW₁t htN hLN Kc hKc S₀ d hdata
  have hZ := lFiveGraphWInterInput_holds G L hset K hK e t ht hKt c W₁ hW₁c hW₁2 hW₁t htN hLN Kc
    hKc S₀ d hdata
  obtain ⟨-, -, -, -, htW₂, -⟩ := graph_swap_facts_of_sylowData htN hdata
  obtain ⟨hS₀p, hS₀N, hS₀odd, htS₀, hdS₀, hdt, -, hdo⟩ := hdata
  set N := seitzTilde W₁ Kc with hNdef
  set W₂ := W₁.map (MulAut.conj d).toMonoidHom with hW₂def
  have hW₁N : W₁ ≤ N := fun w hw => mem_seitzTilde_iff.2 ⟨le_normalizer hw, by
    rw [show QuotientGroup.mk' (W₁.subgroupOf (normalizer (W₁ : Set G))) ⟨w, le_normalizer hw⟩ = 1
      from (QuotientGroup.eq_one_iff _).2 (mem_subgroupOf.2 hw)]
    exact one_mem _⟩
  have hNW₁ : N ≤ normalizer (W₁ : Set G) := seitzTilde_le_normalizer W₁ Kc
  have hW₁S₀ : W₁ ≤ S₀ :=
    wOne_le_of_not_two_dvd_relIndex (IsPGroup.of_card hW₁c) hNW₁ hS₀p hS₀N hW₁N hS₀odd
  obtain ⟨S₀', hS₀'⟩ := exists_lFiveFieldSylow hset hK e ht hKt c hW₁c hW₁2 hW₁t htN hLN hKc
  obtain ⟨F, _, _, _, σ, hF, hσ1, -, ψ, β, hψs, hψker, hψt, hψS, hβ, hβadd, hβact, hβt⟩ :=
    h G L hset K hK e t ht hKt ⟨d, mem_centralizer_singleton_iff.2 hdt, hdo⟩ c W₁ hW₁c hW₁2 hW₁t
      htN hLN Kc hKc S₀' hS₀'
  have hσ : ∀ x, (σ : F →+* F) x = x ^ 2 := by
    rcases ringEquiv_eq_id_or_sq_of_card_four hF σ with h1 | h1
    · exact absurd (RingEquiv.ext fun x => (h1 x).trans rfl) hσ1
    · exact h1
  obtain ⟨m, hm, hS₀m⟩ :=
    exists_conj_of_not_two_dvd_relIndex hS₀p hS₀odd hS₀'.1 hS₀'.2.2.1
  obtain ⟨p, b, c', hdat, hpt, hbt⟩ := exists_isFieldModuleData_of_conj (σ : F →+* F) ψ β hψs
    hψker hψt hψS hβ hβadd hβact hβt hW₁N hNW₁ hS₀N hm hS₀m
  have hW₂S₀ : W₂ ≤ S₀ := by
    rintro _ ⟨w, hw, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (mem_normalizer_iff.1 hdS₀ w).1 (hW₁S₀ hw)
  have hS₀W₂ : S₀ ≤ normalizer (W₂ : Set G) := by
    refine le_normalizer_of_forall_conj_mem fun s hs x hx => ?_
    obtain ⟨w, hw, rfl⟩ := hx
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hs' : d⁻¹ * s * d ∈ S₀ := by
      have h1 := (mem_normalizer_iff.1 (inv_mem hdS₀) s).1 hs
      rwa [inv_inv] at h1
    have hw' := (mem_normalizer_iff.1 (hNW₁ (hS₀N hs')) w).1 hw
    refine ⟨d⁻¹ * s * d * w * (d⁻¹ * s * d)⁻¹, hw', ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hW₂c : Nat.card W₂ = 2 ^ 8 := by
    rw [hW₂def, Subgroup.card_map_of_injective (MulAut.conj d).injective, hW₁c]
  have htW₁ : ∀ w ∈ W₁, t * w * t⁻¹ ∈ W₁ := fun w hw => (mem_normalizer_iff.1 htN w).1 hw
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  obtain ⟨F₀, hF₀N, hF₀W₂, hF₀t, hF₀W₁, hF₀c⟩ := exists_leviStab_le_normalizer hset hK e ht hKt
    c hW₁c hW₁t htN hLN hKc (mem_centralizer_singleton_iff.2 hdt) hdo
  exact hdat.perfectCore_le_normalizer_of_twist hF hW₂S₀ hS₀W₂ hW₂c hZ hσ ht2 htS₀ htW₁ htW₂ hpt
    (fun w hw => hbt w hw (htW₁ w hw)) hF₀N hF₀W₂ hF₀t hF₀W₁ hF₀c

end CFSG.SeitzReduction.LinearPilot
