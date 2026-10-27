module

public import CFSG.LocalAnalysis.ComponentInitial.RootPairRestriction

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem Suzuki_opposite_Sylow_restriction {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω]
    [Finite Ω] [MulAction.IsPretransitive G Ω] [FaithfulSMul G Ω] (hΩ : 3 ≤ Nat.card Ω)
    (ξ : Ω) {p : ℕ} [Fact p.Prime] (U : Sylow p G)
    (hUξ : (U : Subgroup G) ≤ MulAction.stabilizer G ξ)
    (hUn : ((U : Subgroup G).subgroupOf (MulAction.stabilizer G ξ)).Normal)
    (htr : ∀ ω ω' : Ω, ω ≠ ξ → ω' ≠ ξ → ∃ u : (U : Subgroup G), (u : G) • ω = ω')
    (w : G) (hw : w • ξ ≠ ξ) :
    ((pairAutSubgroup (U : Subgroup G) ((U : Subgroup G).map (MulAut.conj w).toMonoidHom) :
      Set (MulAut G)) = {α | (U : Subgroup G).map α.toMonoidHom = U ∧
        ((U : Subgroup G).map (MulAut.conj w).toMonoidHom).map α.toMonoidHom =
          (U : Subgroup G).map (MulAut.conj w).toMonoidHom}) ∧
    Function.Injective (pairAutRestrict (U : Subgroup G)
      ((U : Subgroup G).map (MulAut.conj w).toMonoidHom)) ∧
    (∀ α : MulAut G, ∃ g : G, ∃ β ∈ pairAutSubgroup (U : Subgroup G)
      ((U : Subgroup G).map (MulAut.conj w).toMonoidHom), α = MulAut.conj g * β) ∧
    ∀ d : ℕ, derivedSeries (MulAut (U : Subgroup G)) d = ⊥ → derivedSeries (Outer G) d = ⊥ := by
  set V := (U : Subgroup G).map (MulAut.conj w).toMonoidHom with hV
  set π := sylowPointPerm hΩ htr hUξ hUn (U := U) with hπ
  have hξ : sylowPoint ξ U ξ = U := sylowPoint_self hΩ htr hUξ hUn
  have hη : ((sylowPoint ξ U (w • ξ) : Sylow p G) : Subgroup G) = V := by
    rw [sylowPoint_eq hΩ htr hUξ hUn rfl, coe_smul_sylow']
  have hmemC : ∀ β : MulAut G, π β ξ = ξ → π β (w • ξ) = w • ξ →
      β ∈ pairAutSubgroup (U : Subgroup G) V := by
    intro β h1 h2
    rw [sylowPointPerm_eq_iff, hξ] at h1
    rw [sylowPointPerm_eq_iff, hη] at h2
    exact ⟨h1, h2⟩
  have hfixC : ∀ β ∈ pairAutSubgroup (U : Subgroup G) V, π β ξ = ξ ∧ π β (w • ξ) = w • ξ := by
    intro β hβ
    refine ⟨(sylowPointPerm_eq_iff _ _ _ _ β ξ).2 ?_, (sylowPointPerm_eq_iff _ _ _ _ β _).2 ?_⟩
    · rw [hξ]
      exact hβ.1
    · rw [hη]
      exact hβ.2
  have hInnC : ∀ α : MulAut G, ∃ g : G, ∃ β ∈ pairAutSubgroup (U : Subgroup G) V,
      α = MulAut.conj g * β := by
    intro α
    obtain ⟨h, hh⟩ := MulAction.exists_smul_eq G ξ (π α ξ)
    have hne : h⁻¹ • π α (w • ξ) ≠ ξ := by
      intro he
      rw [inv_smul_eq_iff, hh] at he
      exact hw ((π α).injective he)
    obtain ⟨u, hu⟩ := htr (w • ξ) (h⁻¹ • π α (w • ξ)) hw hne
    set g := h * (u : G) with hg
    have hgξ : g • ξ = π α ξ := by
      rw [hg, mul_smul, show (u : G) • ξ = ξ from hUξ u.2, hh]
    have hgη : g • (w • ξ) = π α (w • ξ) := by
      rw [hg, mul_smul, hu, smul_inv_smul]
    have hπβ : ∀ ω, π ((MulAut.conj g)⁻¹ * α) ω = g⁻¹ • π α ω := fun ω => by
      rw [hπ, sylowPointPerm_mul, Equiv.Perm.mul_apply, ← map_inv, sylowPointPerm_conj]
    refine ⟨g, (MulAut.conj g)⁻¹ * α, hmemC _ ?_ ?_, (mul_inv_cancel_left _ _).symm⟩
    · rw [hπβ, ← hgξ, inv_smul_smul]
    · rw [hπβ, ← hgη, inv_smul_smul]
  have hinj : Function.Injective (pairAutRestrict (U : Subgroup G) V) := by
    rw [injective_iff_map_eq_one]
    intro β hβ
    have hU1 : ∀ u ∈ (U : Subgroup G), (β : MulAut G) u = u := fun u hu => by
      have := congrArg (fun e : MulAut (U : Subgroup G) => ((e ⟨u, hu⟩ : U) : G)) hβ
      exact this
    obtain ⟨h1, h2⟩ := hfixC β β.2
    have hπ1 : ∀ ω, π β ω = ω := by
      intro ω
      by_cases hωξ : ω = ξ
      · rw [hωξ, h1]
      · obtain ⟨u, hu⟩ := htr (w • ξ) ω hw hωξ
        rw [← hu, sylowPointPerm_smul, h2, hU1 _ u.2]
    refine Subtype.ext (MulEquiv.ext fun g => eq_of_smul_eq_smul (α := Ω) fun x => ?_)
    have h := sylowPointPerm_smul hΩ htr hUξ hUn (β : MulAut G) g x
    rw [hπ1, hπ1] at h
    exact h.symm
  refine ⟨rfl, hinj, hInnC, fun d hd => ?_⟩
  have hC : derivedSeries (pairAutSubgroup (U : Subgroup G) V) d = ⊥ := by
    have := map_derivedSeries_le_derivedSeries (pairAutRestrict (U : Subgroup G) V) d
    rw [hd, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ hinj] at this
    exact this
  set q : pairAutSubgroup (U : Subgroup G) V →* Outer G :=
    (QuotientGroup.mk' (inner G)).comp (pairAutSubgroup (U : Subgroup G) V).subtype with hq
  have hqs : Function.Surjective q := by
    intro x
    obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective (inner G) x
    obtain ⟨g, β, hβ, rfl⟩ := hInnC α
    refine ⟨⟨β, hβ⟩, ?_⟩
    have h1 : QuotientGroup.mk' (inner G) (MulAut.conj g) = 1 := by
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
      exact ⟨g, rfl⟩
    change QuotientGroup.mk' (inner G) β = QuotientGroup.mk' (inner G) (MulAut.conj g * β)
    rw [map_mul, h1, one_mul]
  rw [← map_derivedSeries_eq hqs, hC, Subgroup.map_bot]

end CFSG.LocalAnalysis.ComponentInitial
