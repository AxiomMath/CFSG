module

public import CFSG.LocalAnalysis.ComponentInitial.RootPairRestriction

public section

namespace CFSG.LocalAnalysis.ComponentInitial

theorem Suzuki_Sylow_point_recovery {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω]
    [Finite Ω] [MulAction.IsPretransitive G Ω] [FaithfulSMul G Ω] (hΩ : 3 ≤ Nat.card Ω)
    (ξ : Ω) {p : ℕ} [Fact p.Prime] (U : Sylow p G)
    (hUξ : (U : Subgroup G) ≤ MulAction.stabilizer G ξ)
    (hUn : ((U : Subgroup G).subgroupOf (MulAction.stabilizer G ξ)).Normal)
    (htr : ∀ ω ω' : Ω, ω ≠ ξ → ω' ≠ ξ → ∃ u : (U : Subgroup G), (u : G) • ω = ω') :
    {ω : Ω | ∀ u ∈ (U : Subgroup G), u • ω = ω} = {ξ} ∧
    Subgroup.normalizer ((U : Subgroup G) : Set G) = MulAction.stabilizer G ξ ∧
    (∀ x y x' y' : Ω, x ≠ y → x' ≠ y' → ∃ g : G, g • x = x' ∧ g • y = y') ∧
    (∀ φ ψ : Ω ≃ Sylow p G, (∀ (g : G) ω, φ (g • ω) = g • φ ω) → φ ξ = U →
      (∀ (g : G) ω, ψ (g • ω) = g • ψ ω) → ψ ξ = U → φ = ψ) ∧
    ∃ φ : Ω ≃ Sylow p G, (∀ (g : G) ω, φ (g • ω) = g • φ ω) ∧ φ ξ = U ∧
      (∀ g : G, φ (g • ξ) = g • U) ∧
      ∃ τ : MulAut G →* Equiv.Perm Ω, (∀ α x, φ (τ α x) = α • φ x) ∧ Function.Injective τ ∧
        (∀ α (g : G) x, τ α (g • x) = α g • τ α x) ∧
        ∀ (g : G) x, τ (MulAut.conj g) x = g • x := by
  refine ⟨?_, normalizer_eq_stabilizer hΩ htr hUξ hUn, fun x y x' y' hxy hxy' => ?_,
    fun φ ψ hφ hφξ hψ hψξ => ?_, ?_⟩
  · refine Set.ext fun ω => ⟨fun h => eq_of_forall_smul_eq hΩ htr h, fun h u hu => ?_⟩
    rw [Set.mem_singleton_iff.1 h]
    exact hUξ hu
  · obtain ⟨g₁, hg₁⟩ := MulAction.exists_smul_eq G x ξ
    obtain ⟨g₂, hg₂⟩ := MulAction.exists_smul_eq G x' ξ
    have hy : g₁ • y ≠ ξ := fun h => hxy (smul_left_cancel g₁ (hg₁.trans h.symm))
    have hy' : g₂ • y' ≠ ξ := fun h => hxy' (smul_left_cancel g₂ (hg₂.trans h.symm))
    obtain ⟨u, hu⟩ := htr _ _ hy hy'
    refine ⟨g₂⁻¹ * (u : G) * g₁, ?_, ?_⟩
    · rw [mul_smul, mul_smul, hg₁, show (u : G) • ξ = ξ from hUξ u.2, ← hg₂, inv_smul_smul]
    · rw [mul_smul, mul_smul, hu, inv_smul_smul]
  · refine Equiv.ext fun ω => ?_
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G ξ ω
    rw [hφ, hψ, hφξ, hψξ]
  · let φ := sylowPointEquiv hΩ htr hUξ hUn
    have hφ : ∀ (g : G) ω, φ (g • ω) = g • φ ω := fun g ω => sylowPoint_smul hΩ htr hUξ hUn g ω
    let τ : MulAut G →* Equiv.Perm Ω :=
      { toFun := sylowPointPerm hΩ htr hUξ hUn
        map_one' := Equiv.ext fun ω => by
          rw [← MulAut.conj.map_one, sylowPointPerm_conj, one_smul]
          rfl
        map_mul' := sylowPointPerm_mul hΩ htr hUξ hUn }
    refine ⟨φ, hφ, sylowPoint_self hΩ htr hUξ hUn, fun g => sylowPoint_eq hΩ htr hUξ hUn rfl, τ,
      fun α x => apply_sylowPointPerm hΩ htr hUξ hUn α x, ?_,
      fun α g x => sylowPointPerm_smul hΩ htr hUξ hUn α g x,
      fun g x => sylowPointPerm_conj hΩ htr hUξ hUn g x⟩
    rw [injective_iff_map_eq_one]
    intro α hα
    have hfix : ∀ x, sylowPointPerm hΩ htr hUξ hUn α x = x := fun x =>
      congrArg (fun π : Equiv.Perm Ω => π x) hα
    refine MulEquiv.ext fun g => eq_of_smul_eq_smul (α := Ω) fun x => ?_
    have h := sylowPointPerm_smul hΩ htr hUξ hUn α g x
    rw [hfix, hfix] at h
    exact h.symm

end CFSG.LocalAnalysis.ComponentInitial
