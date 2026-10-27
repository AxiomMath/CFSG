module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.LangTorus


theorem exc3core_stab_closure {τ : Tag} {β : Fin τ.rank → ℤ} {u : WeylGroup τ} (hu : u • β = β) :
    u ∈ Subgroup.closure
      {s : WeylGroup τ | ∃ α, IsRoot τ α ∧ iform α β = 0 ∧ s = rootReflection α} := by
  obtain ⟨c, hc, hinner⟩ := exists_inner_ofLattice_eq_iform τ
  have hiff : ∀ α : Fin τ.rank → ℤ,
      inner ℝ (RootSpace.ofLattice α) (RootSpace.ofLattice β) = 0 ↔ iform α β = 0 := by
    intro α
    simp [hinner α β, hc.ne']
  have hset : Subgroup.closure
        {s : WeylGroup τ |
          ∃ α, IsRoot τ α ∧ inner ℝ (RootSpace.ofLattice α) (RootSpace.ofLattice β) = 0 ∧
            s = rootReflection α}
      = Subgroup.closure
        {s : WeylGroup τ | ∃ α, IsRoot τ α ∧ iform α β = 0 ∧ s = rootReflection α} := by
    congr 1
    ext s
    constructor
    · rintro ⟨α, hα, h0, rfl⟩
      exact ⟨α, hα, (hiff α).mp h0, rfl⟩
    · rintro ⟨α, hα, h0, rfl⟩
      exact ⟨α, hα, (hiff α).mpr h0, rfl⟩
  have hu' : u ∈ weylStabilizer τ (RootSpace.ofLattice β) := by
    rw [mem_weylStabilizer, weylAct_ofLattice, hu]
  rw [(exceptional_Lang_Weyl_chamber_point_stabilizers τ).2.2.2.2.2 (RootSpace.ofLattice β),
    hset] at hu'
  exact hu'

private theorem exc3core_inner_of_orth_aux1 {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)}
    {β : Fin τ.rank → ℤ} (hΨ : ∀ α, IsRoot τ α → (iform α β = 0 ↔ α ∈ Ψ)) :
    {s : WeylGroup τ | ∃ α, IsRoot τ α ∧ iform α β = 0 ∧ s = rootReflection α} ⊆
      {s : WeylGroup τ | ∃ γ ∈ Ψ, s = rootReflection γ} := by
  rintro s ⟨α, hα, h0, rfl⟩
  exact ⟨α, (hΨ α hα).1 h0, rfl⟩

theorem exc3core_inner_of_orth {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} {β : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) (hΨr : ∀ α ∈ Ψ, IsRoot τ α)
    (hΨ : ∀ α, IsRoot τ α → (iform α β = 0 ↔ α ∈ Ψ))
    (hβΨ : ∀ ε, IsRoot τ ε → (∀ δ ∈ Ψ, iform ε δ = 0) → ε = β ∨ ε = -β)
    (w : WeylGroup τ) (hw : (fun γ => w • γ) '' Ψ = Ψ) :
    twistInner Ψ (fun γ => w • γ) := by
  have horth : ∀ δ ∈ Ψ, iform (w • β) δ = 0 := by
    intro δ hδ
    have hδ' : δ ∈ (fun γ => w • γ) '' Ψ := by rw [hw]; exact hδ
    obtain ⟨δ₀, hδ₀, hδeq⟩ := (Set.mem_image (fun γ => w • γ) Ψ δ).mp hδ'
    rw [← hδeq, iform_smul, iform_comm]
    exact (hΨ δ₀ (hΨr δ₀ hδ₀)).2 hδ₀
  have hβpm : w • β = β ∨ w • β = -β := hβΨ (w • β) (IsRoot.smul hβ w) horth
  have hcl : ∀ u : WeylGroup τ, u • β = β →
      u ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ Ψ, s = rootReflection γ} :=
    fun u hu => Subgroup.closure_mono (exc3core_inner_of_orth_aux1 hΨ) (exc3core_stab_closure hu)
  by_cases hfix : w • β = β
  · exact ⟨w, hcl w hfix, fun γ _ => rfl⟩
  · have hneg : w • β = -β := hβpm.resolve_left hfix
    have huβ : (rootReflection β * w) • β = β := by
      rw [mul_smul, hneg, smul_neg, rootReflection_smul_self hβ, neg_neg]
    refine ⟨rootReflection β * w, hcl _ huβ, fun γ hγ => ?_⟩
    have hwγ : w • γ ∈ Ψ := by
      rw [← hw]; exact Set.mem_image_of_mem (fun γ => w • γ) hγ
    have h0 : iform β (w • γ) = 0 :=
      (iform_comm β (w • γ)).trans ((hΨ (w • γ) (hΨr (w • γ) hwγ)).2 hwγ)
    rw [mul_smul, rootReflection_smul_of_iform_eq_zero hβ h0]


end CFSG.LocalAnalysis.GLTheoremA.I167

end
