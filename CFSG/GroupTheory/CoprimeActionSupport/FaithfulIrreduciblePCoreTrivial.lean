module


public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.GroupTheory.AutomorphismAction.CommutingPGroup

public section

namespace CFSG.GroupTheory.CoprimeActionSupport.FaithfulIrreduciblePCoreTrivial

variable {p : ℕ} [Fact p.Prime] {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod p) V]
  [Finite V]

theorem pCore_eq_bot [Finite G] (ρ : G →* (V ≃ₗ[ZMod p] V)) (hρ : Function.Injective ρ)
    (hirr : ∀ W : Submodule (ZMod p) V, (∀ g, ∀ w ∈ W, ρ g w ∈ W) → W = ⊥ ∨ W = ⊤) :
    CFSG.pCore p G = ⊥ := by
  have normal_pSubgroup_eq_bot (ρ : G →* (V ≃ₗ[ZMod p] V)) (hρ : Function.Injective ρ)
      (hirr : ∀ W : Submodule (ZMod p) V, (∀ g, ∀ w ∈ W, ρ g w ∈ W) → W = ⊥ ∨ W = ⊤)
      (N : Subgroup G) [N.Normal] (hN : IsPGroup p N) : N = ⊥ := by
    let σ : N →* (V ≃ₗ[ZMod p] V) := ρ.comp N.subtype
    have hinv : ∀ g, ∀ w ∈ CFSG.GroupTheory.AutomorphismAction.CommutingPGroup.fixedSubmodule σ,
        ρ g w ∈ CFSG.GroupTheory.AutomorphismAction.CommutingPGroup.fixedSubmodule σ := by
      intro g w hw x
      have hx : g⁻¹ * (x : G) * g ∈ N := by
        have := Subgroup.Normal.conj_mem ‹N.Normal› (x : G) x.2 g⁻¹
        simpa using this
      have h1 := hw ⟨_, hx⟩
      simp only [σ, MonoidHom.comp_apply, Subgroup.coe_subtype, map_mul] at h1 ⊢
      have h2 := congrArg (ρ g) h1
      simp only [LinearEquiv.mul_apply] at h2 ⊢
      have : ρ g (ρ g⁻¹ (ρ (x : G) (ρ g w))) = ρ (x : G) (ρ g w) := by
        rw [← LinearEquiv.mul_apply, ← map_mul]; simp
      rw [this] at h2
      exact h2
    have htop : CFSG.GroupTheory.AutomorphismAction.CommutingPGroup.fixedSubmodule σ = ⊤ := by
      rcases hirr _ hinv with h | h
      · by_cases hV : Nontrivial V
        · exfalso
          obtain ⟨u, -, hu0, hu⟩ :=
            CFSG.GroupTheory.AutomorphismAction.CommutingPGroup.exists_fixed_of_invariant hN σ ⊤
            (fun _ _ _ => Submodule.mem_top) top_ne_bot
          have : u ∈ CFSG.GroupTheory.AutomorphismAction.CommutingPGroup.fixedSubmodule σ := hu
          rw [h] at this
          exact hu0 (by simpa using this)
        · have : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
          exact Subsingleton.elim _ _
      · exact h
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    apply hρ
    ext v
    have : v ∈ CFSG.GroupTheory.AutomorphismAction.CommutingPGroup.fixedSubmodule σ := by
      rw [htop]
      trivial
    simpa [σ] using this ⟨x, hx⟩
  haveI : (CFSG.pCore p G).Normal := inferInstance
  exact normal_pSubgroup_eq_bot ρ hρ hirr _ CFSG.pCore_isPGroup

end CFSG.GroupTheory.CoprimeActionSupport.FaithfulIrreduciblePCoreTrivial
