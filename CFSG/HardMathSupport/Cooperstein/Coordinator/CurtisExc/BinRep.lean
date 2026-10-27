module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActorBinary
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Basic
public import CFSG.Quasithin.Background.SmithCurtisBasic

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

open CFSG.Quasithin.SmithCurtis CFSG.QuasithinUnique.Setup

theorem exists_simpleRep_of_isIrrOn {W₀ : Type} [CommGroup W₀] [Finite W₀]
    (hW : ∀ w : W₀, w * w = 1) {L : Subgroup (MulAut W₀)} (hirr : X1.IsIrrOn L)
    {S : Type} [Group S] (ι : S ≃* L) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 2) V) (_ : Finite V)
      (ρ : Representation (ZMod 2) S V),
      IsSimpleRep ρ ∧ Function.Injective ρ ∧ Nat.card V = Nat.card W₀ := by
  classical
  obtain ⟨V, _, _, _, ⟨θ⟩⟩ := Layer.Actor.exists_binModel_of_binary hW
  set Ψ : MulAut W₀ ≃* (Module.End (ZMod 2) V)ˣ :=
    (Layer.binPsi θ).trans (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).symm
    with hΨdef
  have hΨ : ∀ (φ : MulAut W₀) (w : V),
      (Ψ φ).val w = Multiplicative.toAdd (θ (φ (θ.symm (Multiplicative.ofAdd w)))) :=
    fun _ _ => rfl
  set c : W₀ → V := fun x => Multiplicative.toAdd (θ x) with hc
  have hc_symm : ∀ w : V, c (θ.symm (Multiplicative.ofAdd w)) = w := fun w => by simp [hc]
  have hc_mul : ∀ x y : W₀, c (x * y) = c x + c y := fun x y => by simp [hc]
  have hc_inv : ∀ x : W₀, c x⁻¹ = - c x := fun x => by simp [hc]
  have hc_inj : Function.Injective c := fun x y h => θ.injective (Multiplicative.toAdd.injective h)
  have hc_one : ∀ x : W₀, c x = 0 ↔ x = 1 := fun x => by
    constructor
    · intro h
      apply hc_inj
      rw [h]
      simp [hc]
    · rintro rfl
      simp [hc]
  have hΨc : ∀ (φ : MulAut W₀) (x : W₀), (Ψ φ).val (c x) = c (φ x) := fun φ x => by
    rw [hΨ]
    simp [hc]
  have hWnt : Nontrivial V := by
    have := hirr.1
    obtain ⟨x, hx⟩ := exists_ne (1 : W₀)
    exact ⟨⟨c x, 0, fun h => hx ((hc_one x).mp h)⟩⟩
  have hFin : Finite V := inferInstance
  let ρ : Representation (ZMod 2) S V :=
    (Units.coeHom (Module.End (ZMod 2) V)).comp (Ψ.toMonoidHom.comp (L.subtype.comp ι.toMonoidHom))
  have hρ : ∀ (s : S) (v : V), ρ s v = (Ψ (ι s : MulAut W₀)).val v := fun _ _ => rfl
  refine ⟨V, inferInstance, inferInstance, hFin, ρ, ⟨hWnt, fun U hU => ?_⟩, ?_, ?_⟩
  · set U₀ : Subgroup W₀ :=
      { carrier := {x | c x ∈ U}
        one_mem' := by
          show c 1 ∈ U
          rw [(hc_one 1).mpr rfl]
          exact U.zero_mem
        mul_mem' := fun {x y} hx hy => by
          show c (x * y) ∈ U
          rw [hc_mul]
          exact U.add_mem hx hy
        inv_mem' := fun {x} hx => by
          show c x⁻¹ ∈ U
          rw [hc_inv]
          exact U.neg_mem hx } with hU₀
    have hU₀inv : ∀ g ∈ L, ∀ u ∈ U₀, g u ∈ U₀ := by
      intro g hg u hu
      have h1 := hU (ι.symm ⟨g, hg⟩) (c u) hu
      rw [hρ, MulEquiv.apply_symm_apply] at h1
      show c (g u) ∈ U
      rw [← hΨc]
      exact h1
    rcases hirr.2 U₀ hU₀inv with h0 | h0
    · left
      rw [eq_bot_iff]
      intro w hw
      have hx : θ.symm (Multiplicative.ofAdd w) ∈ U₀ := by
        show c _ ∈ U
        rw [hc_symm]
        exact hw
      rw [h0, Subgroup.mem_bot] at hx
      rw [Submodule.mem_bot, ← hc_symm w, hx]
      exact (hc_one 1).mpr rfl
    · right
      rw [eq_top_iff]
      intro w _
      have hx : θ.symm (Multiplicative.ofAdd w) ∈ U₀ := by rw [h0]; exact Subgroup.mem_top _
      have hx' : c (θ.symm (Multiplicative.ofAdd w)) ∈ U := hx
      rwa [hc_symm] at hx'
  · intro s t hst
    have h1 : (Ψ (ι s : MulAut W₀)) = Ψ (ι t : MulAut W₀) := by
      apply Units.ext
      exact hst
    exact ι.injective (Subtype.ext (Ψ.injective h1))
  · exact (Layer.Actor.natCard_eq θ).symm

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc
