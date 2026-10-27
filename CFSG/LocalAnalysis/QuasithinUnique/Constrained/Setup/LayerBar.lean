module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerBasic

public section

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.QuasithinUnique.Setup.Offender

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
variable {X : Type*} [Group X]

@[expose] def IsSimpleSub {M : Type*} [AddCommGroup M] [Module k M] (τ : X →* (M ≃ₗ[k] M))
    (H : Subgroup X) (S : Submodule k M) : Prop :=
  Offender.IsInvariant τ H S ∧ S ≠ ⊥ ∧
    ∀ T : Submodule k M, Offender.IsInvariant τ H T → T ≤ S → T = ⊥ ∨ T = S

section Simple

variable {M : Type*} [AddCommGroup M] [Module k M] {τ : X →* (M ≃ₗ[k] M)} {H : Subgroup X}

theorem IsSimpleSub.map {S : Submodule k M} (hS : IsSimpleSub τ H S) {g : X}
    (hg : g ∈ Subgroup.normalizer (H : Set X)) :
    IsSimpleSub τ H (S.map (τ g : M →ₗ[k] M)) := by
  refine ⟨isInvariant_map hS.1 hg, fun h => hS.2.1 ?_, fun T hT hTS => ?_⟩
  · exact (Submodule.map_eq_bot_iff (e := τ g)).1 h
  · have hc : Offender.IsInvariant τ H (T.comap (τ g : M →ₗ[k] M)) := isInvariant_comap hT hg
    have hcS : T.comap (τ g : M →ₗ[k] M) ≤ S := by
      intro x hx
      obtain ⟨y, hy, hyx⟩ := hTS (show τ g x ∈ T from hx)
      have : y = x := (τ g).injective hyx
      rw [← this]; exact hy
    have hTe : T = (T.comap (τ g : M →ₗ[k] M)).map (τ g : M →ₗ[k] M) :=
      (Submodule.map_comap_eq_of_surjective (τ g).surjective T).symm
    rcases hS.2.2 _ hc hcS with h | h
    · left; rw [hTe, h, Submodule.map_bot]
    · right; rw [hTe, h]

theorem IsSimpleSub.inf_eq_bot_or_le {S T : Submodule k M} (hS : IsSimpleSub τ H S)
    (hT : Offender.IsInvariant τ H T) : S ⊓ T = ⊥ ∨ S ≤ T := by
  have hinv : Offender.IsInvariant τ H (S ⊓ T) := fun h hh x hx =>
    ⟨hS.1 h hh x hx.1, hT h hh x hx.2⟩
  rcases hS.2.2 (S ⊓ T) hinv inf_le_left with h | h
  · left; exact h
  · right; rw [← h]; exact inf_le_right

theorem IsSimpleSub.inf_eq_bot_of_ne {S T : Submodule k M} (hS : IsSimpleSub τ H S)
    (hT : IsSimpleSub τ H T) (hne : S ≠ T) : S ⊓ T = ⊥ := by
  rcases hS.inf_eq_bot_or_le hT.1 with h | h
  · exact h
  · rcases hT.2.2 S hS.1 h with h' | h'
    · exact absurd h' hS.2.1
    · exact absurd h' hne

end Simple

section Bar

variable (ρ : X →* (V ≃ₗ[k] V)) (H : Subgroup X)

abbrev bar : V →ₗ[k] (V ⧸ fixSub ρ H) := (fixSub ρ H).mkQ

theorem bar_eq_zero_iff {v : V} : bar ρ H v = 0 ↔ v ∈ fixSub ρ H := by
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

theorem bar_eq_bar_iff {v w : V} : bar ρ H v = bar ρ H w ↔ v - w ∈ fixSub ρ H := by
  rw [← sub_eq_zero, ← map_sub, bar_eq_zero_iff]

variable {ρ H}

theorem IsGoodModule.eq_of_map_bar_eq {I J : Submodule k V} (hI : IsGoodModule ρ H I)
    (hJ : IsGoodModule ρ H J) (h : I.map (bar ρ H) = J.map (bar ρ H)) : I = J := by
  have h1 : I ⊔ fixSub ρ H = J ⊔ fixSub ρ H := by
    have := congrArg (Submodule.comap (bar ρ H)) h
    rwa [Submodule.comap_map_eq, Submodule.comap_map_eq, Submodule.ker_mkQ] at this
  calc I = commSub ρ H I := hI.comm.symm
    _ = commSub ρ H (I ⊔ fixSub ρ H) := (commSub_sup_of_le_fixSub ρ H I _ le_rfl).symm
    _ = commSub ρ H (J ⊔ fixSub ρ H) := by rw [h1]
    _ = commSub ρ H J := commSub_sup_of_le_fixSub ρ H J _ le_rfl
    _ = J := hJ.comm

end Bar

section Normal

variable (ρ : X →* (V ≃ₗ[k] V)) (H : Subgroup X) [H.Normal]

theorem mem_normalizer_of_normal (x : X) : x ∈ Subgroup.normalizer (H : Set X) := by
  rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top x

theorem fixSub_invariant (x : X) {z : V} (hz : z ∈ fixSub ρ H) : ρ x z ∈ fixSub ρ H :=
  (mem_fixSub_map_iff ρ (mem_normalizer_of_normal H x) z).2 hz

@[expose] noncomputable def barHom : X →* ((V ⧸ fixSub ρ H) ≃ₗ[k] (V ⧸ fixSub ρ H)) :=
  quotHom ρ (fixSub ρ H) (fun x _ hz => fixSub_invariant ρ H x hz)

theorem barHom_bar (x : X) (v : V) : barHom ρ H x (bar ρ H v) = bar ρ H (ρ x v) :=
  quotHom_mkQ ρ _ _ x v

theorem isInvariant_map_bar {B : Subgroup X} {U : Submodule k V} (hU : Offender.IsInvariant ρ B U) :
    Offender.IsInvariant (barHom ρ H) B (U.map (bar ρ H)) := by
  rintro b hb _ ⟨u, hu, rfl⟩
  exact ⟨ρ b u, hU b hb u hu, (barHom_bar ρ H b u).symm⟩

theorem map_map_bar (U : Submodule k V) (g : X) :
    (U.map (ρ g : V →ₗ[k] V)).map (bar ρ H) =
      (U.map (bar ρ H)).map (barHom ρ H g : (V ⧸ fixSub ρ H) →ₗ[k] (V ⧸ fixSub ρ H)) := by
  ext x
  simp only [Submodule.mem_map]
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨bar ρ H u, ⟨u, hu, rfl⟩, barHom_bar ρ H g u⟩
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨ρ g u, ⟨u, hu, rfl⟩, (barHom_bar ρ H g u).symm⟩

variable {ρ H}

theorem IsGoodModule.isSimpleSub_bar {I : Submodule k V} (hI : IsGoodModule ρ H I) :
    IsSimpleSub (barHom ρ H) H (I.map (bar ρ H)) := by
  refine ⟨isInvariant_map_bar ρ H hI.inv, ?_, fun S hS hSI => ?_⟩
  · intro h
    apply hI.irr.1
    intro x hx
    have : bar ρ H x ∈ I.map (bar ρ H) := ⟨x, hx, rfl⟩
    rw [h] at this
    exact (bar_eq_zero_iff ρ H).1 (by simpa using this)
  · set U : Submodule k V := I ⊓ S.comap (bar ρ H) with hU
    have hUinv : Offender.IsInvariant ρ H U := by
      intro h hh u hu
      refine ⟨hI.inv h hh u hu.1, ?_⟩
      show bar ρ H (ρ h u) ∈ S
      rw [← barHom_bar ρ H h u]
      exact hS h hh _ hu.2
    have hlo : I ⊓ fixSub ρ H ≤ U := by
      intro x hx
      refine ⟨hx.1, ?_⟩
      show bar ρ H x ∈ S
      rw [(bar_eq_zero_iff ρ H).2 hx.2]
      exact S.zero_mem
    rcases hI.irr.2 U hUinv hlo inf_le_left with h | h
    · left
      refine (Submodule.eq_bot_iff _).2 fun s hs => ?_
      obtain ⟨x, hx, rfl⟩ := hSI hs
      have hxU : x ∈ U := ⟨hx, hs⟩
      rw [h] at hxU
      exact (bar_eq_zero_iff ρ H).2 hxU.2
    · right
      refine le_antisymm hSI ?_
      rintro _ ⟨x, hx, rfl⟩
      have hxU : x ∈ U := by rw [h]; exact hx
      exact hxU.2

theorem IsGoodModule.not_le_fixSub_bar {I : Submodule k V} (hI : IsGoodModule ρ H I) :
    ¬ I.map (bar ρ H) ≤ fixSub (barHom ρ H) H := by
  intro hle
  apply hI.irr.1
  have h1 : commSub ρ H I ≤ fixSub ρ H := by
    rw [commSub_le_iff]
    intro h hh u hu
    have := hle ⟨u, hu, rfl⟩ h hh
    rw [barHom_bar] at this
    exact (bar_eq_bar_iff ρ H).1 this
  rw [hI.comm] at h1
  exact h1

end Normal

end CFSG.QuasithinUnique.Setup.Layer
