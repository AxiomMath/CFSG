module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.Fusion
public import CFSG.Sporadic.Recognition.Fi22MultiplierRho

public section

namespace CFSG.EvenSporadicStandard.TwoFi22

open Subgroup CFSG.Sporadic.Fi23 CFSG.Sporadic.Recognition.Fi22Multiplier

theorem nonempty_mulEquiv_of_unique {X : Type} [Group X] {R : Type} [Group R]
    (hD : ∀ (D : Type) [Group D] (φ : D →* X), Function.Surjective φ → Group.IsPerfect D →
      Nat.card φ.ker = 2 → Nonempty (D ≃* R))
    {Λ : Type} [Group Λ] (hperf : commutator Λ = ⊤) (h2 : Nat.card (center Λ) = 2)
    (e : Λ ⧸ center Λ ≃* X) : Nonempty (Λ ≃* R) := by
  let φ : Λ →* X := e.toMonoidHom.comp (QuotientGroup.mk' (center Λ))
  have hφ : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker = center Λ := by
    ext x
    rw [MonoidHom.mem_ker]
    show e (QuotientGroup.mk x) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  exact hD Λ φ hφ (Group.isPerfect_def.2 hperf) (by rw [hker]; exact h2)

theorem unique_double_cover_R332 :
    ∀ (D : Type) [Group D] (φ : D →* CFSG.Blueprint.NativeSporadic.Fi22),
      Function.Surjective φ → Group.IsPerfect D → Nat.card φ.ker = 2 → Nonempty (D ≃* R332) :=
  fun _ _ φ hφ hperf hk => nonempty_mulEquiv_R332_of_doubleCover φ hφ hperf hk

theorem exists_iso_Cd
    {Λ : Type} [Group Λ]
    (hq : CFSG.Open.IsQuasisimple Λ) (h2 : Nat.card (center Λ) = 2)
    (hQ : CFSG.Blueprint.NativeSporadic.IsSporadic (Λ ⧸ center Λ) .Fi22) {τ : Λ}
    (hτ : τ ∈ center Λ) (hτ1 : τ ≠ 1) : ∃ ψ : Λ ≃* Cd, ((ψ τ : Cd) : J) = d := by
  obtain ⟨e⟩ := hQ
  obtain ⟨f1⟩ := nonempty_mulEquiv_of_unique unique_double_cover_R332 hq.1 h2 e
  obtain ⟨f2⟩ := nonempty_mulEquiv_of_unique unique_double_cover_R332 commutator_C card_center_C
    (quotCenterEquiv.trans CFSG.Sporadic.Fi22.fi22EquivJ.symm)
  let ψ := f1.trans f2.symm
  refine ⟨ψ, ?_⟩
  have hc : ψ τ ∈ center Cd := by
    rw [Subgroup.mem_center_iff] at hτ ⊢
    intro c
    have := hτ (ψ.symm c)
    calc c * ψ τ = ψ (ψ.symm c * τ) := by simp
      _ = ψ (τ * ψ.symm c) := by rw [this]
      _ = ψ τ * c := by simp
  rw [center_C] at hc
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hc
  have hk' : d ^ k = ((ψ τ : Cd) : J) := by
    have := congrArg Subtype.val hk
    rwa [Subgroup.coe_zpow] at this
  rcases d_zpow k with h | h
  · exfalso
    apply hτ1
    apply ψ.injective
    apply Subtype.ext
    rw [← hk', h, map_one]
    rfl
  · rw [← hk', h]

set_option maxRecDepth 100000 in
@[expose] noncomputable def modelOfIso {G : Type} [Group G]
    {t : G} (ψ : centralizer ({t} : Set G) ≃* Cd)
    (hψ : (ψ ⟨t, mem_centralizer_singleton_iff.2 rfl⟩ : Cd) = dCd) : Model G t where
  ψ := (Cd.subtype).comp (ψ : centralizer ({t} : Set G) →* Cd)
  inj := fun a b h => ψ.injective (Subtype.ext (by exact h))
  range c := ⟨fun h => ⟨ψ.symm ⟨c, mem_Cd.2 h⟩, by
    show ((ψ (ψ.symm ⟨c, mem_Cd.2 h⟩) : Cd) : J) = c
    rw [ψ.apply_symm_apply]⟩, fun ⟨x, hx⟩ => by
    subst hx
    exact mem_Cd.1 (ψ x).2⟩
  map_t := by
    show ((ψ ⟨t, mem_centralizer_singleton_iff.2 rfl⟩ : Cd) : J) = d
    rw [hψ]
    rfl

end CFSG.EvenSporadicStandard.TwoFi22
