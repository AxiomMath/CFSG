module

public import CFSG.GroupTheory.ABGLocalTools.PStabilityCore
public import CFSG.GroupTheory.ABGLocalTools.PStabilityCoreSL2
public import CFSG.GroupTheory.ABGLocalTools.PStabilityCoreQuaternion
public import CFSG.GroupTheory.ABGLocalTools.PStabilityBundle
import CFSG.GroupTheory.ABGLocalTools.RelativeStability
public import CFSG.GroupTheory.ABGLocalTools.PStabilityDefs

public section

open Subgroup

namespace CFSG.ABGLocalTools

open CFSG.QuasiDihedralFusion CFSG.ABGQGroups

universe u

@[expose] def OuterQuadraticCase (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ {G M : Type u} [Group G] [Finite G] [Group M] (π : G →* M), Function.Surjective π →
    Odd (Nat.card π.ker) → ∀ {V : Type u} [AddCommGroup V] [Module (ZMod p) V]
    [FiniteDimensional (ZMod p) V] (ρ : G →* LinearMap.GeneralLinearGroup (ZMod p) V),
    Function.Injective ρ → ∀ {x : G}, ((ρ x : V →ₗ[ZMod p] V) - 1) ^ 2 = 0 →
    ∀ (J : Subgroup M) [J.Normal] {F : Type} [Field F] [Finite F], Odd (Nat.card F) →
    ¬ p ∣ Nat.card F → (J ≃* Matrix.SpecialLinearGroup (Fin 2) F) →
    IsPGroup 2 (centralizer (J : Set M)) → π x ^ p = 1 → π x ∈ J

variable {H : Type u} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]

theorem mem_pCore_quotient_of_qGroup
    (hp : p ≠ 2) {q : ℕ} (hst : QGroupStanding p q H)
    (hchar : ¬ p ∣ q) (hfacts : QGroupStabilityFacts q H) (hchoice : SL2ElementChoice)
    (hborel : SL2BorelOfSplitElement) (hoddn : SL2OddNormal) (hdickson : SL2DicksonQuotient)
    (hout : OuterQuadraticCase.{u} p) (L : Subgroup H) [L.Normal] {V : Type u} [AddCommGroup V]
    [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    (ρ : H ⧸ L →* LinearMap.GeneralLinearGroup (ZMod p) V) (hρ : Function.Injective ρ) (x : H)
    (hxp : ∃ k : ℕ, x ^ p ^ k = 1) (hx : ((ρ (x : H ⧸ L) : V →ₗ[ZMod p] V) - 1) ^ 2 = 0) :
    (x : H ⧸ L) ∈ pCore p (H ⧸ L) := by
  obtain ⟨R, K, hRK⟩ := hst.charPower.1
  by_cases hL : L ≤ CFSG.oddCore H
  ·
    have hLO : L ≤ (CFSG.oddCore H).comap (MonoidHom.id H) := by rwa [comap_id]
    set π := QuotientGroup.map L (CFSG.oddCore H) (MonoidHom.id H) hLO with hπdef
    have hπ : Function.Surjective π := by
      refine QuotientGroup.map_surjective_of_surjective _ _ _ (fun y => ?_) hLO
      obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
      exact ⟨h, rfl⟩
    have hker : Odd (Nat.card π.ker) := by
      rw [hπdef, QuotientGroup.ker_map, comap_id]
      exact Odd.of_dvd_nat odd_card_oddCore (card_map_dvd _ _)
    obtain ⟨J, F, hFf, hFfin, hJn, hFq, ⟨e⟩, hC⟩ := hfacts.layer
    have hF : Odd (Nat.card F) := hFq ▸ hst.charPower.2.1
    have h5 : 5 < Nat.card F := hFq ▸ hst.five_lt
    have hpF : ¬ p ∣ Nat.card F := hFq ▸ hchar
    have hxp' : ∃ k : ℕ, (x : H ⧸ L) ^ p ^ k = 1 := by
      obtain ⟨k, hk⟩ := hxp
      exact ⟨k, by rw [← QuotientGroup.mk_pow, hk, QuotientGroup.mk_one]⟩
    have h1 := map_eq_one_of_quadratic hp π hπ hker ρ hρ hx hxp' J hF h5 hpF e hchoice hborel
      hoddn hdickson (fun y hy hyp => hout π hπ hker ρ hρ hy J hF hpF e hC hyp)
    exact mem_pCore_of_map_eq_one hp π hker ρ hρ hx h1
  ·
    exact mem_pCore_quotient_of_not_le_oddCore hp hRK
      (isCyclic_centerOf_of_hasQDOrWreathedSylow hst.sylow R) L hL ρ hρ x hxp hx

theorem isPStable_of_qGroup_of_facts
    (hp : p ≠ 2) {q : ℕ} (hst : QGroupStanding p q H)
    (hchar : ¬ p ∣ q) (hOp : pCore p H ≠ ⊥) (hfacts : QGroupStabilityFacts q H)
    (hchoice : SL2ElementChoice) (hborel : SL2BorelOfSplitElement) (hoddn : SL2OddNormal)
    (hdickson : SL2DicksonQuotient) (hout : OuterQuadraticCase.{u} p) : IsPStable p H :=
  isPStable_of_quadratic_quotients hOp fun L _ _ _ _ _ ρ hρ x hxp hx =>
    map_pCore_le_of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
      ⟨_, mem_pCore_quotient_of_qGroup hp hst hchar hfacts hchoice hborel hoddn hdickson hout L
        ρ hρ x hxp hx, rfl⟩

end CFSG.ABGLocalTools
