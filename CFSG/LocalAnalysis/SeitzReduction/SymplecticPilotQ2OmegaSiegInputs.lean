module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14OmegaSpA

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped commutatorElement

@[expose] def SpTwoLagPerfectInput : Prop :=
  ∀ (N j : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 → 3 ≤ j → 2 * j = N →
    ⁅centralizer ({spARep N j} : Set (StatedSp N K)),
      centralizer ({spARep N j} : Set (StatedSp N K))⁆ =
      centralizer ({spARep N j} : Set (StatedSp N K))

@[expose] def SpTwoLagClosureInput : Prop :=
  ∀ (N j : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 → 3 ≤ j → 2 * j = N →
    ∀ (H : Type) [Group H] (Φ₁ Φ₂ : StatedSp N K →* H), Function.Injective Φ₁ →
      Function.Injective Φ₂ → Φ₁ (spARep N j) = Φ₂ (spARep N j) →
      (centralizer ({spARep N j} : Set (StatedSp N K))).map Φ₁ =
        (centralizer ({spARep N j} : Set (StatedSp N K))).map Φ₂ →
      ∃ c d : StatedSp N K,
        (∃ y ∈ centralizer ({spARep N j} : Set (StatedSp N K)),
          c * y * c⁻¹ ∉ centralizer ({spARep N j} : Set (StatedSp N K))) ∧
        Φ₁ (spARep N j) * Φ₂ (c * spARep N j * c⁻¹) = Φ₁ (d * spARep N 1 * d⁻¹)

section Perfect

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

omit [Finite G] in
theorem commutatorElement_mul_central_eq {t p q : G} (hp : Commute t p) (hq : Commute t q) :
    ⁅t * p, q⁆ = ⁅p, q⁆ ∧ ⁅p, t * q⁆ = ⁅p, q⁆ := by
  have h1 : Commute t (p * q * p⁻¹) := (hp.mul_right hq).mul_right hp.inv_right
  have h2 : Commute t (p * q * p⁻¹ * q⁻¹) := h1.mul_right hq.inv_right
  refine ⟨?_, ?_⟩
  · rw [commutatorElement_def, commutatorElement_def]
    calc t * p * q * (t * p)⁻¹ * q⁻¹ = t * (p * q * p⁻¹) * t⁻¹ * q⁻¹ := by group
      _ = (p * q * p⁻¹) * t * t⁻¹ * q⁻¹ := by rw [h1.eq]
      _ = p * q * p⁻¹ * q⁻¹ := by group
  · rw [commutatorElement_def, commutatorElement_def]
    calc p * (t * q) * p⁻¹ * (t * q)⁻¹ = t * (p * q * p⁻¹) * q⁻¹ * t⁻¹ := by
          rw [show p * (t * q) * p⁻¹ * (t * q)⁻¹ = (p * t) * q * p⁻¹ * q⁻¹ * t⁻¹ by group,
            ← hp.eq]
          group
      _ = t * (p * q * p⁻¹ * q⁻¹) * t⁻¹ := by group
      _ = p * q * p⁻¹ * q⁻¹ := by rw [h2.eq]; group

end Perfect

section Embed

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] {N : ℕ}

variable (e : L ≃* StatedSp N K) (c : G) in
@[expose] def conjEmbed : StatedSp N K →* G :=
  (MulAut.conj c⁻¹).toMonoidHom.comp (L.subtype.comp e.symm.toMonoidHom)

theorem conjEmbed_apply (e : L ≃* StatedSp N K) (c : G) (y : StatedSp N K) :
    conjEmbed e c y = c⁻¹ * ((e.symm y : L) : G) * c := by
  simp [conjEmbed]

theorem conjEmbed_injective (e : L ≃* StatedSp N K) (c : G) :
    Function.Injective (conjEmbed e c) := by
  intro y y' h
  rw [conjEmbed_apply, conjEmbed_apply] at h
  have h1 : ((e.symm y : L) : G) = ((e.symm y' : L) : G) := by
    have := congrArg (fun z => c * z * c⁻¹) h
    simpa [mul_assoc] using this
  exact e.symm.injective (Subtype.ext h1)

theorem conjEmbed_mem (e : L ≃* StatedSp N K) {c : G} (hc : c ∈ L) (y : StatedSp N K) :
    conjEmbed e c y ∈ L := by
  rw [conjEmbed_apply]
  exact L.mul_mem (L.mul_mem (L.inv_mem hc) (e.symm y).2) hc

theorem map_centralizer_conjEmbed (e : L ≃* StatedSp N K) {c : G} (hc : c ∈ L)
    (m : StatedSp N K) :
    (centralizer ({m} : Set (StatedSp N K))).map (conjEmbed e c) =
      L ⊓ centralizer ({conjEmbed e c m} : Set G) := by
  ext l
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨conjEmbed_mem e hc y, mem_centralizer_singleton_iff.2 ?_⟩
    rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.1 hy]
  · rintro ⟨hl, hlm⟩
    set l' : G := c * l * c⁻¹ with hl'
    have hl'L : l' ∈ L := L.mul_mem (L.mul_mem hc hl) (L.inv_mem hc)
    have hback : conjEmbed e c (e ⟨l', hl'L⟩) = l := by
      rw [conjEmbed_apply, MulEquiv.symm_apply_apply]
      change c⁻¹ * (c * l * c⁻¹) * c = l
      group
    refine ⟨e ⟨l', hl'L⟩, mem_centralizer_singleton_iff.2 ?_, hback⟩
    apply conjEmbed_injective e c
    rw [map_mul, map_mul, hback]
    exact mem_centralizer_singleton_iff.1 hlm

end Embed

theorem card_centralizer_conj_two {X : Type*} [Group X] (d m : X) :
    Nat.card (centralizer ({d * m * d⁻¹} : Set X)) = Nat.card (centralizer ({m} : Set X)) := by
  refine Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj d⁻¹).toEquiv fun y => ?_)
  simp only [mem_centralizer_singleton_iff, MulAut.conj_apply, MulEquiv.toEquiv_eq_coe,
    MulEquiv.coe_toEquiv]
  constructor
  · intro h
    calc d⁻¹ * y * d⁻¹⁻¹ * m = d⁻¹ * (y * (d * m * d⁻¹)) * d := by group
      _ = d⁻¹ * ((d * m * d⁻¹) * y) * d := by rw [h]
      _ = m * (d⁻¹ * y * d⁻¹⁻¹) := by group
  · intro h
    calc y * (d * m * d⁻¹) = d * ((d⁻¹ * y * d⁻¹⁻¹) * m) * d⁻¹ := by group
      _ = d * (m * (d⁻¹ * y * d⁻¹⁻¹)) * d⁻¹ := by rw [h]
      _ = d * m * d⁻¹ * y := by group

end CFSG.SeitzReduction.SymplecticPilot
