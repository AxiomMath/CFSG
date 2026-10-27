module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionRecognizedThreePoint

variable {G Q : Type*} [Group G] [Group Q]

@[expose] def cosetProjection (f : G →* Q) (H : Subgroup G) :
    G ⧸ H → Q ⧸ H.map f :=
  Quotient.map' f (fun a b hab => by
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    simpa only [map_mul, map_inv] using Subgroup.mem_map_of_mem f hab)

theorem cosetProjection_mk (f : G →* Q) (H : Subgroup G) (g : G) :
    cosetProjection f H (QuotientGroup.mk g) = QuotientGroup.mk (f g) := rfl

theorem cosetProjection_smul (f : G →* Q) (H : Subgroup G)
    (g : G) (omega : G ⧸ H) :
    cosetProjection f H (g • omega) = f g • cosetProjection f H omega := by
  refine Quotient.inductionOn' omega fun a => ?_
  change QuotientGroup.mk (f (g * a)) =
    (QuotientGroup.mk (f g * f a) : Q ⧸ H.map f)
  rw [map_mul]

theorem cosetProjection_injective (f : G →* Q) (H : Subgroup G)
    (hker : f.ker ≤ H) : Function.Injective (cosetProjection f H) := by
  intro omega eta
  refine Quotient.inductionOn' omega fun a => ?_
  refine Quotient.inductionOn' eta fun b => ?_
  intro h
  apply Quotient.sound
  change QuotientGroup.leftRel H a b
  rw [QuotientGroup.leftRel_apply]
  have hmem : f (a⁻¹ * b) ∈ H.map f := by
    change (QuotientGroup.mk (f a) : Q ⧸ H.map f) = QuotientGroup.mk (f b) at h
    simpa only [map_mul, map_inv] using QuotientGroup.eq.mp h
  have hpre : a⁻¹ * b ∈ (H.map f).comap f := hmem
  rwa [Subgroup.comap_map_eq_self hker] at hpre

theorem cosetProjection_surjective (f : G →* Q) (H : Subgroup G)
    (hf : Function.Surjective f) : Function.Surjective (cosetProjection f H) := by
  intro omega
  refine Quotient.inductionOn' omega fun q => ?_
  obtain ⟨g, rfl⟩ := hf q
  exact ⟨QuotientGroup.mk g, rfl⟩

@[expose] def cosetProjectionEquiv (f : G →* Q) (H : Subgroup G)
    (hf : Function.Surjective f) (hker : f.ker ≤ H) :
    G ⧸ H ≃ Q ⧸ H.map f :=
  Equiv.ofBijective (cosetProjection f H)
    ⟨cosetProjection_injective f H hker, cosetProjection_surjective f H hf⟩

theorem cosetProjection_fixed_iff (f : G →* Q) (H P : Subgroup G)
    (hker : f.ker ≤ H) (omega : G ⧸ H) :
    (∀ q ∈ P.map f, q • cosetProjection f H omega = cosetProjection f H omega) ↔
      ∀ p ∈ P, p • omega = omega := by
  constructor
  · intro h p hp
    apply cosetProjection_injective f H hker
    rw [cosetProjection_smul]
    exact h (f p) (Subgroup.mem_map_of_mem f hp)
  · intro h q hq
    obtain ⟨p, hp, rfl⟩ := hq
    rw [← cosetProjection_smul, h p hp]

theorem cosetProjection_fixed_card (f : G →* Q) (H P : Subgroup G)
    (hf : Function.Surjective f) (hker : f.ker ≤ H) :
    Nat.card {omega : G ⧸ H // ∀ p ∈ P, p • omega = omega} =
      Nat.card {omega : Q ⧸ H.map f // ∀ q ∈ P.map f, q • omega = omega} := by
  let e := cosetProjectionEquiv f H hf hker
  apply Nat.card_congr
  exact e.subtypeEquiv (fun omega =>
    (cosetProjection_fixed_iff f H P hker omega).symm)

end CFSG.ProperTwoGeneratedCore.LocalCriterionRecognizedThreePoint
