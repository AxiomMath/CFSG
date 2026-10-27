module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftOffender
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesFour

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique
  CFSG.Quasithin.B6 CFSG.QuasithinUnique.Setup.SL2Modules
  CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
open scoped MatrixGroups LinearAlgebra.Projectivization commutatorElement
open Projectivization

universe v

section Root

variable {F : Type*} [Field F] [Fintype F]

theorem natCard_rootSet (ℓ : Submodule F (Fin 2 → F)) (hℓ : Module.finrank F ℓ = 1)
    (U : Subgroup SL(2, F))
    (hU : ∀ g : SL(2, F), g ∈ U ↔ ((∀ v ∈ ℓ, (g : Matrix (Fin 2) (Fin 2) F).mulVec v = v) ∧
      ∀ v, (g : Matrix (Fin 2) (Fin 2) F).mulVec v - v ∈ ℓ)) :
    Nat.card U = Fintype.card F := by
  obtain ⟨⟨v, hvmem⟩, hv0, hall⟩ := finrank_eq_one_iff'.1 hℓ
  have hv0' : v ≠ 0 := fun h => hv0 (Subtype.ext h)
  have hℓv : ℓ = Submodule.span F {v} := by
    apply le_antisymm
    · intro w hw
      obtain ⟨c, hc⟩ := hall ⟨w, hw⟩
      have : c • v = w := congrArg Subtype.val hc
      rw [← this]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact hvmem
  have he0 : (Pi.single 0 1 : Fin 2 → F) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  obtain ⟨x, hx⟩ := exists_smul_eq_of_ne_zero (Pi.single 0 1 : Fin 2 → F) v he0 hv0'
  have hℓx : ℓ = rootLine x := by rw [hℓv, rootLine, hx]
  have hmem : ∀ g : SL(2, F), g ∈ U ↔ x⁻¹ * g * x ∈ (upperUnipotent (F := F)).range := by
    intro g
    rw [conj_mem_range_iff_fixes_line, ← hℓx, hU g]
    rfl
  have e : Nat.card U = Nat.card (upperUnipotent (F := F)).range := by
    refine Nat.card_congr
      { toFun := fun g => ⟨x⁻¹ * g * x, (hmem g).1 g.2⟩
        invFun := fun h => ⟨x * h * x⁻¹, (hmem _).2 (by simp [mul_assoc])⟩
        left_inv := fun g => by apply Subtype.ext; simp [mul_assoc]
        right_inv := fun h => by apply Subtype.ext; simp [mul_assoc] }
  rw [e, upperUnipotent_card, Nat.card_eq_fintype_card]

end Root

section Nat

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] {F : Type} [Field F]

@[expose] def thetaL (L : Subgroup (V ≃ₗ[ZMod 2] V))
    (α : (↥L ⧸ Subgroup.center ↥L) ≃* SL(2, F)) : ↥L →* SL(2, F) :=
  α.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))

theorem thetaL_apply (L : Subgroup (V ≃ₗ[ZMod 2] V))
    (α : (↥L ⧸ Subgroup.center ↥L) ≃* SL(2, F)) (l : ↥L) :
    thetaL L α l = α (QuotientGroup.mk l) := rfl

theorem thetaL_injective {L : Subgroup (V ≃ₗ[ZMod 2] V)}
    (α : (↥L ⧸ Subgroup.center ↥L) ≃* SL(2, F)) (hc : Subgroup.center ↥L = ⊥) :
    Function.Injective (thetaL L α) := by
  intro a b hab
  have h1 : (QuotientGroup.mk a : ↥L ⧸ Subgroup.center ↥L) = QuotientGroup.mk b := α.injective hab
  rw [QuotientGroup.eq, hc, Subgroup.mem_bot, inv_mul_eq_one] at h1
  exact h1

variable [Fintype F]

@[expose] def NatData (L A : Subgroup (V ≃ₗ[ZMod 2] V))
    (α : (↥L ⧸ Subgroup.center ↥L) ≃* SL(2, F)) : Prop :=
  A ≤ L ∧ Nat.card A = Fintype.card F ∧
    ∃ β : (↥(commGL L ⊤) ⧸ fixIn L (commGL L ⊤)) ≃+ (Fin 2 → F),
      (∀ (l : ↥L) (u u' : ↥(commGL L ⊤)), (u' : V) = (l : V ≃ₗ[ZMod 2] V) (u : V) →
        β (Submodule.Quotient.mk u') =
          (thetaL L α l : Matrix (Fin 2) (Fin 2) F).mulVec (β (Submodule.Quotient.mk u))) ∧
      ∃ ℓ : Submodule F (Fin 2 → F), Module.finrank F ℓ = 1 ∧
        ∀ g : SL(2, F), g ∈ (A.subgroupOf L).map (thetaL L α) ↔
          ((∀ v ∈ ℓ, (g : Matrix (Fin 2) (Fin 2) F).mulVec v = v) ∧
            ∀ v, (g : Matrix (Fin 2) (Fin 2) F).mulVec v - v ∈ ℓ)

theorem natData_of_natural {L A : Subgroup (V ≃ₗ[ZMod 2] V)} {I : Submodule (ZMod 2) V}
    (α : (↥L ⧸ Subgroup.center ↥L) ≃* SL(2, F))
    (hAn : A ≤ Subgroup.normalizer (L : Set (V ≃ₗ[ZMod 2] V)))
    (hI : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (L ⊔ A) I)
    (hker : (actOn L A I hAn hI L le_sup_left).ker = Subgroup.center ↥L)
    (hc : Subgroup.center ↥L = ⊥) (hAL : A ≤ L) (hIdef : I = commGL L ⊤)
    (θ : ↥(Lbar L A I hAn hI) ≃* SL(2, F))
    (hθ : ∀ l : ↥L, θ ⟨actOn L A I hAn hI L le_sup_left l, ⟨l, rfl⟩⟩ = α (QuotientGroup.mk l))
    (hnat : NaturalAlt (Lbar L A I hAn hI) (Abar L A I hAn hI) θ) : NatData L A α := by
  obtain ⟨-, β, hβ, ℓ, hℓ1, hℓ⟩ := hnat
  have hinjL : Function.Injective (actOn L A I hAn hI L le_sup_left) := by
    rw [← MonoidHom.ker_eq_bot_iff, hker, hc]
  have hroot : ∀ g : SL(2, F), g ∈ (A.subgroupOf L).map (thetaL L α) ↔
      g ∈ (((Abar L A I hAn hI).subgroupOf (Lbar L A I hAn hI)).map θ.toMonoidHom) := by
    intro g
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨⟨actOn L A I hAn hI L le_sup_left a, ⟨a, rfl⟩⟩, ?_, hθ a⟩
      exact ⟨⟨a.1, ha⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨l, hl⟩ := x.2
      obtain ⟨a, ha⟩ := hx
      have e1 : actOn L A I hAn hI L le_sup_left ⟨a.1, hAL a.2⟩ =
          actOn L A I hAn hI L le_sup_left l := by rw [hl]; exact ha
      have e2 : (⟨a.1, hAL a.2⟩ : ↥L) = l := hinjL e1
      have e3 : x = ⟨actOn L A I hAn hI L le_sup_left l, ⟨l, rfl⟩⟩ := Subtype.ext hl.symm
      refine ⟨⟨a.1, hAL a.2⟩, a.2, ?_⟩
      show thetaL L α ⟨a.1, hAL a.2⟩ = θ x
      rw [e3, hθ l, ← e2]
      rfl
  refine ⟨hAL, ?_, ?_⟩
  · have hinj' : Function.Injective (thetaL L α) := thetaL_injective α hc
    have h1 : Nat.card ↥A = Nat.card ↥((A.subgroupOf L).map (thetaL L α)) := by
      rw [Subgroup.card_map_of_injective hinj']
      exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv).symm
    rw [h1]
    exact natCard_rootSet ℓ hℓ1 _ fun g => (hroot g).trans (hℓ g)
  · subst hIdef
    refine ⟨β, fun l u u' hu' => ?_, ℓ, hℓ1, fun g => (hroot g).trans (hℓ g)⟩
    have e1 : (Submodule.Quotient.mk u' : ↥(commGL L ⊤) ⧸ fixIn L (commGL L ⊤)) =
        actOn L A (commGL L ⊤) hAn hI L le_sup_left l (Submodule.Quotient.mk u) := by
      rw [actOn_L_mk]
      congr 1
      apply Subtype.ext
      rw [resSub_apply]
      exact hu'
    rw [e1]
    have := hβ ⟨actOn L A (commGL L ⊤) hAn hI L le_sup_left l, ⟨l, rfl⟩⟩
      (Submodule.Quotient.mk u)
    rw [hθ l] at this
    exact this

end Nat

end CFSG.QuasithinUnique.Setup.Lift
