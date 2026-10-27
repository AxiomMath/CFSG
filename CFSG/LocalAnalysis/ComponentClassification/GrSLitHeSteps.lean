module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitCases

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup

@[expose] def HeldSetting (X : Type) [Group X] [Finite X] (L : Subgroup X) : Prop :=
  IsSimpleGroup X ∧ (∃ x y : X, x * y ≠ y * x) ∧ Assembly.KProper Blueprint.Catalog X ∧
    ¬ OutcomeLocal.UOutcome X ∧ LocallyTwoBalanced X ∧
    (∃ a : X, orderOf a = 2 ∧ L ≤ centralizer ({a} : Set X) ∧
      IsPComponent 2 (L.subgroupOf (centralizer ({a} : Set X)))) ∧
    Nonempty (L ⧸ pPrimeCore 2 L ≃* Blueprint.NativeSporadic.He)

@[expose] def IsFourGroup {G : Type*} [Group G] (A : Subgroup G) : Prop :=
  Nonempty (A ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2))

@[expose] def HeldWGroupStep : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), HeldSetting X L →
    ∀ A : Subgroup X, A ≤ normalizer (L : Set X) → IsFourGroup A → wGroup A = ⊥

@[expose] def HeldStandardStep : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), HeldSetting X L →
    (∀ A : Subgroup X, A ≤ normalizer (L : Set X) → IsFourGroup A → wGroup A = ⊥) →
    IsStandardSubgroup L ∧ pPrimeCore 2 L = ⊥

@[expose] def HeldEndStep : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), HeldSetting X L →
    (∀ A : Subgroup X, A ≤ normalizer (L : Set X) → IsFourGroup A → wGroup A = ⊥) →
    IsStandardSubgroup L → Nonempty (L ≃* Blueprint.NativeSporadic.He) →
    pRank 2 ↥(centralizer (L : Set X)) = 1 → False

theorem nonempty_mulEquiv_held_of_pPrimeCore_eq_bot {L : Type*} [Group L]
    (h : pPrimeCore 2 L = ⊥) (e : L ⧸ pPrimeCore 2 L ≃* Blueprint.NativeSporadic.He) :
    Nonempty (L ≃* Blueprint.NativeSporadic.He) :=
  ⟨(QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq h.symm)).trans e⟩

theorem heldCase_of_steps (hW : HeldWGroupStep) (hStd : HeldStandardStep)
    (hAS : AschbacherSeitzHeldInput) (hEnd : HeldEndStep) : HeldCase := by
  rintro X _ _ _ hnonab hK hU hloc ⟨t, L, ht, hLt, hL, ⟨e⟩⟩
  have hset : HeldSetting X L :=
    ⟨inferInstance, hnonab, hK, hU, hloc, ⟨t, ht, hLt, hL⟩, ⟨e⟩⟩
  have hWL := hW X L hset
  obtain ⟨hstd, hO⟩ := hStd X L hset hWL
  have hHe := nonempty_mulEquiv_held_of_pPrimeCore_eq_bot hO e
  have htop : GeneralizedFitting.subgroup X = ⊤ := GSLit.generalizedFitting_eq_top_of_simple
  let eF : GeneralizedFitting.subgroup X ≃* X :=
    (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
  have hsF : IsSimpleGroup (GeneralizedFitting.subgroup X) := eF.isSimpleGroup
  have hnF : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    exact ⟨eF.symm a, eF.symm b, fun h => hab (eF.symm.injective (by rw [map_mul, map_mul, h]))⟩
  exact hEnd X L hset hWL hstd hHe (hAS X hK hsF hnF L hstd hHe)

end CFSG.ComponentClassification.GrSLit
