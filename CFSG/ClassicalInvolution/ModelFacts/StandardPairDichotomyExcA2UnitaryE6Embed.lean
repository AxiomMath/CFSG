module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryEmbed
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2E6Data

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.RootSystem CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Universal CFSG.LieType
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.Timmesfeld
  CFSG.ClassicalInvolution.WeakCT CFSG.LocalAnalysis.ComponentInitial CFSG.Timmesfeld.LevisExtras
open scoped MatrixGroups

section E6

@[expose] def idxE6 (n : ℕ) (h : n < 6 := by decide) : Fin (Tag.rank .E6) := ⟨n, h⟩

theorem neighbour_E6_adj : ∀ i : Fin (Tag.rank .E6), ∃ l,
    Tag.cartan .E6 i l = -1 ∧ Tag.cartan .E6 l i = -1 := by
  intro i
  fin_cases i <;> decide

@[expose] def transportWordE6 : List (Fin (Tag.rank .E6)) :=
  [idxE6 3, idxE6 2, idxE6 1, idxE6 3, idxE6 4, idxE6 5, idxE6 0, idxE6 2, idxE6 3,
   idxE6 4, idxE6 1, idxE6 3, idxE6 0]

theorem simpleWordAct_transportE6_two :
    simpleWordAct .E6 transportWordE6 (Pi.single (⟨2, by decide⟩ : Fin (Tag.rank .E6)) 1) =
      thetaE6' := by
  unfold transportWordE6 simpleWordAct idxE6
  decide +kernel

theorem simpleWordAct_transportE6_zero :
    simpleWordAct .E6 transportWordE6 (Pi.single (⟨0, by decide⟩ : Fin (Tag.rank .E6)) 1) =
      deltaE6 := by
  unfold transportWordE6 simpleWordAct idxE6
  decide +kernel

theorem exists_sl3_simple_E6 (F : Type) [Field F] [Finite F] :
    ∃ emb : SL(3, F) →* ↥(adjointGroup .E6 F), Function.Injective emb ∧
      ∀ c, emb (tv 0 1 c) = xPar (rootOperatorFamily .E6)
          (Pi.single (⟨2, by decide⟩ : Fin (Tag.rank .E6)) 1) c ∧
        emb (tv 1 0 c) = xPar (rootOperatorFamily .E6)
          (-Pi.single (⟨2, by decide⟩ : Fin (Tag.rank .E6)) 1) c ∧
        emb (tv 1 2 c) = xPar (rootOperatorFamily .E6)
          (Pi.single (⟨0, by decide⟩ : Fin (Tag.rank .E6)) 1) c ∧
        emb (tv 2 1 c) = xPar (rootOperatorFamily .E6)
          (-Pi.single (⟨0, by decide⟩ : Fin (Tag.rank .E6)) 1) c := by
  obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan
    (adjDatum (rootOperatorFamily .E6) F).isFiniteType
    (Dv := (adjDatum (rootOperatorFamily .E6) F).divisible) rfl
  have hE := adjDatum_chevalleyExtras _ F e6AdjData_valid noG2_E6 neighbour_E6_adj O
    (commC (rootOperatorFamily .E6) e6AdjData_valid)
    (commutatorFormula_commC e6AdjData_valid noG2_E6 _ (adjDatum_roots _ F) O)
  have hdiv : (adjDatum (rootOperatorFamily .E6) F).divisible = ∅ := rfl
  obtain ⟨emb, hinj, -, hx⟩ := exists_sl3Levi hE hdiv (i := ⟨2, by show 2 < 6; decide⟩)
    (j := ⟨0, by show 0 < 6; decide⟩) (k := ⟨3, by show 3 < 6; decide⟩)
    (by intro h; have := congrArg Fin.val h; simp at this)
    (by show Blueprint.Chevalley.Tag.cartan .E6 ⟨2, by decide⟩ ⟨0, by decide⟩ = -1; decide)
    (by show Blueprint.Chevalley.Tag.cartan .E6 ⟨0, by decide⟩ ⟨2, by decide⟩ = -1; decide)
    (by show ¬ (3 : ℤ) ∣ Blueprint.Chevalley.Tag.cartan .E6 ⟨2, by decide⟩ ⟨3, by decide⟩ +
      2 * Blueprint.Chevalley.Tag.cartan .E6 ⟨0, by decide⟩ ⟨3, by decide⟩; decide)
  exact ⟨emb, hinj, hx⟩

theorem nonempty_a2Embedding_E6 (F : Type) [Field F] [Finite F] :
    Nonempty (A2Embedding .E6 thetaE6 deltaE6 F) := by
  obtain ⟨emb, hinj, hx⟩ := exists_sl3_simple_E6 F
  have hcoe : ∀ {γ : Fin (Tag.rank .E6) → ℤ}, IsRoot .E6 γ → ∀ c : F,
      ((xPar (rootOperatorFamily .E6) γ c : ↥(adjointGroup .E6 F)) : ModGL .E6 F) =
        pinnedX .E6 F γ ((((rootOperatorFamily .E6).pinnedFamilySign γ : ℤ) : F) * c) :=
    fun hγ c => CFSG.ClassicalInvolution.Balance.coe_xPar_eq_pinnedX hγ c
  have hsg : ∀ γ : Fin (Tag.rank .E6) → ℤ,
      (((rootOperatorFamily .E6).pinnedFamilySign γ : ℤ) : F) *
        (((rootOperatorFamily .E6).pinnedFamilySign γ : ℤ) : F) = 1 := fun γ =>
    (rootOperatorFamily .E6).pinnedFamilySign_mul_self F γ
  refine nonempty_a2Embedding_of_levi (i := ⟨2, by decide⟩) (j := ⟨0, by decide⟩) transportWordE6
    (by rw [simpleWordAct_transportE6_two, thetaE6_eq]) simpleWordAct_transportE6_zero
    ((adjointGroup .E6 F).subtype.comp emb) (fun x y h => hinj (Subtype.ext h))
    (fun y => (emb y).2) (hsg (Pi.single (⟨2, by decide⟩ : Fin (Tag.rank .E6)) 1))
    (hsg (-Pi.single (⟨2, by decide⟩ : Fin (Tag.rank .E6)) 1))
    (hsg (Pi.single (⟨0, by decide⟩ : Fin (Tag.rank .E6)) 1))
    (hsg (-Pi.single (⟨0, by decide⟩ : Fin (Tag.rank .E6)) 1)) (fun c => ?_) (fun c => ?_)
    (fun c => ?_) (fun c => ?_)
  · change ((emb (tv 0 1 c) : ↥(adjointGroup .E6 F)) : ModGL .E6 F) = _
    rw [(hx c).1, hcoe (isRoot_single _ _)]
  · change ((emb (tv 1 0 c) : ↥(adjointGroup .E6 F)) : ModGL .E6 F) = _
    rw [(hx c).2.1, hcoe (isRoot_neg_single _ _)]
  · change ((emb (tv 1 2 c) : ↥(adjointGroup .E6 F)) : ModGL .E6 F) = _
    rw [(hx c).2.2.1, hcoe (isRoot_single _ _)]
  · change ((emb (tv 2 1 c) : ↥(adjointGroup .E6 F)) : ModGL .E6 F) = _
    rw [(hx c).2.2.2, hcoe (isRoot_neg_single _ _)]

end E6

end CFSG.ClassicalInvolution.ModelFacts.Levi
