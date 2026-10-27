module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryEmbed
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2E7Data

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.RootSystem CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Universal CFSG.LieType
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.Timmesfeld
  CFSG.ClassicalInvolution.WeakCT CFSG.LocalAnalysis.ComponentInitial CFSG.Timmesfeld.LevisExtras
open scoped MatrixGroups

section E7

@[expose] def idxE7 (n : ℕ) (h : n < 7 := by decide) : Fin (Tag.rank .E7) := ⟨n, h⟩

theorem neighbour_E7_adj : ∀ i : Fin (Tag.rank .E7), ∃ l,
    Tag.cartan .E7 i l = -1 ∧ Tag.cartan .E7 l i = -1 := by
  intro i
  fin_cases i <;> decide

@[expose] def transportWordE7 : List (Fin (Tag.rank .E7)) :=
  [idxE7 0, idxE7 2, idxE7 3, idxE7 4, idxE7 5, idxE7 6, idxE7 0, idxE7 2, idxE7 3,
   idxE7 4, idxE7 5, idxE7 1, idxE7 3, idxE7 4, idxE7 2, idxE7 3, idxE7 0, idxE7 2,
   idxE7 1, idxE7 3, idxE7 4]

theorem simpleWordAct_transportE7_five :
    simpleWordAct .E7 transportWordE7 (Pi.single (⟨5, by decide⟩ : Fin (Tag.rank .E7)) 1) =
      thetaE7' := by
  unfold transportWordE7 simpleWordAct idxE7
  decide +kernel

theorem simpleWordAct_transportE7_six :
    simpleWordAct .E7 transportWordE7 (Pi.single (⟨6, by decide⟩ : Fin (Tag.rank .E7)) 1) =
      deltaE7 := by
  unfold transportWordE7 simpleWordAct idxE7
  decide +kernel

theorem exists_sl3_simple_E7 (F : Type) [Field F] [Finite F] :
    ∃ emb : SL(3, F) →* ↥(adjointGroup .E7 F), Function.Injective emb ∧
      ∀ c, emb (tv 0 1 c) = xPar (rootOperatorFamily .E7)
          (Pi.single (⟨5, by decide⟩ : Fin (Tag.rank .E7)) 1) c ∧
        emb (tv 1 0 c) = xPar (rootOperatorFamily .E7)
          (-Pi.single (⟨5, by decide⟩ : Fin (Tag.rank .E7)) 1) c ∧
        emb (tv 1 2 c) = xPar (rootOperatorFamily .E7)
          (Pi.single (⟨6, by decide⟩ : Fin (Tag.rank .E7)) 1) c ∧
        emb (tv 2 1 c) = xPar (rootOperatorFamily .E7)
          (-Pi.single (⟨6, by decide⟩ : Fin (Tag.rank .E7)) 1) c := by
  obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan
    (adjDatum (rootOperatorFamily .E7) F).isFiniteType
    (Dv := (adjDatum (rootOperatorFamily .E7) F).divisible) rfl
  have hE := adjDatum_chevalleyExtras _ F e7AdjData_valid noG2_E7 neighbour_E7_adj O
    (commC (rootOperatorFamily .E7) e7AdjData_valid)
    (commutatorFormula_commC e7AdjData_valid noG2_E7 _ (adjDatum_roots _ F) O)
  have hdiv : (adjDatum (rootOperatorFamily .E7) F).divisible = ∅ := rfl
  obtain ⟨emb, hinj, -, hx⟩ := exists_sl3Levi hE hdiv (i := ⟨5, by show 5 < 7; decide⟩)
    (j := ⟨6, by show 6 < 7; decide⟩) (k := ⟨4, by show 4 < 7; decide⟩)
    (by intro h; have := congrArg Fin.val h; simp at this)
    (by show Blueprint.Chevalley.Tag.cartan .E7 ⟨5, by decide⟩ ⟨6, by decide⟩ = -1; decide)
    (by show Blueprint.Chevalley.Tag.cartan .E7 ⟨6, by decide⟩ ⟨5, by decide⟩ = -1; decide)
    (by show ¬ (3 : ℤ) ∣ Blueprint.Chevalley.Tag.cartan .E7 ⟨5, by decide⟩ ⟨4, by decide⟩ +
      2 * Blueprint.Chevalley.Tag.cartan .E7 ⟨6, by decide⟩ ⟨4, by decide⟩; decide)
  exact ⟨emb, hinj, hx⟩

theorem nonempty_a2Embedding_E7 (F : Type) [Field F] [Finite F] :
    Nonempty (A2Embedding .E7 thetaE7 deltaE7 F) := by
  obtain ⟨emb, hinj, hx⟩ := exists_sl3_simple_E7 F
  have hcoe : ∀ {γ : Fin (Tag.rank .E7) → ℤ}, IsRoot .E7 γ → ∀ c : F,
      ((xPar (rootOperatorFamily .E7) γ c : ↥(adjointGroup .E7 F)) : ModGL .E7 F) =
        pinnedX .E7 F γ ((((rootOperatorFamily .E7).pinnedFamilySign γ : ℤ) : F) * c) :=
    fun hγ c => CFSG.ClassicalInvolution.Balance.coe_xPar_eq_pinnedX hγ c
  have hsg : ∀ γ : Fin (Tag.rank .E7) → ℤ,
      (((rootOperatorFamily .E7).pinnedFamilySign γ : ℤ) : F) *
        (((rootOperatorFamily .E7).pinnedFamilySign γ : ℤ) : F) = 1 := fun γ =>
    (rootOperatorFamily .E7).pinnedFamilySign_mul_self F γ
  refine nonempty_a2Embedding_of_levi (i := ⟨5, by decide⟩) (j := ⟨6, by decide⟩) transportWordE7
    (by rw [simpleWordAct_transportE7_five, thetaE7_eq_vec]) simpleWordAct_transportE7_six
    ((adjointGroup .E7 F).subtype.comp emb) (fun x y h => hinj (Subtype.ext h))
    (fun y => (emb y).2) (hsg (Pi.single (⟨5, by decide⟩ : Fin (Tag.rank .E7)) 1))
    (hsg (-Pi.single (⟨5, by decide⟩ : Fin (Tag.rank .E7)) 1))
    (hsg (Pi.single (⟨6, by decide⟩ : Fin (Tag.rank .E7)) 1))
    (hsg (-Pi.single (⟨6, by decide⟩ : Fin (Tag.rank .E7)) 1)) (fun c => ?_) (fun c => ?_)
    (fun c => ?_) (fun c => ?_)
  · change ((emb (tv 0 1 c) : ↥(adjointGroup .E7 F)) : ModGL .E7 F) = _
    rw [(hx c).1, hcoe (isRoot_single _ _)]
  · change ((emb (tv 1 0 c) : ↥(adjointGroup .E7 F)) : ModGL .E7 F) = _
    rw [(hx c).2.1, hcoe (isRoot_neg_single _ _)]
  · change ((emb (tv 1 2 c) : ↥(adjointGroup .E7 F)) : ModGL .E7 F) = _
    rw [(hx c).2.2.1, hcoe (isRoot_single _ _)]
  · change ((emb (tv 2 1 c) : ↥(adjointGroup .E7 F)) : ModGL .E7 F) = _
    rw [(hx c).2.2.2, hcoe (isRoot_neg_single _ _)]

end E7

end CFSG.ClassicalInvolution.ModelFacts.Levi
