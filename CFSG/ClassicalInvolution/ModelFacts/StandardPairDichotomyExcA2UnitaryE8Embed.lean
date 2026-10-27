module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryEmbed
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2E8Data

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.RootSystem CFSG.LieType.AlgebraicGroups CFSG.LieType.Universal CFSG.LieType
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.Timmesfeld
  CFSG.ClassicalInvolution.WeakCT CFSG.LocalAnalysis.ComponentInitial CFSG.Timmesfeld.LevisExtras
open scoped MatrixGroups

section E8

@[expose] def transportWordE8 : List (Fin (Tag.rank .E8)) :=
    [idxE8 7, idxE8 6, idxE8 5, idxE8 4, idxE8 3, idxE8 2, idxE8 1, idxE8 3, idxE8 4,
     idxE8 5, idxE8 6, idxE8 7, idxE8 6, idxE8 5, idxE8 4, idxE8 3, idxE8 2, idxE8 1,
     idxE8 3, idxE8 4, idxE8 5, idxE8 6, idxE8 0, idxE8 2, idxE8 3, idxE8 4, idxE8 5,
     idxE8 1, idxE8 3, idxE8 4, idxE8 2, idxE8 3, idxE8 0, idxE8 2, idxE8 1, idxE8 3,
     idxE8 4, idxE8 5]

theorem simpleWordAct_transportE8_six :
    simpleWordAct .E8 transportWordE8 (Pi.single (⟨6, by decide⟩ : Fin (Tag.rank .E8)) 1) =
      thetaE8' := by
  unfold transportWordE8 simpleWordAct idxE8
  decide +kernel

theorem simpleWordAct_transportE8_seven :
    simpleWordAct .E8 transportWordE8 (Pi.single (⟨7, by decide⟩ : Fin (Tag.rank .E8)) 1) =
      deltaE8 := by
  unfold transportWordE8 simpleWordAct idxE8
  decide +kernel

theorem exists_sl3_simple_E8 (F : Type) [Field F] [Finite F] :
    ∃ emb : SL(3, F) →* ↥(adjointGroup .E8 F), Function.Injective emb ∧
      ∀ c, emb (tv 0 1 c) = e8Par F (Pi.single (⟨6, by decide⟩ : Fin (Tag.rank .E8)) 1) c ∧
        emb (tv 1 0 c) = e8Par F (-Pi.single (⟨6, by decide⟩ : Fin (Tag.rank .E8)) 1) c ∧
        emb (tv 1 2 c) = e8Par F (Pi.single (⟨7, by decide⟩ : Fin (Tag.rank .E8)) 1) c ∧
        emb (tv 2 1 c) = e8Par F (-Pi.single (⟨7, by decide⟩ : Fin (Tag.rank .E8)) 1) c := by
  obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan (Steinberg.Adjoint.e8Datum F).isFiniteType
    (Dv := (Steinberg.Adjoint.e8Datum F).divisible) rfl
  obtain ⟨C, -, hC⟩ := Steinberg.Adjoint.e8_commutatorFormula F O
  have hE := Steinberg.Adjoint.e8_chevalleyExtras F O C hC
  have hdiv : (Steinberg.Adjoint.e8Datum F).divisible = ∅ := rfl
  obtain ⟨emb, hinj, -, hx⟩ := exists_sl3Levi hE hdiv (i := ⟨6, by show 6 < 8; decide⟩)
    (j := ⟨7, by show 7 < 8; decide⟩) (k := ⟨5, by show 5 < 8; decide⟩)
    (by intro h; have := congrArg Fin.val h; simp at this)
    (by show Blueprint.Chevalley.Tag.cartan .E8 ⟨6, by decide⟩ ⟨7, by decide⟩ = -1; decide)
    (by show Blueprint.Chevalley.Tag.cartan .E8 ⟨7, by decide⟩ ⟨6, by decide⟩ = -1; decide)
    (by show ¬ (3 : ℤ) ∣ Blueprint.Chevalley.Tag.cartan .E8 ⟨6, by decide⟩ ⟨5, by decide⟩ +
      2 * Blueprint.Chevalley.Tag.cartan .E8 ⟨7, by decide⟩ ⟨5, by decide⟩; decide)
  exact ⟨emb, hinj, hx⟩

theorem nonempty_a2Embedding_E8 (F : Type) [Field F] [Finite F] :
    Nonempty (A2Embedding .E8 thetaE8 deltaE8 F) := by
  obtain ⟨emb, hinj, hx⟩ := exists_sl3_simple_E8 F
  have hcoe : ∀ {γ : Fin (Tag.rank .E8) → ℤ}, IsRoot .E8 γ → ∀ c : F,
      ((e8Par F γ c : ↥(adjointGroup .E8 F)) : ModGL .E8 F) =
        pinnedX .E8 F γ ((((rootOperatorFamily .E8).pinnedFamilySign γ : ℤ) : F) * c) :=
    fun hγ c => CFSG.ClassicalInvolution.Balance.coe_xPar_eq_pinnedX hγ c
  have hsg : ∀ γ : Fin (Tag.rank .E8) → ℤ,
      (((rootOperatorFamily .E8).pinnedFamilySign γ : ℤ) : F) *
        (((rootOperatorFamily .E8).pinnedFamilySign γ : ℤ) : F) = 1 := fun γ =>
    (rootOperatorFamily .E8).pinnedFamilySign_mul_self F γ
  refine nonempty_a2Embedding_of_levi (i := ⟨6, by decide⟩) (j := ⟨7, by decide⟩) transportWordE8
    (by rw [simpleWordAct_transportE8_six, thetaE8_eq]) simpleWordAct_transportE8_seven
    ((adjointGroup .E8 F).subtype.comp emb) (fun x y h => hinj (Subtype.ext h))
    (fun y => (emb y).2) (hsg (Pi.single (⟨6, by decide⟩ : Fin (Tag.rank .E8)) 1))
    (hsg (-Pi.single (⟨6, by decide⟩ : Fin (Tag.rank .E8)) 1))
    (hsg (Pi.single (⟨7, by decide⟩ : Fin (Tag.rank .E8)) 1))
    (hsg (-Pi.single (⟨7, by decide⟩ : Fin (Tag.rank .E8)) 1)) (fun c => ?_) (fun c => ?_)
    (fun c => ?_) (fun c => ?_)
  · change ((emb (tv 0 1 c) : ↥(adjointGroup .E8 F)) : ModGL .E8 F) = _
    rw [(hx c).1, hcoe (isRoot_single _ _)]
  · change ((emb (tv 1 0 c) : ↥(adjointGroup .E8 F)) : ModGL .E8 F) = _
    rw [(hx c).2.1, hcoe (isRoot_neg_single _ _)]
  · change ((emb (tv 1 2 c) : ↥(adjointGroup .E8 F)) : ModGL .E8 F) = _
    rw [(hx c).2.2.1, hcoe (isRoot_single _ _)]
  · change ((emb (tv 2 1 c) : ↥(adjointGroup .E8 F)) : ModGL .E8 F) = _
    rw [(hx c).2.2.2, hcoe (isRoot_neg_single _ _)]

end E8

end CFSG.ClassicalInvolution.ModelFacts.Levi
