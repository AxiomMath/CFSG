module

public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.WeylTorusAct
public import CFSG.LieType.Chevalley.LangRootRankOneTorus

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Tables.T1b

set_option linter.unusedSectionVars false


@[expose] def weylWord {τ : Tag} (L : Type) [Field L] (ω : List (Fin τ.rank)) : ModGL τ L :=
  (ω.map fun i => weylElt τ L i 1).prod

theorem weylWord_nil {τ : Tag} (L : Type) [Field L] : weylWord (τ := τ) L [] = 1 := rfl

theorem weylWord_cons {τ : Tag} (L : Type) [Field L] (i : Fin τ.rank) (ω : List (Fin τ.rank)) :
    weylWord L (i :: ω) = weylElt τ L i 1 * weylWord L ω := by
  simp [weylWord]

theorem weylWord_append {τ : Tag} (L : Type) [Field L] (ω ω' : List (Fin τ.rank)) :
    weylWord L (ω ++ ω') = weylWord L ω * weylWord L ω' := by
  simp [weylWord]

theorem weylWord_conj_rootDiagUnit {τ : Tag} {L : Type} [Field L] (ω : List (Fin τ.rank))
    (a : Fin τ.rank → Lˣ) :
    weylWord L ω * rootDiagUnit τ a * (weylWord L ω)⁻¹ =
      rootDiagUnit τ (weylAct ((coxeterSystem τ).wordProd ω) a) := by
  induction ω generalizing a with
  | nil => simp [weylWord_nil, weylAct_one]
  | cons i ω ih =>
    rw [weylWord_cons, CoxeterSystem.wordProd_cons, weylAct_mul]
    calc weylElt τ L i 1 * weylWord L ω * rootDiagUnit τ a *
          (weylElt τ L i 1 * weylWord L ω)⁻¹
        = weylElt τ L i 1 * (weylWord L ω * rootDiagUnit τ a * (weylWord L ω)⁻¹) *
            (weylElt τ L i 1)⁻¹ := by group
      _ = weylElt τ L i 1 * rootDiagUnit τ (weylAct ((coxeterSystem τ).wordProd ω) a) *
            (weylElt τ L i 1)⁻¹ := by rw [ih]
      _ = rootDiagUnit τ (weylAct ((coxeterSystem τ).simple i)
            (weylAct ((coxeterSystem τ).wordProd ω) a)) := by
          rw [← canonicalRep_simple (coxeterSystem τ) L i]
          exact canonicalRep_conj_rootDiagUnit _ _

theorem conj_mem_rootRankOneGroup {τ : Tag} {L : Type} [Field L] (ω : List (Fin τ.rank))
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) {g : ModGL τ L} (hg : g ∈ rootRankOneGroup τ L β) :
    weylWord L ω * g * (weylWord L ω)⁻¹ ∈
      rootRankOneGroup τ L ((coxeterSystem τ).wordProd ω • β) := by
  have hL : ∀ {δ : Fin τ.rank → ℤ}, IsRoot τ δ →
      rootRankOneGroup τ L δ = rootSubgroup τ L δ ⊔ rootSubgroup τ L (-δ) :=
    fun hδ => (exceptional_Lang_root_rank_one_torus_transport τ L hδ).1
  rw [hL hβ] at hg
  have hmem : weylWord L ω * g * (weylWord L ω)⁻¹ ∈
      (rootSubgroup τ L β ⊔ rootSubgroup τ L (-β)).map (MulAut.conj (weylWord L ω)).toMonoidHom :=
    ⟨g, hg, rfl⟩
  rw [Subgroup.map_sup, weylWord, map_conj_prod_weylElt_rootSubgroup L ω hβ,
    map_conj_prod_weylElt_rootSubgroup L ω (IsRoot.neg hβ), smul_neg,
    ← hL (IsRoot.smul hβ _)] at hmem
  exact hmem

theorem simpleRootSL2_mem_rootRankOneGroup {τ : Tag} {L : Type} [Field L] (j : Fin τ.rank)
    (A : SL2 L) :
    simpleRootSL2 τ L j A ∈ rootRankOneGroup τ L (Pi.single j 1) := by
  refine ⟨A, ?_⟩
  rw [rootSL2_apply, pinnedWeyl, pinnedData_single]
  simp

theorem baseChangeGL_weylElt_one' {τ : Tag} {R S : Type} [Field R] [Field S] (f : R →+* S)
    (i : Fin τ.rank) : baseChangeGL f (weylElt τ R i 1) = weylElt τ S i 1 := by
  rw [weylElt_eq_xUnit_mul, map_mul, map_mul, baseChangeGL_xUnit, baseChangeGL_yUnit,
    weylElt_eq_xUnit_mul]
  simp

theorem baseChangeGL_weylWord {τ : Tag} {R S : Type} [Field R] [Field S] (f : R →+* S)
    (ω : List (Fin τ.rank)) : baseChangeGL f (weylWord R ω) = weylWord S ω := by
  induction ω with
  | nil => simp [weylWord_nil]
  | cons i ω ih => rw [weylWord_cons, weylWord_cons, map_mul, baseChangeGL_weylElt_one', ih]

theorem weylWord_mem_adjointGroup {τ : Tag} {L : Type} [Field L] (ω : List (Fin τ.rank)) :
    weylWord L ω ∈ adjointGroup τ L := by
  induction ω with
  | nil => rw [weylWord_nil]; exact one_mem _
  | cons i ω ih => rw [weylWord_cons]; exact mul_mem (weylElt_mem_adjointGroup i 1) ih

end CFSG.LieType.SeitzGeneration.ExcHighThree
