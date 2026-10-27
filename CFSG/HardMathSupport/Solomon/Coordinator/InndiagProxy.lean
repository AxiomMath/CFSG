module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514Cover
public import CFSG.HardMathSupport.Solomon.Coordinator.L3AExcl
public import CFSG.LocalAnalysis.ComponentClassification.InnAutDerived

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ClassicalGroups.UnitaryFlag CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs

export CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived commutator_le_innAutDerived
  map_mem_commutator_mulAut innerAut_le_commutator_of_perfect innAutDerived_eq_commutator_of_perfect
  map_commutator_mulAut_congr map_innAutDerived_congr mem_innAutDerived_congr)

theorem innerAut_le_innAutDerived (Y : Type*) [Group Y] : innerAut Y ≤ innAutDerived Y :=
  le_sup_left

@[expose] noncomputable def innAutDerivedVocab : InndiagVocab where
  innDiag Y _ := innAutDerived Y

theorem innAutDerivedVocab_innDiag (Y : Type) [Group Y] :
    innAutDerivedVocab.innDiag Y = innAutDerived Y :=
  rfl

theorem mem_innAutDerivedVocab_of_commutator {Y : Type} [Group Y] {α : MulAut Y}
    (h : α ∈ commutator (MulAut Y)) : α ∈ innAutDerivedVocab.innDiag Y :=
  commutator_le_innAutDerived Y h

theorem innAutDerivedVocab_le_commutator {Y : Type} [Group Y] (hY : CFSG.Open.IsQuasisimple Y) :
    innAutDerivedVocab.innDiag Y ≤ commutator (MulAut Y) :=
  (innAutDerived_eq_commutator_of_perfect hY.1).le

section Marked

variable {Y M : Type*} [Group Y] [Group M]

theorem comap_inndiag_eq_innAutDerived_iff (P : PinnedAut M) (e : Y ≃* M) :
    (P.comap e).inndiag = innAutDerived Y ↔ P.inndiag = innAutDerived M := by
  constructor
  · intro h
    ext σ
    have := SetLike.ext_iff.1 h ((MulAut.congr e).symm σ)
    rwa [PinnedAut.mem_comap_inndiag, ← mem_innAutDerived_congr e,
      MulEquiv.apply_symm_apply] at this
  · intro h
    ext τ
    rw [PinnedAut.mem_comap_inndiag, ← mem_innAutDerived_congr e, h]

theorem GoodPinned.inndiag_eq_innAutDerived {P : PinnedAut M} (hP : GoodPinned P) :
    P.inndiag = innAutDerived M :=
  le_antisymm (hP.up.trans le_sup_right) (sup_le P.inn_le hP.down)

theorem GoodPinned.comap_inndiag_eq {P : PinnedAut M} (hP : GoodPinned P) (e : Y ≃* M) :
    (P.comap e).inndiag = innAutDerived Y :=
  (comap_inndiag_eq_innAutDerived_iff P e).2 hP.inndiag_eq_innAutDerived

theorem GoodPinned.comap_inndiag_eq_comap {M' : Type*} [Group M'] {P : PinnedAut M}
    {P' : PinnedAut M'} (hP : GoodPinned P) (hP' : GoodPinned P') (e : Y ≃* M) (e' : Y ≃* M') :
    (P.comap e).inndiag = (P'.comap e').inndiag :=
  (hP.comap_inndiag_eq e).trans (hP'.comap_inndiag_eq e').symm

theorem comap_stdPinnedPSL_three_inndiag_eq (F : Type) [Field F] [Finite F]
    (e : Y ≃* projectiveSL 3 F) : ((stdPinnedPSL 3 F).comap e).inndiag = innAutDerived Y :=
  (goodPinned_psl F).comap_inndiag_eq e

theorem comap_stdPinnedPSU3_inndiag_eq {p f : ℕ} {F : Type} [Field F] (hF : UnitaryFieldData p f F)
    (hq : 2 < p ^ f) (e : Y ≃* unitaryPSU hF 3) :
    ((stdPinnedPSU3 hF).comap e).inndiag = innAutDerived Y :=
  (goodPinned_psu hF hq).comap_inndiag_eq e

theorem comap_inndiag_ne_innAutDerived_of_mem_commutator {P : PinnedAut M} (e : Y ≃* M)
    {τ : MulAut M} (hτ : τ ∈ commutator (MulAut M)) (hout : τ ∉ P.inndiag) :
    (P.comap e).inndiag ≠ innAutDerived Y := fun h =>
  hout (((comap_inndiag_eq_innAutDerived_iff P e).1 h).symm ▸ commutator_le_innAutDerived M hτ)

theorem comap_inndiag_ne_innAutDerived_of_not_mem {P : PinnedAut M} (e : Y ≃* M)
    {τ : MulAut M} (hτ : τ ∈ P.inndiag) (hout : τ ∉ innAutDerived M) :
    (P.comap e).inndiag ≠ innAutDerived Y := fun h =>
  hout (((comap_inndiag_eq_innAutDerived_iff P e).1 h) ▸ hτ)

end Marked

theorem not_vocab_eq_of_comap_inndiag_ne (V : InndiagVocab) {Y : Type} [Group Y]
    {M₁ M₂ : Type*} [Group M₁] [Group M₂] (P₁ : PinnedAut M₁) (P₂ : PinnedAut M₂)
    (e₁ : Y ≃* M₁) (e₂ : Y ≃* M₂) (hne : (P₁.comap e₁).inndiag ≠ (P₂.comap e₂).inndiag) :
    ¬ (V.innDiag Y = (P₁.comap e₁).inndiag ∧ V.innDiag Y = (P₂.comap e₂).inndiag) :=
  fun h => hne (h.1.symm.trans h.2)

section Vocab

variable {V W : InndiagVocab}

theorem indInn_mono (hVW : ∀ (Y : Type) [Group Y], V.innDiag Y ≤ W.innDiag Y) {G : Type}
    [Group G] [Finite G] {K : Subgroup G} {g : G} (h : IndInn V K g) : IndInn W K g :=
  let ⟨hg, hmem⟩ := h
  ⟨hg, hVW _ hmem⟩

theorem input9_2_3_mono (hVW : ∀ (Y : Type) [Group Y], V.innDiag Y ≤ W.innDiag Y)
    (h : Input9_2_3 V) : Input9_2_3 W :=
  fun G _ _ I hI hK x hx hx3 hnot =>
    h G I hI hK x hx hx3 fun hV => hnot (indInn_mono hVW hV)

theorem inputL3fld_mono (hVW : ∀ (Y : Type) [Group Y], V.innDiag Y ≤ W.innDiag Y)
    (h : InputL3fld V) : InputL3fld W :=
  fun G _ _ K g r hq hr hg hg3 hnot =>
    h G K g r hq hr hg hg3 fun hV => hnot (indInn_mono hVW hV)

theorem inputL2exp_mono (hVW : ∀ (Y : Type) [Group Y], V.innDiag Y ≤ W.innDiag Y)
    (h : InputL2exp V) : InputL2exp W :=
  fun G _ _ K g h' s r0 hq hs hg hh hg3 hh3 hgh hnot =>
    h G K g h' s r0 hq hs hg hh hg3 hh3 hgh fun hV => hnot (indInn_mono hVW hV)

theorem input14_31_4_anti (hVW : ∀ (Y : Type) [Group Y], V.innDiag Y ≤ W.innDiag Y)
    (h : Input14_31_4 W) : Input14_31_4 V :=
  fun G _ _ I B hI hK hB hrk hE hc A x hAB hx hA hT J hJ q hq h3 h8 hA' =>
    h G I B hI hK hB hrk hE hc A x hAB hx hA hT J hJ q hq h3 h8 fun a ha =>
      indInn_mono hVW (hA' a ha)

theorem inputL3inn_anti (hVW : ∀ (Y : Type) [Group Y], V.innDiag Y ≤ W.innDiag Y)
    (h : InputL3inn W) : InputL3inn V :=
  fun G _ _ K g r hq hr hg3 hV hT => h G K g r hq hr hg3 (indInn_mono hVW hV) hT

@[expose] def Input14_31_4Residual (V W : InndiagVocab) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (I B : Subgroup G), CFSG.Open.IsQuasisimple (barOf 3 I) →
    IsKGroup ↥I → B ≤ Subgroup.normalizer (I : Set G) →
    CFSG.Open.GLATwoLocalRank 3 ↥(I ⊔ B) ≤ 4 → CFSG.Open.IsElemAbelian 3 B →
    (∃ c ∈ B, c ≠ 1 ∧ c ∈ CD I) →
    ∀ (A : Subgroup G) (x : G), A ≤ B → x ∈ A → Nat.card A = 9 → ¬ TrivOn I x →
    ∀ J : Subgroup G, CFSG.Open.GLAPComponent 3 (I ⊓ Cs x) J → ∀ q : ℕ,
      IsTypeL2 q (barOf 3 J) → ¬ 3 ∣ q → q ≠ 8 →
      (∀ a ∈ A, a ∉ Subgroup.zpowers x → InducesFieldAutN 2 J a ∧ ¬ TrivOn J a) →
      (∀ a ∈ A, IndInn V I a) → ∀ a ∈ A, IndInn W I a

theorem input14_31_4_of_residual (hW : Input14_31_4 W) (hres : Input14_31_4Residual V W) :
    Input14_31_4 V :=
  fun G _ _ I B hI hK hB hrk hE hc A x hAB hx hA hT J hJ q hq h3 h8 hA' hfld =>
    hW G I B hI hK hB hrk hE hc A x hAB hx hA hT J hJ q hq h3 h8
      (hres G I B hI hK hB hrk hE hc A x hAB hx hA hT J hJ q hq h3 h8 hfld hA') hfld

end Vocab

end CFSG.HardMathSupport.Solomon.Coordinator
