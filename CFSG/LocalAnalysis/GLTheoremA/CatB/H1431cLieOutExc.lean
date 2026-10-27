module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieOutCharTwo
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieOutEnt
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoOutExc

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.Yardstones.Md0ec50421ce4
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.UniquenessMaximal
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.HardMathSupport.Lang.E6Descent
  CFSG.RankThree.Chevalley CFSG.RankThree.LocalRank CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Dickson.Sec6 (FamG2 FamF4 FamE7 FamE8 blueprintLieModel_G2
  blueprintLieModel_F4 blueprintLieModel_E7 blueprintLieModel_E8)
open CFSG.HardMathSupport.Dickson.Sec6.I923
open CFSG.LocalAnalysis.GLTheoremA.I1431C2 (u42Exc_chevalleyExceptionalModel
  not_mem_range_conj_of_not_mem_innAutDerived)
open scoped commutatorElement

variable {T Pc : TauCeti.CFSGIndex → Prop} {tm tf tN : ℕ}

section Exceptional


theorem typeLayer_entrywise_exc (hD : LieSOutType T tm tf tN) {τ : Tag} {t : StatedLieTag}
    (ht : t ≠ .PSp) {K : Type}
    [Field K] [Finite K] (σ : K ≃+* K) {d : ℕ}
    (hX : Blueprint.LieModel ↥(adjointGroup τ (fixSubfield σ)) t 0 2 d)
    (hs : IsSimpleGroup ↥(adjointGroup τ (fixSubfield σ)))
    (hZ : Subgroup.center ↥(adjointGroup τ (fixSubfield σ)) = ⊥) :
    TypeLayer T (entrywiseAdjointAut τ σ) False :=
  typeLayer_entrywise σ hs (exists_noncomm_of_center_bot hZ) fun h =>
    ht (hD.det h hX).1

theorem typeLayer_entrywise_G2 (hD : LieSOutType T tm tf tN) {K : Type} [Field K] [Finite K]
    (σ : K ≃+* K) {d : ℕ} (hd : 1 ≤ d)
    (hk : Nat.card ↥(fixSubfield σ) = 2 ^ d) :
    TypeLayer T (entrywiseAdjointAut Tag.G2 σ) False := by
  haveI : Finite ↥(fixSubfield σ) := Subtype.finite
  by_cases h3 : 3 ≤ 2 ^ d
  · have hM : ChevalleyExceptionalModel ↥(adjointGroup Tag.G2 ↥(fixSubfield σ)) .G2 2 d :=
      ⟨⟨Nat.prime_two, hd, rfl, h3⟩, untwisted_adjointGroup hk⟩
    obtain ⟨-, hsimp⟩ := CFSG.LieType.Simplicity.fam_g2_simplicity _ 2 d hM
    exact typeLayer_entrywise_exc hD (t := .G2) (by decide) σ (Or.inr (Or.inl ⟨rfl, by decide, hM⟩))
      hsimp center_adjointGroup_eq_bot
  · have h2 : 2 ^ d = 2 := by
      have : 2 ≤ 2 ^ d := Nat.le_self_pow (by omega) 2
      omega
    refine typeLayer_of_card_dvd hD.card_eq _ (M := 12096) ?_ hD.ord.not_dvd_12096
    have hfix : Nat.card ↥(fixSubgroup (entrywiseAdjointAut Tag.G2 σ)) =
        Nat.card ↥(entrywiseFixedGroup Tag.G2 σ) := by
      rw [fixSubgroup_entrywiseAdjointAut]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    rw [hfix, card_entrywiseFixedGroup_G2 σ (hk.trans h2)]
    simp [CFSG.ComponentClassification.CatLeaf.lieOrderNumerator]

theorem typeLayer_entrywise_F4 (hD : LieSOutType T tm tf tN) {K : Type} [Field K] [Finite K]
    (σ : K ≃+* K) {d : ℕ} (hd : 1 ≤ d)
    (hk : Nat.card ↥(fixSubfield σ) = 2 ^ d) :
    TypeLayer T (entrywiseAdjointAut Tag.F4 σ) False := by
  haveI : Finite ↥(fixSubfield σ) := Subtype.finite
  have hM : ChevalleyExceptionalModel ↥(adjointGroup Tag.F4 ↥(fixSubfield σ)) .F4 2 d :=
    ⟨⟨Nat.prime_two, hd, rfl⟩, untwisted_adjointGroup hk⟩
  obtain ⟨-, hsimp⟩ := CFSG.LieType.Simplicity.fam_f4_simplicity _ 2 d hM
  exact typeLayer_entrywise_exc hD (t := .F4) (by decide) σ (Or.inr (Or.inl ⟨rfl, by decide, hM⟩))
    hsimp center_adjointGroup_eq_bot

theorem typeLayer_entrywise_E7 (hD : LieSOutType T tm tf tN) {K : Type} [Field K] [Finite K]
    (σ : K ≃+* K) {d : ℕ} (hd : 1 ≤ d)
    (hk : Nat.card ↥(fixSubfield σ) = 2 ^ d) :
    TypeLayer T (entrywiseAdjointAut Tag.E7 σ) False := by
  haveI : Finite ↥(fixSubfield σ) := Subtype.finite
  have hM : ChevalleyExceptionalModel ↥(adjointGroup Tag.E7 ↥(fixSubfield σ)) .E7 2 d :=
    ⟨⟨Nat.prime_two, hd, rfl⟩, untwisted_adjointGroup hk⟩
  obtain ⟨-, hsimp⟩ := CFSG.LieType.Simplicity.fam_e7_simplicity _ 2 d hM
  exact typeLayer_entrywise_exc hD (t := .E7) (by decide) σ (Or.inr (Or.inl ⟨rfl, by decide, hM⟩))
    hsimp center_adjointGroup_eq_bot

theorem typeLayer_entrywise_E8 (hD : LieSOutType T tm tf tN) {K : Type} [Field K] [Finite K]
    (σ : K ≃+* K) {d : ℕ} (hd : 1 ≤ d)
    (hk : Nat.card ↥(fixSubfield σ) = 2 ^ d) :
    TypeLayer T (entrywiseAdjointAut Tag.E8 σ) False := by
  haveI : Finite ↥(fixSubfield σ) := Subtype.finite
  have hM : ChevalleyExceptionalModel ↥(adjointGroup Tag.E8 ↥(fixSubfield σ)) .E8 2 d :=
    ⟨⟨Nat.prime_two, hd, rfl⟩, untwisted_adjointGroup hk⟩
  obtain ⟨-, hsimp⟩ := CFSG.LieType.Simplicity.fam_e8_simplicity _ 2 d hM
  exact typeLayer_entrywise_exc hD (t := .E8) (by decide) σ (Or.inr (Or.inl ⟨rfl, by decide, hM⟩))
    hsimp center_adjointGroup_eq_bot

theorem lieSOut_exc_setup {S : Type} [Group S] [Finite S] {τ : Tag} {q : ℕ}
    (hU : UntwistedChevalleyModel S τ q) {α : MulAut S} (hα : α ∉ innAutDerived S)
    (hp : TypePumpup T S α) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (θ : S ≃* ↥(adjointGroup τ F)),
      Nat.card F = q ∧ MulAut.congr θ α ^ 3 = 1 ∧
        MulAut.congr θ α ∉ inner ↥(adjointGroup τ F) := by
  obtain ⟨F, hFf, hFin, hFcard, ⟨θ⟩⟩ := exists_equiv_adjointGroup_of_untwisted hU
  refine ⟨F, hFf, hFin, θ, hFcard, ?_, fun hin => ?_⟩
  · rw [← map_pow, hp.1, map_one]
  · exact not_mem_range_conj_of_not_mem_innAutDerived hα
      ((congr_mem_inner_iff_of_equiv θ α).mp hin)

theorem lieSOut_exc_false_of_conj_pow {S : Type} [Group S] [Finite S] {τ : Tag} {F : Type} [Field F]
    [Finite F] (θ : S ≃* ↥(adjointGroup τ F)) {α : MulAut S} (hp : TypePumpup T S α) {Tf : F ≃+* F}
    {δ : MulAut ↥(adjointGroup τ F)} {r j : ℕ}
    (hrj : (MulAut.congr θ α ^ r) ^ j = MulAut.congr θ α)
    (hδ : δ * MulAut.congr θ α ^ r * δ⁻¹ = entrywiseAdjointAut τ Tf)
    (hNo : TypeLayer T (entrywiseAdjointAut τ Tf) False) : False :=
  hp.apply (typeLayer_congr θ (typeLayer_of_conj_pow hrj hδ hNo))

theorem lieSOut_g2 (hD : LieSOutType T tm tf tN) : TypeOuterAt T Pc FamG2 := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ α hα hp
  cases d with
  | G2 q =>
    exfalso
    have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
      ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
    have hq3 : 3 ≤ q.p ^ q.exponent := by rw [← TauCeti.PrimePower.card_def]; exact hr
    have hf : 1 ≤ q.exponent := q.exponent_pos
    have hU : UntwistedChevalleyModel S .G2 (q.p ^ q.exponent) :=
      (u42Exc_chevalleyExceptionalModel (blueprintLieModel_G2 q hv e)
        (by decide) (by decide) (by decide)).2
    obtain ⟨F, hFf, hFin, θ, hFcard, hβ3, hβinn⟩ := lieSOut_exc_setup hU hα hp
    obtain ⟨d, Tf, δ, hfd, hTo, hTc, hδ⟩ := G2_descent q.prime_p hf hq3 F hFcard _ hβ3 hβinn
    have hq2 : q.p = 2 := hc
    rw [hq2] at hTc
    exact lieSOut_exc_false_of_conj_pow θ hp (r := 1) (j := 1) (by simp) (by simpa using hδ)
      (typeLayer_entrywise_G2 hD Tf (by omega) hTc)
  | _ => exact hF.elim

theorem lieSOut_f4 (hD : LieSOutType T tm tf tN) : TypeOuterAt T Pc FamF4 := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ α hα hp
  cases d with
  | F4 q =>
    exfalso
    haveI : Fact q.p.Prime := ⟨q.prime_p⟩
    have hf : 1 ≤ q.exponent := q.exponent_pos
    have hU : UntwistedChevalleyModel S .F4 (q.p ^ q.exponent) :=
      (u42Exc_chevalleyExceptionalModel (blueprintLieModel_F4 q hv e)
        (by decide) (by decide) (by decide)).2
    obtain ⟨F, hFf, hFin, θ, hFcard, hβ3, hβinn⟩ := lieSOut_exc_setup hU hα hp
    obtain ⟨d, Tf, δ, hfd, hTo, hTc, hδ⟩ := F4_descent hf F hFcard _ hβ3 hβinn
    have hq2 : q.p = 2 := hc
    rw [hq2] at hTc
    exact lieSOut_exc_false_of_conj_pow θ hp (r := 1) (j := 1) (by simp) (by simpa using hδ)
      (typeLayer_entrywise_F4 hD Tf (by omega) hTc)
  | _ => exact hF.elim

theorem lieSOut_e7 (hD : LieSOutType T tm tf tN) : TypeOuterAt T Pc FamE7 := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ α hα hp
  cases d with
  | E7 q =>
    exfalso
    haveI : Fact q.p.Prime := ⟨q.prime_p⟩
    have hf : 1 ≤ q.exponent := q.exponent_pos
    have hU : UntwistedChevalleyModel S .E7 (q.p ^ q.exponent) :=
      (u42Exc_chevalleyExceptionalModel (blueprintLieModel_E7 q hv e)
        (by decide) (by decide) (by decide)).2
    obtain ⟨F, hFf, hFin, θ, hFcard, hβ3, hβinn⟩ := lieSOut_exc_setup hU hα hp
    have hdet : ¬ 3 ∣ Tag.E7.cartan.det.natAbs := by
      rw [det_cartan_E7]
      decide
    obtain ⟨d, Tf, r, j, δ, hfd, hTo, hTc, hrj, hδ⟩ :=
      exists_conj_entrywise_of_outer_E Tag.E7 (Or.inr (Or.inl rfl)) hf F hFcard Nat.prime_three
        (by norm_num) hdet _ hβ3 hβinn
    have hq2 : q.p = 2 := hc
    rw [hq2] at hTc
    exact lieSOut_exc_false_of_conj_pow θ hp hrj hδ (typeLayer_entrywise_E7 hD Tf (by omega) hTc)
  | _ => exact hF.elim

theorem lieSOut_e8 (hD : LieSOutType T tm tf tN) : TypeOuterAt T Pc FamE8 := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ α hα hp
  cases d with
  | E8 q =>
    exfalso
    haveI : Fact q.p.Prime := ⟨q.prime_p⟩
    have hf : 1 ≤ q.exponent := q.exponent_pos
    have hU : UntwistedChevalleyModel S .E8 (q.p ^ q.exponent) :=
      (u42Exc_chevalleyExceptionalModel (blueprintLieModel_E8 q hv e)
        (by decide) (by decide) (by decide)).2
    obtain ⟨F, hFf, hFin, θ, hFcard, hβ3, hβinn⟩ := lieSOut_exc_setup hU hα hp
    have hdet : ¬ 3 ∣ Tag.E8.cartan.det.natAbs := by
      rw [det_cartan_E8]
      decide
    obtain ⟨d, Tf, r, j, δ, hfd, hTo, hTc, hrj, hδ⟩ :=
      exists_conj_entrywise_of_outer_E Tag.E8 (Or.inr (Or.inr rfl)) hf F hFcard Nat.prime_three
        (by norm_num) hdet _ hβ3 hβinn
    have hq2 : q.p = 2 := hc
    rw [hq2] at hTc
    exact lieSOut_exc_false_of_conj_pow θ hp hrj hδ (typeLayer_entrywise_E8 hD Tf (by omega) hTc)
  | _ => exact hF.elim

end Exceptional

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end

