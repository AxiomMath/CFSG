module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoOutEnt
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Split
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.G2
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.F4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I1431C2

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.Yardstones.Md0ec50421ce4
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.UniquenessMaximal
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.HardMathSupport.Lang.E6Descent
  CFSG.RankThree.Chevalley CFSG.RankThree.LocalRank CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Dickson.Sec6 (FamG2 FamF4 FamE7 FamE8 blueprintLieModel_G2
  blueprintLieModel_F4 blueprintLieModel_E7 blueprintLieModel_E8)
open CFSG.HardMathSupport.Dickson.Sec6.I923
open scoped commutatorElement

section Exceptional


theorem u42Layer_entrywise_exc {τ : Tag} {t : StatedLieTag} (ht : t ≠ .PSU) {K : Type}
    [Field K] [Finite K] (σ : K ≃+* K) {d : ℕ}
    (hX : Blueprint.LieModel ↥(adjointGroup τ (fixSubfield σ)) t 0 2 d)
    (hs : IsSimpleGroup ↥(adjointGroup τ (fixSubfield σ)))
    (hZ : Subgroup.center ↥(adjointGroup τ (fixSubfield σ)) = ⊥) :
    U42Layer (entrywiseAdjointAut τ σ) False :=
  u42Layer_entrywise σ hs (exists_noncomm_of_center_bot hZ) fun h =>
    ht (eq_of_catalogIs_u4two_lieModel h hX).1

theorem u42Layer_entrywise_G2 {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {d : ℕ} (hd : 1 ≤ d)
    (hk : Nat.card ↥(fixSubfield σ) = 2 ^ d) :
    U42Layer (entrywiseAdjointAut Tag.G2 σ) False := by
  haveI : Finite ↥(fixSubfield σ) := Subtype.finite
  by_cases h3 : 3 ≤ 2 ^ d
  · have hM : ChevalleyExceptionalModel ↥(adjointGroup Tag.G2 ↥(fixSubfield σ)) .G2 2 d :=
      ⟨⟨Nat.prime_two, hd, rfl, h3⟩, untwisted_adjointGroup hk⟩
    obtain ⟨-, hsimp⟩ := CFSG.LieType.Simplicity.fam_g2_simplicity _ 2 d hM
    exact u42Layer_entrywise_exc (t := .G2) (by decide) σ (Or.inr (Or.inl ⟨rfl, by decide, hM⟩))
      hsimp center_adjointGroup_eq_bot
  · have h2 : 2 ^ d = 2 := by
      have : 2 ≤ 2 ^ d := Nat.le_self_pow (by omega) 2
      omega
    refine u42Layer_of_card_dvd _ (N := 12096) ?_ (by norm_num)
    have hfix : Nat.card ↥(fixSubgroup (entrywiseAdjointAut Tag.G2 σ)) =
        Nat.card ↥(entrywiseFixedGroup Tag.G2 σ) := by
      rw [fixSubgroup_entrywiseAdjointAut]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    rw [hfix, card_entrywiseFixedGroup_G2 σ (hk.trans h2)]
    simp [CFSG.ComponentClassification.CatLeaf.lieOrderNumerator]

theorem u42Layer_entrywise_F4 {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {d : ℕ} (hd : 1 ≤ d)
    (hk : Nat.card ↥(fixSubfield σ) = 2 ^ d) :
    U42Layer (entrywiseAdjointAut Tag.F4 σ) False := by
  haveI : Finite ↥(fixSubfield σ) := Subtype.finite
  have hM : ChevalleyExceptionalModel ↥(adjointGroup Tag.F4 ↥(fixSubfield σ)) .F4 2 d :=
    ⟨⟨Nat.prime_two, hd, rfl⟩, untwisted_adjointGroup hk⟩
  obtain ⟨-, hsimp⟩ := CFSG.LieType.Simplicity.fam_f4_simplicity _ 2 d hM
  exact u42Layer_entrywise_exc (t := .F4) (by decide) σ (Or.inr (Or.inl ⟨rfl, by decide, hM⟩))
    hsimp center_adjointGroup_eq_bot

theorem u42Layer_entrywise_E7 {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {d : ℕ} (hd : 1 ≤ d)
    (hk : Nat.card ↥(fixSubfield σ) = 2 ^ d) :
    U42Layer (entrywiseAdjointAut Tag.E7 σ) False := by
  haveI : Finite ↥(fixSubfield σ) := Subtype.finite
  have hM : ChevalleyExceptionalModel ↥(adjointGroup Tag.E7 ↥(fixSubfield σ)) .E7 2 d :=
    ⟨⟨Nat.prime_two, hd, rfl⟩, untwisted_adjointGroup hk⟩
  obtain ⟨-, hsimp⟩ := CFSG.LieType.Simplicity.fam_e7_simplicity _ 2 d hM
  exact u42Layer_entrywise_exc (t := .E7) (by decide) σ (Or.inr (Or.inl ⟨rfl, by decide, hM⟩))
    hsimp center_adjointGroup_eq_bot

theorem u42Layer_entrywise_E8 {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {d : ℕ} (hd : 1 ≤ d)
    (hk : Nat.card ↥(fixSubfield σ) = 2 ^ d) :
    U42Layer (entrywiseAdjointAut Tag.E8 σ) False := by
  haveI : Finite ↥(fixSubfield σ) := Subtype.finite
  have hM : ChevalleyExceptionalModel ↥(adjointGroup Tag.E8 ↥(fixSubfield σ)) .E8 2 d :=
    ⟨⟨Nat.prime_two, hd, rfl⟩, untwisted_adjointGroup hk⟩
  obtain ⟨-, hsimp⟩ := CFSG.LieType.Simplicity.fam_e8_simplicity _ 2 d hM
  exact u42Layer_entrywise_exc (t := .E8) (by decide) σ (Or.inr (Or.inl ⟨rfl, by decide, hM⟩))
    hsimp center_adjointGroup_eq_bot

theorem u42Exc_chevalleyExceptionalModel {S : Type} [Group S] {t : StatedLieTag} {p f : ℕ}
    (hm : Blueprint.LieModel S t 0 p f) (hc : t ∉ classicalTags) (hr : t ∉ reeTitsTags)
    (hs : t ≠ .twistedB2) : ChevalleyExceptionalModel S t p f := by
  rcases hm with ⟨ht, -⟩ | ⟨-, -, hE⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact absurd ht hc
  · exact hE
  · exact absurd ht hr
  · exact absurd ht hs

theorem u42Exc_setup {S : Type} [Group S] [Finite S] {τ : Tag} {q : ℕ}
    (hU : UntwistedChevalleyModel S τ q) {α : MulAut S} (hα : α ∉ innAutDerived S)
    (hp : U42Pumpup S α) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (θ : S ≃* ↥(adjointGroup τ F)),
      Nat.card F = q ∧ MulAut.congr θ α ^ 3 = 1 ∧
        MulAut.congr θ α ∉ inner ↥(adjointGroup τ F) := by
  obtain ⟨F, hFf, hFin, hFcard, ⟨θ⟩⟩ := exists_equiv_adjointGroup_of_untwisted hU
  refine ⟨F, hFf, hFin, θ, hFcard, ?_, fun hin => ?_⟩
  · rw [← map_pow, hp.1, map_one]
  · exact not_mem_range_conj_of_not_mem_innAutDerived hα
      ((congr_mem_inner_iff_of_equiv θ α).mp hin)

theorem u42Exc_false_of_conj_pow {S : Type} [Group S] [Finite S] {τ : Tag} {F : Type} [Field F]
    [Finite F] (θ : S ≃* ↥(adjointGroup τ F)) {α : MulAut S} (hp : U42Pumpup S α) {T : F ≃+* F}
    {δ : MulAut ↥(adjointGroup τ F)} {r j : ℕ}
    (hrj : (MulAut.congr θ α ^ r) ^ j = MulAut.congr θ α)
    (hδ : δ * MulAut.congr θ α ^ r * δ⁻¹ = entrywiseAdjointAut τ T)
    (hNo : U42Layer (entrywiseAdjointAut τ T) False) : False :=
  hp.apply (u42Layer_congr θ (u42Layer_of_conj_pow hrj hδ hNo))

theorem u42Out_g2 : U42OuterAt FamG2 := by
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
    obtain ⟨F, hFf, hFin, θ, hFcard, hβ3, hβinn⟩ := u42Exc_setup hU hα hp
    obtain ⟨d, T, δ, hfd, hTo, hTc, hδ⟩ := G2_descent q.prime_p hf hq3 F hFcard _ hβ3 hβinn
    have hq2 : q.p = 2 := hc
    rw [hq2] at hTc
    exact u42Exc_false_of_conj_pow θ hp (r := 1) (j := 1) (by simp) (by simpa using hδ)
      (u42Layer_entrywise_G2 T (by omega) hTc)
  | _ => exact hF.elim

theorem u42Out_f4 : U42OuterAt FamF4 := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ α hα hp
  cases d with
  | F4 q =>
    exfalso
    haveI : Fact q.p.Prime := ⟨q.prime_p⟩
    have hf : 1 ≤ q.exponent := q.exponent_pos
    have hU : UntwistedChevalleyModel S .F4 (q.p ^ q.exponent) :=
      (u42Exc_chevalleyExceptionalModel (blueprintLieModel_F4 q hv e)
        (by decide) (by decide) (by decide)).2
    obtain ⟨F, hFf, hFin, θ, hFcard, hβ3, hβinn⟩ := u42Exc_setup hU hα hp
    obtain ⟨d, T, δ, hfd, hTo, hTc, hδ⟩ := F4_descent hf F hFcard _ hβ3 hβinn
    have hq2 : q.p = 2 := hc
    rw [hq2] at hTc
    exact u42Exc_false_of_conj_pow θ hp (r := 1) (j := 1) (by simp) (by simpa using hδ)
      (u42Layer_entrywise_F4 T (by omega) hTc)
  | _ => exact hF.elim

theorem u42Out_e7 : U42OuterAt FamE7 := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ α hα hp
  cases d with
  | E7 q =>
    exfalso
    haveI : Fact q.p.Prime := ⟨q.prime_p⟩
    have hf : 1 ≤ q.exponent := q.exponent_pos
    have hU : UntwistedChevalleyModel S .E7 (q.p ^ q.exponent) :=
      (u42Exc_chevalleyExceptionalModel (blueprintLieModel_E7 q hv e)
        (by decide) (by decide) (by decide)).2
    obtain ⟨F, hFf, hFin, θ, hFcard, hβ3, hβinn⟩ := u42Exc_setup hU hα hp
    have hdet : ¬ 3 ∣ Tag.E7.cartan.det.natAbs := by
      rw [det_cartan_E7]
      decide
    obtain ⟨d, T, r, j, δ, hfd, hTo, hTc, hrj, hδ⟩ :=
      exists_conj_entrywise_of_outer_E Tag.E7 (Or.inr (Or.inl rfl)) hf F hFcard Nat.prime_three
        (by norm_num) hdet _ hβ3 hβinn
    have hq2 : q.p = 2 := hc
    rw [hq2] at hTc
    exact u42Exc_false_of_conj_pow θ hp hrj hδ (u42Layer_entrywise_E7 T (by omega) hTc)
  | _ => exact hF.elim

theorem u42Out_e8 : U42OuterAt FamE8 := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ α hα hp
  cases d with
  | E8 q =>
    exfalso
    haveI : Fact q.p.Prime := ⟨q.prime_p⟩
    have hf : 1 ≤ q.exponent := q.exponent_pos
    have hU : UntwistedChevalleyModel S .E8 (q.p ^ q.exponent) :=
      (u42Exc_chevalleyExceptionalModel (blueprintLieModel_E8 q hv e)
        (by decide) (by decide) (by decide)).2
    obtain ⟨F, hFf, hFin, θ, hFcard, hβ3, hβinn⟩ := u42Exc_setup hU hα hp
    have hdet : ¬ 3 ∣ Tag.E8.cartan.det.natAbs := by
      rw [det_cartan_E8]
      decide
    obtain ⟨d, T, r, j, δ, hfd, hTo, hTc, hrj, hδ⟩ :=
      exists_conj_entrywise_of_outer_E Tag.E8 (Or.inr (Or.inr rfl)) hf F hFcard Nat.prime_three
        (by norm_num) hdet _ hβ3 hβinn
    have hq2 : q.p = 2 := hc
    rw [hq2] at hTc
    exact u42Exc_false_of_conj_pow θ hp hrj hδ (u42Layer_entrywise_E8 T (by omega) hTc)
  | _ => exact hF.elim

end Exceptional

end CFSG.LocalAnalysis.GLTheoremA.I1431C2

end
