module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineCatCross
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineCatalogue
public import CFSG.LieType.SeitzGeneration.QuasiHigh5UnitaryEight
public import CFSG.LieType.SeitzGeneration.QuasiHigh5E6CoverTw
import CFSG.Adapters.LinearCatalogStated
public import CFSG.RankThree.PartTwo.Sec4.Census.CoverSLThree46

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.Open TauCeti
open CFSG.LocalAnalysis.AGL81TheoremCD.Section12 (gammaOver)
open CFSG.LieType.Seitz (seitzHyperGamma)
open CFSG.LieType.SeitzGeneration.QuasiHigh (CoverIndex)

theorem le_gammaOver_of_seitzHyperGamma {X : Type} [Group X] [Finite X] {K E : Subgroup X}
    {p : ℕ} (hp : p.Prime) (hKn : K.Normal) (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 2)
    (h : ∀ A : Subgroup (MulAut ↥K), IsElemAbelian p A → Nat.card A = p ^ 2 →
      seitzHyperGamma p A = ⊤) :
    K ≤ gammaOver 1 p E K := by
  by_cases hc : ∃ x ∈ E, x ≠ 1 ∧ ∀ c ∈ K, x * c = c * x
  · obtain ⟨x, hxE, hx1, hxc⟩ := hc
    exact fun c hcK => mem_gammaOver_of_commute hp hxE hx1 (hE.2 x hxE) hcK (hxc c hcK)
  push Not at hc
  have : K.Normal := hKn
  set f : ↥E →* MulAut ↥K := (MulAut.conjNormal : X →* MulAut ↥K).comp E.subtype with hf
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    by_contra hne
    have hx1 : (x : X) ≠ 1 := fun h1 => hne (Subtype.ext h1)
    obtain ⟨c, hcK, hxc⟩ := hc x x.2 hx1
    apply hxc
    have h2 := congrArg (fun α : MulAut ↥K => ((α ⟨c, hcK⟩ : ↥K) : X)) hx
    simp only [hf, MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conjNormal_apply,
      MulAut.one_apply] at h2
    calc (x : X) * c = (x : X) * c * (x : X)⁻¹ * x := by group
      _ = c * x := by rw [h2]
  have hA : CFSG.LieType.SeitzGeneration.actionImage K E = f.range := by
    rw [hf, ← MonoidHom.map_range, Subgroup.range_subtype]
    rfl
  have hAc : Nat.card (CFSG.LieType.SeitzGeneration.actionImage K E) = p ^ 2 := by
    rw [hA, MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj, Subgroup.card_top, hEc]
  have hAe : IsElemAbelian p (CFSG.LieType.SeitzGeneration.actionImage K E) :=
    CFSG.SectionRank.isElemAbelian_map hE _
  refine (CFSG.LieType.SeitzGeneration.hyperGen_of_seitzHyperGamma p K E
    (h _ hAe hAc)).trans ((Subgroup.closure_le _).mpr ?_)
  rintro k ⟨hkK, F, hFE, hFi, hFk⟩
  have hF : F ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.relIndex_bot_left, hEc] at hFi
    have h2 := hp.two_le
    nlinarith
  obtain ⟨⟨x, hxF⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hF
  have hx1' : x ≠ 1 := fun h1 => hx1 (Subtype.ext h1)
  exact mem_gammaOver_of_commute hp (hFE hxF) hx1' (hE.2 x (hFE hxF)) hkK (hFk x hxF)

section Unitary

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.QuasiHigh5

theorem seitzHyperGamma_eq_top_unitary_of_ne
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Group K] [Finite K]
    (hperf : commutator K = ⊤) {m : ℕ} {q : PrimePower}
    {hv : (LieTypeIndex.twistedA m q).Valid}
    (e : K ⧸ Subgroup.center K ≃* (CFSGIndex.lie ⟨.twistedA m q, hv⟩).Group)
    (hpq : p ≠ q.p) (hci : CoverIndex p (.twistedA m q)) (hq2 : q.card ≠ 2)
    (hq8 : m = 2 → q.card ≠ 2 ^ p) {E : Subgroup (MulAut K)}
    (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 2) :
    seitzHyperGamma p E = ⊤ := by
  classical
  obtain ⟨hℓ, hf, hn3, hne, Kf, _, hU, ⟨θ'⟩⟩ :=
    CFSG.RankThree.PartOne.exists_primeFormP_of_statedClassicalModel_PSU
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA m q hv e)
  have := hU.finite
  have : Fact q.p.Prime := ⟨hℓ⟩
  have : CharP Kf q.p := hU.charP
  have hqcard : q.p ^ q.exponent = q.card := (PrimePower.card_def q).symm
  have hpq1 : p ∣ q.p ^ q.exponent + 1 := by
    rw [hqcard]
    exact hci.2
  have hq2' : q.p ^ q.exponent ≠ 2 := by
    rw [hqcard]
    exact hq2
  have hq4 : Even (m + 1) → 4 ≤ q.p ^ q.exponent := by
    intro _
    have h2 : 2 ≤ q.p ^ q.exponent :=
      le_trans hℓ.two_le (Nat.le_self_pow q.exponent_pos.ne' q.p)
    have h3 : q.p ^ q.exponent ≠ 3 := by
      intro h3
      rw [h3] at hpq1
      have : p ∣ 2 ^ 2 := by norm_num; exact hpq1
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow this))
    omega
  by_cases hD : E.map (QuasiHigh2.modelAut θ') ≤ primeFormD hU (idGram Kf (m + 1))
  · exact seitzHyperGamma_eq_top_unitary_diag hperf hU hn3 hq2' hp hp2 hpq1 hq4 θ' hE hcard hD
  · refine seitzHyperGamma_eq_top_unitary_field hperf hU hn3 hne hp hp2 hpq hq4 ?_ θ' hE hcard hD
    intro hm3 h8
    exact hq8 (by omega) (by rw [← hqcard]; exact h8)

end Unitary

theorem not_isD2SeitzException_three_E6 (q : PrimePower) :
    ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException 3 (.E6 q) := by
  simp [CFSG.AGLEmbeddingD2.IsD2SeitzException]

theorem not_isD2SeitzException_three_twistedE6 (q : PrimePower) :
    ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException 3 (.twistedE6 q) := by
  simp [CFSG.AGLEmbeddingD2.IsD2SeitzException]

section E6


theorem seitzHyperGamma_eq_top_E6_three {K : Type} [Group K] [Finite K]
    (hperf : commutator K = ⊤) {q : PrimePower} {hv : (LieTypeIndex.E6 q).Valid}
    (e : K ⧸ Subgroup.center K ≃* (CFSGIndex.lie ⟨.E6 q, hv⟩).Group) (hpq : 3 ≠ q.p)
    (h3 : 3 ∣ q.card - 1) {E : Subgroup (MulAut K)} (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 2) : seitzHyperGamma 3 E = ⊤ := by
  have hq2 : 2 ≤ q.card := by
    rw [PrimePower.card_def]
    exact le_trans q.prime_p.two_le (Nat.le_self_pow q.exponent_pos.ne' q.p)
  have hc : (LieTypeIndex.E6 q).characteristic = q.p := LieTypeIndex.characteristic_E6 q
  refine CFSG.LieType.SeitzGeneration.seitzHyperGamma_eq_top_of_uniPlaneGen hperf e
    Nat.prime_three (LieTypeIndex.characteristic_prime _) (by rw [hc]; exact Ne.symm hpq) hE hcard
    ?_
  exact CFSG.LieType.SeitzGeneration.QuasiHigh5E6Cover.uniSeitzPlanes_E6_three_one ⟨.E6 q, hv⟩ 3
    Nat.prime_three (by norm_num) (by rw [Subtype.coe_mk, hc]; exact hpq)
    (not_isD2SeitzException_three_E6 q) _
    (CFSG.LieType.SeitzGeneration.isElemAbelian_coverImage e hE)
    (by rw [CFSG.LieType.SeitzGeneration.card_coverImage hperf e E, hcard])
    ⟨rfl, q, rfl, by omega⟩

theorem seitzHyperGamma_eq_top_twistedE6_three
    (hD : CFSG.LieType.SeitzGeneration.QuasiHigh5E6Cover.TwE6ThreeOpenDiag)
    {K : Type} [Group K] [Finite K] (hperf : commutator K = ⊤) {q : PrimePower}
    {hv : (LieTypeIndex.twistedE6 q).Valid}
    (e : K ⧸ Subgroup.center K ≃* (CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group) (hpq : 3 ≠ q.p)
    (h3 : 3 ∣ q.card + 1) (hq2 : q.card ≠ 2) (hq8 : q.card ≠ 8) {E : Subgroup (MulAut K)}
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 2) : seitzHyperGamma 3 E = ⊤ := by
  have hc : (LieTypeIndex.twistedE6 q).characteristic = q.p :=
    LieTypeIndex.characteristic_twistedE6 q
  refine CFSG.LieType.SeitzGeneration.seitzHyperGamma_eq_top_of_uniPlaneGen hperf e
    Nat.prime_three (LieTypeIndex.characteristic_prime _) (by rw [hc]; exact Ne.symm hpq) hE hcard
    ?_
  exact CFSG.LieType.SeitzGeneration.QuasiHigh5E6Cover.uniSeitzPlanes_twE6_three_two_of_open
    (CFSG.LieType.SeitzGeneration.QuasiHigh5E6Cover.twE6ThreeOpenPlanes_of
      CFSG.LieType.SeitzGeneration.QuasiHigh5E6Cover.twE6ThreeOpenInner_holds hD)
    ⟨.twistedE6 q, hv⟩ 3 Nat.prime_three (by norm_num) (by rw [Subtype.coe_mk, hc]; exact hpq)
    (not_isD2SeitzException_three_twistedE6 q) _
    (CFSG.LieType.SeitzGeneration.isElemAbelian_coverImage e hE)
    (by rw [CFSG.LieType.SeitzGeneration.card_coverImage hperf e E, hcard])
    ⟨rfl, q, rfl, by omega, hq2, fun h8 => absurd h8 hq8⟩

end E6

theorem isSLType_three_four_of_cover
    {K : Type} [Group K] [Finite K]
    (hKq : CFSG.IsQuasisimple K) (hZ3 : IsPGroup 3 (Subgroup.center K))
    (hZ : Subgroup.center K ≠ ⊥) {q : PrimePower} {hv : (LieTypeIndex.A 2 q).Valid}
    (hq4 : q.card = 4) (e : K ⧸ Subgroup.center K ≃* (CFSGIndex.lie ⟨.A 2 q, hv⟩).Group) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsSLType 3 F K := by
  have : Group.IsPerfect K := hKq.1
  have hodd : Odd (Nat.card (Subgroup.center K)) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hZ3
    rw [hn]
    exact Odd.pow (by decide)
  have hm := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
  obtain ⟨-, F, _, _, hF, ⟨e'⟩⟩ := hm
  have hF4 : Nat.card F = 2 ^ 2 := by
    rw [hF, ← PrimePower.card_def, hq4]
    norm_num
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card hF4
  have hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* StatedSL 3 F),
      Function.Surjective π → π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) →
      ∃ s : StatedSL 3 F →* E, ∀ g, π (s g) = g := by
    intro E _ _ π hπ hC hoddπ
    obtain ⟨s, hs, -⟩ :=
      CFSG.SectionRank.EvenCover.even_linear_central_odd_extension_splitting_stated (n := 3)
        (by norm_num) hπ hC hoddπ
    exact ⟨s, hs⟩
  obtain ⟨φ⟩ := CFSG.RankThree.PartTwo.Sec4.Census.nonempty_mulEquiv_of_odd_splitting hodd hZ e'
    (CFSG.RankThree.PartTwo.Sec4.Census.card_scalars_dvd_three (Or.inl ⟨hF4, rfl⟩)) hsplit
  exact ⟨F, inferInstance, inferInstance, by rw [hF4]; norm_num,
    ⟨φ.trans (CFSG.RankThree.PartTwo.Sec4.statedSLEquiv 3 F)⟩⟩

private theorem primePower_two_of_card_eq {q : PrimePower} {k : ℕ} (h : q.card = 2 ^ k) :
    q.p = 2 ∧ q.exponent = k := by
  have hq' : q.p ^ q.exponent = 2 ^ k := by rw [← PrimePower.card_def, h]
  have hp2 : q.p = 2 := by
    have h1 : q.p ∣ 2 ^ k := hq' ▸ dvd_pow_self q.p q.exponent_pos.ne'
    exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 (q.prime_p.dvd_of_dvd_pow h1)
  refine ⟨hp2, ?_⟩
  rw [hp2] at hq'
  exact Nat.pow_right_injective (le_refl 2) hq'

@[expose] def IsCrossCoverResidualIndex : LieTypeIndex → Prop
  | .twistedA r q => q.p = 2 ∧ q.exponent = 1 ∧ 3 ∣ r + 1 ∧ 5 ≤ r
  | .twistedE6 q => q.p = 2 ∧ (q.exponent = 1 ∨ q.exponent = 3)
  | _ => False

@[expose] def CrossCoverResidual24_12Three : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K E : Subgroup X) (d : ValidLieTypeIndex),
    K.Normal → CFSG.IsQuasisimple ↥K → 3 ∣ Nat.card (Subgroup.center ↥K) →
    Nonempty (↥K ⧸ Subgroup.center ↥K ≃* (CFSGIndex.lie d).Group) →
    IsCrossCoverResidualIndex d.1 → IsElemAbelian 3 E → Nat.card E = 3 ^ 2 →
    CFSG.Open.pRank 3 (K ⊔ E) ≤ 3 → K ≤ gammaOver 1 3 E K

theorem kGroupLowRank24_12_three_of_cross_cover
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hD : CFSG.LieType.SeitzGeneration.QuasiHigh5E6Cover.TwE6ThreeOpenDiag)
    (hCR : CrossCoverResidual24_12Three)
    {X : Type} [Group X] [Finite X] {K E : Subgroup X} (hKq : CFSG.IsQuasisimple ↥K)
    (hOp : CFSG.pPrimeCore 3 ↥K = ⊥) (hKcat : CFSG.SectionRank.IsKGroupCat ↥K) (hKn : K.Normal)
    (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 3 ^ 2) (hrk : CFSG.Open.pRank 3 (K ⊔ E) ≤ 3)
    (hΓ : ¬ K ≤ gammaOver 1 3 E K) {d : ValidLieTypeIndex} (hpd : 3 ≠ d.1.characteristic)
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* (CFSGIndex.lie d).Group)
    (hZ : Subgroup.center ↥K ≠ ⊥) : KGroupLowRank24_12 3 ↥K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZp : IsPGroup 3 (Subgroup.center ↥K) :=
    CFSG.isPGroup_of_nilpotent_normal (Subgroup.center ↥K) inferInstance inferInstance hOp
  have hdvd : 3 ∣ Nat.card (Subgroup.center ↥K) :=
    hZp.card_eq_or_dvd.resolve_left fun h => hZ (Subgroup.card_eq_one.mp h)
  have hq' : CFSG.Open.IsQuasisimple ↥K := ⟨Group.isPerfect_def.mp hKq.1, hKq.2.1⟩
  have hperf : commutator ↥K = ⊤ := hq'.1
  have hci := CFSG.LieType.SeitzGeneration.QuasiHigh.coverIndex_of_dvd_card_center hGA
    Nat.prime_three (by norm_num) hq' d e hpd hdvd
  by_cases hres : IsCrossCoverResidualIndex d.1
  · exact absurd (hCR X K E d hKn hKq hdvd ⟨e⟩ hres hE hEc hrk) hΓ
  refine ⟨Nat.prime_three, by norm_num, hKq, hKcat, ?_⟩
  obtain ⟨d, hv⟩ := d
  cases d
  case A r q =>
    by_cases hL : r = 2 ∧ q.card = 4
    · obtain ⟨rfl, hq4⟩ := hL
      refine Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩))
      iterate 11 right
      left
      exact isSLType_three_four_of_cover hKq hZp hZ hq4 e
    · refine absurd (le_gammaOver_of_seitzHyperGamma Nat.prime_three hKn hE hEc
        fun A hA hAc => ?_) hΓ
      exact CFSG.LieType.SeitzGeneration.QuasiHigh5.seitzHyperGamma_eq_top_linear
        Nat.prime_three (by norm_num) hperf e (by simpa using hpd) hci
        (fun h => hL ⟨h.2.1, h.2.2⟩) hA hAc
  case twistedA r q =>
    refine absurd (le_gammaOver_of_seitzHyperGamma Nat.prime_three hKn hE hEc
      fun A hA hAc => ?_) hΓ
    have hpq : 3 ≠ q.p := by simpa using hpd
    by_cases h8 : r = 2 ∧ q.card = 8
    · obtain ⟨rfl, h8⟩ := h8
      exact CFSG.LieType.SeitzGeneration.QuasiHigh5.seitzHyperGamma_eq_top_unitary_eight hq' e
        h8 hA hAc
    · have hq2 : q.card ≠ 2 := by
        intro hq2
        have hr := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
        have hr2 : r ≠ 2 := fun h => by have := hr.2 h; omega
        obtain ⟨hp2, he1⟩ := primePower_two_of_card_eq (k := 1) (by rw [hq2]; norm_num)
        obtain ⟨k, hk⟩ := hci.1
        exact hres ⟨hp2, he1, hci.1, by omega⟩
      exact seitzHyperGamma_eq_top_unitary_of_ne Nat.prime_three (by norm_num) hperf e hpq hci
        hq2 (fun hr h => h8 ⟨hr, by rw [h]; norm_num⟩) hA hAc
  case E6 q =>
    refine absurd (le_gammaOver_of_seitzHyperGamma Nat.prime_three hKn hE hEc
      fun A hA hAc => ?_) hΓ
    exact seitzHyperGamma_eq_top_E6_three hperf e (by simpa using hpd) hci.2 hA hAc
  case twistedE6 q =>
    refine absurd (le_gammaOver_of_seitzHyperGamma Nat.prime_three hKn hE hEc
      fun A hA hAc => ?_) hΓ
    have hq2 : q.card ≠ 2 := fun h => by
      obtain ⟨hp2, he⟩ := primePower_two_of_card_eq (k := 1) (by rw [h]; norm_num)
      exact hres ⟨hp2, Or.inl he⟩
    have hq8 : q.card ≠ 8 := fun h => by
      obtain ⟨hp2, he⟩ := primePower_two_of_card_eq (k := 3) (by rw [h]; norm_num)
      exact hres ⟨hp2, Or.inr he⟩
    exact seitzHyperGamma_eq_top_twistedE6_three hD hperf e (by simpa using hpd) hci.2 hq2 hq8
      hA hAc
  all_goals simp [CoverIndex] at hci

end CFSG.LocalAnalysis.AGL81I.Section3
