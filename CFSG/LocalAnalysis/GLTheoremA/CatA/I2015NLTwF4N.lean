module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015NLTwF4
import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalLargeReeTits
import CFSG.SignalizerFunctorTheorem.CatalogBridge.LargeReeFixed

public section

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

open CFSG.Open (signalizerFixedSubgroup)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Simplicity.TitsBits CFSG.SectionRank.TitsOrder CFSG.SectionRank.TitsGen
open CFSG.RankThree.Chevalley.SteinbergBT (card_fixSubfield)
open CFSG.RankThree.PartOne.Sec66T (fixSub fixRes)
open CFSG.LieType.Simplicity (titsData)
open CFSG.SignalizerFunctorTheorem.NonLocal CFSG.SignalizerFunctorTheorem.NonLocalExc
open scoped IsMulCommutative commutatorElement

section TitsOdd

set_option linter.unusedSectionVars false


theorem commutator_le_fixRes {T G : Type} [Group T] [Finite T] [Group G] (α : MulAut T)
    (Φ : G ≃* ↥(fixSub α)) (hperf : Group.IsPerfect ↥(commutator G)) :
    ∀ d ∈ commutator G, ((Φ d : ↥(fixSub α)) : T) ∈ fixRes α := by
  have : Finite ↥(fixSub α) := Subtype.finite
  have hcomm : (commutator G).map Φ.toMonoidHom = commutator ↥(fixSub α) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ Φ.surjective]
  have hperfJ : Group.IsPerfect ↥(commutator ↥(fixSub α)) := by
    have e' : ↥(commutator G) ≃* ↥(commutator ↥(fixSub α)) :=
      (Subgroup.equivMapOfInjective _ Φ.toMonoidHom Φ.injective).trans
        (MulEquiv.subgroupCongr hcomm)
    exact Group.IsPerfect.ofSurjective (f := e'.toMonoidHom) e'.surjective
  have hsub : commutator ↥(fixSub α) ≤ perfectResidual ↥(fixSub α) :=
    (perfect_residual_transport (MonoidHom.id ↥(fixSub α))).2.2 _ hperfJ
  intro d hd
  have hmem : Φ d ∈ commutator ↥(fixSub α) := by
    rw [← hcomm]
    exact ⟨d, hd, rfl⟩
  exact ⟨Φ d, hsub hmem, rfl⟩

theorem titsFixIso {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpa : p = 2 * a + 1) (σ : K ≃+* K) (hσ : orderOf σ = p) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k ReeTag.F4.prime) (f : k →+* K)
      (Φ : reeFixed ReeTag.F4 k 0 ≃* ↥(fixSub (ReeTag.F4.reeGammaFieldAut K a σ))),
      Nat.card k = 2 ∧
      ∀ t : reeFixed ReeTag.F4 k 0,
        ((Φ t : ↥(fixSub (ReeTag.F4.reeGammaFieldAut K a σ))) : ModGL ReeTag.F4.tag K) =
          baseChangeGL f (((t : adjointGroup ReeTag.F4.tag k)) : ModGL ReeTag.F4.tag k) := by
  classical
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have : Finite ↥(ReeTag.F4.reeGamma K a) := Subtype.finite
  obtain ⟨hpf, hcard⟩ := card_fixSubfield Nat.prime_two (by omega) hK σ
  rw [hσ] at hpf hcard
  have hk2 : Nat.card (fixSubfield σ) = 2 := by
    rw [hcard, hpa, Nat.div_self (by omega), pow_one]
  obtain ⟨b, -, hkcard, hfixed⟩ := largeRee_fixed_data_odd hK hp hp2 σ hσ
  have hb : b = 0 := by
    have h1 : 2 ^ (2 * b + 1) = 2 ^ 1 := by rw [← hkcard, hk2, pow_one]
    have := Nat.pow_right_injective (le_refl 2) h1
    omega
  subst hb
  have : Finite (fixSubfield σ) := Subtype.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP (fixSubfield σ) ReeTag.F4.prime := by
    have : Fintype (fixSubfield σ) := Fintype.ofFinite _
    exact charP_of_card_eq_prime_pow (f := 2 * 0 + 1) (by
      rw [← Nat.card_eq_fintype_card, hkcard]
      rfl)
  have hinj : Function.Injective (baseChangeGL (τ := ReeTag.F4.tag) (fixSubfield σ).subtype) :=
    baseChangeGL_injective (τ := ReeTag.F4.tag) (fixSubfield σ).subtype
  let eC : fixSub (ReeTag.F4.reeGammaFieldAut K a σ) ≃* ReeTag.F4.reeGamma (fixSubfield σ) 0 :=
    isoOfMapEq (ReeTag.F4.reeGamma K a) _ (ReeTag.F4.reeGamma (fixSubfield σ) 0)
      (baseChangeGL (fixSubfield σ).subtype) hinj hfixed
  have heC : ∀ x : fixSub (ReeTag.F4.reeGammaFieldAut K a σ),
      baseChangeGL (fixSubfield σ).subtype
        ((eC x : ReeTag.F4.reeGamma (fixSubfield σ) 0) : ModGL ReeTag.F4.tag (fixSubfield σ)) =
        (((x : ↥(ReeTag.F4.reeGamma K a)) : ModGL ReeTag.F4.tag K)) := fun x =>
    isoOfMapEq_val _ _ _ _ hinj _ x
  refine ⟨fixSubfield σ, inferInstance, inferInstance, inferInstance, (fixSubfield σ).subtype,
    (ReeTag.reeFixedEquivReeGamma (fixSubfield σ) 0).trans eC.symm, hk2, fun t => ?_⟩
  have h := heC (eC.symm (ReeTag.reeFixedEquivReeGamma (fixSubfield σ) 0 t))
  rw [MulEquiv.apply_symm_apply, ReeTag.coe_reeFixedEquivReeGamma] at h
  exact h.symm

theorem titsEmbedData {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpa : p = 2 * a + 1) (σ : K ≃+* K) (hσ : orderOf σ = p) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k ReeTag.F4.prime) (f : k →+* K)
      (ι : reeFixed ReeTag.F4 k 0 →* ↥(ReeTag.F4.reeGamma K a)),
      Nat.card k = 2 ∧
      (∀ t : reeFixed ReeTag.F4 k 0,
        ((ι t : ↥(ReeTag.F4.reeGamma K a)) : ModGL ReeTag.F4.tag K) =
          baseChangeGL f (((t : adjointGroup ReeTag.F4.tag k)) : ModGL ReeTag.F4.tag k)) ∧
      ∀ d ∈ commutator (reeFixed ReeTag.F4 k 0),
        ι d ∈ fixRes (ReeTag.F4.reeGammaFieldAut K a σ) := by
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have : Finite ↥(ReeTag.F4.reeGamma K a) := Subtype.finite
  obtain ⟨k, _, _, _, f, Φ, hk2, hΦ⟩ := titsFixIso ha hK hp hp2 hpa σ hσ
  refine ⟨k, inferInstance, inferInstance, inferInstance, f,
    (fixSub (ReeTag.F4.reeGammaFieldAut K a σ)).subtype.comp Φ.toMonoidHom, hk2, hΦ, ?_⟩
  exact commutator_le_fixRes (ReeTag.F4.reeGammaFieldAut K a σ) Φ
    ((titsData k hk2).isPerfect hk2)

theorem nonLocalized_tits_of_odd {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpa : p = 2 * a + 1) (σ : K ≃+* K) (hσ : orderOf σ = p) :
    NonLocalized (fixRes (ReeTag.F4.reeGammaFieldAut K a σ)) := by
  classical
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have : Finite ↥(ReeTag.F4.reeGamma K a) := Subtype.finite
  obtain ⟨k, _, _, _, f, ι, hk2, hι, hfixι⟩ := titsEmbedData ha hK hp hp2 hpa σ hσ
  refine nonLocalized_of_elemAbelian (fun s E hs hE0 hEcomm hEexp hle => hE0 ?_)
  have hnorm : ∀ d ∈ commutator (reeFixed ReeTag.F4 k 0), ∀ e ∈ E,
      ι d * e * (ι d)⁻¹ ∈ E := fun d hd e he =>
    (Subgroup.mem_normalizer_iff.1 (hle (hfixι d hd)) e).1 he
  by_cases hs2 : s = 2
  · subst hs2
    have : Fact (Nat.Prime 2) := ⟨hs⟩
    have hEp : IsPGroup 2 E := by
      refine IsPGroup.iff_orderOf.mpr (fun g => ?_)
      have h1 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (Subtype.ext (hEexp g g.2))
      rcases (Nat.dvd_prime hs).mp h1 with h | h
      · exact ⟨0, by simpa using h⟩
      · exact ⟨1, by simpa using h⟩
    exact largeRee_twoGroup_eq_bot_tits f ι hι E hEp hnorm
  · exact largeRee_oddGroup_eq_bot_tits hK hk2 f ι hι hs hs2 E hEcomm hEexp hnorm

end TitsOdd

end CFSG.SignalizerFunctorTheorem.CatalogBridge

namespace CFSG.LocalAnalysis.GLTheoremA.I2015

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA.MI
  CFSG.LocalAnalysis.GLTheoremA.FQ CFSG.LocalAnalysis.GLTheoremA.FR
open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

section Perfect

theorem fixRes_perfect {T : Type} [Group T] [Finite T] (α : MulAut T) :
    ⁅CFSG.RankThree.PartOne.Sec66T.fixRes α, CFSG.RankThree.PartOne.Sec66T.fixRes α⁆ =
      CFSG.RankThree.PartOne.Sec66T.fixRes α := by
  have hP : Group.IsPerfect (perfectResidual ↥(CFSG.RankThree.PartOne.Sec66T.fixSub α)) :=
    (CFSG.perfect_residual_characterization
      (G := ↥(CFSG.RankThree.PartOne.Sec66T.fixSub α))).2.2.1
  rw [Subgroup.isPerfect_iff] at hP
  unfold CFSG.RankThree.PartOne.Sec66T.fixRes CFSG.inSubgroup
  rw [← Subgroup.map_commutator, hP]

theorem fixRes_le_fixSub {T : Type} [Group T] (α : MulAut T) :
    CFSG.RankThree.PartOne.Sec66T.fixRes α ≤ CFSG.RankThree.PartOne.Sec66T.fixSub α :=
  Subgroup.map_subtype_le _

end Perfect

section Family

set_option linter.unusedSectionVars false


theorem twF4NoLocalTwoN {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpa : p = 2 * a + 1) {f : MulAut (LargeEvenCenterQuot (LargeEvenTwF4H a K))}
    (hord : orderOf f = p)
    (hnot : f ∉ (MulAut.conj : LargeEvenCenterQuot (LargeEvenTwF4H a K) →* _).range) :
    NoLocalTwo p f := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K F4.prime := charP_of_card_eq_prime_pow (p := 2) (f := 2 * a + 1) (by
    rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨β, eT, hβord, key⟩ := twF4Lang ha hK hp hord hnot
  haveI : Finite (ModGL F4.tag K) := finite_modGL
  haveI : Finite ↥(F4.reeGamma K a) := Subtype.finite
  haveI : Finite (LargeEvenCenterQuot (LargeEvenTwF4H a K)) := Finite.of_equiv _ eT.symm.toEquiv
  have hcore : CoreSub (FP.fixSub f) := by
    obtain ⟨eS⟩ := CFSG.StandardType.centerQuot_twF4H_equiv K a
    obtain ⟨-, b₀, hb, k, _, _, _, hk, ⟨eF⟩⟩ := FR.Res.ree_fix_equiv ha hK hp hp2 eS f hord hnot
    have hb0 : b₀ = 0 := by
      have h1 : (2 * b₀ + 1) * p = 1 * p := by rw [hb, hpa, one_mul]
      have := Nat.eq_of_mul_eq_mul_right hp.pos h1
      omega
    subst hb0
    have hk2 : Nat.card k = 2 := by simpa using hk
    have hC : DatumCore ↥(FP.fixSub f) := FR.Res.datumCore_of_equiv eF (FR.Res.datumCore_reeGamma_zero hk2)
    exact coreSub_of_subfield ⟨le_rfl, Subgroup.commutator_le_of_le le_rfl le_rfl,
      by rw [Subgroup.relIndex_self]; exact odd_one⟩ hC
  obtain ⟨E, hEC, hE, hna, hperf, -, -⟩ := id hcore
  have hTE : CFSG.RankThree.PartOne.Sec66T.fixRes (F4.reeGammaFieldAut K a β) ≤
      E.map eT.toMonoidHom := by
    set T := CFSG.RankThree.PartOne.Sec66T.fixRes (F4.reeGammaFieldAut K a β) with hT
    have hTfix : T ≤ CFSG.RankThree.PartOne.Sec66T.fixSub (F4.reeGammaFieldAut K a β) :=
      fixRes_le_fixSub _
    have hC' : T.map eT.symm.toMonoidHom ≤ FP.fixSub f := by
      rintro _ ⟨x, hx, rfl⟩
      have hx' : F4.reeGammaFieldAut K a β x = x := hTfix hx
      rw [FP.mem_fixSub]
      apply eT.injective
      rw [key]
      show F4.reeGammaFieldAut K a β (eT (eT.symm x)) = eT (eT.symm x)
      rw [MulEquiv.apply_symm_apply]
      exact hx'
    have hperf' : ⁅T.map eT.symm.toMonoidHom, T.map eT.symm.toMonoidHom⁆ =
        T.map eT.symm.toMonoidHom := by
      rw [← Subgroup.map_commutator, hT, fixRes_perfect]
    have hle := hperf _ hC' hperf'
    intro x hx
    refine ⟨eT.symm x, hle ⟨x, hx, rfl⟩, ?_⟩
    simp
  have hW : NLWitness f := by
    refine ⟨E, by rw [← fpFixSub_eq_fixSub]; exact hEC, hE, hna, ?_⟩
    intro U hU hU2 hN
    have hU' : U.map eT.toMonoidHom ≠ ⊥ := fun hbot =>
      hU ((Subgroup.map_eq_bot_iff_of_injective U eT.injective).1 hbot)
    have hsolv : Group.IsSolvable ↥(U.map eT.toMonoidHom) :=
      isSolvable_of_isPGroup_two (hU2.map eT.toMonoidHom)
    have hNL := CFSG.SignalizerFunctorTheorem.CatalogBridge.nonLocalized_tits_of_odd ha hK hp hp2
      hpa β hβord
    exact hNL _ hU' hsolv (hTE.trans (map_le_normalizer_map eT hN))
  exact noLocalTwo_of_coreSub hp hcore hW

theorem i2015NLResTwF4_holds : I2015NLResTwF4 := by
  intro lab hlab ht p hp hp2 _ hC
  have ht' : lab.tag = .twF4 := ht
  have hInn := canonRawInnAny hp.ne_one hlab
  have h₁ : CAll lab fun R _ I F => GGRawInnField p R I F →
      LargeEvenSimpleGuard (fun R _ _ F => ∀ f ∈ F, orderOf f = p → Finite R → NoLocalTwo p f)
        R I F := by
    obtain ⟨t, r, n⟩ := lab
    obtain ⟨hn, hl⟩ := hlab
    dsimp only [regN] at ht' hn hl hC
    subst ht'
    obtain ⟨rfl, ⟨k, hk⟩, hn3⟩ := hl
    subst hk
    have e : (2 * k + 1 - 1) / 2 = k := by omega
    intro Q hQ
    unfold CFSG.Assembly.LargeEvenRawDatum at hQ ⊢
    dsimp only at hQ ⊢
    rw [e] at hQ ⊢
    obtain ⟨K, hF, hfin, hK, hQ'⟩ := hQ
    refine ⟨K, hF, hfin, hK, hQ', ?_⟩
    intro hinn hs hna f hf hord _
    obtain ⟨-, -, hconj, hFI⟩ := hinn hs hna
    exact twF4NoLocalTwoN (by omega) hK hp hp2 hC.symm hord
      fun ⟨r, hr⟩ => hFI f hf hord (hr ▸ hconj r)
  exact (h₁.and hInn).mono fun R _ I F ⟨h1, h2⟩ => h1 h2

end Family

end CFSG.LocalAnalysis.GLTheoremA.I2015

end
