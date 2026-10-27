module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.LeviFinal
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.LeviFamilies
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.LeviExc
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.LeviExcMin
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.LeviSU
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.LeviSpinMinus
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.LeviTwD4
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.LeviTwE6

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.AGLEmbedding CFSG.QuasithinUnique
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.LieType.Chevalley
  CFSG.QuasithinUnique.Bridge.Over CFSG.Quasithin
  CFSG.ClassicalInvolution.ModelFacts.ChevAut CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.AGLEmbedding.ParabHub
  CFSG.AGLEmbedding.ParabHub.ParabThreeInv CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

set_option linter.unusedSectionVars false


section Models

open CFSG.LieType.Universal.Symplectic TauCeti.GLSymplecticFin
open CFSG.Assembly.LowTwoRank

theorem hasBQLevi_of_model_psp {Y : Type} [Group Y] {n f : ℕ}
    (h : StatedClassicalModel Y .PSp n 2 f) : HasBQLevi Y := by
  obtain ⟨-, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  exact ⟨_, inferInstance, inferInstance, _, _, _, _, _, borelQuotient_sp e,
    fun i => nodeLevi_sp i⟩

open CFSG.LieType.Universal.Spin in
theorem hasBQLevi_of_model_pomegaPlus {Y : Type} [Group Y] {n f : ℕ}
    (h : StatedClassicalModel Y .POmegaPlus n 2 f) : HasBQLevi Y := by
  obtain ⟨⟨-, -, hn⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have hn3 : 3 ≤ n := by omega
  have : NeZero n := ⟨by omega⟩
  have : Finite (spinGroup (quadPlus n F)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadPlus (n := n) (K := F))
  exact ⟨_, inferInstance, inferInstance, _, _, _, _, _, borelQuotient_spinPlus hn3 e,
    fun i => nodeLevi_spinPlus hn3 i⟩

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted in
theorem hasBQLevi_of_model_pomegaMinus {Y : Type} [Group Y] {n f : ℕ}
    (h : StatedClassicalModel Y .POmegaMinus n 2 f) : HasBQLevi Y := by
  obtain ⟨⟨-, -, hn⟩, F, hF, hFfin, hcard, b, c, hirr, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have : Finite (spinGroup (quadMinus n F b c)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)
  exact ⟨_, inferInstance, inferInstance, _, _, _, _, _, borelQuotient_spinMinus hirr (by omega) e,
    fun i => nodeLevi_spinMinus hirr i⟩

theorem hasBQLevi_of_model_psu {Y : Type} [Group Y] {n f : ℕ}
    (h : StatedClassicalModel Y .PSU n 2 f) : HasBQLevi Y := by
  obtain ⟨⟨-, -, hn, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
  obtain ⟨ζ, hζ⟩ := CFSG.LieType.Universal.Unitary.exists_traceZero_ne_zero hcard
  exact ⟨_, inferInstance, inferInstance, _, _, _, _, _, borelQuotient_su hcard (by omega) ζ hζ e,
    fun i => nodeLevi_su hcard i⟩

end Models

theorem hasBQLevi_g2 {K : Type} [Field K] [Finite K] [CharP K 2] {Y : Type} [Group Y]
    (e : Y ≃* CFSG.Blueprint.AdjointQuotient .G2 K) : HasBQLevi Y :=
  ⟨_, inferInstance, inferInstance, _, _, _, _, _, borelQuotient_g2 e, fun i => nodeLevi_g2 i⟩

theorem hasBQLevi_psl {Y : Type} [Group Y] {m : ℕ} {F : Type} [Field F] [Finite F]
    [CharP F 2] (e : Matrix.ProjectiveSpecialLinearGroup (Fin (m + 1)) F ≃* Y) :
    HasBQLevi Y :=
  ⟨_, inferInstance, inferInstance, _, _, _, _, _, borelQuotient_sl e, fun i => nodeLevi_sl i⟩

theorem hasBQLevi_alt_five {Y : Type} [Group Y]
    (e : Y ≃* alternatingGroup (Fin 5)) : HasBQLevi Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : NeZero 2 := ⟨by norm_num⟩
  have hK : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five
    (GaloisField 2 2) (Or.inl hK)
  exact hasBQLevi_psl (m := 1) (F := GaloisField 2 2)
    (((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2
      (GaloisField 2 2)).trans e5).trans e.symm)

theorem hasBQLevi_alt_eight {Y : Type} [Group Y]
    (e : Y ≃* alternatingGroup (Fin 8)) : HasBQLevi Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : NeZero 1 := ⟨by norm_num⟩
  obtain ⟨e8⟩ := (CFSG.ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff
    (Matrix.ProjectiveSpecialLinearGroup (Fin 4) (GaloisField 2 1))).1
    CFSG.LieType.Steinberg.CentralExt.SLClosed.psl_four_two_lieModel
  exact hasBQLevi_psl (m := 3) (F := GaloisField 2 1) (e8.trans e.symm)

theorem hasBQLevi_model_seven {Y : Type} [Group Y]
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel Y .PSL 2 7 1) : HasBQLevi Y := by
  obtain ⟨e7⟩ := CFSG.QuasithinUnique.Bridge.Over.nonempty_equiv_sl_three_two_of_model_seven h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact hasBQLevi_psl (m := 2) (F := ZMod 2)
    (((QuotientGroup.quotientMulEquivOfEq
      CFSG.LocalAnalysis.ComponentInitial.center_SL_three_zmod_two_eq_bot).trans
        QuotientGroup.quotientBot).trans e7.symm)

theorem hasBQLevi_lieIndex {Y : Type} [Group Y] (d : TauCeti.ValidLieTypeIndex)
    (hd : CFSG.AGLEmbedding.IsClassicalOrG2Index d.1)
    (e : Y ≃* (TauCeti.CFSGIndex.lie d).Group) : HasBQLevi Y := by
  obtain ⟨d, hv⟩ := d
  cases d with
  | A r q =>
    have : Fact q.p.Prime := ⟨q.prime_p⟩
    have : CharP (GaloisField q.p q.exponent) 2 := CharP.congr q.p hd
    exact hasBQLevi_psl ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv).symm.trans
        e.symm)
  | twistedA r q =>
    have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
    change q.p = 2 at hd
    rw [hd] at h
    exact hasBQLevi_of_model_psu h
  | B r q =>
    change q.p = 2 at hd
    have hr := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1)
    by_cases h2 : r = 2
    · subst h2
      have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
      rw [hd] at h
      exact hasBQLevi_of_model_psp h
    · have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hd
        (by omega) e
      rw [hd] at h
      exact hasBQLevi_of_model_psp h
  | C r q => exact hd.elim
  | D r q =>
    change q.p = 2 at hd
    have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even r q hv hd e
    rw [hd] at h
    exact hasBQLevi_of_model_pomegaPlus h
  | twistedD r q =>
    change q.p = 2 at hd
    have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even r q hv hd e
    rw [hd] at h
    exact hasBQLevi_of_model_pomegaMinus h
  | G2 q =>
    change q.p = 2 at hd
    have : Fact q.p.Prime := ⟨q.prime_p⟩
    have : CharP (GaloisField q.p q.exponent) 2 := CharP.congr q.p hd
    have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
      rw [TauCeti.PrimePower.card_def, GaloisField.card q.p q.exponent q.exponent_pos.ne']
    obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hd
      (GaloisField q.p q.exponent) hK
    exact hasBQLevi_g2 (e.trans b.symm)
  | _ => exact hd.elim


theorem hasBQLevi_or_residual {Y : Type} [Group Y] (h : IsChevTwo Y) :
    HasBQLevi Y ∨ MinParResidual Y := by
  rcases h with ⟨d, hd, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨d, hdq, ⟨e⟩⟩
  · obtain ⟨i, hv⟩ := d
    cases i with
    | A r q => exact Or.inl (hasBQLevi_lieIndex ⟨_, hv⟩ hd e)
    | twistedA r q =>
      exact Or.inl (hasBQLevi_lieIndex ⟨_, hv⟩ hd e)
    | B r q => exact Or.inl (hasBQLevi_lieIndex ⟨_, hv⟩ hd e)
    | C r q =>
      exfalso
      have h := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
      rw [TauCeti.LieTypeIndex.inStandardRange_iff] at h
      exact h.2 hd
    | D r q => exact Or.inl (hasBQLevi_lieIndex ⟨_, hv⟩ hd e)
    | twistedD r q =>
      exact Or.inl (hasBQLevi_lieIndex ⟨_, hv⟩ hd e)
    | G2 q => exact Or.inl (hasBQLevi_lieIndex ⟨_, hv⟩ hd e)
    | E6 q =>
      have hq : q.p = 2 := hd
      obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.chevalleyBridgesEven.e6 q hv hq e
      have : CharP K 2 := hq ▸ CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        q.prime_p q.exponent_pos hK
      haveI : Finite ↥(e6Data_valid.minGroup K) := finite_minGroup e6Data_valid K
      exact Or.inl ⟨_, inferInstance, inferInstance, _, _, _, _, _,
        Exceptional.borelQuotient_e6 φ, fun i => nodeLevi_e6 i⟩
    | E7 q =>
      have hq : q.p = 2 := hd
      obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.chevalleyBridgesEven.e7 q hv hq e
      have : CharP K 2 := hq ▸ CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        q.prime_p q.exponent_pos hK
      haveI : Finite ↥(e7Data_valid.minGroup K) := finite_minGroup e7Data_valid K
      exact Or.inl ⟨_, inferInstance, inferInstance, _, _, _, _, _,
        Exceptional.borelQuotient_e7 φ, fun i => nodeLevi_e7 i⟩
    | E8 q =>
      have hq : q.p = 2 := hd
      obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.chevalleyBridgesEven.e8 q hv hq e
      have : CharP K 2 := hq ▸ CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        q.prime_p q.exponent_pos hK
      haveI : Finite ↥(adjointGroup .E8 K) := generated_group_finite .E8 K
      exact Or.inl ⟨_, inferInstance, inferInstance, _, _, _, _, _,
        Exceptional.borelQuotient_e8 φ, fun i => nodeLevi_e8 i⟩
    | F4 q =>
      have hq : q.p = 2 := hd
      obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.chevalleyBridgesEven.f4 q hv hq e
      have : CharP K 2 := hq ▸ CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        q.prime_p q.exponent_pos hK
      haveI : Finite ↥(adjointGroup .F4 K) := generated_group_finite .F4 K
      exact Or.inl ⟨_, inferInstance, inferInstance, _, _, _, _, _,
        Exceptional.borelQuotient_f4 φ, fun i => nodeLevi_f4 i⟩
    | twistedE6 q =>
      have hq : q.p = 2 := hd
      obtain ⟨K, _, _, hK, σ, hσ, ⟨φ⟩⟩ := CFSG.TauCetiBridge.Even.twistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.chevalleyBridgesEven.twistedE6 q hv hq (by decide) e
      have hK' : Nat.card K = (q.p ^ q.exponent) ^ 2 := hK
      have : CharP K 2 := by
        have h := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
          q.prime_p (show 1 ≤ q.exponent * 2 by have := q.exponent_pos; omega)
          (show Nat.card K = q.p ^ (q.exponent * 2) by rw [hK', pow_mul])
        rwa [hq] at h
      have h2le : 2 ≤ q.p ^ q.exponent := by
        rw [hq]
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) q.exponent_pos
      have hθ := Exceptional.involutive_of_card hK' hσ
      haveI : Finite ↥(e6Data_valid.minGroup K) := finite_minGroup e6Data_valid K
      haveI : Finite ↥(CFSG.LieType.Steinberg.TwistedE6.fixedGroup K σ) := Subtype.finite
      have hK4 : 4 ≤ Nat.card K := by
        rw [hK']
        calc 4 ≤ 2 ^ 2 := by norm_num
          _ ≤ (q.p ^ q.exponent) ^ 2 := Nat.pow_le_pow_left h2le 2
      exact Or.inl ⟨_, inferInstance, inferInstance, _, _, _, _, _,
        Exceptional.borelQuotient_e6tw hθ hK4 hK' hσ φ, fun i => nodeLevi_e6tw hθ i⟩
    | trialityD4 q =>
      have hq : q.p = 2 := hd
      obtain ⟨K, _, _, hK, σ, hσ, ⟨φ⟩⟩ := CFSG.TauCetiBridge.Even.twistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.chevalleyBridgesEven.trialityD4 q hv hq (by decide) e
      have hK' : Nat.card K = (q.p ^ q.exponent) ^ 3 := hK
      have : CharP K 2 := by
        have h := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
          q.prime_p (show 1 ≤ q.exponent * 3 by have := q.exponent_pos; omega)
          (show Nat.card K = q.p ^ (q.exponent * 3) by rw [hK', pow_mul])
        rwa [hq] at h
      have h2le : 2 ≤ q.p ^ q.exponent := by
        rw [hq]
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) q.exponent_pos
      haveI : Finite ↥(adjointGroup d4 K) := generated_group_finite d4 K
      haveI : Finite ↥(twistedGroup σ) := Subtype.finite
      have hσ3 : ∀ c, σ (σ (σ c)) = c :=
        CFSG.LieType.Steinberg.TwistedD4.sigma_three_of_card hK' hσ
      exact Or.inl ⟨_, inferInstance, inferInstance, _, _, _, _, _,
        Exceptional.borelQuotient_d4tw h2le hK' hσ φ, fun i => nodeLevi_d4tw hσ3 i⟩
    | suzuki m => exact Or.inr (Or.inr (Or.inr ⟨⟨_, hv⟩, Or.inl ⟨m, rfl⟩, ⟨e⟩⟩))
    | reeG2 m => exact absurd hd (by simp [IsChevIndexTwo])
    | reeF4 m => exact Or.inr (Or.inr (Or.inr ⟨⟨_, hv⟩, Or.inr (Or.inl ⟨m, rfl⟩), ⟨e⟩⟩))
    | tits => exact Or.inr (Or.inr (Or.inr ⟨⟨_, hv⟩, Or.inr (Or.inr rfl), ⟨e⟩⟩))
  · rcases hn with rfl | rfl | rfl
    · exact Or.inl (hasBQLevi_alt_five e)
    · exact Or.inr (Or.inl ⟨e⟩)
    · exact Or.inl (hasBQLevi_alt_eight e)
  · rcases hdq with ⟨q, hq, hdq⟩ | ⟨q, hq, hdq⟩
    · obtain ⟨dd, hv⟩ := d
      simp only at hdq
      subst hdq
      obtain ⟨hp, hf⟩ := CFSG.AGLEmbedding.ParabHub.primePower_eq_of_card_eq Nat.prime_seven hq
      have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
      rw [hp, hf] at h
      exact Or.inl (hasBQLevi_model_seven h)
    · exact Or.inr (Or.inr (Or.inl ⟨d, ⟨q, hq, hdq⟩, ⟨e⟩⟩))


theorem kFactChevMinParabolicLevi_of_residual (hres : ResidualLeviCase) :
    KFactChevMinParabolicLevi :=
  kFactChevMinParabolicLevi_of_families (fun _ _ _ h => hasBQLevi_or_residual h) hres

end CFSG.AGLEmbeddingD2.Tits.GN516
