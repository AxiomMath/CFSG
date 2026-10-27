module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcTwD4Wit
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcTwD4Arith
public import CFSG.RankThree.PartOne.K128.D4Syl
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieCrossTags
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureVacuous
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.FrobeniusOnRoots

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge CFSG.RankThree.PartOne.KGD CFSG.RankThree.Lattice
  CFSG.HardMathSupport.Timmesfeld.LangTorus Polynomial
open scoped Matrix commutatorElement

set_option linter.unusedSectionVars false


theorem tw_not_dvd_six {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : ¬ p ∣ 6 := by
  intro h
  have := Nat.le_of_dvd (by norm_num) h
  interval_cases p <;> first | omega | exact absurd hp (by norm_num)

theorem wcOn_trialityD4_class {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (F : Type) [Field F]
    (hF3 : Nat.card F = (ℓ ^ f) ^ 3) (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {K : Type} [Group K] [Finite K]
    (eK : K ≃* graphFixedRootGroup TwistTag.D4 F σ.toRingHom) {p : ℕ} [hp : Fact p.Prime]
    (hp5 : 5 ≤ p) (hpq : ¬ p ∣ ℓ ^ f)
    (hC : Nat.card (graphFixedRootGroup TwistTag.D4 F σ.toRingHom) = ordTrialityD4 (ℓ ^ f))
    {e : ℕ} (he : orderOf (((ℓ ^ f : ℕ)) : ZMod p) = e) (hE : e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 6) :
    WCOn p K := by
  have hF := frobeniusOnRoots_proved
  have hp2 : p ≠ 2 := by omega
  have hq2 : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
  rcases hE with rfl | rfl | rfl | rfl
  · obtain ⟨L, _, _, Fr, hFr, D, hΦ, hn, hMΓ, ⟨S₀, hS₀⟩, ⟨eΓ⟩⟩ :=
      exists_lang_triD4_data_of_class hF hℓ hf F hF3 σ hσ hp.out hp5 hpq hC he (Or.inl rfl)
        ((coxeterSystem TwistTag.D4.tag).wordProd d4OneWord) d4One_hw (by norm_num) d4One_pow
        (cyclotomic 3 ℤ) d4One_det
        (not_dvd_cyclotomic_eval_of_ne hp.out he (by norm_num) (fun h => by
          have := Nat.le_of_dvd (by norm_num) h
          omega))
    haveI : Finite D.Γ := Finite.of_equiv K (eK.trans eΓ).toEquiv
    exact WCOn.of_mulEquiv (eK.trans eΓ) (WCOn.of_normalizerMovesLines S₀ fun _ _ =>
      d4One_moves D hq2 hFr hΦ hn hMΓ hp2 hp5 he S₀ hS₀)
  · obtain ⟨L, _, _, Fr, hFr, D, hΦ, hn, hMΓ, ⟨S₀, hS₀⟩, ⟨eΓ⟩⟩ :=
      exists_lang_triD4_data_of_class hF hℓ hf F hF3 σ hσ hp.out hp5 hpq hC he (by decide)
        ((coxeterSystem TwistTag.D4.tag).wordProd d4TwoWord) d4Two_hw (by norm_num) d4Two_pow
        (cyclotomic 6 ℤ) d4Two_det
        (not_dvd_cyclotomic_eval_of_ne hp.out he (by norm_num) (tw_not_dvd_six hp.out hp5))
    haveI : Finite D.Γ := Finite.of_equiv K (eK.trans eΓ).toEquiv
    exact WCOn.of_mulEquiv (eK.trans eΓ) (WCOn.of_normalizerMovesLines S₀ fun _ _ =>
      d4Two_moves D hq2 hFr hΦ hn hMΓ hp2 hp5 he S₀ hS₀)
  · obtain ⟨L, _, _, Fr, hFr, D, hΦ, hn, hMΓ, ⟨S₀, hS₀⟩, ⟨eΓ⟩⟩ :=
      exists_lang_triD4_data_of_class hF hℓ hf F hF3 σ hσ hp.out hp5 hpq hC he (by decide)
        ((coxeterSystem TwistTag.D4.tag).wordProd d4ThreeWord) d4Three_hw (by norm_num)
        d4Three_pow (1) d4Three_det (by rw [eval_one]; exact not_dvd_one_int hp.out)
    haveI : Finite D.Γ := Finite.of_equiv K (eK.trans eΓ).toEquiv
    exact WCOn.of_mulEquiv (eK.trans eΓ) (WCOn.of_normalizerMovesLines S₀ fun _ _ =>
      d4Three_moves D hq2 hFr hΦ hn hMΓ hp2 he S₀ hS₀)
  · obtain ⟨L, _, _, Fr, hFr, D, hΦ, hn, hMΓ, ⟨S₀, hS₀⟩, ⟨eΓ⟩⟩ :=
      exists_lang_triD4_data_of_class hF hℓ hf F hF3 σ hσ hp.out hp5 hpq hC he (by decide)
        ((coxeterSystem TwistTag.D4.tag).wordProd d4SixWord) d4Six_hw (by norm_num)
        d4Six_pow (1) d4Six_det (by rw [eval_one]; exact not_dvd_one_int hp.out)
    haveI : Finite D.Γ := Finite.of_equiv K (eK.trans eΓ).toEquiv
    exact WCOn.of_mulEquiv (eK.trans eΓ) (WCOn.of_normalizerMovesLines S₀ fun _ _ =>
      d4Six_moves D hq2 hFr hΦ hn hMΓ hp2 he S₀ hS₀)

theorem wcOn_trialityD4_three {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (F : Type) [Field F]
    (hF3 : Nat.card F = (ℓ ^ f) ^ 3) (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {K : Type} [Group K] [Finite K]
    (eK : K ≃* graphFixedRootGroup TwistTag.D4 F σ.toRingHom) (hℓ3 : ℓ ≠ 3)
    (he : orderOf (((ℓ ^ f : ℕ)) : ZMod 3) = 1 ∨ orderOf (((ℓ ^ f : ℕ)) : ZMod 3) = 2) :
    WCOn 3 K := by
  have hq2 : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
  rcases he with he | he
  · obtain ⟨L, _, _, hLchar, Fr, hFr, D, hΦ, hn, hMΓ, hfin, ⟨eΓ⟩⟩ :=
      exists_lang_triD4_model hℓ hf F hF3 σ hσ
        ((coxeterSystem TwistTag.D4.tag).wordProd d4OneWord)
    haveI := hfin
    haveI : Finite D.Γ := Finite.of_equiv K (eK.trans eΓ).toEquiv
    haveI : NeZero ((3 : ℕ) : L) := ⟨by
      intro h
      have := (CharP.cast_eq_zero_iff L ℓ 3).1 h
      exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 this)⟩
    obtain ⟨ζ0, hζ0⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L 3
    have hζu := hζ0.isUnit_unit (by norm_num)
    obtain ⟨Q, x, y, hQ, hxQ, hyQ, hxM, hyM, hxy⟩ :=
      d4One_witness D hq2 hFr hΦ hn (ζ := (hζ0.isUnit (by norm_num)).unit) hζu.pow_eq_one
        hζu.eq_orderOf.symm (tw_dvd_sub_of_orderOf_one Nat.prime_three he)
    exact WCOn.of_mulEquiv (eK.trans eΓ) (tw_wcOn_of_noncomm hQ hxQ hyQ (hMΓ hxM) (hMΓ hyM) hxy)
  · obtain ⟨L, _, _, hLchar, Fr, hFr, D, hΦ, hn, hMΓ, hfin, ⟨eΓ⟩⟩ :=
      exists_lang_triD4_model hℓ hf F hF3 σ hσ
        ((coxeterSystem TwistTag.D4.tag).wordProd d4TwoWord)
    haveI := hfin
    haveI : Finite D.Γ := Finite.of_equiv K (eK.trans eΓ).toEquiv
    haveI : NeZero ((3 : ℕ) : L) := ⟨by
      intro h
      have := (CharP.cast_eq_zero_iff L ℓ 3).1 h
      exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 this)⟩
    obtain ⟨ζ0, hζ0⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L 3
    have hζu := hζ0.isUnit_unit (by norm_num)
    obtain ⟨Q, x, y, hQ, hxQ, hyQ, hxM, hyM, hxy⟩ :=
      d4Two_witness D hq2 hFr hΦ hn (ζ := (hζ0.isUnit (by norm_num)).unit) hζu.pow_eq_one
        hζu.eq_orderOf.symm (tw_dvd_add_of_orderOf_two Nat.prime_three (by norm_num) he)
    exact WCOn.of_mulEquiv (eK.trans eΓ) (tw_wcOn_of_noncomm hQ hxQ hyQ (hMΓ hxM) (hMΓ hyM) hxy)

theorem crossChevalley_trialityD4 : CrossChevalley .trialityD4 := by
  intro K _ _ ℓ f p hp hadm hp2 hpℓ hmodel
  obtain ⟨hℓ, hf, -⟩ := hadm
  have hpq : ¬ p ∣ ℓ ^ f := fun h =>
    hpℓ ((Nat.prime_dvd_prime_iff_eq hp.out hℓ).1 (hp.out.dvd_of_dvd_pow h))
  have hcardK : Nat.card K = ordTrialityD4 (ℓ ^ f) := by
    by_cases h2 : ℓ = 2
    · subst h2
      exact CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hmodel
    · exact CFSG.ClassicalInvolution.card_chevalleyExceptionalModel_of_ne_two h2 hmodel
  obtain ⟨F, _, hFfin, hFcard, σ0, hσ0, ⟨e1⟩⟩ := hmodel.2
  have hF3 : Nat.card F = (ℓ ^ f) ^ 3 := hFcard
  obtain ⟨e2⟩ := CFSG.RankThree.Chevalley.nonempty_derivedCentralQuotient_equiv TwistTag.D4 hℓ hf F
    hFcard σ0 hσ0
  obtain ⟨σ, hσE⟩ : ∃ σ : F ≃+* F, σ.toRingHom = σ0 :=
    ⟨RingEquiv.ofBijective σ0 ⟨σ0.injective, Finite.surjective_of_injective σ0.injective⟩, rfl⟩
  subst hσE
  have hσ : ∀ c, σ c = c ^ (ℓ ^ f) := hσ0
  have eK : K ≃* graphFixedRootGroup TwistTag.D4 F σ.toRingHom := e1.trans e2
  have hC : Nat.card (graphFixedRootGroup TwistTag.D4 F σ.toRingHom) = ordTrialityD4 (ℓ ^ f) :=
    (Nat.card_congr eK.toEquiv).symm.trans hcardK
  have hq0 : (((ℓ ^ f : ℕ)) : ZMod p) ≠ 0 := fun h =>
    hpq ((ZMod.natCast_eq_zero_iff _ p).1 h)
  by_cases hdvd : p ∣ ordTrialityD4 (ℓ ^ f)
  · rcases tw_d4_eclass hp.out hpq hdvd with hE | ⟨h12, hpd⟩
    · by_cases hp3 : p = 3
      · subst hp3
        have hdv : orderOf (((ℓ ^ f : ℕ)) : ZMod 3) ∣ 3 - 1 := ZMod.orderOf_dvd_card_sub_one hq0
        refine wcOn_trialityD4_three hℓ hf F hF3 σ hσ eK (fun h => hpℓ h.symm) ?_
        rcases hE with h | h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · rw [h] at hdv; omega
        · rw [h] at hdv; omega
      · have hp5 : 5 ≤ p := by
          have := hp.out.two_le
          have h4 : p ≠ 4 := fun h => by rw [h] at hp; exact absurd hp.out (by norm_num)
          omega
        exact wcOn_trialityD4_class hℓ hf F hF3 σ hσ eK hp5 hpq hC rfl hE
    · have hdv : 12 ∣ p - 1 := h12 ▸ ZMod.orderOf_dvd_card_sub_one hq0
      have hp5 : 5 ≤ p := by
        have := hp.out.two_le
        omega
      haveI : Finite (graphFixedRootGroup TwistTag.D4 F σ.toRingHom) :=
        Finite.of_equiv K eK.toEquiv
      exact WCOn.of_mulEquiv eK (WCOn.of_pRank_top_le_one (by
        rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
        exact CFSG.RankThree.PartOne.K128.pRank_le_one_D4_twelve hℓ hf F hF3 σ hσ hp.out hp5 hpd))
  · refine WCOn.of_factorization_le_one ?_
    rw [hcardK, Nat.factorization_eq_zero_of_not_dvd hdvd]
    exact Nat.zero_le _

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross
