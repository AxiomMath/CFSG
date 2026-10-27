module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.OutE6
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6Diag
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderSmallRee

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.HardMathSupport.Lang.E6Descent
  CFSG.HardMathSupport.Lang.Coordinator CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.Chevalley CFSG.LieType.Ree CFSG.HardMathSupport.Dickson.Sec6.I923
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.GLTheoremB

private theorem noL34Layer_of_fixed_card_lt {P : Type} [Group P] [Finite P] (ψ : MulAut P)
    (h : Nat.card ↥(fixSubgroup ψ) < 20160) : NoL34Layer ψ := by
  intro A hA hT
  have hcard : Nat.card (barOf 3 A) = 20160 := card_eq_of_isLThreeFour hT
  have h1 : Nat.card (barOf 3 A) ≤ Nat.card ↥A :=
    Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥A))
  have h2 : Nat.card ↥A ≤ Nat.card ↥(fixSubgroup ψ) := Subgroup.card_le_of_le hA.1
  omega

section G2


theorem noL34OuterAt3_g2 (hO : ComponentClassification.CatLeaf.LieOrderFormulasInput) :
    NoL34OuterAtThree FamG2 := by
  intro P _ _ t n f hadm ht hF hm ψ hψ3 hψ
  obtain rfl := hF
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hf : 1 ≤ f := hadm.2.1
  have hU : UntwistedChevalleyModel P .G2 (3 ^ f) := by
    rcases hm with ⟨ht', -⟩ | ⟨-, -, hE⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
    · exact absurd ht' (by decide)
    · exact hE.2
    · exact absurd ht' (by decide)
    · exact absurd ht' (by decide)
  obtain ⟨F, hFf, hFin, hFcard, ⟨θ⟩⟩ := exists_equiv_adjointGroup_of_untwisted hU
  have hβ3 : MulAut.congr θ ψ ^ 3 = 1 := by rw [← map_pow, hψ3, map_one]
  have hβinn : MulAut.congr θ ψ ∉ inner ↥(adjointGroup Tag.G2 F) := fun hin =>
    hψ ((congr_mem_inner_iff_of_equiv θ ψ).mp hin)
  obtain ⟨d, T, δ, hfd, hTo, hTc, hδ⟩ :=
    G2_descent Nat.prime_three hf hadm.2.2.2 F hFcard _ hβ3 hβinn
  refine noL34Layer_congr θ (noL34Layer_of_conj_pow (r := 1) (j := 1) (by simp)
    (by simpa using hδ) ?_)
  have hd : 1 ≤ d := by omega
  haveI : Finite ↥(fixSubfield T) := Subtype.finite
  have h3 : 3 ≤ 3 ^ d := Nat.le_self_pow (by omega) 3
  have hM : ChevalleyExceptionalModel ↥(adjointGroup Tag.G2 ↥(fixSubfield T)) .G2 3 d :=
    ⟨⟨Nat.prime_three, hd, rfl, h3⟩, untwisted_adjointGroup hTc⟩
  obtain ⟨hnt, hsimp⟩ := CFSG.LieType.Simplicity.fam_g2_simplicity _ 3 d hM
  have hZ : Subgroup.center ↥(adjointGroup Tag.G2 ↥(fixSubfield T)) = ⊥ :=
    center_adjointGroup_eq_bot
  exact noL34Layer_entrywise_of_model hO T (by norm_num)
    (Or.inr (Or.inl ⟨rfl, by decide, hM⟩)) hsimp (exists_noncomm_of_center_bot hZ)

end G2

section F4


theorem noL34OuterAt3_f4 (hO : ComponentClassification.CatLeaf.LieOrderFormulasInput) :
    NoL34OuterAtThree FamF4 := by
  intro P _ _ t n f hadm ht hF hm ψ hψ3 hψ
  obtain rfl := hF
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hf : 1 ≤ f := hadm.2.1
  have hU : UntwistedChevalleyModel P .F4 (3 ^ f) := by
    rcases hm with ⟨ht', -⟩ | ⟨-, -, hE⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
    · exact absurd ht' (by decide)
    · exact hE.2
    · exact absurd ht' (by decide)
    · exact absurd ht' (by decide)
  obtain ⟨F, hFf, hFin, hFcard, ⟨θ⟩⟩ := exists_equiv_adjointGroup_of_untwisted hU
  have hβ3 : MulAut.congr θ ψ ^ 3 = 1 := by rw [← map_pow, hψ3, map_one]
  have hβinn : MulAut.congr θ ψ ∉ inner ↥(adjointGroup Tag.F4 F) := fun hin =>
    hψ ((congr_mem_inner_iff_of_equiv θ ψ).mp hin)
  obtain ⟨d, T, δ, hfd, hTo, hTc, hδ⟩ := F4_descent hf F hFcard _ hβ3 hβinn
  refine noL34Layer_congr θ (noL34Layer_of_conj_pow (r := 1) (j := 1) (by simp)
    (by simpa using hδ) ?_)
  have hd : 1 ≤ d := by omega
  haveI : Finite ↥(fixSubfield T) := Subtype.finite
  have hM : ChevalleyExceptionalModel ↥(adjointGroup Tag.F4 ↥(fixSubfield T)) .F4 3 d :=
    ⟨⟨Nat.prime_three, hd, rfl⟩, untwisted_adjointGroup hTc⟩
  obtain ⟨hnt, hsimp⟩ := CFSG.LieType.Simplicity.fam_f4_simplicity _ 3 d hM
  have hZ : Subgroup.center ↥(adjointGroup Tag.F4 ↥(fixSubfield T)) = ⊥ :=
    center_adjointGroup_eq_bot
  exact noL34Layer_entrywise_of_model hO T (by norm_num)
    (Or.inr (Or.inl ⟨rfl, by decide, hM⟩)) hsimp (exists_noncomm_of_center_bot hZ)

end F4

section E7


theorem noL34OuterAt3_e7 (hO : ComponentClassification.CatLeaf.LieOrderFormulasInput) :
    NoL34OuterAtThree FamE7 := by
  intro P _ _ t n f hadm ht hF hm ψ hψ3 hψ
  obtain rfl := hF
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hf : 1 ≤ f := hadm.2.1
  have hU : UntwistedChevalleyModel P .E7 (3 ^ f) := by
    rcases hm with ⟨ht', -⟩ | ⟨-, -, hE⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
    · exact absurd ht' (by decide)
    · exact hE.2
    · exact absurd ht' (by decide)
    · exact absurd ht' (by decide)
  obtain ⟨F, hFf, hFin, hFcard, ⟨θ⟩⟩ := exists_equiv_adjointGroup_of_untwisted hU
  have hβ3 : MulAut.congr θ ψ ^ 3 = 1 := by rw [← map_pow, hψ3, map_one]
  have hβinn : MulAut.congr θ ψ ∉ inner ↥(adjointGroup Tag.E7 F) := fun hin =>
    hψ ((congr_mem_inner_iff_of_equiv θ ψ).mp hin)
  have hdet : ¬ 3 ∣ Tag.E7.cartan.det.natAbs := by
    rw [det_cartan_E7]
    decide
  obtain ⟨d, T, r, j, δ, hfd, hTo, hTc, hrj, hδ⟩ :=
    exists_conj_entrywise_of_outer_E Tag.E7 (Or.inr (Or.inl rfl)) hf F hFcard Nat.prime_three
      (by norm_num) hdet _ hβ3 hβinn
  refine noL34Layer_congr θ (noL34Layer_of_conj_pow hrj hδ ?_)
  have hd : 1 ≤ d := by omega
  haveI : Finite ↥(fixSubfield T) := Subtype.finite
  have hM : ChevalleyExceptionalModel ↥(adjointGroup Tag.E7 ↥(fixSubfield T)) .E7 3 d :=
    ⟨⟨Nat.prime_three, hd, rfl⟩, untwisted_adjointGroup hTc⟩
  obtain ⟨hnt, hsimp⟩ := CFSG.LieType.Simplicity.fam_e7_simplicity _ 3 d hM
  have hZ : Subgroup.center ↥(adjointGroup Tag.E7 ↥(fixSubfield T)) = ⊥ :=
    center_adjointGroup_eq_bot
  exact noL34Layer_entrywise_of_model hO T (by norm_num)
    (Or.inr (Or.inl ⟨rfl, by decide, hM⟩)) hsimp (exists_noncomm_of_center_bot hZ)

end E7

section E8


theorem noL34OuterAt3_e8 (hO : ComponentClassification.CatLeaf.LieOrderFormulasInput) :
    NoL34OuterAtThree FamE8 := by
  intro P _ _ t n f hadm ht hF hm ψ hψ3 hψ
  obtain rfl := hF
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hf : 1 ≤ f := hadm.2.1
  have hU : UntwistedChevalleyModel P .E8 (3 ^ f) := by
    rcases hm with ⟨ht', -⟩ | ⟨-, -, hE⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
    · exact absurd ht' (by decide)
    · exact hE.2
    · exact absurd ht' (by decide)
    · exact absurd ht' (by decide)
  obtain ⟨F, hFf, hFin, hFcard, ⟨θ⟩⟩ := exists_equiv_adjointGroup_of_untwisted hU
  have hβ3 : MulAut.congr θ ψ ^ 3 = 1 := by rw [← map_pow, hψ3, map_one]
  have hβinn : MulAut.congr θ ψ ∉ inner ↥(adjointGroup Tag.E8 F) := fun hin =>
    hψ ((congr_mem_inner_iff_of_equiv θ ψ).mp hin)
  have hdet : ¬ 3 ∣ Tag.E8.cartan.det.natAbs := by
    rw [det_cartan_E8]
    decide
  obtain ⟨d, T, r, j, δ, hfd, hTo, hTc, hrj, hδ⟩ :=
    exists_conj_entrywise_of_outer_E Tag.E8 (Or.inr (Or.inr rfl)) hf F hFcard Nat.prime_three
      (by norm_num) hdet _ hβ3 hβinn
  refine noL34Layer_congr θ (noL34Layer_of_conj_pow hrj hδ ?_)
  have hd : 1 ≤ d := by omega
  haveI : Finite ↥(fixSubfield T) := Subtype.finite
  have hM : ChevalleyExceptionalModel ↥(adjointGroup Tag.E8 ↥(fixSubfield T)) .E8 3 d :=
    ⟨⟨Nat.prime_three, hd, rfl⟩, untwisted_adjointGroup hTc⟩
  obtain ⟨hnt, hsimp⟩ := CFSG.LieType.Simplicity.fam_e8_simplicity _ 3 d hM
  have hZ : Subgroup.center ↥(adjointGroup Tag.E8 ↥(fixSubfield T)) = ⊥ :=
    center_adjointGroup_eq_bot
  exact noL34Layer_entrywise_of_model hO T (by norm_num)
    (Or.inr (Or.inl ⟨rfl, by decide, hM⟩)) hsimp (exists_noncomm_of_center_bot hZ)

end E8

section E6


theorem noL34OuterAt3_e6 (hO : ComponentClassification.CatLeaf.LieOrderFormulasInput) :
    NoL34OuterAtThree FamE6 := by
  intro P _ _ t n f hadm ht hF hm ψ hψ3 hψ
  obtain rfl := hF
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hf : 1 ≤ f := hadm.2.1
  have hU : UntwistedChevalleyModel P .E6 (3 ^ f) := by
    rcases hm with ⟨ht', -⟩ | ⟨-, -, hE⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
    · exact absurd ht' (by decide)
    · exact hE.2
    · exact absurd ht' (by decide)
    · exact absurd ht' (by decide)
  obtain ⟨F, hFf, hFin, hFcard, ⟨θ⟩⟩ := exists_equiv_adjointGroup_of_untwisted hU
  have hβ3 : MulAut.congr θ ψ ^ 3 = 1 := by rw [← map_pow, hψ3, map_one]
  have hβinn : MulAut.congr θ ψ ∉ inner ↥(adjointGroup Tag.E6 F) := fun hin =>
    hψ ((congr_mem_inner_iff_of_equiv θ ψ).mp hin)
  have hq : ¬ 3 ∣ Nat.card F - 1 := by
    have h3 : 3 ∣ 3 ^ f := dvd_pow_self 3 (by omega)
    have h1 : 1 ≤ 3 ^ f := Nat.one_le_pow _ _ (by norm_num)
    rw [hFcard]
    omega
  obtain ⟨d, T, r, j, δ, hfd, hTo, hTc, -, -, hrj, hδ⟩ :=
    exists_conj_entrywise_of_not_innerDiag .E6 (Or.inl rfl) hf F hFcard Nat.prime_three
      (by norm_num) _ hβ3 fun g a hdiag =>
        hq (prime_dvd_of_diag_noninner .E6 (Or.inl rfl) F Nat.prime_three g a _ hdiag hβ3 hβinn).2
  refine noL34Layer_congr θ (noL34Layer_of_conj_pow hrj hδ ?_)
  exact noL34Layer_entrywise_e6 hO Nat.prime_three (by norm_num) (by omega) T hTc

end E6

section TwE6


theorem noL34OuterAt3_twE6 (hO : ComponentClassification.CatLeaf.LieOrderFormulasInput) :
    NoL34OuterAtThree FamTwE6 := by
  intro P _ _ t n f hadm ht hF hm ψ hψ3 hψ
  obtain rfl := hF
  have hf : 1 ≤ f := hadm.2.1
  have hE : ChevalleyExceptionalModel P .twistedE6 3 f := by
    rcases hm with ⟨ht', -⟩ | ⟨-, -, hE⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
    · exact absurd ht' (by decide)
    · exact hE
    · exact absurd ht' (by decide)
    · exact absurd ht' (by decide)
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_twistedE6RootGroup_equiv Nat.prime_three hf hE.2
  let θ : P ≃* twistedE6RootGroup K σ := e.symm
  have hβ3 : MulAut.congr θ ψ ^ 3 = 1 := by rw [← map_pow, hψ3, map_one]
  have hβinn : MulAut.congr θ ψ ∉ twistedE6Inn K σ := fun hin =>
    hψ ((congr_mem_inner_iff_of_equiv θ ψ).mp hin)
  have hg : Nat.gcd 3 (3 ^ f + 1) = 1 := by
    refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 ?_
    have h3 : 3 ∣ 3 ^ f := dvd_pow_self 3 (by omega)
    omega
  have hΔ : twistedE6Diag K σ ≤ twistedE6Inn K σ := by
    rintro _ ⟨u, rfl⟩
    exact compatDiagAutHom_mem_inner hK hσ hg u
  have hdiag : MulAut.congr θ ψ ∉ twistedE6Inn K σ ⊔ twistedE6Diag K σ := by
    rw [sup_eq_left.2 hΔ]
    exact hβinn
  exact noL34Layer_congr θ
    (noL34Layer_of_not_mem_twistedE6Inndiag hO Nat.prime_three (by norm_num) hf hK σ hσ hβ3
      hdiag)

end TwE6

section ReeG2


theorem noL34Layer_reeGammaFieldAut_G2 (hO : ComponentClassification.CatLeaf.LieOrderFormulasInput)
    {a b : ℕ} (hb : 1 ≤ b) (F : Type) [Field F] [Finite F] [CharP F ReeTag.G2.prime]
    (σ : F ≃+* F) (hk : Nat.card ↥(fixSubfield σ) = 3 ^ (2 * b + 1))
    (hfix : ((ReeTag.G2.reeGammaFieldAut F a σ).toMonoidHom.eqLocus (MonoidHom.id _)).map
          (ReeTag.G2.reeGamma F a).subtype =
        (ReeTag.G2.reeGamma (fixSubfield σ) b).map (baseChangeGL (fixSubfield σ).subtype)) :
    NoL34Layer (ReeTag.G2.reeGammaFieldAut F a σ) := by
  haveI : Finite ↥(fixSubfield σ) := Subtype.finite
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : CharP ↥(fixSubfield σ) ReeTag.G2.prime :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_three
      (by omega) hk
  let C : Subgroup ↥(ReeTag.G2.reeGamma F a) :=
    (ReeTag.G2.reeGammaFieldAut F a σ).toMonoidHom.eqLocus (MonoidHom.id _)
  have hCfix : fixSubgroup (ReeTag.G2.reeGammaFieldAut F a σ) = C :=
    Subgroup.ext fun _ => Iff.rfl
  let eC : ↥(fixSubgroup (ReeTag.G2.reeGammaFieldAut F a σ)) ≃*
      ↥(ReeTag.G2.reeGamma (fixSubfield σ) b) :=
    (MulEquiv.subgroupCongr hCfix).trans
      (((C.equivMapOfInjective (ReeTag.G2.reeGamma F a).subtype
        (Subgroup.subtype_injective _)).trans (MulEquiv.subgroupCongr hfix)).trans
        ((ReeTag.G2.reeGamma (fixSubfield σ) b).equivMapOfInjective _
          (baseChangeGL_injective (τ := ReeTag.G2.tag) (fixSubfield σ).subtype)).symm)
  have hrel : ReeTitsModel ↥(ReeTag.G2.reeGamma (fixSubfield σ) b) .twistedG2 3 (2 * b + 1) :=
    ⟨⟨Nat.prime_three, by omega, rfl, rfl, ⟨b, rfl⟩, by omega⟩, b, rfl,
      (reeTitsRelationModel_iff ReeTag.G2 _ (2 * b + 1) b).2
        ⟨fixSubfield σ, inferInstance, inferInstance, inferInstance, hk,
          ⟨(nonempty_derivedCentralQuotient_reeGamma_G2 hb hk).some.symm⟩⟩⟩
  obtain ⟨-, hsimp⟩ := CFSG.LieType.Simplicity.fam_2g2_simplicity (h := hrel)
  have hZ : Subgroup.center ↥(ReeTag.G2.reeGamma (fixSubfield σ) b) = ⊥ :=
    ReeTag.center_reeGamma_G2_eq_bot hk
  have hX : LieModel ↥(ReeTag.G2.reeGamma (fixSubfield σ) b) .twistedG2 0 3 (2 * b + 1) :=
    Or.inr (Or.inr (Or.inl ⟨rfl, by decide, hrel⟩))
  haveI : Nontrivial ↥(ReeTag.G2.reeGamma (fixSubfield σ) b) := hsimp.toNontrivial
  exact noL34Layer_of_fixed_equiv _ eC hsimp (exists_noncomm_of_center_bot hZ)
    (not_isLThreeFour_of_lieModel_odd hO (by norm_num) hX)

theorem noL34Layer_reeGamma_G2 (hO : ComponentClassification.CatLeaf.LieOrderFormulasInput)
    {a : ℕ} (ha : 1 ≤ a) (F : Type) [Field F] [Finite F] [CharP F ReeTag.G2.prime]
    (hF : Nat.card F = 3 ^ (2 * a + 1)) (β : MulAut ↥(ReeTag.G2.reeGamma F a)) (hβ3 : β ^ 3 = 1)
    (hβinn : β ∉ inner ↥(ReeTag.G2.reeGamma F a)) : NoL34Layer β := by
  obtain ⟨d, hd, hdvd⟩ := small_Ree_outer_fixed_order a ha F hF Nat.prime_three (by norm_num) β
    hβ3 hβinn
  obtain ⟨-, δ, σ, -, hδ, hcard, hfix⟩ :=
    small_Ree_odd_prime_field_descent a ha F hF Nat.prime_three (by norm_num) β hβ3 hβinn
  have hd' : (2 * a + 1) / 3 = d := by rw [hd, Nat.mul_div_cancel_left _ (by norm_num)]
  have hdodd : Odd d := by
    have h1 : Odd (3 * d) := hd ▸ odd_two_mul_add_one a
    exact (Nat.odd_mul.1 h1).2
  by_cases hd1 : d = 1
  · subst hd1
    have hfixeq : fixSubgroup β =
        CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup β :=
      Subgroup.ext fun _ => Iff.rfl
    refine noL34Layer_of_fixed_card_lt β ?_
    rw [hfixeq]
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    norm_num at hle
    omega
  · obtain ⟨b, hb⟩ := hdodd
    have hb1 : 1 ≤ b := by omega
    refine noL34Layer_of_conj_pow (r := 1) (j := 1) (by simp) (by simpa using hδ) ?_
    rw [hd'] at hcard hfix
    have hbd : (d - 1) / 2 = b := by omega
    rw [hbd] at hfix
    exact noL34Layer_reeGammaFieldAut_G2 hO hb1 F σ (by rw [hcard, hb]) hfix

theorem noL34OuterAt3_reeG2 (hO : ComponentClassification.CatLeaf.LieOrderFormulasInput) :
    NoL34OuterAtThree FamReeG2 := by
  intro P _ _ t n f hadm ht hF hm ψ hψ3 hψ
  obtain rfl := hF
  obtain ⟨-, -, -, -, -, hf3⟩ := hadm
  have hR : ReeTitsModel P .twistedG2 3 f := by
    rcases hm with ⟨ht', -⟩ | ⟨-, ht', -⟩ | ⟨-, -, h⟩ | ⟨-, ht', -⟩
    · exact absurd ht' (by decide)
    · exact absurd ht' (by decide)
    · exact h
    · exact absurd ht' (by decide)
  obtain ⟨-, a, hfa, hrel⟩ := hR
  obtain ⟨F, _, _, _, hF, ⟨e₁⟩⟩ := (reeTitsRelationModel_iff ReeTag.G2 P f a).1 hrel
  have ha : 1 ≤ a := by omega
  have hF' : Nat.card F = 3 ^ (2 * a + 1) := hfa ▸ hF
  obtain ⟨e₂⟩ := nonempty_derivedCentralQuotient_reeGamma_G2 (K := F) ha hF'
  let e := e₁.trans e₂
  haveI : Finite ↥(ReeTag.G2.reeGamma F a) := Finite.of_equiv P e.toEquiv
  have hβ3 : MulAut.congr e ψ ^ 3 = 1 := by rw [← map_pow, hψ3, map_one]
  have hβinn : MulAut.congr e ψ ∉ inner ↥(ReeTag.G2.reeGamma F a) := fun hin =>
    hψ ((congr_mem_inner_iff_of_equiv e ψ).mp hin)
  exact noL34Layer_congr e (noL34Layer_reeGamma_G2 hO ha F hF' _ hβ3 hβinn)

end ReeG2

end CFSG.HardMathSupport.Dickson.Sec6
