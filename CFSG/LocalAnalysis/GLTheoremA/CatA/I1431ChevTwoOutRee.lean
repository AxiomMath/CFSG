module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoOutBase
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.ReeF4
public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.FamSz
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Split

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I1431C2

open CFSG CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Lang.Coordinator CFSG.Sporadic.Schreier.Tits
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.ComponentClassification.CatLeaf
open CFSG.HardMathSupport.Dickson.Sec6.I923
open CFSG.HardMathSupport.Dickson.Sec6 (FamReeF4 FamSz FamTits)

open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_model_field_outer_group_and_inner_involutions
    large_Ree_full_inner_field_automorphism_normal_form)

section Family


theorem not_catalogIs_u4two_titsD : ¬ catalogIs titsD S9.isU4two := fun h => by
  have h1 := CFSG.LocalAnalysis.GLTheoremA.I1431Z.card_eq_of_u4two h
  rw [card_titsD] at h1
  exact absurd h1 (by norm_num)

theorem reeGamma_F4_simple_model {b : ℕ} (hb : 1 ≤ b) (k : Type) [Field k] [Finite k]
    [CharP k ReeTag.F4.prime] (hk : Nat.card k = 2 ^ (2 * b + 1)) :
    IsSimpleGroup ↥(ReeTag.F4.reeGamma k b) ∧
      (∃ x y : ↥(ReeTag.F4.reeGamma k b), x * y ≠ y * x) ∧
      LieModel ↥(ReeTag.F4.reeGamma k b) .twistedF4 0 2 (2 * b + 1) := by
  have hrel : ReeTitsModel ↥(ReeTag.F4.reeGamma k b) .twistedF4 2 (2 * b + 1) :=
    ⟨⟨Nat.prime_two, by omega, rfl, rfl, ⟨b, rfl⟩, by omega⟩, b, rfl,
      (reeTitsRelationModel_iff ReeTag.F4 _ (2 * b + 1) b).2
        ⟨k, inferInstance, inferInstance, inferInstance, hk,
          ⟨(CFSG.RankThree.PartTwo.Census.Carrier.ReeF4.nonempty_derivedCentralQuotient_equiv
            hb hk).some.symm⟩⟩⟩
  obtain ⟨-, hsimp⟩ := CFSG.LieType.Simplicity.fam_2f4_simplicity (h := hrel)
  have hZ : Subgroup.center ↥(ReeTag.F4.reeGamma k b) = ⊥ :=
    ReeTag.large_Ree_fixed_group_center_trivial b k hk
  haveI : Nontrivial ↥(ReeTag.F4.reeGamma k b) := hsimp.toNontrivial
  exact ⟨hsimp, exists_noncomm_of_center_bot hZ,
    Or.inr (Or.inr (Or.inl ⟨rfl, by decide, hrel⟩))⟩

theorem nonempty_fixSubgroup_reeGammaFieldAut_equiv {a b : ℕ} {F : Type} [Field F] [Finite F]
    [CharP F ReeTag.F4.prime] (σ : F ≃+* F) [CharP ↥(fixSubfield σ) ReeTag.F4.prime]
    (hfix : ((ReeTag.F4.reeGammaFieldAut F a σ).toMonoidHom.eqLocus (MonoidHom.id _)).map
          (ReeTag.F4.reeGamma F a).subtype =
        (ReeTag.F4.reeGamma (fixSubfield σ) b).map (baseChangeGL (fixSubfield σ).subtype)) :
    Nonempty (↥(fixSubgroup (ReeTag.F4.reeGammaFieldAut F a σ)) ≃*
      ↥(ReeTag.F4.reeGamma (fixSubfield σ) b)) := by
  have hCfix : fixSubgroup (ReeTag.F4.reeGammaFieldAut F a σ) =
      (ReeTag.F4.reeGammaFieldAut F a σ).toMonoidHom.eqLocus (MonoidHom.id _) :=
    Subgroup.ext fun _ => Iff.rfl
  exact ⟨(MulEquiv.subgroupCongr hCfix).trans
    (((Subgroup.equivMapOfInjective _ (ReeTag.F4.reeGamma F a).subtype
      (Subgroup.subtype_injective _)).trans (MulEquiv.subgroupCongr hfix)).trans
      ((ReeTag.F4.reeGamma (fixSubfield σ) b).equivMapOfInjective _
        (baseChangeGL_injective (τ := ReeTag.F4.tag) (fixSubfield σ).subtype)).symm)⟩

theorem u42Layer_reeGammaFieldAut_F4 {a b : ℕ} (F : Type) [Field F] [Finite F]
    [CharP F ReeTag.F4.prime] (σ : F ≃+* F)
    (hk : Nat.card ↥(fixSubfield σ) = 2 ^ (2 * b + 1))
    (hfix : ((ReeTag.F4.reeGammaFieldAut F a σ).toMonoidHom.eqLocus (MonoidHom.id _)).map
          (ReeTag.F4.reeGamma F a).subtype =
        (ReeTag.F4.reeGamma (fixSubfield σ) b).map (baseChangeGL (fixSubfield σ).subtype)) :
    U42Layer (ReeTag.F4.reeGammaFieldAut F a σ) False := by
  haveI : Finite ↥(fixSubfield σ) := Subtype.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP ↥(fixSubfield σ) ReeTag.F4.prime :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hk
  obtain ⟨eC⟩ := nonempty_fixSubgroup_reeGammaFieldAut_equiv σ hfix
  by_cases hb : b = 0
  · subst hb
    have hk2 : Nat.card ↥(fixSubfield σ) = 2 := by simpa using hk
    obtain ⟨c⟩ := nonempty_commutator_reeGamma_tits hk2
    obtain ⟨cc⟩ := nonempty_commutator_mulEquiv eC
    haveI : Nontrivial titsD := titsD_simple.toNontrivial
    exact u42Layer_of_fixed_commutator_equiv _ (cc.trans c) titsD_simple
      (exists_noncomm_of_center_bot titsD_center) not_catalogIs_u4two_titsD
  · obtain ⟨hsimp, hnab, hX⟩ :=
      reeGamma_F4_simple_model (Nat.one_le_iff_ne_zero.2 hb) (fixSubfield σ) hk
    exact u42Layer_of_fixed_equiv _ eC hsimp hnab fun h =>
      absurd (eq_of_catalogIs_u4two_lieModel h hX).1 (by decide)

theorem exists_conj_mul_reeGammaFieldAut_of_not_inner {a : ℕ} (ha : 1 ≤ a) (F : Type) [Field F]
    [Finite F] [CharP F ReeTag.F4.prime] (hK : Nat.card F = 2 ^ (2 * a + 1))
    (β' : MulAut ↥(ReeTag.F4.reeGamma F a)) (hβ3 : β' ^ 3 = 1)
    (hβinn : β' ∉ inner ↥(ReeTag.F4.reeGamma F a)) :
    ∃ (x : ↥(ReeTag.F4.reeGamma F a)) (β : F ≃+* F), orderOf β = 3 ∧
      β' = MulAut.conj x * ReeTag.F4.reeGammaFieldAut F a β := by
  obtain ⟨-, hNF, ⟨Ψ, hΨ⟩, -⟩ := large_Ree_full_inner_field_automorphism_normal_form a ha F hK
  obtain ⟨⟨x, β⟩, hxβ, -⟩ := hNF β'
  have hΨα : Ψ ⟨x, β⟩ = β' := by rw [hΨ x β]; exact hxβ.symm
  let Θ : MulAut ↥(ReeTag.F4.reeGamma F a) →* (F ≃+* F) :=
    SemidirectProduct.rightHom.comp Ψ.symm.toMonoidHom
  have hΘα : Θ β' = β := by
    show SemidirectProduct.rightHom (Ψ.symm β') = β
    rw [← hΨα, MulEquiv.symm_apply_apply]
    rfl
  have hβp : β ^ 3 = 1 := by rw [← hΘα, ← map_pow, hβ3, map_one]
  have hone : ReeTag.F4.reeGammaFieldAut F a 1 = 1 := by
    rw [← ReeTag.reeGammaFieldAutHom_apply, map_one]
  have hβ1 : β ≠ 1 := by
    intro h
    apply hβinn
    rw [h, hone, mul_one] at hxβ
    exact ⟨x, hxβ.symm⟩
  exact ⟨x, β, orderOf_eq_prime hβp hβ1, hxβ⟩

theorem u42Layer_reeGamma_F4 {a : ℕ} (ha : 1 ≤ a) (F : Type) [Field F] [Finite F]
    [CharP F ReeTag.F4.prime] (hK : Nat.card F = 2 ^ (2 * a + 1))
    (β' : MulAut ↥(ReeTag.F4.reeGamma F a)) (hβ3 : β' ^ 3 = 1)
    (hβinn : β' ∉ inner ↥(ReeTag.F4.reeGamma F a)) : U42Layer β' False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, β, hβord, hxβ⟩ := exists_conj_mul_reeGammaFieldAut_of_not_inner ha F hK β' hβ3 hβinn
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartOne.RF4.largeRee_fieldAut_coset_conj a hK Nat.prime_three
    β hβord β' hβ3 ⟨x, hxβ⟩
  obtain ⟨b, hbp, hbcard, hfix⟩ :=
    largeRee_fixed_data_of_odd hK Nat.prime_three (by norm_num) β hβord
  refine u42Layer_of_conj_pow (r := 1) (j := 1) (δ := (MulAut.conj g)⁻¹) (by simp) ?_
    (u42Layer_reeGammaFieldAut_F4 F β hbcard hfix)
  rw [pow_one, hg]
  group

theorem reeTitsModel_of_lieModel_twistedF4 {S : Type} [Group S] {f : ℕ}
    (hm : LieModel S .twistedF4 0 2 f) : ReeTitsModel S .twistedF4 2 f := by
  rcases hm with ⟨ht', -⟩ | ⟨-, ht', -⟩ | ⟨-, -, h⟩ | ⟨-, ht', -⟩
  · exact absurd ht' (by decide)
  · exact absurd ht' (by decide)
  · exact h
  · exact absurd ht' (by decide)

theorem exists_equiv_reeGamma_F4 {S : Type} [Group S] [Finite S] {m : ℕ}
    (hR : ReeTitsModel S .twistedF4 2 (2 * m + 1)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F ReeTag.F4.prime),
      Nat.card F = 2 ^ (2 * m + 1) ∧ Nonempty (S ≃* ReeTag.F4.reeGamma F m) := by
  obtain ⟨-, -, -, -, -, -, hmain⟩ :=
    large_Ree_model_field_outer_group_and_inner_involutions S 2 (2 * m + 1) hR
  obtain ⟨-, a, hfa, F, _, _, hFcard, he⟩ := hR
  have ha : a = m := by omega
  subst ha
  have : CharP F ReeTag.F4.prime := by
    have : Fintype F := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (p := 2) (f := 2 * a + 1) (by
      rw [← Nat.card_eq_fintype_card, hFcard])
  obtain ⟨⟨e1⟩, -⟩ := hmain a F hfa hFcard he
  exact ⟨F, inferInstance, inferInstance, this, hFcard, ⟨e1⟩⟩

theorem u42Out_reeF4 : U42OuterAt FamReeF4 := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ α hα hp
  cases d with
  | reeF4 m =>
    exfalso
    have hR := reeTitsModel_of_lieModel_twistedF4
      (CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_reeF4 m hv e)
    have hm1 : 1 ≤ m := by
      have h := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
      simpa only [TauCeti.LieTypeIndex.inStandardRange_iff] using h
    obtain ⟨F, _, _, _, hFcard, ⟨e'⟩⟩ := exists_equiv_reeGamma_F4 hR
    haveI : Finite ↥(ReeTag.F4.reeGamma F m) := Finite.of_equiv S e'.toEquiv
    have hβ3 : MulAut.congr e' α ^ 3 = 1 := by rw [← map_pow, hp.1, map_one]
    have hβinn : MulAut.congr e' α ∉ inner ↥(ReeTag.F4.reeGamma F m) := fun hin =>
      not_mem_range_conj_of_not_mem_innAutDerived hα
        ((congr_mem_inner_iff_of_equiv e' α).mp hin)
    exact hp.apply (u42Layer_congr e' (u42Layer_reeGamma_F4 hm1 F hFcard _ hβ3 hβinn))
  | _ => exact hF.elim

theorem not_three_dvd_card_of_lieModel_suzuki {S : Type} [Group S] [Finite S] {m : ℕ}
    (hm1 : 1 ≤ m) (hm : LieModel S .twistedB2 0 2 (2 * m + 1)) : ¬ 3 ∣ Nat.card S := by
  have hadm : StatedLieAdmissible .twistedB2 0 2 (2 * m + 1) :=
    ⟨Nat.prime_two, by omega, rfl, rfl, odd_two_mul_add_one m, by omega⟩
  obtain ⟨-, hord, -⟩ := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput S
    .twistedB2 0 2 (2 * m + 1) hadm hm
  intro h3
  have h3' : 3 ∣ lieOrderNumerator .twistedB2 0 (2 ^ (2 * m + 1)) := by
    rw [← hord]
    exact Dvd.dvd.mul_right h3 _
  exact not_three_dvd_suzuki_numerator (odd_two_mul_add_one m) h3'

theorem u42Out_sz : U42OuterAt FamSz := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ α hα hp
  cases d with
  | suzuki m =>
    exfalso
    have hm1 : 1 ≤ m := by
      have h := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
      simpa only [TauCeti.LieTypeIndex.inStandardRange_iff] using h
    exact not_three_dvd_card_of_lieModel_suzuki hm1
      (CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_suzuki m hv e)
      ((by norm_num : 3 ∣ 25920).trans hp.card_dvd)
  | _ => exact hF.elim

theorem card_eq_of_lieModel_tits {S : Type} [Group S] (hm : LieModel S .Tits 0 2 1) :
    Nat.card S = 17971200 := by
  have hadm : StatedLieAdmissible .Tits 0 2 1 := ⟨Nat.prime_two, le_rfl, rfl, rfl, rfl⟩
  obtain ⟨-, hord, -⟩ := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput S
    .Tits 0 2 1 hadm hm
  simpa [lieOrderDivisor, lieOrderNumerator] using hord

theorem u42Out_tits : U42OuterAt FamTits := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ α hα hp
  cases d with
  | tits =>
    exfalso
    have h := hp.card_dvd
    rw [card_eq_of_lieModel_tits (CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_tits hv e)]
      at h
    exact absurd h (by norm_num)
  | _ => exact hF.elim

end Family

end CFSG.LocalAnalysis.GLTheoremA.I1431C2

end
