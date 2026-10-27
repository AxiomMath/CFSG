module

public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderSmallRee
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.LieArith
public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.Transport

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Ree CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.HardMathSupport.Lang.Coordinator

section


theorem not_dvd_reeG2_three (r m : ℕ) (hr : 10 ≤ r) (hm : m + r = r ^ 3) : ¬ m ∣ 2 * 1512 := by
  intro hdvd
  have hle : m ≤ 2 * 1512 := Nat.le_of_dvd (by norm_num) hdvd
  have hr15 : r ≤ 14 := by
    by_contra hcon
    have h15 : 15 ≤ r := by omega
    have h1 : 15 * 15 * r ≤ r * r * r := Nat.mul_le_mul (Nat.mul_le_mul h15 h15) le_rfl
    have h2 : r ^ 3 = r * r * r := by ring
    rw [h2] at hm
    generalize r * r * r = u at h1 hm
    omega
  have hm' : m = r ^ 3 - r := by omega
  subst hm'
  interval_cases r <;> simp at hdvd

theorem noL2Layer_reeGammaFieldAut_G2 (hO : ComponentClassification.CatLeaf.LieOrderFormulasInput)
    {a b : ℕ} (hb : 1 ≤ b) (F : Type) [Field F] [Finite F] [CharP F ReeTag.G2.prime]
    (σ : F ≃+* F) (hk : Nat.card ↥(fixSubfield σ) = 3 ^ (2 * b + 1))
    (hfix : ((ReeTag.G2.reeGammaFieldAut F a σ).toMonoidHom.eqLocus (MonoidHom.id _)).map
          (ReeTag.G2.reeGamma F a).subtype =
        (ReeTag.G2.reeGamma (fixSubfield σ) b).map (baseChangeGL (fixSubfield σ).subtype)) :
    NoL2Layer (ReeTag.G2.reeGammaFieldAut F a σ) := by
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
  exact noL2Layer_of_fixed_equiv _ eC hsimp (exists_noncomm_of_center_bot hZ) fun r hr =>
    not_typeL2_of_lieModel hO hX.admissible hX (by decide) (by decide) hZ hr

theorem noL2Layer_reeGamma_G2 (hO : ComponentClassification.CatLeaf.LieOrderFormulasInput)
    {a : ℕ} (ha : 1 ≤ a) (F : Type) [Field F] [Finite F] [CharP F ReeTag.G2.prime]
    (hF : Nat.card F = 3 ^ (2 * a + 1)) (β : MulAut ↥(ReeTag.G2.reeGamma F a)) (hβ3 : β ^ 3 = 1)
    (hβinn : β ∉ inner ↥(ReeTag.G2.reeGamma F a)) : NoL2Layer β := by
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
    have hfixeq : fixSubgroup β = CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup β :=
      Subgroup.ext fun _ => Iff.rfl
    refine noL2Layer_of_card_dvd β (N := 1512) ?_ fun r m hr hm => not_dvd_reeG2_three r m hr hm
    rw [hfixeq]
    exact hdvd.trans (by norm_num)
  · obtain ⟨b, hb⟩ := hdodd
    have hb1 : 1 ≤ b := by omega
    refine noL2Layer_of_conj_pow (r := 1) (j := 1) (by simp) (by simpa using hδ) ?_
    rw [hd'] at hcard hfix
    have hbd : (d - 1) / 2 = b := by omega
    rw [hbd] at hfix
    exact noL2Layer_reeGammaFieldAut_G2 hO hb1 F σ (by rw [hcard, hb]) hfix

theorem noL2OuterAt_reeg2 (hO : ComponentClassification.CatLeaf.LieOrderFormulasInput) :
    NoL2OuterAt FamReeG2 := by
  intro P _ _ t n p f hadm ht hF hm ψ hψ3 hψ
  obtain rfl := hF
  obtain ⟨-, -, -, hp3, -, hf3⟩ := hadm
  subst hp3
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
  exact noL2Layer_congr e (noL2Layer_reeGamma_G2 hO ha F hF' _ hβ3 hβinn)

theorem y923_reeg2_holds :
    Y923_ReeG2 :=
  y923_lieRestAt_of_noL2Outer
    (noL2OuterAt_reeg2 CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput)

end

end CFSG.HardMathSupport.Dickson.Sec6.I923
