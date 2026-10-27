module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusUniqueBounds
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIOrthogonal
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open CFSG Subgroup QuadraticMap Matrix Module CFSG.ClassicalGroups.Orthogonal
open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.OmegaRadical
open CFSG.RankThree.PartOne.KCOrthogonalSubfield
open CFSG.LieType.Universal.Spin (quadMinus quadMinus_apply)
open CFSG.GroupTheory.WeirSylow (binForm binForm_isometry quadMinusIsometry)
open CFSG.SeitzReduction.TwistedE6Pilot (coordinateQuadMinus_fieldMap_of_fixed
  exists_mulEquiv_conj_fieldAutT_of_minus fieldAutT_congr_right)
open CFSG.Open (ordD ordTwistedD)
open CFSG.Quasithin (perfectCore perfectCore_le)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.UnbalancingLocal.EvenOrthogonalComponents
  (conj_injective_matrixProjectiveDerived)

section Cases

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

theorem involution_cases_omegaPlus_minusForm_of_mem_image (hn : 4 ≤ n) {σ : F ≃+* F}
    (hσ : orderOf σ = 2) {b c : F} (hb : σ b = b) (hc : σ c = c)
    (hirr : ∀ s : F, σ s = s → s ^ 2 + b * s + c ≠ 0)
    {β : MulAut (matrixProjectiveDerived (coordinateQuadPlus n F))} (hβ : β * β = 1)
    (hβim : β ∈ matrixProjectiveImage (coordinateQuadPlus n F)) :
    (∃ s : matrixIsometries (coordinateQuadPlus n F), s * s = 1 ∧
      matrixProjectiveConjugationHom _ (matrixIsometryInclusion _ s) = β) ∨
    (∃ g : ℕ, 1 ≤ g ∧ Nat.card F = 2 ^ (2 * g) ∧
      ordD n (2 ^ g) ∣ Nat.card (fixedSubgroup β)) ∨
    (∃ Θ : matrixProjectiveDerived (coordinateQuadPlus n F) ≃*
        matrixProjectiveDerived (coordinateQuadMinus n F (by omega) b c),
      MulAut.congr Θ β = fieldAutT (coordinateQuadMinus n F (by omega) b c) σ
        (coordinateQuadMinus_fieldMap_of_fixed (by omega) hb hc)) := by
  obtain ⟨f, hf, hK⟩ := F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := F)
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus n F (by omega)
  have hE := commutator_coordinateQuadPlus n F (by omega)
  obtain ⟨-, -, -, huniq, Fm, hFm, hker, hinjκ, hinv⟩ :=
    evenOrthogonalRealization_of_regular hf hK (by omega : 1 ≤ 2 * n) _ hQ hT hE
  have hcj := conj_injective_matrixProjectiveDerived hQ hT hE
  by_cases hβ1 : β = 1
  · left
    exact ⟨1, mul_one 1, by rw [map_one, map_one, hβ1]⟩
  have hβ2 : orderOf β = 2 := orderOf_eq_prime (by rw [pow_two]; exact hβ) hβ1
  obtain ⟨S, ⟨hS, hSβ⟩, -⟩ := huniq β hβim
  obtain ⟨hSS, hTT, hright⟩ := hinv β hβim hβ2 S hS hSβ
  rcases hright with hσ1 | ⟨hord, huniqσ, -⟩
  ·
    left
    have hmem : (⟨matrixProjectiveConjugationHom _ S, ⟨S, rfl⟩⟩ :
        matrixProjectiveImage (coordinateQuadPlus n F)) ∈ Fm.ker := by
      rw [MonoidHom.mem_ker, hFm, hσ1]
    rw [hker, Subgroup.mem_subgroupOf] at hmem
    obtain ⟨s, hs⟩ := hmem
    have hs' : matrixProjectiveConjugationHom _ (matrixIsometryInclusion _ s) = β := hs.trans hSβ
    refine ⟨s, hinjκ ?_, hs'⟩
    change matrixProjectiveConjugationHom _ (matrixIsometryInclusion _ (s * s)) =
      matrixProjectiveConjugationHom _ (matrixIsometryInclusion _ 1)
    rw [map_mul, map_mul, hs', hβ, map_one, map_one]
  right
  have hσS : σ = S.val.right := huniqσ σ hσ
  have hσ1 : S.val.right ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hord
    exact absurd hord (by norm_num)
  have hσσ : S.val.right * S.val.right = 1 := by
    have h1 := congrArg (fun y : similarityPairs (coordinateQuadPlus n F) => y.val.right) hSS
    rw [Subgroup.coe_mul, Subgroup.coe_one] at h1
    exact h1
  obtain ⟨hfin, -, -, hQ₀, -, -, -, -⟩ := even_quadratic_semilinear_involution_descent hσσ hσ1 hQ
    (T := pairSemilinearMap S.val) hTT (pairSemilinearMap_quad hS)
  have : FiniteDimensional (descentField S.val.right) (pairFix S) := finite_fixSpace
  have hdim : Module.finrank (descentField S.val.right) (pairFix S) = 2 * n := by
    rw [hfin, Module.finrank_fin_fun]
  rcases (finite_even_regular_quadratic_normal_forms (pairDescentForm hS) hQ₀).2.2.1 n
      (by omega) hdim with ⟨b', hb'⟩ | ⟨β', γ', -, hroot, b', hb'⟩
  ·
    left
    obtain ⟨hfeven, hkcard, hsimple, -, ext, -, -, hinj, hinn, hNC, -, -⟩ :=
      evenOrthogonalFieldCentralizer_of_regular hf hK (by omega : 4 ≤ n) _ hQ hT hE β hβim hβ2
        S hS hSβ hσ1
    obtain ⟨g, hg⟩ := hfeven
    have hg1 : 1 ≤ g := by omega
    have hfg : f / 2 = g := by omega
    rw [hfg] at hkcard
    have hreg := regular_coordinateQuadPlus n (descentField S.val.right) (by omega)
    obtain ⟨eM⟩ := E7Pilot.nonempty_derived_mulEquiv_of_isometry hg1 hkcard (by omega) _
      ((plusBasisIsometry b' hb').trans (coordinatePlusIsometry n (descentField S.val.right)))
      hreg.1 hreg.2 (commutator_coordinateQuadPlus n (descentField S.val.right) (by omega))
    have hJ : Nat.card ↥(pairDescentDerived hS) = ordD n (2 ^ g) :=
      (Nat.card_congr eM.toEquiv).trans (card_coordinatePlus hg1 hkcard (by omega))
    have eJ : ↥(pairDescentDerived hS) ≃* (extKappa _ ext).range := MonoidHom.ofInjective hinj
    have hNle : (extKappa _ ext).range ≤
        inner (matrixProjectiveDerived (coordinateQuadPlus n F)) ⊓ Subgroup.centralizer {β} :=
      fun x hx => Subgroup.mem_inf.mpr ⟨hinn hx, (Subgroup.mem_inf.mp (hNC hx)).2⟩
    have : IsSimpleGroup ↥(pairDescentDerived hS) := hsimple
    have hNs : IsSimpleGroup (extKappa _ ext).range := eJ.symm.isSimpleGroup
    have hJN : Nat.card ↥(pairDescentDerived hS) = Nat.card (extKappa _ ext).range :=
      Nat.card_congr eJ.toEquiv
    have := finite_mulAut_matrixProjectiveDerived (coordinateQuadPlus n F)
    have h4 : 4 ∣ Nat.card (extKappa _ ext).range := by
      rw [← hJN, hJ]
      exact four_dvd_of_eq_ord hg1 (by omega) (by rw [← hJ, hJN]; exact Nat.card_pos.ne')
        (Or.inl rfl)
    have hdvd := card_dvd_card_perfectCore_fixedSubgroup hcj β hNle hNs h4
    refine ⟨g, hg1, by rw [hK, hg, two_mul], ?_⟩
    rw [← hJ, hJN]
    exact hdvd.trans (Subgroup.card_dvd_of_le (perfectCore_le _))
  ·
    right
    have hbk : b ∈ descentField S.val.right := by
      rw [mem_descentField, ← hσS]
      exact hb
    have hck : c ∈ descentField S.val.right := by
      rw [mem_descentField, ← hσS]
      exact hc
    have hirr₀ : ∀ s : descentField S.val.right,
        s ^ 2 + ⟨b, hbk⟩ * s + ⟨c, hck⟩ ≠ 0 := by
      intro s hs
      refine hirr s (by rw [hσS]; exact mem_descentField.1 s.2) ?_
      have h1 := congrArg (fun x : descentField S.val.right => (x : F)) hs
      simpa using h1
    obtain ⟨ι⟩ := binForm_isometry hirr₀ hroot
    let φ : (pairDescentForm hS).IsometryEquiv
        (quadMinus n (descentField S.val.right) ⟨b, hbk⟩ ⟨c, hck⟩) :=
      (minusBasisIsometry b' hb').trans ((quadMinusIsometry n β' γ').trans
        (((QuadraticMap.IsometryEquiv.refl _).prod ι).trans
          (quadMinusIsometry n _ _).symm))
    have hQ'σ : ∀ v, coordinateQuadMinus n F (by omega) b c
        (coordinateFieldMap (2 * n) S.val.right v) =
          S.val.right (coordinateQuadMinus n F (by omega) b c v) := by
      rw [← hσS]
      exact coordinateQuadMinus_fieldMap_of_fixed (by omega) hb hc
    obtain ⟨Θ, hΘ⟩ := exists_mulEquiv_conj_fieldAutT_of_minus (K := F) (n := n) (by omega) hQ
      hS hσσ hσ1 hTT ⟨b, hbk⟩ ⟨c, hck⟩ φ hQ'σ
    refine ⟨Θ, ?_⟩
    rw [fieldAutT_congr_right _ hσS _ hQ'σ]
    apply MulEquiv.ext
    intro x
    obtain ⟨y, rfl⟩ := Θ.surjective x
    change Θ (β (Θ.symm (Θ y))) = _
    rw [MulEquiv.symm_apply_apply, ← hSβ]
    exact hΘ y

end Cases

section Four

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem inv_mul_mul_eq_congr {X : Type*} [Group X] (ψ β : MulAut X) :
    ψ⁻¹ * β * ψ = MulAut.congr ψ⁻¹ β :=
  MulEquiv.ext fun _ => rfl

theorem congr_trans_apply {X Y Z : Type*} [Group X] [Group Y] [Group Z] (e₁ : X ≃* Y)
    (e₂ : Y ≃* Z) (β : MulAut X) :
    MulAut.congr (e₁.trans e₂) β = MulAut.congr e₂ (MulAut.congr e₁ β) :=
  MulEquiv.ext fun _ => rfl

theorem involution_cases_omegaPlus_minusForm_four {σ : F ≃+* F} (hσ : orderOf σ = 2) {b c : F}
    (hb : σ b = b) (hc : σ c = c) (hirr : ∀ s : F, σ s = s → s ^ 2 + b * s + c ≠ 0)
    {β : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 F))} (hβ : β * β = 1) :
    (∃ s : matrixIsometries (coordinateQuadPlus 4 F), s * s = 1 ∧
      Nat.card (fixedSubgroup (matrixProjectiveConjugationHom _ (matrixIsometryInclusion _ s))) =
        Nat.card (fixedSubgroup β)) ∨
    (∃ g : ℕ, 1 ≤ g ∧ Nat.card F = 2 ^ (2 * g) ∧
      ordD 4 (2 ^ g) ∣ Nat.card (fixedSubgroup β)) ∨
    (∃ Θ : matrixProjectiveDerived (coordinateQuadPlus 4 F) ≃*
        matrixProjectiveDerived (coordinateQuadMinus 4 F (by omega) b c),
      MulAut.congr Θ β = fieldAutT (coordinateQuadMinus 4 F (by omega) b c) σ
        (coordinateQuadMinus_fieldMap_of_fixed (by omega) hb hc)) := by
  obtain ⟨f, hf, hK⟩ := F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := F)
  have hβ2 : IsPGroup 2 (zpowers β) := by
    have hdvd : orderOf β ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [_root_.sq]; exact hβ)
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h2, pow_one])
  obtain ⟨ψ, hψ⟩ := RankTwoHypIIOrthogonal.exists_conj_le_image_plus_four (K := F) hf hK
    (zpowers β) hβ2
  have hβ'im : MulAut.congr ψ⁻¹ β ∈ matrixProjectiveImage (coordinateQuadPlus 4 F) := by
    have h1 := hψ ⟨β, mem_zpowers β, rfl⟩
    change ψ⁻¹ * β * ψ⁻¹⁻¹ ∈ _ at h1
    rw [inv_inv, inv_mul_mul_eq_congr] at h1
    exact h1
  have hββ' : MulAut.congr ψ⁻¹ β * MulAut.congr ψ⁻¹ β = 1 := by
    rw [← map_mul, hβ, map_one]
  have hcard : Nat.card (fixedSubgroup (MulAut.congr ψ⁻¹ β)) = Nat.card (fixedSubgroup β) := by
    rw [ExcSelector.fixedSubgroup_congr, Subgroup.card_map_of_injective (ψ⁻¹).injective]
  rcases involution_cases_omegaPlus_minusForm_of_mem_image le_rfl hσ hb hc hirr hββ' hβ'im with
    ⟨s, hss, hsβ⟩ | ⟨g, hg, hFg, hdg⟩ | ⟨Θ, hΘ⟩
  · exact Or.inl ⟨s, hss, by rw [hsβ, hcard]⟩
  · exact Or.inr (Or.inl ⟨g, hg, hFg, hcard ▸ hdg⟩)
  · refine Or.inr (Or.inr ⟨(ψ⁻¹ : MulAut _).trans Θ, ?_⟩)
    rw [congr_trans_apply]
    exact hΘ

end Four

section Main

variable {F : Type} [Field F] [Finite F] [CharP F 2]

@[expose] def OmegaPlusFourLinearTwoPartInput : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (g : ℕ), Nat.card F = 2 ^ g → 2 ≤ g →
    OmegaLinearInvolutionTwoPart (coordinateQuadPlus 4 F) 4 g

theorem not_dvd_two_mul_card_mulAut_minus_of_isometry_four
    (hlin : OmegaPlusFourLinearTwoPartInput) {K : Type} [Field K] [Finite K] [CharP K 2]
    (hFK : Nat.card F = Nat.card K ^ 2) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (s : matrixIsometries (coordinateQuadPlus 4 F)) (hss : s * s = 1) :
    ¬ Nat.card (fixedSubgroup (matrixProjectiveConjugationHom _ (matrixIsometryInclusion _ s))) ∣
      2 * Nat.card (MulAut (matrixProjectiveDerived (coordinateQuadMinus 4 K (by omega) b c))) := by
  intro hdvd
  obtain ⟨f, hf, hK⟩ := F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := K)
  have hF : Nat.card F = 2 ^ (2 * f) := by rw [hFK, hK, ← pow_mul, mul_comm]
  have := finite_mulAut_matrixProjectiveDerived (coordinateQuadMinus 4 K (by omega) b c)
  have hAut := factorization_two_card_mulAut_coordinateMinus hf hK (le_refl 4) hirr
  have h2A := factorization_two_two_mul_le
    (Nat.card (MulAut (matrixProjectiveDerived (coordinateQuadMinus 4 K (by omega) b c))))
  have hvf : f.factorization 2 < f := Nat.factorization_lt 2 (by omega)
  have hle := factorization_two_le_of_dvd_ne_zero hdvd (mul_ne_zero two_ne_zero Nat.card_pos.ne')
  by_cases hs1 : s = 1
  · subst hs1
    rw [map_one, map_one, fixedSubgroup_one_eq_top, Subgroup.card_top,
      card_coordinatePlus (by omega) hF (le_refl 4), factorization_two_ordD (by omega) (by omega)]
      at hle
    have e12 : (4 : ℕ) * (4 - 1) = 12 := rfl
    rw [e12] at hle hAut
    omega
  · have h := hlin F (2 * f) hF (by omega) s hss hs1
    have e12 : (4 : ℕ) * (4 - 1) + 4 = 16 := rfl
    have e12' : (4 : ℕ) * (4 - 1) = 12 := rfl
    rw [e12] at h
    rw [e12'] at hAut
    omega

theorem omegaMinusInvolutionCentralizerInput_four (hlin : OmegaPlusFourLinearTwoPartInput) :
    OmegaMinusInvolutionCentralizerInput 4 := by
  intro hn K F _ _ _ _ _ _ σ hσ hFK b c hirr β γ hβ hγ hirrF B hBB hB hdvd
  obtain ⟨α, hα, -, hβ0⟩ := exists_root_frob_of_irreducible hσ hβ hγ hirrF
  have hαα : α ≠ -β - α := root_ne_other_of_ne_zero hβ0
  set E := minusPlusProjEquiv (r := 3) (by omega) hα hαα with hEdef
  set Y := MulAut.congr E B with hY
  have hYY : Y * Y = 1 := by rw [hY, ← map_mul, hBB, map_one]
  have hCY : Nat.card (fixedSubgroup Y) = Nat.card (fixedSubgroup B) := by
    rw [hY, ExcSelector.fixedSubgroup_congr, Subgroup.card_map_of_injective E.injective]
  obtain ⟨f, hf, hKf⟩ := F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := K)
  have hF : Nat.card F = 2 ^ (2 * f) := by rw [hFK, hKf, ← pow_mul, mul_comm]
  rcases involution_cases_omegaPlus_minusForm_four hσ hβ hγ hirrF hYY with
    ⟨s, hss, hsY⟩ | ⟨g, hg, hFg, hdg⟩ | ⟨Θ, hΘ⟩
  ·
    apply not_dvd_two_mul_card_mulAut_minus_of_isometry_four hlin hFK hirr s hss
    rw [hsY, hCY]
    exact hdvd
  ·
    have hgf : g = f := by
      have h1 : 2 * g = 2 * f := Nat.pow_right_injective (le_refl 2) (hFg.symm.trans hF)
      omega
    subst hgf
    have h1 : ordD 4 (2 ^ g) ∣ 4 * g * ordTwistedD 4 (2 ^ g) := by
      refine hdg.trans ?_
      rw [hCY]
      refine hdvd.trans ?_
      have h2 := card_mulAut_coordinateMinus_dvd hf hKf (le_refl 4) hirr
      have e : 4 * g * ordTwistedD 4 (2 ^ g) = 2 * (2 * g * ordTwistedD 4 (2 ^ g)) := by
        ring
      rw [e]
      exact Nat.mul_dvd_mul_left 2 h2
    exact not_ordD_dvd_mul_ordTwistedD hg (by omega) h1
  ·
    apply hB (E.trans Θ)
    rw [mul_mul_inv_trans_eq_congr, ← hY]
    exact hΘ

end Main

end CFSG.SeitzReduction.OmegaPilot
