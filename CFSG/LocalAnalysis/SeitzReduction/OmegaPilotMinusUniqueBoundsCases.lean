module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSwapBoundsField
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotFieldYDescent
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

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

theorem involution_cases_omegaPlus_minusForm (hn : 5 ≤ n) {σ : F ≃+* F} (hσ : orderOf σ = 2)
    {b c : F} (hb : σ b = b) (hc : σ c = c) (hirr : ∀ s : F, σ s = s → s ^ 2 + b * s + c ≠ 0)
    {β : MulAut (matrixProjectiveDerived (coordinateQuadPlus n F))} (hβ : β * β = 1) :
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
  have hβim : β ∈ matrixProjectiveImage (coordinateQuadPlus n F) := by
    rw [CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_plus F n hn]
    exact Subgroup.mem_top β
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

end CFSG.SeitzReduction.OmegaPilot
