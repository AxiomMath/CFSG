module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotUniqueGen
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotNotLongRoot

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open CFSG Subgroup QuadraticMap
open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.OmegaRadical
open CFSG.RankThree.PartOne.KCOrthogonalSubfield
open CFSG.SeitzReduction.E7Pilot

@[expose] def OmegaPlusLinearInvolutionInput (n : ℕ) : Prop :=
  ∀ (K F : Type) [Field K] [Finite K] [CharP K 2] [Field F] [Finite F] [CharP F 2],
    Nat.card F = Nat.card K ^ 2 →
    ∀ s : matrixIsometries (coordinateQuadPlus n F), s * s = 1 →
      ¬ Nat.card (fixedSubgroup (matrixProjectiveConjugationHom _
          (matrixIsometryInclusion _ s))) ∣
        2 * Nat.card (MulAut (matrixProjectiveDerived (coordinateQuadPlus n K)))

section Orders

theorem card_coordinatePlus_lt_card_coordinateMinus {n : ℕ} (hn : 4 ≤ n) {K k : Type} [Field K]
    [Finite K] [CharP K 2] [Field k] [Finite k] [CharP k 2] (hkK : Nat.card k = Nat.card K)
    {b c : k} (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0) :
    Nat.card (matrixProjectiveDerived (coordinateQuadPlus n K)) <
      Nat.card (matrixProjectiveDerived (coordinateQuadMinus n k (by omega) b c)) := by
  have hP := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega_quadPlus (K := K) hn
  have hM := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega_quadMinus (K := k) hn hirr
  rw [Nat.card_congr (coordinatePlusWitnessEquiv K (MulEquiv.refl _)).toEquiv] at hP
  rw [Nat.card_congr (coordinateMinusWitnessEquiv k (by omega) b c (MulEquiv.refl _)).toEquiv,
    hkK] at hM
  have hq : (2 : ℤ) ≤ Nat.card K := by
    have := Finite.one_lt_card (α := K)
    exact_mod_cast this
  have hprod : (0 : ℤ) < ∏ i ∈ Finset.Icc 1 (n - 1), ((Nat.card K : ℤ) ^ (2 * i) - 1) := by
    refine Finset.prod_pos fun i hi => ?_
    have hi1 : 1 ≤ i := (Finset.mem_Icc.1 hi).1
    have h1 : (2 : ℤ) ≤ (Nat.card K : ℤ) ^ (2 * i) :=
      le_trans hq (le_self_pow₀ (by linarith) (by omega))
    linarith
  have hpow : (0 : ℤ) < (Nat.card K : ℤ) ^ (n * (n - 1)) := by positivity
  have hdiff : (Nat.card (matrixProjectiveDerived (coordinateQuadMinus n k (by omega) b c)) : ℤ) -
      Nat.card (matrixProjectiveDerived (coordinateQuadPlus n K)) =
      2 * ((Nat.card K : ℤ) ^ (n * (n - 1)) *
        ∏ i ∈ Finset.Icc 1 (n - 1), ((Nat.card K : ℤ) ^ (2 * i) - 1)) := by
    rw [hP, hM]
    ring
  have hlt : (Nat.card (matrixProjectiveDerived (coordinateQuadPlus n K)) : ℤ) <
      Nat.card (matrixProjectiveDerived (coordinateQuadMinus n k (by omega) b c)) := by
    nlinarith [mul_pos hpow hprod]
  exact_mod_cast hlt

end Orders

section Cases

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

theorem mulAut_mul_conj_mul_inv {X : Type*} [Group X] (β : MulAut X) (x : X) :
    β * MulAut.conj x * β⁻¹ = MulAut.conj (β x) := by
  refine MulEquiv.ext fun y => ?_
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem involution_cases_omegaPlus (hn : 5 ≤ n) {σ : F ≃+* F} (hσ : orderOf σ = 2)
    {β : MulAut (matrixProjectiveDerived (coordinateQuadPlus n F))} (hβ : β * β = 1) :
    (∃ s : matrixIsometries (coordinateQuadPlus n F), s * s = 1 ∧
      matrixProjectiveConjugationHom _ (matrixIsometryInclusion _ s) = β) ∨
    (∃ ψ : MulAut (matrixProjectiveDerived (coordinateQuadPlus n F)),
      ψ * β * ψ⁻¹ = fieldAutT (coordinateQuadPlus n F) σ (coordinateQuadPlus_fieldMap n σ)) ∨
    (∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2) (b c : k)
      (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0), Nat.card k ^ 2 = Nat.card F ∧
      ∃ N : Subgroup (matrixProjectiveDerived (coordinateQuadPlus n F)),
        N ≤ fixedSubgroup β ∧ ⁅N, N⁆ = N ∧
        Nonempty (N ≃* matrixProjectiveDerived (coordinateQuadMinus n k (by omega) b c))) := by
  obtain ⟨f, hf, hK⟩ := F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := F)
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus n F (by omega)
  have hE := commutator_coordinateQuadPlus n F (by omega)
  have hβim : β ∈ matrixProjectiveImage (coordinateQuadPlus n F) := by
    rw [CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_plus F n hn]
    exact Subgroup.mem_top β
  obtain ⟨-, -, -, huniq, Fm, hFm, hker, hinjκ, hinv⟩ :=
    evenOrthogonalRealization_of_regular hf hK (by omega : 1 ≤ 2 * n) _ hQ hT hE
  have hcj := UnbalancingLocal.EvenOrthogonalComponents.conj_injective_matrixProjectiveDerived
    hQ hT hE
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
      (by omega) hdim with ⟨b, hb⟩ | ⟨β', γ', -, hroot, b, hb⟩
  ·
    left
    obtain ⟨ψ, hψ⟩ := exists_conj_eq_fieldAutT_of_plus (by omega) hS hσσ hσ1 hTT b hb
    refine ⟨ψ, ?_⟩
    rw [← hSβ, hψ]
    subst hσS
    rfl
  ·
    right
    obtain ⟨hfeven, hkcard, -, -, ext, -, -, hinj, hinn, hNC, -, -⟩ :=
      evenOrthogonalFieldCentralizer_of_regular hf hK (by omega : 4 ≤ n) _ hQ hT hE β hβim hβ2 S
        hS hSβ hσ1
    obtain ⟨g', hg', hk'⟩ :=
      F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := descentField S.val.right)
    have hreg := regular_coordinateQuadMinus n (descentField S.val.right) β' γ' (by omega) hroot
    obtain ⟨eM⟩ := nonempty_derived_mulEquiv_of_isometry hg' hk' (by omega) _
      ((minusBasisIsometry b hb).trans
        (coordinateMinusIsometry n (descentField S.val.right) (by omega) β' γ'))
      hreg.1 hreg.2 (commutator_coordinateQuadMinus n (descentField S.val.right) β' γ' (by omega)
        hroot)
    refine ⟨descentField S.val.right, inferInstance, inferInstance, inferInstance, β', γ', hroot,
      ?_, ?_⟩
    · obtain ⟨r, hr⟩ := hfeven
      rw [hkcard, hK, ← pow_mul]
      congr 1
      omega
    obtain ⟨N, hNdef⟩ : ∃ N : Subgroup (MulAut (matrixProjectiveDerived (coordinateQuadPlus n F))),
        N = (extKappa (coordinateQuadPlus n F) ext).range := ⟨_, rfl⟩
    obtain ⟨N', hN'def⟩ : ∃ N' : Subgroup (matrixProjectiveDerived (coordinateQuadPlus n F)),
        N' = N.comap (MulAut.conj : matrixProjectiveDerived (coordinateQuadPlus n F) →*
          MulAut (matrixProjectiveDerived (coordinateQuadPlus n F))) := ⟨_, rfl⟩
    have hinn' : N ≤ (MulAut.conj : matrixProjectiveDerived (coordinateQuadPlus n F) →*
        MulAut (matrixProjectiveDerived (coordinateQuadPlus n F))).range := hNdef ▸ hinn
    have hNC' : N ≤ matrixProjectiveImage (coordinateQuadPlus n F) ⊓ Subgroup.centralizer {β} :=
      hNdef ▸ hNC
    have hmapN : N'.map MulAut.conj = N := by
      rw [hN'def]
      exact Subgroup.map_comap_eq_self hinn'
    let e1 : N' ≃* N :=
      (N'.equivMapOfInjective _ hcj).trans (MulEquiv.subgroupCongr hmapN)
    let e2 : N ≃* pairDescentDerived hS :=
      (MulEquiv.subgroupCongr hNdef).trans (MonoidHom.ofInjective hinj).symm
    let eN : N' ≃* matrixProjectiveDerived (coordinateQuadMinus n (descentField S.val.right)
        (by omega) β' γ') := (e1.trans e2).trans eM
    refine ⟨N', ?_, ?_, ⟨eN⟩⟩
    ·
      intro x hx
      have hxN : MulAut.conj x ∈ N := by
        rw [hN'def] at hx
        exact hx
      have hc : MulAut.conj x ∈ Subgroup.centralizer {β} := (Subgroup.mem_inf.1 (hNC' hxN)).2
      have hcomm : β * MulAut.conj x = MulAut.conj x * β :=
        (Subgroup.mem_centralizer_singleton_iff.1 hc).symm
      have h1 : MulAut.conj (β x) = MulAut.conj x := by
        rw [← mulAut_mul_conj_mul_inv, hcomm, mul_inv_cancel_right]
      exact hcj h1
    ·
      have hsimp := matrix_simple_nonabelian (by omega : 0 < 2 * n) hreg.1 hreg.2
      have : IsSimpleGroup (matrixProjectiveDerived
        (coordinateQuadMinus n (descentField S.val.right) (by omega) β' γ')) := hsimp.1
      have htop := commutator_top_of_isSimpleGroup hsimp.2
      set φ := N'.subtype.comp eN.symm.toMonoidHom with hφ
      have hφr : φ.range = N' := by
        rw [hφ, MonoidHom.range_comp, MonoidHom.range_eq_top.2 eN.symm.surjective,
          ← MonoidHom.range_eq_map, range_subtype]
      rw [← hφr]
      exact commutator_range_of_commutator_top φ htop

end Cases

section Unique

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {F : Type} [Field F] [Finite F] [CharP F 2]

theorem conjugate_eq_of_omegaPlusFieldRow_of_linear {n f : ℕ}
    (hlin : OmegaPlusLinearInvolutionInput n) (hset : SeitzSetting G L) (hn : 5 ≤ n)
    (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) (ι : K →+* F)
    {σ : F ≃+* F} (hσ : orderOf σ = 2) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    {G₀ : Subgroup G} (hG₀ : G₀ = ⨆ j, plusNode e j)
    (ψ₀ : G₀ ≃* matrixProjectiveDerived (coordinateQuadPlus n F)) (h : G)
    (htM : t ∈ normalizer (CFSG.conjugate G₀ h : Set G)) : CFSG.conjugate G₀ h = G₀ := by
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have htt : t * t = 1 := by rw [← _root_.sq, ← ht, pow_orderOf_eq_one]
  have hf1 : 1 ≤ f := LinearPilot.one_le_of_card_eq_two_pow hKc
  have hOut : Group.IsSolvable (Outer L) := isSolvable_outer_of_mulEquiv_plus (by omega) hf1 hKc e
  have hF : Nat.card F = 2 ^ (2 * f) :=
    SymplecticPilot.natCard_eq_two_pow_two_mul_of_fix ι hKc hσ hfix
  have hFK : Nat.card F = Nat.card K ^ 2 := by rw [hF, hKc, ← pow_mul, mul_comm]
  have hF4 : 4 ≤ Nat.card F := by
    rw [hFK]
    nlinarith
  set Ψ : matrixProjectiveDerived (coordinateQuadPlus n F) →* G :=
    (MulAut.conj h⁻¹).toMonoidHom.comp (G₀.subtype.comp ψ₀.symm.toMonoidHom) with hΨ
  have hinj : Function.Injective Ψ :=
    (MulAut.conj h⁻¹).injective.comp (G₀.subtype_injective.comp ψ₀.symm.injective)
  have hrange : Ψ.range = CFSG.conjugate G₀ h := by
    rw [hΨ, MonoidHom.range_comp, MonoidHom.range_comp, MonoidHom.range_eq_top.2
      ψ₀.symm.surjective, ← MonoidHom.range_eq_map, range_subtype]
    rfl
  obtain ⟨β, hβ⟩ := SymplecticPilot.exists_mulAut_of_mem_normalizer_range hinj (hrange ▸ htM)
  have hββ := SymplecticPilot.mul_self_eq_one_of_conj_eq hinj htt hβ
  have hC := SymplecticPilot.range_inf_centralizer_eq_map hinj hβ
  have hCt : (fixedSubgroup β).map Ψ ≤ centralizer ({t} : Set G) := by
    rw [← hC]
    exact inf_le_right
  rcases involution_cases_omegaPlus hn hσ hββ with ⟨s, hs1, hsβ⟩ | ⟨ψ', hψ'⟩ |
      ⟨k, _, _, _, b, c, hirr, hk, N, hNβ, hNperf, ⟨eN⟩⟩
  ·
    exfalso
    apply hlin K F hFK s hs1
    rw [hsβ]
    have hdvd := E6Pilot.card_dvd_two_mul_card_mulAut_of_le_centralizer
      hset.standardSetting.standard e ht hKt hCt
    rwa [Subgroup.card_map_of_injective hinj] at hdvd
  ·
    obtain ⟨Φ, hΦr, hΦ⟩ := exists_comp_fieldEmbed_eq hset.standardSetting hOut hn e htC ht ι hfix
      hinj hβ hψ'
    have hle : CFSG.conjugate G₀ h ≤ G₀ := by
      rw [← hrange, ← hΦr, hG₀]
      exact range_le_iSup_plusNode_of_comp_fieldEmbed (by omega) e hF hF4 ι hΦ
    exact Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective).ge
  ·
    exfalso
    have hkK : Nat.card k = Nat.card K :=
      Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) (hk.trans hFK)
    have hNt : N.map Ψ ≤ centralizer ({t} : Set G) := (Subgroup.map_mono hNβ).trans hCt
    have hNperf' : ⁅N.map Ψ, N.map Ψ⁆ = N.map Ψ := by
      rw [← Subgroup.map_commutator, hNperf]
    have hNL : N.map Ψ ≤ L := std_perfect_le hset.standardSetting hOut htC ht hNperf' hNt
    have h1 : Nat.card (N.map Ψ) ≤ Nat.card L := Subgroup.card_le_of_le hNL
    rw [Subgroup.card_map_of_injective hinj, Nat.card_congr eN.toEquiv,
      Nat.card_congr e.toEquiv] at h1
    exact absurd h1 (not_le.2 (card_coordinatePlus_lt_card_coordinateMinus (by omega) hkK hirr))

theorem unique_of_omegaPlusFieldRow_of_linear {n f : ℕ} (hlin : OmegaPlusLinearInvolutionInput n)
    (hset : SeitzSetting G L) (hn : 5 ≤ n) (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) (ι : K →+* F)
    {σ : F ≃+* F} (hσ : orderOf σ = 2) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    {G₀ : Subgroup G} (hG₀ : G₀ = ⨆ j, plusNode e j)
    (ψ₀ : G₀ ≃* matrixProjectiveDerived (coordinateQuadPlus n F)) :
    ∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) → g ∈ normalizer (G₀ : Set G) :=
  F4Pilot.unique_of_forall_conjugate_eq fun h htM =>
    conjugate_eq_of_omegaPlusFieldRow_of_linear hlin hset hn hKc hq e ht hKt ι hσ hfix hG₀ ψ₀ h
      htM

end Unique

end CFSG.SeitzReduction.OmegaPilot
