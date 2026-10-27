module

public import CFSG.GH74.Uniqueness.Bender.UnitaryFixed
public import CFSG.GH74.Uniqueness.Bender.Aut
public import CFSG.GH74.Uniqueness.Bender.FixedLinear
public import CFSG.GH74.Uniqueness.Bender.Unitary
public import CFSG.GH74.Uniqueness.Bender.Outer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldFullAutomorphism
public import CFSG.LieType.Suzuki.SuzukiOuterCyclic
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder
public import CFSG.StronglyEmbedded.Catalog.Suzuki
import CFSG.Models.BenderSuzuki
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthLinearFrobenius
public import CFSG.StronglyEmbedded.MatrixGroups.PSL2
public import CFSG.Walter.Defs

public section

namespace CFSG.GH74.Uniqueness.Bender

open CFSG.ComponentClassification
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section Abstract

theorem isCyclic_sylow_of_quotient {G : Type*} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    (hN : Odd (Nat.card N)) (hq : IsCyclic (G ⧸ N)) (S : Sylow 2 G) : IsCyclic S := by
  have hinj : Function.Injective ((QuotientGroup.mk' N).comp (S : Subgroup G).subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxN : (x : G) ∈ N := (QuotientGroup.eq_one_iff _).mp hx
    obtain ⟨k, hk⟩ := S.isPGroup' x
    have h1 : orderOf (x : G) ∣ 2 ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      simpa using congrArg Subtype.val hk
    have h2 : orderOf (x : G) ∣ Nat.card N := by
      have := orderOf_dvd_natCard (⟨x, hxN⟩ : N)
      rwa [Subgroup.orderOf_mk] at this
    have hcop : Nat.Coprime (2 ^ k) (Nat.card N) :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hN)
    have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2
    rw [orderOf_eq_one_iff] at this
    exact Subtype.ext this
  exact isCyclic_of_injective _ hinj

theorem outerStructure_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) {d m : ℕ}
    (h : ∃ (Dd : Subgroup (Outer B)) (_ : Dd.Normal), IsCyclic Dd ∧ Nat.card Dd = d ∧
      IsCyclic (Outer B ⧸ Dd) ∧ Nat.card (Outer B ⧸ Dd) = m) :
    ∃ (Dd : Subgroup (Outer A)) (_ : Dd.Normal), IsCyclic Dd ∧ Nat.card Dd = d ∧
      IsCyclic (Outer A ⧸ Dd) ∧ Nat.card (Outer A ⧸ Dd) = m := by
  obtain ⟨Dd, hn, hc, hd, hq, hm⟩ := h
  have := hn
  set ε := CFSG.ComponentClassification.OuterAutomorphisms.equivalence e with hε
  have hmap : (Dd.map ε.symm.toMonoidHom).map ε.toMonoidHom = Dd := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id Dd
    ext x
    simp
  refine ⟨Dd.map ε.symm.toMonoidHom, Subgroup.Normal.map hn ε.symm.toMonoidHom
    ε.symm.surjective, ?_, ?_, ?_, ?_⟩
  · exact isCyclic_of_surjective
      (Subgroup.equivMapOfInjective Dd ε.symm.toMonoidHom ε.symm.injective).toMonoidHom
      (Equiv.surjective _)
  · exact (Subgroup.card_map_of_injective ε.symm.injective).trans hd
  · have : (Dd.map ε.symm.toMonoidHom).Normal := Subgroup.Normal.map hn _ ε.symm.surjective
    exact isCyclic_of_surjective
      (QuotientGroup.congr (Dd.map ε.symm.toMonoidHom) Dd ε hmap).symm.toMonoidHom
      (Equiv.surjective _)
  · rw [← hm]
    have : (Dd.map ε.symm.toMonoidHom).Normal := Subgroup.Normal.map hn _ ε.symm.surjective
    exact Nat.card_congr (QuotientGroup.congr (Dd.map ε.symm.toMonoidHom) Dd ε hmap).toEquiv

end Abstract

section Linear

theorem BenderType.outer_linear {K : Type*} [Group K] {n : ℕ} (h : BenderType K n 1 1) :
    IsCyclic (Outer K) ∧ Nat.card (Outer K) = n := by
  obtain ⟨hn, ⟨e₁⟩⟩ : 2 ≤ n ∧ Nonempty (K ≃* CFSG.Theory.Comparator.PSL2Model n) := by
    cases h with
    | linear n hn e => exact ⟨hn, ⟨e⟩⟩
  have hF : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have e₂ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n) ≃*
      CFSG.Theory.Comparator.PSL2Model n :=
    CFSG.ShultStronglyClosedTI.OddPrimeInverters.sl2EquivPSL2Binary (by omega) hF
  obtain ⟨-, -, hc, hcard, -⟩ :=
    CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField.even_SL2_full_automorphism_semilinear_model
      (F := GaloisField 2 n) (by omega) hF
  let ε := CFSG.ComponentClassification.OuterAutomorphisms.equivalence (e₁.trans e₂.symm)
  exact ⟨ε.isCyclic.mpr hc, by rw [Nat.card_congr ε.toEquiv]; exact hcard⟩

end Linear

section Suzuki

theorem BenderType.outer_suzuki
    {K : Type} [Group K] {n e : ℕ} (h : BenderType K n 2 e) :
    IsCyclic (Outer K) ∧ Nat.card (Outer K) ∣ n ∧ Odd (Nat.card (Outer K)) := by
  have hodd : Odd (Nat.card (Outer K)) := by
    have h0 : Odd (MulAut.conj : K →* MulAut K).range.index := h.lemma_3_1_b_suzuki
    rw [Subgroup.index_eq_card] at h0
    exact h0
  cases h with
  | suzuki a ha e₁ =>
    have hF : Nat.card (GaloisField 2 (2 * a + 1)) = 2 ^ (2 * a + 1) :=
      GaloisField.card 2 (2 * a + 1) (by omega)
    obtain ⟨hc, hd⟩ := CFSG.LieType.Suzuki.suzukiGroup_outer_isCyclic_card_dvd
      (a := a) (K := GaloisField 2 (2 * a + 1)) ha hF
    have e₂ : K ≃* CFSG.Blueprint.suzukiGroup a (GaloisField 2 (2 * a + 1)) :=
      (e₁.trans (MulEquiv.subgroupCongr (CFSG.BenderSuzuki.szModel_eq_suzukiMatrixGroup a))).trans
        (CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup hF).symm
    let ε := CFSG.ComponentClassification.OuterAutomorphisms.equivalence e₂
    refine ⟨ε.isCyclic.mpr hc, ?_, hodd⟩
    rw [Nat.card_congr ε.toEquiv]
    exact hd

end Suzuki

section Unitary

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.BenderSuzuki CFSG.ShultStronglyClosedTI CFSG.Assembly.LowTwoRank

theorem unitaryModel_outer_structure {n : ℕ} (hn : 2 ≤ n)
    (hU : UnitaryFieldData 2 n (GaloisField 2 (2 * n))) :
    ∃ (Dd : Subgroup (Outer (UnitaryModelP n hU))) (_ : Dd.Normal), IsCyclic Dd ∧
      Nat.card Dd = Nat.gcd 3 (2 ^ n + 1) ∧ IsCyclic (Outer (UnitaryModelP n hU) ⧸ Dd) ∧
      Nat.card (Outer (UnitaryModelP n hU) ⧸ Dd) = 2 * n := by
  classical
  have hq : ¬(3 = 3 ∧ 2 ^ n = 2) := by
    rintro ⟨-, h2⟩
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  have hC : IsPrimeFormGram (1 : GL (Fin 3) (GaloisField 2 (2 * n))) := isPrimeFormGram_one
  obtain ⟨-, -, -, -, -, -, hFsurj, hFker, hDnormal, hinn, -⟩ :=
    unitary_prime_form_full_semilinear_realization hU hC (le_refl 3) hq
  obtain ⟨-, hcyc, hcard, -, -, -⟩ := unitary_full_diagonal_outer_order hU (le_refl 3) hq
  have hRA := card_ringAut_and_isCyclic hU.prime (GaloisField 2 (2 * n)) hU.card
  set T := UnitaryModelP n hU with hT
  set D := primeFormD hU ((1 : GL (Fin 3) (GaloisField 2 (2 * n))) :
    Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * n))) with hD
  set I := OuterAutomorphisms.inner T with hI
  have hID : I ≤ D := fun α hα => by
    obtain ⟨s, rfl⟩ := (hinn α).1 hα
    exact ⟨_, rfl⟩
  set f₁ : D →* Outer T := (QuotientGroup.mk' I).comp D.subtype with hf₁
  have hker : f₁.ker = I.subgroupOf D := by
    ext x
    rw [MonoidHom.mem_ker, hf₁, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rfl
  have hrange : f₁.range = D.map (QuotientGroup.mk' I) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, a.2, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  have eDd : D.map (QuotientGroup.mk' I) ≃* D ⧸ I.subgroupOf D :=
    (MulEquiv.subgroupCongr hrange.symm).trans
      ((QuotientGroup.quotientKerEquivRange f₁).symm.trans
        (QuotientGroup.quotientMulEquivOfEq hker))
  refine ⟨D.map (QuotientGroup.mk' I), Subgroup.Normal.map hDnormal _
    (QuotientGroup.mk'_surjective I), eDd.isCyclic.mpr hcyc, ?_, ?_, ?_⟩
  · rw [Nat.card_congr eDd.toEquiv]
    exact hcard
  · have e₂ : Outer T ⧸ D.map (QuotientGroup.mk' I) ≃* MulAut T ⧸ D :=
      QuotientGroup.quotientQuotientEquivQuotient I D hID
    have e₃ : MulAut T ⧸ D ≃* (GaloisField 2 (2 * n) ≃+* GaloisField 2 (2 * n)) :=
      (QuotientGroup.quotientMulEquivOfEq hFker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective _ hFsurj)
    exact (e₂.trans e₃).isCyclic.mpr hRA.2
  · have e₂ : Outer T ⧸ D.map (QuotientGroup.mk' I) ≃* MulAut T ⧸ D :=
      QuotientGroup.quotientQuotientEquivQuotient I D hID
    have e₃ : MulAut T ⧸ D ≃* (GaloisField 2 (2 * n) ≃+* GaloisField 2 (2 * n)) :=
      (QuotientGroup.quotientMulEquivOfEq hFker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective _ hFsurj)
    rw [Nat.card_congr (e₂.trans e₃).toEquiv]
    exact hRA.1

theorem BenderType.outer_unitary {K : Type*} [Group K] {n e : ℕ} (h : BenderType K n 3 e) :
    ∃ (Dd : Subgroup (Outer K)) (_ : Dd.Normal), IsCyclic Dd ∧
      Nat.card Dd = Nat.gcd 3 (2 ^ n + 1) ∧ IsCyclic (Outer K ⧸ Dd) ∧
      Nat.card (Outer K ⧸ Dd) = 2 * n := by
  obtain ⟨hn, ⟨e₁⟩⟩ : 2 ≤ n ∧ Nonempty (K ≃* PSU3Model n) := by
    cases h with
    | unitary n hn e => exact ⟨hn, ⟨e⟩⟩
  have hmodel : PSU3Model n = CFSG.Open.PSU3 2 n := CFSG.Models.benderPSU3Model_eq_psu3 n
  have hU : UnitaryFieldData 2 n (GaloisField 2 (2 * n)) := unitaryFieldData_gf (by omega)
  have e₀ : K ≃* StatedProj (StatedSU 3 (2 ^ n) (GaloisField 2 (2 * n))) :=
    (e₁.trans (MulEquiv.subgroupCongr hmodel)).trans (glaSUCanonicalEquivNative n).symm
  have hC : IsPrimeFormGram (1 : GL (Fin 3) (GaloisField 2 (2 * n))) := isPrimeFormGram_one
  obtain ⟨χ⟩ := nonempty_primeFormP_mulEquiv hU hC
  let ψ : K ≃* UnitaryModelP n hU :=
    e₀.trans ((unitaryPSUEquiv hU (by omega)).symm.trans χ.symm)
  exact outerStructure_of_mulEquiv ψ (unitaryModel_outer_structure hn hU)

end Unitary

section Sylow

theorem BenderType.isCyclic_sylow_outer
    {K : Type} [Group K] [Finite K] {n i e : ℕ}
    (h : BenderType K n i e) (S : Sylow 2 (Outer K)) : IsCyclic S := by
  have : Finite (MulAut K) := Finite.of_injective (fun f : MulAut K => (f : K → K))
    DFunLike.coe_injective
  have : Finite (Outer K) := inferInstance
  rcases h.cases' with ⟨hi, he, -⟩ | ⟨hi, he, -⟩ | ⟨hi, he, -⟩
  · subst hi
    subst he
    have : IsCyclic (Outer K) := h.outer_linear.1
    infer_instance
  · subst hi
    obtain ⟨-, -, hodd⟩ := h.outer_suzuki
    have : IsCyclic ((Outer K) ⧸ (⊤ : Subgroup (Outer K))) := by
      have : Subsingleton ((Outer K) ⧸ (⊤ : Subgroup (Outer K))) :=
        QuotientGroup.subsingleton_quotient_top
      infer_instance
    exact isCyclic_sylow_of_quotient (⊤ : Subgroup (Outer K)) (by rwa [Subgroup.card_top]) this S
  · subst hi
    obtain ⟨Dd, hn, -, hd, hq, -⟩ := h.outer_unitary
    have := hn
    have : Odd (Nat.card Dd) := by
      rw [hd]
      exact Odd.of_dvd_nat (by decide : Odd 3) (Nat.gcd_dvd_left 3 _)
    exact isCyclic_sylow_of_quotient Dd this hq S

end Sylow

section Rank

open CFSG.BenderSuzuki

theorem BenderType.card_le_of_sq_eq_one
    {K : Type*} [Group K] [Finite K] {n i e : ℕ}
    (h : BenderType K n i e) (E : Subgroup K) (hsq : ∀ x ∈ E, x * x = 1) :
    Nat.card E ≤ 2 ^ n := by
  have hEp : IsPGroup 2 E := isPGroup_two_of_mul_self_eq_one hsq
  obtain ⟨Q, hEQ⟩ := hEp.exists_le_sylow
  obtain ⟨t, hc⟩ := h.exists_benderCore Q
  have hEZ : E ≤ rootCenter (Q : Subgroup K) := hc.elemAbelian_le_rootCenter hEQ hsq
  calc Nat.card E ≤ Nat.card (rootCenter (Q : Subgroup K)) := Subgroup.card_le_of_le hEZ
    _ = 2 ^ n := hc.card_center

theorem card_le_of_sq_eq_one_psl2 {m : ℕ} (hm : 1 ≤ m) (E : Subgroup (PSL2Model m))
    (hsq : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 2 ^ m := by
  have hEp : IsPGroup 2 E := isPGroup_two_of_mul_self_eq_one hsq
  obtain ⟨k, hk⟩ := hEp.exists_card_eq
  have hdvd : Nat.card E ∣ Nat.card (PSL2Model m) := Subgroup.card_subgroup_dvd_card E
  rw [show Nat.card (PSL2Model m) = 2 ^ m * ((2 ^ m) ^ 2 - 1) from card_psl2_even m hm,
    hk] at hdvd
  have hodd : Odd ((2 ^ m) ^ 2 - 1) := by
    have h1 : 1 ≤ (2 ^ m) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    have h2 : Even ((2 ^ m) ^ 2) := by
      rw [← pow_mul]
      exact (Nat.even_pow' (by omega)).mpr even_two
    exact Nat.Even.sub_odd h1 h2 odd_one
  have hcop : Nat.Coprime (2 ^ k) ((2 ^ m) ^ 2 - 1) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
  have h3 : 2 ^ k ∣ 2 ^ m := hcop.dvd_of_dvd_mul_right hdvd
  rw [hk]
  exact Nat.le_of_dvd (by positivity) h3

theorem BenderType.card_le_of_sq_eq_one_aut
    {K : Type} [Group K] [Finite K] {n i e : ℕ}
    (h : BenderType K n i e) (E : Subgroup (MulAut K)) (hsq : ∀ x ∈ E, x * x = 1) :
    Nat.card E ≤ 2 ^ (n + 1) ∧ (i ≠ 3 → Nat.card E ≤ 2 ^ n) := by
  classical
  have : Finite (MulAut K) := Finite.of_injective (fun f : MulAut K => (f : K → K))
    DFunLike.coe_injective
  have hconj_inj : Function.Injective (MulAut.conj : K →* MulAut K) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hg' : g ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro y
      have := congrArg (fun σ : MulAut K => σ y) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc y * g = (g * y * g⁻¹) * g := by rw [this]
        _ = g * y := by group
    rw [h.center_eq_bot, Subgroup.mem_bot] at hg'
    exact hg'
  set E₁ : Subgroup K := E.comap (MulAut.conj : K →* MulAut K) with hE₁
  have hE₁sq : ∀ k ∈ E₁, k * k = 1 := by
    intro k hk
    apply hconj_inj
    rw [map_mul, map_one]
    exact hsq _ hk
  set E₀ : Subgroup (MulAut K) := E ⊓ OuterAutomorphisms.inner K with hE₀
  have hmap : E₁.map (MulAut.conj : K →* MulAut K) = E₀ := by
    ext σ
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨hk, k, rfl⟩
    · rintro ⟨hσ, k, rfl⟩
      exact ⟨k, hσ, rfl⟩
  have hE₀E₁ : Nat.card E₀ = Nat.card E₁ := by
    rw [← hmap, Subgroup.card_map_of_injective hconj_inj]
  set f : E →* Outer K := (QuotientGroup.mk' (OuterAutomorphisms.inner K)).comp E.subtype with hf
  have hker : f.ker = E₀.subgroupOf E := by
    ext x
    rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact ⟨fun hx => ⟨x.2, hx⟩, fun hx => hx.2⟩
  have hcardE : Nat.card E = Nat.card f.range * Nat.card E₀ := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hker,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : E₀ ≤ E)).toEquiv] at h1
    exact h1
  have hrange : Nat.card f.range ≤ 2 := by
    have hsqr : ∀ r ∈ f.range, r * r = 1 := by
      rintro _ ⟨x, rfl⟩
      rw [← map_mul]
      have : (x * x : E) = 1 := Subtype.ext (hsq x x.2)
      rw [this, map_one]
    have hp : IsPGroup 2 f.range := isPGroup_two_of_mul_self_eq_one hsqr
    obtain ⟨S, hS⟩ := hp.exists_le_sylow
    have hcyc : IsCyclic S := h.isCyclic_sylow_outer S
    have hcycR : IsCyclic f.range :=
      isCyclic_of_injective (Subgroup.inclusion hS) (Subgroup.inclusion_injective hS)
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := f.range)
    have hog : orderOf g = Nat.card f.range := orderOf_eq_card_of_forall_mem_zpowers hg
    have hg2 : g ^ 2 = 1 := by
      have := hsqr g g.2
      exact Subtype.ext (by simpa [sq] using this)
    rw [← hog]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hg2)
  have hE₀card : Nat.card E₀ ≤ 2 ^ n := by
    rw [hE₀E₁]
    exact h.card_le_of_sq_eq_one E₁ hE₁sq
  refine ⟨?_, fun hi => ?_⟩
  · rw [hcardE, pow_succ, mul_comm (2 ^ n) 2]
    exact Nat.mul_le_mul hrange hE₀card
  ·
    have habel : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
      intro x hx y hy
      have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hsq x hx)
      have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hsq y hy)
      have hxy : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right (hsq _ (E.mul_mem hx hy))
      rw [mul_inv_rev, hx', hy'] at hxy
      exact hxy.symm
    have hinner : (∀ x ∈ E, x ∈ OuterAutomorphisms.inner K) → Nat.card E ≤ 2 ^ n := by
      intro hall
      have hbot : f.range = ⊥ := by
        rw [Subgroup.eq_bot_iff_forall]
        rintro _ ⟨x, rfl⟩
        rw [hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hall x x.2
      rw [hcardE, hbot, Subgroup.card_bot, one_mul]
      exact hE₀card
    rcases h.cases' with ⟨hi1, he1, -⟩ | ⟨hi2, he2, -⟩ | ⟨hi3, -, -⟩
    ·
      subst hi1
      subst he1
      by_cases hall : ∀ x ∈ E, x ∈ OuterAutomorphisms.inner K
      · exact hinner hall
      · obtain ⟨u, hu⟩ := not_forall.mp hall
        obtain ⟨huE, huout'⟩ := not_imp.mp hu
        have hu2 : u * u = 1 := hsq u huE
        have hout : ¬ ∃ g : K, ∀ x : K, u x = g * x * g⁻¹ := by
          rintro ⟨g, hg⟩
          apply huout'
          exact ⟨g, MulEquiv.ext fun x => by rw [hg x]; simp [MulAut.conj_apply]⟩
        obtain ⟨m, hnm, ⟨eF⟩, -⟩ := h.fixed_linear u hu2 hout
        have hn2 : 2 ≤ n := h.two_le.2
        have hconjmul : ∀ (γ : MulAut K) (r : K), γ * MulAut.conj r * γ⁻¹ = MulAut.conj (γ r) :=
          fun γ r => by ext x; simp [MulAut.mul_apply, map_mul, map_inv]
        have hE₁fix : E₁ ≤ autFixed u := by
          intro k hk
          have hk' : MulAut.conj k ∈ E := hk
          have h1 : MulAut.conj (u k) = MulAut.conj k := by
            rw [← hconjmul u k, habel u huE _ hk']
            group
          exact hconj_inj h1
        have hE₂card : Nat.card (E₁.subgroupOf (autFixed u)) = Nat.card E₁ :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₁fix).toEquiv
        have hE₂sq : ∀ y ∈ (E₁.subgroupOf (autFixed u)).map eF.toMonoidHom, y * y = 1 := by
          rintro _ ⟨x, hx, rfl⟩
          rw [← map_mul]
          have : x * x = 1 := Subtype.ext (hE₁sq _ hx)
          rw [this, map_one]
        have hbound : Nat.card ((E₁.subgroupOf (autFixed u)).map eF.toMonoidHom) ≤ 2 ^ m :=
          card_le_of_sq_eq_one_psl2 (by omega) _ hE₂sq
        have hE₁le : Nat.card E₁ ≤ 2 ^ m := by
          rw [← hE₂card, ← Subgroup.card_map_of_injective (f := eF.toMonoidHom) eF.injective]
          exact hbound
        rw [hcardE, hE₀E₁]
        calc Nat.card f.range * Nat.card E₁ ≤ 2 * 2 ^ m := Nat.mul_le_mul hrange hE₁le
          _ = 2 ^ (m + 1) := by ring
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    ·
      subst hi2
      apply hinner
      intro x hx
      obtain ⟨v, -, hv⟩ := h.exists_inner_of_sq_eq_one_suzuki x (hsq x hx)
      exact ⟨v, MulEquiv.ext fun k => by rw [hv k]; simp [MulAut.conj_apply]⟩
    · exact absurd hi3 hi

end Rank

end CFSG.GH74.Uniqueness.Bender
