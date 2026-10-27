module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossUniField
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryOuter
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderPSUDescent
public import CFSG.RankThree.PartOne.KC.UnitaryNoninnerPlaneGeneral
public import CFSG.Assembly.QuasithinDefs
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossBase
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.Classical.SteinbergBTHigherUnitaryPrimeSubfield
public import CFSG.RankThree.Classical.SteinbergBTNonsplitUnitaryPrimeSubfield
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.PlaneReductionGeneral
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits
public import CFSG.RankThree.PartOne.KC.UnitaryEndpointStatements
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.Classical CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.HardMathSupport.Timmesfeld.CrossChar

variable {ℓ f n p : ℕ} {K : Type} [Field K]

theorem dvd_pow_div_add_one {q₀ : ℕ} (hp : p.Prime) (hpq : p ∣ q₀ ^ p + 1) : p ∣ q₀ + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have h1 : ((q₀ ^ p + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hpq
  push_cast at h1
  rw [ZMod.pow_card] at h1
  exact (ZMod.natCast_eq_zero_iff _ _).1 (by push_cast; exact h1)

theorem dvd_card_range_of_dvd_q (h : UnitaryFieldData ℓ f K) (hp : p.Prime) (hp2 : p ≠ 2)
    {σ : K ≃+* K} (hσ : orderOf σ = p) (hn : 3 ≤ n) (hpq : p ∣ ℓ ^ f + 1) :
    p ∣ Nat.card (primeSubfieldPSU h hp hp2 hσ n).range := by
  have hfin := h.finite
  set h₀ := fixSubfield_unitaryFieldData h hp hp2 hσ with hh₀
  have hbar := fixSubfield_unitaryFieldData_bar h hp hp2 hσ
  obtain ⟨hpf, -⟩ := dvd_and_card_fixSubfield_unitary h hp hp2 hσ
  have : Finite (fixSubfield σ) := Subtype.finite
  have hinj := subfieldPSU_injective h h₀ hbar n (by omega)
  have hqp : ℓ ^ f = (ℓ ^ (f / p)) ^ p := by
    rw [← pow_mul, Nat.div_mul_cancel hpf]
  rw [hqp] at hpq
  have hdvd := dvd_card_primeFormP_one h₀ hp hn (dvd_pow_div_add_one hp hpq)
  have e := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  rw [← e]
  exact hdvd

theorem exists_fieldCore_unitary_outer (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n)
    (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) (hp : p.Prime) (hp5 : 5 < p) (hpℓ : p ≠ ℓ)
    {D : Subgroup (MulAut (primeFormP h (idGram K n)))} (hD : IsElemAbelian p D)
    (hcard : Nat.card D = p ^ 2) (hDl : ¬ D ≤ primeFormD h (idGram K n)) :
    ∃ x ∈ D, x ∉ primeFormD h (idGram K n) ∧ FieldCoreAt p x := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hfin := h.finite
  have : Finite (primeFormP h (idGram K n)) := finite_primeFormP
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_idGram
  obtain ⟨x, hxD, hxl⟩ := Set.not_subset.mp hDl
  have hx1 : x ≠ 1 := fun h1 => hxl (h1 ▸ one_mem _)
  have hxp : x ^ p = 1 := hD.2 x hxD
  have hxord : orderOf x = p := orderOf_eq_prime hxp hx1
  set π := primeFormFieldFactor h hC hn hne with hπ
  have hσ1 : π x ≠ 1 := fun h1 => hxl (by
    rw [← ker_primeFormFieldFactor h hC hn hne]
    exact h1)
  have hσp : (π x) ^ p = 1 := by rw [← map_pow, hxp, map_one]
  have hσord : orderOf (π x) = p := orderOf_eq_prime hσp hσ1
  obtain ⟨-, -, -, -, -, M, hM⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.unitary_prime_semilinear_field_descent' h hn hne hp hp2
      x hxord (π x) rfl hσord
  set u := primeFormConjHom h (idGram K n) M with hu
  set σ := π x with hσ
  set δ := primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ with hδ
  have hxh : x = u * δ * u⁻¹ := by
    have : u⁻¹ * x * u = δ := hM
    rw [← this]
    group
  have hδp : orderOf δ = p := by
    have hδp' : δ ^ p = 1 := by rw [hδ, ← map_pow, ← hσord, pow_orderOf_eq_one, map_one]
    have hδ1 : δ ≠ 1 := by
      intro h1
      apply hx1
      rw [hxh, h1]
      group
    exact orderOf_eq_prime hδp' hδ1
  refine ⟨x, hxD, hxl, ?_⟩
  suffices hfc : FieldCoreAt p δ from fieldCoreAt_of_conj hfc u⁻¹ (by rw [hxh]; group)
  obtain ⟨hpf, hcard0⟩ := dvd_and_card_fixSubfield_unitary h hp hp2 hσord
  by_cases hpg : p ∣ Nat.gcd n (ℓ ^ f + 1)
  ·
    have hpq : p ∣ ℓ ^ f + 1 := hpg.trans (Nat.gcd_dvd_right _ _)
    have hpn : p ∣ n := hpg.trans (Nat.gcd_dvd_left _ _)
    have hn7 : p ≤ n := Nat.le_of_dvd (by omega) hpn
    exact fieldCoreAt_fieldHom_of_subfield h hp hp2 hσord hn hne (fun ⟨h1, _⟩ => by omega)
      (dvd_card_range_of_dvd_q h hp hp2 hσord hn hpq)
  ·
    have hinj := CFSG.RankThree.PartOne.KCUnitaryRegular.conj_injective_primeFormP h (isPrimeFormGram_idGram (K := K) (n := n)) hn hne
    have hZ : ¬ p ∣ Nat.card (normOneScalars h
        (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n) := by
      rw [card_normOneScalars_one h (by omega)]
      exact hpg
    obtain ⟨-, -, -, -, -, -, hrange, -, -, hsimp, hexc⟩ :=
      prime_subfield_fixed_group_package h hp hp2 hσord n hn hne hZ
    have hDpow : ∀ x : D, x ^ p = 1 := fun x => Subtype.ext (hD.2 x x.2)
    have : IsCyclic (K ≃+* K) :=
      CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
    set π' : D →* (K ≃+* K) := π.comp D.subtype with hπ'
    have hπne : π' ≠ 1 := by
      intro h1
      apply hσ1
      have := congrArg (fun φ : D →* (K ≃+* K) => φ ⟨x, hxD⟩) h1
      simpa [hπ'] using this
    obtain ⟨hker, -⟩ := CFSG.RankThree.PartOne.card_ker_eq_prime_of_ne_one hp hDpow hcard π' hπne
    obtain ⟨y', hy'k, hy'1⟩ : ∃ y' ∈ π'.ker, y' ≠ 1 := by
      by_contra hno
      push Not at hno
      have hbot : π'.ker = ⊥ := eq_bot_iff.2 fun z hz => (Subgroup.mem_bot).2 (hno z hz)
      rw [hbot, Subgroup.card_bot] at hker
      exact hp.one_lt.ne hker
    set y : MulAut (primeFormP h (idGram K n)) := (y' : MulAut (primeFormP h (idGram K n)))
      with hy
    have hyD : y ∈ D := y'.2
    have hy1 : y ≠ 1 := fun h1 => hy'1 (Subtype.ext h1)
    have hyp : y ^ p = 1 := hD.2 y hyD
    have hyDu : y ∈ primeFormD h (idGram K n) := by
      rw [← ker_primeFormFieldFactor h hC hn hne]
      exact hy'k
    have hyin : y ∈ (MulAut.conj : primeFormP h (idGram K n) →*
        MulAut (primeFormP h (idGram K n))).range :=
      CFSG.RankThree.PartOne.pElement_mem_inner_of_not_dvd_gcd h hn hne hp hpg hyDu hyp
    have hcomm : y * x = x * y := congrArg Subtype.val
      (hD.1.is_comm.comm ⟨y, hyD⟩ ⟨x, hxD⟩)
    obtain ⟨k, hkδ, hkord⟩ := exists_fixed_orderOf_of_canonical_conj hp hinj hxh hyin hy1 hyp hcomm
    have hkJ : k ∈ fieldFixedPSU h n σ := hkδ
    have hnexc : ¬(n = 3 ∧ ℓ ^ (f / p) = 2) := by
      rintro hex
      obtain ⟨-, hord72⟩ := hexc hex (by omega)
      exact hord72 k hkJ hkord
    have hJp : p ∣ Nat.card (primeSubfieldPSU h hp hp2 hσord n).range := by
      rw [hrange]
      have : orderOf (⟨k, hkJ⟩ : fieldFixedPSU h n σ) = p := by
        rw [Subgroup.orderOf_mk]
        exact hkord
      rw [← this]
      exact orderOf_dvd_natCard _
    exact fieldCoreAt_fieldHom_of_subfield h hp hp2 hσord hn hne hnexc hJp

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
