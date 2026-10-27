module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuter
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagProjectiveOrder
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PslBadAux.Diag
public import CFSG.GH74.GLS.IVK.L2.FixedSLQuasisimple
public import CFSG.LocalAnalysis.ComponentClassification.InnAutDerivedOdd
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLinOuter
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.AOne
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.PSLnTwo

public section

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.HardMathSupport.Timmesfeld.LocalTwo
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.ComponentClassification.UnbalancedCatalog.EvenLinearSL
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCLinearSubfield
open CFSG.HardMathSupport.Lang.UnitaryAutomorphisms
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
open CFSG.LieType.SeitzGeneration
open CFSG.GorensteinWalter CFSG.GH74.GLS.IVK CFSG.GroupTheory.SteinbergBK
open Matrix

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

theorem mem_innAutDerived_of_mem_linearAutGroup {m : ℕ} {F : Type} [Field F] [Finite F]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {x : MulAut (projectiveSL m F)}
    (hxp : x ^ p = 1) (hxD : x ∈ linearAutGroup m F) :
    x ∈ innAutDerived (projectiveSL m F) := by
  refine mem_innAutDerived_of_inner_inv_of_odd (α := x) (τ := dualAut m F)
    (hp.odd_of_ne_two hp2) hxp ?_
  obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.mp hxD
  rw [← hA]
  exact CFSG.HardMathSupport.Dickson.Sec6.I923.isInnerAut_dual_conj_mul A

theorem fieldCoreAt_projectiveSL_of_dvd_card {m : ℕ} (hm : 3 ≤ m) {F : Type}
    [Field F] [Finite F] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpF : ¬ p ∣ Nat.card F) (hpdvd : p ∣ Nat.card (projectiveSL m F)) :
    ∀ x : MulAut (projectiveSL m F), x ^ p = 1 → x ∉ innAutDerived (projectiveSL m F) →
      FieldCoreAt p x := by
  intro x hxp hxo
  haveI : Fact p.Prime := ⟨hp⟩
  have hxin : x ∉ inner (projectiveSL m F) :=
    fun h => hxo (CFSG.ComponentClassification.OuterAutomorphisms.inner_le_innAutDerived _ h)
  have hx1 : x ≠ 1 := fun h => hxin (by rw [h]; exact one_mem _)
  have hxord : orderOf x = p := orderOf_eq_prime hxp hx1
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hxE : x ∈ semilinearAutGroup m F :=
    mem_semilinearAutGroup_of_odd hm (by rw [hxord]; exact hpodd)
  have hxlin : x ∉ linearAutGroup m F := by
    intro hxD
    exact hxo (mem_innAutDerived_of_mem_linearAutGroup hp hp2 hxp hxD)
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨f, hℓ, hcard⟩ := FiniteField.card F (ringChar F)
  let f' : ℕ := f
  have hf'pos : 0 < f' := f.pos
  have hFc : Nat.card F = ringChar F ^ f' := by
    rw [Nat.card_eq_fintype_card]
    simpa [f'] using hcard
  obtain ⟨hpf, σ, hσ, ⟨h, hh, hxh⟩, hcardk⟩ :=
    higher_linear_prime_semilinear_field_descent' hℓ hf'pos hm hFc hp x hxE hxlin hxord
  let k := semilinearFixedSubfield σ
  have hk : ∀ c, c ∈ k ↔ σ c = c := fun c => RingHom.mem_eqLocusField
  have hFE : Nat.card F = Nat.card k ^ p := by
    rw [hFc, hcardk, ← pow_mul, Nat.mul_comm, Nat.mul_div_cancel' hpf]
  have hpE : ¬ p ∣ Nat.card k := fun hd => hpF (hFE ▸ dvd_pow hd hp.ne_zero)
  have hGL : p ∣ Nat.card (GL (Fin m) F) :=
    hpdvd.trans (card_projectiveSL_dvd_card_GL (n := m) (by omega))
  have hT_dvd : p ∣ Nat.card (linearSubfieldInclusion m k).range := by
    rw [show Nat.card (linearSubfieldInclusion m k).range = Nat.card (projectiveSL m k) from
      (Nat.card_congr (MonoidHom.ofInjective
        (linearSubfieldInclusion_injective (by omega) k)).toEquiv).symm]
    exact dvd_card_projectiveSL_of_dvd_card_GL hp hm hFE hpE hGL
  have hfcδ : FieldCoreAt p (fieldAut m F σ) := by
    refine ⟨(linearSubfieldInclusion m k).range, ?_, ?_,
      isQuasisimple_range_linearSubfieldInclusion hm k, ?_, ?_⟩
    · rintro _ ⟨y, rfl⟩
      exact mem_fixSub.2 (fieldAut_linearSubfieldInclusion (fun c hc => (hk c).1 hc) y)
    · intro g hg t ht
      exact conj_mem_range_linearSubfieldInclusion σ (mem_fixSub.1 hg) ht
    · exact fun hc => ((Nat.Prime.coprime_iff_not_dvd hp).1 hc) hT_dvd
    · intro g hgp _ hgT
      have hmem : g ∈ fixingSubgroup (MulAut (projectiveSL m F))
          ((linearSubfieldInclusion m k).range : Set (projectiveSL m F)) :=
        (mem_fixingSubgroup_iff _).2 hgT
      rw [fixingSubgroup_range_linearSubfieldInclusion hk hm] at hmem
      have hdvd : orderOf g ∣ p := by
        rw [← hσ, ← orderOf_fieldAut hm σ]
        exact orderOf_dvd_of_mem_zpowers hmem
      exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hgp.symm hdvd)
  exact fieldCoreAt_of_conj hfcδ h⁻¹ (by rw [hxh]; group)

theorem fieldCoreAt_psl2 {F : Type} [Field F] [Finite F] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (h4F : 4 ≤ Nat.card F)
    (hpF : ¬ p ∣ Nat.card F) (hF8 : p = 3 → Nat.card F ≠ 8)
    (hpdvd : p ∣ Nat.card (PSL2 F)) :
    ∀ x : MulAut (PSL2 F), x ^ p = 1 → x ∉ innAutDerived (PSL2 F) → FieldCoreAt p x := by
  intro x hxp hxo
  haveI : Fact p.Prime := ⟨hp⟩
  have hxin : x ∉ inner (PSL2 F) := fun h => hxo (CFSG.ComponentClassification.OuterAutomorphisms.inner_le_innAutDerived _ h)
  obtain ⟨σ, h, hσ, hxh⟩ := exists_outer_data hp hp2 hxp hxin
  have hodd : Odd (orderOf σ) := by rw [hσ]; exact hp.odd_of_ne_two hp2
  have hδp : orderOf (psl2FieldAut F σ) = p := by rw [orderOf_psl2FieldAut, hσ]
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h4F)
  haveI : Nontrivial (PSL2 F) :=
    (CFSG.LinearGroups.linear_projective_simple (n := 2) (K := F)
      (by norm_num) (Or.inr ⟨s, hs⟩)).1
  haveI : IsSimpleGroup (PSL2 F) :=
    (CFSG.LinearGroups.linear_projective_simple (n := 2) (K := F)
      (by norm_num) (Or.inr ⟨s, hs⟩)).2.1
  have hperf := (CFSG.LinearGroups.linear_projective_perfect (n := 2) (K := F)
    (by norm_num) (Or.inr ⟨s, hs⟩)).commutator_eq_top
  have hinj := CFSG.LieType.SeitzGeneration.conj_injective_of_simple_perfect hperf
  obtain ⟨y0, hy0, hy0ord⟩ := exists_orderOf_eq_prime_mem_fixSubgroup hp x hxp hpdvd
  have hy0' : y0 ∈ fixSub x := by
    rw [show fixSub x = fixSubgroup x from Subgroup.ext fun _ => Iff.rfl]
    exact hy0
  let y : MulAut (PSL2 F) := MulAut.conj y0
  have hy : y ∈ inner (PSL2 F) := ⟨y0, rfl⟩
  have hy1 : y ≠ 1 := by
    intro h1
    have h1' : MulAut.conj y0 = MulAut.conj (1 : PSL2 F) := by simpa [y] using h1
    have hy0one : y0 = 1 := hinj h1'
    rw [hy0one, orderOf_one] at hy0ord
    exact hp.ne_one hy0ord.symm
  have hyp : y ^ p = 1 := by
    rw [show y = MulAut.conj y0 from rfl, ← map_pow, ← hy0ord, pow_orderOf_eq_one, map_one]
  have hcomm : y * x = x * y := (conj_commute_of_mem_fixSub hy0').symm
  obtain ⟨k, hkδ, hkord⟩ := exists_fixed_orderOf_of_canonical_conj hp hinj hxh hy hy1 hyp hcomm
  have hpF0 : ¬ p ∣ Nat.card (fixedField σ) := fun hd =>
    hpF (by rw [← fixedField_card_pow σ, hσ]; exact dvd_pow hd hp.ne_zero)
  have h4 : 4 ≤ Nat.card (fixedField σ) := by
    by_cases hp35 : p = 3 ∨ p = 5
    · exact four_le_card_fixedField_odd hp hp35 hF8 hσ hpF0 k hkδ hkord
    · have hpne3 : p ≠ 3 := fun h => hp35 (Or.inl h)
      have hpne5 : p ≠ 5 := fun h => hp35 (Or.inr h)
      have hpne4 : p ≠ 4 := fun h => by rw [h] at hp; norm_num at hp
      have hp5 : 5 < p := by
        have hp3 : 3 ≤ p := by have := hp.two_le; omega
        omega
      exact four_le_card_fixedField hp hp5 hσ hpF0 k hkδ hkord
  exact fieldCoreAt_of_canonical_conj hp hinj hδp
    (isQuasisimple_range_pslIncl σ h4)
    (fun g => mem_range_pslIncl_iff σ hodd g)
    (mem_zpowers_of_fixes_range σ hodd) hxh hy hy1 hyp hcomm

theorem lieOuterPLayer_linear (p : ℕ) : p.Prime → p ≠ 2 → LieOuterPLayer p isLinearIdx := by
  intro hp hp2 d hd hlin hnExc S hS hfin he hnot hpdvd
  obtain ⟨e⟩ := he
  cases d with
  | A n q =>
    have hpq : q.p ≠ p := by
      have h := characteristic_ne_of_not_isChevSimple hd ⟨e⟩ hnot
      rwa [TauCeti.LieTypeIndex.characteristic_A] at h
    haveI : Fact q.p.Prime := ⟨q.prime_p⟩
    let F := GaloisField q.p q.exponent
    have hFcard : Nat.card F = q.card := by
      dsimp only [F]
      rw [GaloisField.card q.p q.exponent q.exponent_pos.ne']
      exact (TauCeti.PrimePower.card_def q).symm
    have hpF : ¬ p ∣ Nat.card F := by
      rw [hFcard]
      exact not_dvd_card_of_ne hp hpq.symm
    have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hd).1
    have hn1 : 1 ≤ n := hrange.1
    by_cases hn : n = 1
    · subst hn
      have hnExc' : ¬ (p = 3 ∧ q.card = 8) := by
        simpa [outerPLayerExc] using hnExc
      have h4q : 4 ≤ q.card := by
        have h7 := CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.seven_le_card_of_valid_A_one hd
        omega
      have h4F : 4 ≤ Nat.card F := by rw [hFcard]; exact h4q
      have hF8 : p = 3 → Nat.card F ≠ 8 := by
        intro hp3 h8
        exact hnExc' ⟨hp3, by rw [← hFcard]; exact h8⟩
      have eModel : S ≃* PSL2 F :=
        e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hd)
      have hpdvdM : p ∣ Nat.card (PSL2 F) := by
        rw [← Nat.card_congr eModel.toEquiv]
        exact hpdvd
      exact outerPLayerAt_of_mulEquiv_of_fieldCoreAt hp eModel
        (fieldCoreAt_psl2 hp hp2 h4F hpF hF8 hpdvdM)
    · have hn2 : 2 ≤ n := by omega
      have eModel : S ≃* projectiveSL (n + 1) F :=
        (e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL n q hd)).trans
          (LinearCover.projectiveSpecialLinearEquivProjectiveSL (n + 1) F)
      have hpdvdM : p ∣ Nat.card (projectiveSL (n + 1) F) := by
        rw [← Nat.card_congr eModel.toEquiv]
        exact hpdvd
      exact outerPLayerAt_of_mulEquiv_of_fieldCoreAt hp eModel
        (fieldCoreAt_projectiveSL_of_dvd_card (by omega) hp hp2 hpF hpdvdM)
  | _ => exact absurd hlin (by simp [isLinearIdx])

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
