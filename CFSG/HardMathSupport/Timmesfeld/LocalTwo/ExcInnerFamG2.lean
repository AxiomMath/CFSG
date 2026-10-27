module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerFamE
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldG2Eight
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldOrders
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuousG2
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuousTriality
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LieType.SeitzGeneration CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.TauCetiBridge CFSG.Timmesfeld.ExceptionalOrders CFSG.LieType.Ree
  CFSG.RankThree.Chevalley CFSG.RankThree.Chevalley.SteinbergBT
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo (fieldAut_isCyclic)
open CFSG.LocalAnalysis.ComponentInitial (finite_field_prime_power_characteristic)

set_option linter.unusedSectionVars false




theorem not_coprime_card_adjointG2_of_dvd_pow_six (k : Type) [Field k] [Finite k] {p : ℕ}
    (hp : p.Prime) (hd : p ∣ Nat.card k ^ 6 - 1) :
    ¬ Nat.Coprime p (Nat.card (adjointGroup Tag.G2 k)) := by
  rw [← Nat.Prime.dvd_iff_not_coprime hp, card_adjointGroup_G2]
  unfold ordG2
  exact Dvd.dvd.mul_right (dvd_mul_of_dvd_right hd _) _

theorem not_dvd_card_adjointG2 (k : Type) [Field k] [Finite k] {p : ℕ} (hp : p.Prime)
    (hpk : ¬ p ∣ Nat.card k) (hd : ¬ p ∣ Nat.card k ^ 6 - 1) :
    ¬ p ∣ Nat.card (adjointGroup Tag.G2 k) := by
  rw [card_adjointGroup_G2]
  unfold ordG2
  simp only [hp.dvd_mul]
  rintro ((h | h) | h)
  · exact hpk (hp.dvd_of_dvd_pow h)
  · exact hd h
  · exact hd (h.trans (sq_sub_one_dvd_pow_six_sub_one _))

theorem fieldCoreAt_entrywise_G2_two {f p : ℕ} (hf : 2 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ f) (hp : p.Prime) (hp6048 : p ∣ 6048) {σ : K ≃+* K}
    (hσp : orderOf σ = p) (hk2 : Nat.card (fixSubfield σ) = 2) :
    FieldCoreAt p (entrywiseAdjointAut Tag.G2 σ) := by
  classical
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  obtain ⟨-, -, hJC, hfixeq, -, -, -, -, -, -, hcent, -, -⟩ :=
    even_G2_canonical_field_centralizer_all_orders hf hK σ
  have : Finite (fixSubfield σ) := Subtype.finite
  have hmemφ : ∀ a : adjointGroup Tag.G2 (fixSubfield σ),
      baseChangeGL (fixSubfield σ).subtype (a : ModGL Tag.G2 (fixSubfield σ)) ∈
        adjointGroup Tag.G2 K := fun a => hJC ⟨a, a.2, rfl⟩
  obtain ⟨φ, hφdef⟩ : ∃ φ : adjointGroup Tag.G2 (fixSubfield σ) →* adjointGroup Tag.G2 K,
      ∀ a, (φ a : ModGL Tag.G2 K) =
        baseChangeGL (fixSubfield σ).subtype (a : ModGL Tag.G2 (fixSubfield σ)) :=
    ⟨((baseChangeGL (fixSubfield σ).subtype).comp
      (adjointGroup Tag.G2 (fixSubfield σ)).subtype).codRestrict _ hmemφ, fun _ => rfl⟩
  have hφ : Function.Injective φ := fun a b h =>
    Subtype.ext (baseChangeGL_injective _ (by rw [← hφdef, ← hφdef, h]))
  have hJfix : ∀ g : adjointGroup Tag.G2 K, g ∈ φ.range ↔ entrywiseAdjointAut Tag.G2 σ g = g := by
    intro g
    have h1 : g ∈ φ.range ↔ (g : ModGL Tag.G2 K) ∈ fixedFieldImage Tag.G2 σ := by
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨a, a.2, (hφdef a).symm⟩
      · rintro ⟨a, ha, hga⟩
        exact ⟨⟨a, ha⟩, Subtype.ext ((hφdef _).trans hga)⟩
    rw [h1, ← hfixeq]
    constructor
    · rintro ⟨g', hg', hgg'⟩
      have : g' = g := Subtype.ext hgg'
      subst this
      exact hg'
    · intro h
      exact ⟨g, h, rfl⟩
  obtain ⟨hq, hTcard, hZT, hJcard, hZJ⟩ := derived_range_adjointG2_two (fixSubfield σ) hk2 φ hφ
  obtain ⟨hTJ, hTn⟩ := commutator_self_le_and_normalized φ.range
  have hidx : (⁅φ.range, φ.range⁆.subgroupOf φ.range).index = 2 := by
    have h := (⁅φ.range, φ.range⁆.subgroupOf φ.range).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTJ).toEquiv, hTcard, hJcard] at h
    omega
  refine ⟨⁅φ.range, φ.range⁆, fun t ht => (hJfix t).1 (hTJ ht),
    fun f hf t ht => hTn f ((hJfix f).2 hf) t ht, hq, ?_, ?_⟩
  · rw [hTcard, Nat.Prime.coprime_iff_not_dvd hp]
    exact not_not.2 hp6048
  · intro g hgp hgδ hgT
    have hgJ : ∀ j ∈ φ.range, g j ∈ φ.range := by
      intro j hj
      rw [hJfix]
      have h1 := congrArg (fun β : MulAut (adjointGroup Tag.G2 K) => β j) hgδ
      simp only [MulAut.mul_apply] at h1
      rw [← h1, (hJfix j).1 hj]
    have hfixJ := fixes_of_fixes_derived φ.range hidx hZT hZJ g hgJ hgT
    have hJ₀ : φ.range = (fixedFieldImage Tag.G2 σ).subgroupOf (adjointGroup Tag.G2 K) := by
      ext j
      rw [Subgroup.mem_subgroupOf]
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨a, a.2, (hφdef a).symm⟩
      · rintro ⟨a, ha, hga⟩
        exact ⟨⟨a, ha⟩, Subtype.ext ((hφdef _).trans hga)⟩
    have hg1 : g ∈ Subgroup.centralizer {entrywiseAdjointAut Tag.G2 σ} ⊓
        Subgroup.centralizer ((((fixedFieldImage Tag.G2 σ).subgroupOf
          (adjointGroup Tag.G2 K)).map MulAut.conj : Subgroup (MulAut (adjointGroup Tag.G2 K))) :
            Set (MulAut (adjointGroup Tag.G2 K))) := by
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 hgδ, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨j, hj, rfl⟩
      rw [← hJ₀] at hj
      have h1 := mul_conj_mul_inv g j
      rw [hfixJ j hj] at h1
      change MulAut.conj j * g = g * MulAut.conj j
      calc MulAut.conj j * g = (g * MulAut.conj j * g⁻¹) * g := by rw [h1]
        _ = g * MulAut.conj j := by group
    rw [hcent] at hg1
    have hδp : orderOf (entrywiseAdjointAut Tag.G2 σ) = p :=
      (orderOf_entrywiseAdjointAut (by decide : 0 < Tag.G2.rank) σ).trans hσp
    have hdvd : orderOf g ∣ p := hδp ▸ orderOf_dvd_of_mem_zpowers hg1
    exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hgp.symm hdvd)


theorem fieldCoreAt_G2_even_of_dvd_pow_six {f : ℕ} (hf : 2 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (hdf : ∀ σ : K ≃+* K, orderOf σ = p → p ∣ Nat.card (fixSubfield σ) ^ 6 - 1)
    {x : MulAut (adjointGroup Tag.G2 K)} (hxp : orderOf x = p)
    (hxo : x ∉ (MulAut.conj : adjointGroup Tag.G2 K →* MulAut (adjointGroup Tag.G2 K)).range) :
    FieldCoreAt p x := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hNF := conj_normalForm_of_pointwise
    (CFSG.ComponentClassification.UnbalancedCatalog.even_G2_exact_automorphism_normal_form hf K
      hK).1
  obtain ⟨⟨y, σ⟩, hyσ, -⟩ := hNF x
  have hαp : orderOf (⟨x, Subgroup.mem_top x⟩ :
      (⊤ : Subgroup (MulAut (adjointGroup Tag.G2 K)))) = p := by
    rw [Subgroup.orderOf_mk]
    exact hxp
  obtain ⟨hσp, -, ⟨h, hh⟩, -⟩ := even_G2_noninner_prime_local_core_trivial hf hK hp ⊤ le_top
    ⟨x, Subgroup.mem_top x⟩ hxo hαp y σ hyσ
  by_cases h3 : 3 ≤ Nat.card (fixSubfield σ)
  · obtain ⟨-, -, hJC, -, -, -, -, hNδ, hnormal, -, hcent, -, -⟩ :=
      even_G2_canonical_field_centralizer_all_orders hf hK σ
    have hq : CFSG.IsQuasisimple (fixedFieldImage Tag.G2 σ) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv (fixedFieldImageEquiv σ)
        (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card (fixSubfield σ) h3)
    exact fieldCoreAt_of_conj (fieldCoreAt_entrywise_of_quasisimple hσp hJC hq hNδ hnormal hcent
      (not_coprime_card_adjointG2_of_dvd_pow_six (fixSubfield σ) hp (hdf σ hσp)))
      (MulAut.conj h) hh
  · have h2 : Nat.card (fixSubfield σ) = 2 := by
      have := Finite.one_lt_card (α := fixSubfield σ)
      omega
    have h63 := hdf σ hσp
    rw [h2] at h63
    have hp63 : p ∣ 63 := by simpa using h63
    have hp7' : p = 7 := by
      have hle := Nat.le_of_dvd (by norm_num) hp63
      have key : ∀ p ∈ Finset.Icc 7 63, p.Prime → p ∣ 63 → p = 7 := by decide
      exact key p (Finset.mem_Icc.2 ⟨hp7, hle⟩) hp hp63
    subst hp7'
    exact fieldCoreAt_of_conj (fieldCoreAt_entrywise_G2_two hf hK hp (by norm_num) hσp h2)
      (MulAut.conj h) hh

theorem crossCharTwoFamCat_G2_of_planes
    (h : ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.G2 q).Valid) (p : ℕ), p.Prime →
      7 ≤ p → p ≠ q.p → p ∣ q.card ^ 2 - 1 → InnerPlaneBalance p (CatT ⟨.G2 q, hv⟩)) :
    CrossCharTwoFamCat .G2 := by
  rintro ⟨d, hv⟩ ⟨q, hd⟩ p hp hp5 hc -
  change d = _ at hd
  subst hd
  have hpq : p ≠ q.p := fun h => hc (by simp [h])
  have hp7 := seven_le_of_prime_of_five_lt hp hp5
  have : Fact p.Prime := ⟨hp⟩
  have hq3 : 3 ≤ q.card := (TauCeti.LieTypeIndex.inStandardRange_iff (.G2 q)).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  obtain ⟨K, _, _, hK, hKc, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.g2 q hv
  have := hKc
  have hK' : Nat.card K = q.p ^ q.exponent := hK.trans (TauCeti.PrimePower.card_def q)
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne hp hpq
  have hinj := mulAut_conj_injective_adjointGroup (τ := Tag.G2) (K := K)
  have hin : InnerPlaneBalance p (adjointGroup Tag.G2 K) := by
    by_cases h2 : p ∣ q.card ^ 2 - 1
    · exact (h q hv p hp hp7 hpq h2).of_mulEquiv e.symm
    · exact (innerPlaneBalance_of_rankLE1 hp (conj_injective_cat_G2 q hv)
        (rankLE1_cat_G2 q hv hp (by omega) hpq h2)).of_mulEquiv e.symm
  have hout : OuterFields p (adjointGroup Tag.G2 K) := by
    obtain ⟨Q, _, _, Θ, -, hker⟩ := exists_hom_cyclic_G2 q hq3 K hK
    refine outerFields_of_hom Θ hp hinj (fun x hx _ => by rw [hker] at hx; exact hx) ?_
    by_cases hd6 : p ∣ Nat.card K ^ 6 - 1
    · refine Or.inr fun x hxp hxo => ?_
      have hxord := orderOf_eq_of_pow_eq_one_of_not_mem hp hxp hxo
      have hK1 : 1 ≤ Nat.card K := Nat.card_pos
      have hdf : ∀ σ : K ≃+* K, orderOf σ = p → p ∣ Nat.card (fixSubfield σ) ^ 6 - 1 :=
        fun σ hσp => dvd_pow_sub_one_of_cast_eq hK1 Nat.card_pos
          (card_fixSubfield_cast q.prime_p q.exponent_pos hK' hp hσp).symm hd6
      have hdvd : ∀ σ : K ≃+* K, orderOf σ = p →
          ¬ Nat.Coprime p (Nat.card (adjointGroup Tag.G2 (fixSubfield σ))) :=
        fun σ hσp => not_coprime_card_adjointG2_of_dvd_pow_six (fixSubfield σ) hp (hdf σ hσp)
      by_cases h2 : q.p = 2
      · have hK2 : Nat.card K = 2 ^ q.exponent := by rw [hK', h2]
        have hf2 : 2 ≤ q.exponent := by
          by_contra hlt
          have h1 : q.exponent = 1 := by have := q.exponent_pos; omega
          rw [TauCeti.PrimePower.card_def, h2, h1] at hq3
          omega
        exact fieldCoreAt_G2_even_of_dvd_pow_six hf2 K hK2 hp hp7 hdf hxord hxo
      · by_cases h3 : q.p = 3
        · have hK3 : Nat.card K = 3 ^ q.exponent := by rw [hK', h3]
          have : CharP K ReeTag.G2.prime := by
            rw [show ReeTag.G2.prime = 3 from rfl]
            exact finite_field_prime_power_characteristic Nat.prime_three q.exponent_pos hK3
          exact fieldCoreAt_G2_three q.exponent_pos K hK3 hp (by omega) hdvd hxord hxo
        · have hNF := conj_normalForm_of_pointwise
            (odd_F4_and_nonexceptional_G2_automorphism_normal_form q.prime_p h2 q.exponent_pos K
              hK' .G2 (Or.inr ⟨rfl, h3⟩)).1
          exact fieldCoreAt_of_oddInnerField q.prime_p h2 q.exponent_pos K hK' hNF hp hdvd
            hxord hxo
    · exact Or.inl (elemAbelian_card_eq_one_of_not_dvd hp (not_dvd_card_adjointG2 K hp hpK hd6))
  exact isLocallyBalancedAbs_two_of_model e hp hinj hin hout

theorem crossCharTwoFamCat_G2_of_classes (h1 : InnerPlaneBalanceAt .G2 1)
    (h2 : InnerPlaneBalanceAt .G2 2) : CrossCharTwoFamCat .G2 := by
  refine crossCharTwoFamCat_G2_of_planes fun q hv p hp hp7 hpq hd => ?_
  have hpK : ¬ p ∣ q.card := not_dvd_card_of_ne hp hpq
  have hdvd := orderOf_dvd_two_of_dvd_sq_sub_one hpK hd
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with he | he
  · exact h1 q hv p hp hp7 trivial hpq he
  · exact h2 q hv p hp hp7 trivial hpq he

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
