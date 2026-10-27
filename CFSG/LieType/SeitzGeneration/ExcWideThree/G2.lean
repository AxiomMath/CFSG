module

public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.Assembly
public import CFSG.LieType.SeitzGeneration.ExcSeitzGaps
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.Untwisted
public import CFSG.RankThree.Chevalley.SteinbergCFOddInnerFieldLocalCore
public import CFSG.RankThree.PartTwo.Sec19.SeitzG2F4G2
public import CFSG.HardMathSupport.Seitz.G2Noninner.Descent.Standard
public import CFSG.HardMathSupport.Seitz.G2Noninner.SubfieldPair.EntryAll
public import CFSG.HardMathSupport.Seitz.G2Noninner.SubfieldPair.PairOdd

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartOne.SEITZ2 CFSG.RankThree.PartOne.SEITZ3 CFSG.RankThree.PartOne.SEITZ6
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Seitz.G2Noninner
  CFSG.HardMathSupport.Seitz.G2Noninner.SubfieldPair

section Pair


theorem subfieldPairG2_odd_all_ge3 {K : Type} [Field K] [Finite K] {r : ℕ} [CharP K r]
    (hrp : r.Prime) (hr2 : r ≠ 2) (σ : K ≃+* K) {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hσ : orderOf σ = p) (g : adjointGroup .G2 K)
    (hne : (g2Fixed σ).map (MulAut.conj g).toMonoidHom ≠ g2Fixed σ) :
    Subgroup.closure ((g2Fixed σ : Set (adjointGroup .G2 K)) ∪
      ((g2Fixed σ).map (MulAut.conj g).toMonoidHom : Set (adjointGroup .G2 K))) = ⊤ := by
  have hr3 : 3 ≤ r := by
    have := hrp.two_le
    omega
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K r] at h'
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hrp Nat.prime_two).1 h')
  set R : Subgroup (adjointGroup .G2 K) := g2Fixed σ with hRdef
  set k : Subfield K := fixSubfield σ with hkdef
  have hKcard : Nat.card K = Nat.card k ^ p := by
    have := card_eq_card_fixSubfield_pow σ
    rwa [hσ] at this
  have hR : ∀ q < 12, ∀ c ∈ k, xp q c ∈ R := fun q hq c hc => rat_root_mem σ hq hc
  have hg : g ∉ R := fun hg => hne (map_conj_eq_self hg)
  obtain ⟨r₁, hr₁, r', hr', hbad⟩ := exists_bad_entryA σ h2 g hg
  set H : Subgroup (adjointGroup .G2 K) :=
    Subgroup.closure ((R : Set (adjointGroup .G2 K)) ∪
      ((R.map (MulAut.conj g).toMonoidHom : Subgroup (adjointGroup .G2 K)) :
        Set (adjointGroup .G2 K))) with hH
  have hRH : R ≤ H := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hRgH : R.map (MulAut.conj g).toMonoidHom ≤ H := fun x hx =>
    Subgroup.subset_closure (Or.inr hx)
  have hH1 : ∀ c ∈ k, xp 7 c ∈ H := fun c hc => hRH (hR 7 (by norm_num) c hc)
  have hH2 : ∀ c ∈ k, (r₁ * g * r') * xp 7 c * (r₁ * g * r')⁻¹ ∈ H := by
    intro c hc
    have h1 : r' * xp 7 c * r'⁻¹ ∈ R :=
      R.mul_mem (R.mul_mem hr' (hR 7 (by norm_num) c hc)) (R.inv_mem hr')
    have h2 : g * (r' * xp 7 c * r'⁻¹) * g⁻¹ ∈ R.map (MulAut.conj g).toMonoidHom :=
      ⟨_, h1, by simp [MulAut.conj_apply]⟩
    have h3 : r₁ * (g * (r' * xp 7 c * r'⁻¹) * g⁻¹) * r₁⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem (hRH hr₁) (hRgH h2)) (H.inv_mem (hRH hr₁))
    have e : (r₁ * g * r') * xp 7 c * (r₁ * g * r')⁻¹ =
        r₁ * (g * (r' * xp 7 c * r'⁻¹) * g⁻¹) * r₁⁻¹ := by group
    rw [e]
    exact h3
  have h7 : Full H 7 := full_seven_of_pair_odd hr3 k hp (Or.inr (by omega)) hKcard (r₁ * g * r')
    hH1 hH2 hbad
  have hm1 : (-1 : K) ≠ 1 := fun e => h2 (by linear_combination -e)
  exact eq_top_of_subfield_gen k (t := -1) (k.neg_mem k.one_mem) (neg_ne_zero.2 one_ne_zero) hm1
    (fun q hq c hc => hRH (hR q hq c hc)) h7

end Pair

section Descent


@[expose] def SubfieldPairG2AtGe3 (K : Type) [Field K] [Finite K] : Prop :=
  ∀ (σ : K ≃+* K) (p : ℕ), p.Prime → 3 ≤ p → orderOf σ = p → ∀ g : adjointGroup .G2 K,
    (g2Fixed σ).map (MulAut.conj g).toMonoidHom ≠ g2Fixed σ →
    Subgroup.closure ((g2Fixed σ : Set (adjointGroup .G2 K)) ∪
      ((g2Fixed σ).map (MulAut.conj g).toMonoidHom : Set (adjointGroup .G2 K))) = ⊤ ∨
      ¬ p ∣ Nat.card (g2Fixed σ)

theorem subfieldPairG2AtGe3 {K : Type} [Field K] [Finite K] (h2 : ringChar K ≠ 2) :
    SubfieldPairG2AtGe3 K := by
  intro σ p hp hp3 hσ g hne
  left
  have := ringChar.charP K
  have hrp : (ringChar K).Prime := by
    rcases CharP.char_is_prime_or_zero K (ringChar K) with h | h
    · exact h
    · exact absurd h (CharP.char_ne_zero_of_finite K (ringChar K))
  exact subfieldPairG2_odd_all_ge3 hrp h2 σ hp hp3 hσ g hne

theorem fieldAutData_G2_of_descent_ge3 {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hpair : SubfieldPairG2AtGe3 K)
    (hp3 : 3 ≤ p)
    (hrank : ∀ E : Subgroup (MulAut (adjointGroup .G2 K)), IsElementaryAbelian p E →
      Nat.card E = p ^ 2 → ∃ g : adjointGroup .G2 K, g ≠ 1 ∧ MulAut.conj g ∈ E)
    (hdesc : ∀ α : MulAut (adjointGroup .G2 K), IsOuterOfOrder p α →
      ∃ (h : adjointGroup .G2 K) (σ : K ≃+* K), orderOf σ = p ∧
        MulAut.conj h * α * (MulAut.conj h)⁻¹ = entrywiseAdjointAut .G2 σ) :
    FieldAutData (adjointGroup .G2 K) p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  refine fieldAutData_of_standard (MulAut.conj : adjointGroup .G2 K →* MulAut _).range
    {g | ∃ σ : K ≃+* K, orderOf σ = p ∧ g = entrywiseAdjointAut .G2 σ} ?_ ?_ ?_ ?_ ?_
  · intro E hE hEc
    have := hE
    exact hrank E hE hEc
  · intro α hα
    obtain ⟨h0, σ, hσ, h⟩ := hdesc α hα
    refine ⟨(MulAut.conj h0)⁻¹, ?_, entrywiseAdjointAut .G2 σ, ⟨σ, hσ, rfl⟩, ?_⟩
    · exact (MulAut.conj : adjointGroup .G2 K →* MulAut _).range.inv_mem ⟨h0, rfl⟩
    · rw [← h]
      group
  · rintro _ ⟨σ, hσ, rfl⟩ _ ⟨τ, hτ, rfl⟩
    rw [fixedSubgroup_entrywise_eq, fixedSubgroup_entrywise_eq]
    exact g2Fixed_congr (fixedField_eq_of_orderOf hℓ hf hK hσ hτ)
  · rintro _ ⟨σ, hσ, rfl⟩ _ x hx hc
    rw [fixedSubgroup_entrywise_eq] at hx hc
    exact eq_one_of_central_g2Fixed σ hx hc
  · rintro _ ⟨σ, hσ, rfl⟩ d ⟨g, rfl⟩ hne
    rw [fixedSubgroup_entrywise_eq] at hne ⊢
    exact hpair σ p hp hp3 hσ g hne

theorem fieldAutData_G2_odd_ne_three_ge3 {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3)
    (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f) (hp : p.Prime)
    (hpair : SubfieldPairG2AtGe3 K) (hp3 : 3 ≤ p) :
    FieldAutData (adjointGroup .G2 K) p := by
  classical
  obtain ⟨hNFpt, Θ, hΘspec, -, hker, -⟩ :=
    odd_F4_and_nonexceptional_G2_automorphism_normal_form hℓ hℓ2 hf K hK .G2
      (Or.inr ⟨rfl, hℓ3⟩)
  have hNF := conj_normalForm_of_pointwise hNFpt
  have hcyc : IsCyclic (K ≃+* K) := isCyclic_ringEquiv_of_card hℓ hf hK
  have : Finite (K ≃+* K) :=
    Finite.of_injective (fun σ : K ≃+* K => (σ : K → K)) DFunLike.coe_injective
  refine fieldAutData_G2_of_descent_ge3 hℓ hf hK hp hpair hp3 ?_ ?_
  · intro E hE hEc
    exact exists_conj_mem_of_plane_of_hom hp Θ hker E hEc
  · intro α hα
    obtain ⟨hord, hout⟩ := hα
    obtain ⟨⟨x, σ⟩, hxσ, -⟩ := hNF α
    obtain ⟨hσp, -, ⟨δ, hδ⟩, -⟩ :=
      odd_Chevalley_inner_field_noninner_prime_local_core_trivial .G2 hℓ hℓ2 hf K hK hNF hp ⊤
        le_top ⟨α, Subgroup.mem_top _⟩ (fun ⟨g, hg⟩ => hout g hg.symm)
        (by rw [Subgroup.orderOf_mk]; exact hord) x σ hxσ
    set τ : K ≃+* K := Θ δ with hτ
    have hΘτ : Θ (entrywiseAdjointAut .G2 τ) = τ := by
      refine hΘspec _ 1 τ fun h => ?_
      rw [coe_entrywiseAdjointAut]
      simp
    have hker1 : δ⁻¹ * entrywiseAdjointAut .G2 τ ∈ Θ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hΘτ, ← hτ, inv_mul_cancel]
    rw [hker] at hker1
    obtain ⟨g, hg⟩ := hker1
    have hcomm : τ * σ = σ * τ := by
      let _ := IsCyclic.commGroup (α := K ≃+* K)
      exact mul_comm τ σ
    have hcomm' : entrywiseAdjointAut .G2 σ * entrywiseAdjointAut .G2 τ =
        entrywiseAdjointAut .G2 τ * entrywiseAdjointAut .G2 σ := by
      rw [← entrywiseAdjointAut_mul, ← entrywiseAdjointAut_mul, hcomm]
    refine ⟨g⁻¹, σ, hσp, ?_⟩
    have hgi : MulAut.conj g⁻¹ = (δ⁻¹ * entrywiseAdjointAut .G2 τ)⁻¹ := by
      rw [map_inv, hg]
    rw [hgi]
    calc (δ⁻¹ * entrywiseAdjointAut .G2 τ)⁻¹ * α * (δ⁻¹ * entrywiseAdjointAut .G2 τ)⁻¹⁻¹
        = (entrywiseAdjointAut .G2 τ)⁻¹ * (δ * α * δ⁻¹) * entrywiseAdjointAut .G2 τ := by
          group
      _ = (entrywiseAdjointAut .G2 τ)⁻¹ * (entrywiseAdjointAut .G2 σ *
            entrywiseAdjointAut .G2 τ) := by rw [hδ, mul_assoc]
      _ = entrywiseAdjointAut .G2 σ := by
          rw [hcomm', inv_mul_cancel_left]

end Descent

section Wide

open CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.ExcOuterLeOne CFSG.AGLEmbeddingD2
  CFSG.Open TauCeti


theorem seitzExcOuterWide_G2_three : SeitzExcOuterWideForAt IsG2Index PrimeRange.three := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, -, ⟨q, hd⟩, hp3⟩
  subst hd
  have hp3' : p = 3 := hp3
  subst hp3'
  by_cases h2 : q.p = 2
  · exact CFSG.RankThree.PartTwo.Sec19.seitzG2NoninnerTwo ⟨.G2 q, hv⟩ 3 hp hp2 hpd hex E hE hc
      ⟨hout, rfl, ⟨q, rfl⟩, by simpa [TauCeti.LieTypeIndex.characteristic_G2] using h2⟩
  · have h3 : q.p ≠ 3 := fun h => hpd (by
      simpa [TauCeti.ValidLieTypeIndex.characteristic,
        TauCeti.LieTypeIndex.characteristic_G2] using h.symm)
    obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ :=
      exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv
    have hK' : Nat.card K = q.p ^ q.exponent := hK.trans (TauCeti.PrimePower.card_def q)
    have hpair : SubfieldPairG2AtGe3 K := subfieldPairG2AtGe3 (by
      rw [ringChar_eq_of_card_pow q.prime_p q.exponent_pos hK']
      exact h2)
    have hd : FieldAutData (adjointGroup .G2 K) 3 :=
      fieldAutData_G2_odd_ne_three_ge3 q.prime_p h2 h3 q.exponent_pos hK' Nat.prime_three hpair
        (le_refl 3)
    exact planeGen_outer_of_fieldAutData
      CFSG.AGLEmbedding.SeitzEqTwo.conj_injective_adjointGroup e Nat.prime_three hd hE hc hout

end Wide

end CFSG.LieType.SeitzGeneration.ExcWideThree
