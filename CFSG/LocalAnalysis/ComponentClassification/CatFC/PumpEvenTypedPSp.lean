module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpEvenTyped
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenPSp

public section

namespace CFSG.ComponentClassification.CatFC

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LocalAnalysis.ComponentInitial SymplecticFlag SymplecticHigher
open CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.ComponentClassification.CatLeafProof

theorem evenPSpTypedConclusion_of_mulEquiv {τ : StatedLieTag} {n f : ℕ} {X Y : Type} [Group X]
    [Group Y] [Finite X] [Finite Y] (Φ : X ≃* Y)
    (h : ∀ M : Subgroup Y, IsPComponent 2 M → EvenOuterTypedConclusion τ n f M) {P : Subgroup X}
    (hP : IsPComponent 2 P) : EvenOuterTypedConclusion τ n f P := by
  have hM := LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 Φ hP
  obtain ⟨eZ⟩ := GrSLit.nonempty_fusionZStar_equiv_of_mulEquiv'
    (P.equivMapOfInjective Φ.toMonoidHom Φ.injective)
  rcases h _ hM with ⟨τ', n', f', hadm, hL, hc⟩ | ⟨⟨e⟩⟩ | hL
  · exact Or.inl ⟨τ', n', f', hadm, LieType.CurtisTits.lieModel_of_mulEquiv eZ.symm hL, hc⟩
  · exact Or.inr (Or.inl ⟨eZ.trans e⟩)
  · exact Or.inr (Or.inr (LieType.CurtisTits.lieModel_of_mulEquiv eZ.symm hL))

theorem evenPSpTypedConclusion_of_simple {τ : StatedLieTag} {n f : ℕ} {X Y : Type} [Group X]
    [Finite X] [Group Y] [IsSimpleGroup Y] (e : X ≃* Y)
    (hY : (∃ (τ' : StatedLieTag) (n' f' : ℕ), StatedLieAdmissible τ' n' 2 f' ∧
        Blueprint.LieModel Y τ' n' 2 f' ∧ (τ' ≠ .PSL ∨ n' ≠ 4)) ∨
      Nonempty (Y ≃* alternatingGroup (Fin 6)) ∨ Blueprint.LieModel Y .PSU 3 3 1)
    {P : Subgroup X} (hP : IsPComponent 2 P) : EvenOuterTypedConclusion τ n f P := by
  have hXs : IsSimpleGroup X := e.isSimpleGroup
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsub := ((CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 P).mp hP).1
  have htop : P = ⊤ := by
    rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hXs hsub with h | h
    · exfalso
      have hnt := GrSLit.nontrivial_of_isPComponent hP
      rw [h] at hnt
      exact not_nontrivial_iff_subsingleton.mpr inferInstance hnt
    · exact h
  obtain ⟨eZ⟩ := GrSLit.nonempty_fusionZStar_equiv_of_simple hP
    (((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).trans e)
  rcases hY with ⟨τ', n', f', hadm, hm, hne⟩ | ⟨⟨eA⟩⟩ | hm
  · exact EvenOuterTypedConclusion.of_ne hadm (LieType.CurtisTits.lieModel_of_mulEquiv eZ.symm hm) hne
  · exact Or.inr (Or.inl ⟨eZ.trans eA⟩)
  · exact Or.inr (Or.inr (LieType.CurtisTits.lieModel_of_mulEquiv eZ.symm hm))

theorem evenPSpTypedConclusion_statedSp {τ : StatedLieTag} {N F : ℕ} {K : Type} [Field K]
    [Finite K] {f r : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hr : 1 ≤ r)
    (M : Subgroup (StatedSp r K)) (hM : IsPComponent 2 M) :
    EvenOuterTypedConclusion τ N F M := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (GL (Fin r ⊕ Fin r) K) := Finite.of_injective Units.val Units.val_injective
  have hSp := SymplecticFlag.card_statedSp (K := K) r
  rcases (by omega : r = 1 ∨ 2 ≤ r) with rfl | hr2
  · rcases (by omega : f = 1 ∨ 2 ≤ f) with rfl | hf2
    · exfalso
      have hcard : Nat.card (StatedSp 1 K) = 2 ^ 1 * 3 ^ 1 := by
        rw [hSp, hK]
        decide
      have : Fintype (StatedSp 1 K) := Fintype.ofFinite _
      have : Group.IsSolvable (StatedSp 1 K) :=
        Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 1) (b := 1)
          Nat.prime_two Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, hcard])
      exact GrSLit.not_isPComponent_of_isSolvable M hM
    · obtain ⟨e₂⟩ := RankThree.PartOne.KFU.nonempty_SL2_mulEquiv_statedProj (F := K)
      have h4 : 4 ≤ 2 ^ f :=
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
      have hadm : StatedLieAdmissible .PSL 2 2 f := ⟨Nat.prime_two, hf, le_rfl,
        fun h => by rw [Prod.mk.injEq] at h; omega,
        fun h => by rw [Prod.mk.injEq] at h; omega⟩
      have hstated : StatedClassicalModel (StatedProj (StatedSL 2 K)) .PSL 2 2 f :=
        ⟨hadm, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
      have := (LieType.Simplicity.fam_PSL_simplicity _ 2 2 f hstated).2
      exact evenPSpTypedConclusion_of_simple
        ((ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne K).symm.trans e₂)
        (Or.inl ⟨.PSL, 2, f, hadm, Or.inl ⟨by decide, hstated⟩, Or.inr (by decide)⟩) hM
  · by_cases h21 : r = 2 ∧ f = 1
    · obtain ⟨rfl, rfl⟩ := h21
      have := Fintype.ofFinite K
      have : IsSimpleGroup (alternatingGroup (Fin 6)) :=
        alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)
      obtain ⟨eS⟩ := RankThree.CASymplecticSubfield.nonempty_statedSp_two_mulEquiv_perm (k := K)
        (by rw [← Nat.card_eq_fintype_card, hK, pow_one])
      obtain ⟨eA⟩ := RankThree.CASymplecticSubfield.nonempty_commutator_mulEquiv_alternating eS
      obtain ⟨eZ⟩ := nonempty_fusionZStar_equiv_of_derived (MulEquiv.refl _) eA hM
      exact Or.inr (Or.inl ⟨eZ⟩)
    · have hcond : (Infinite K ∨ 4 ≤ Nat.card K) ∨ (Nat.card K = 3 ∧ 2 ≤ r) ∨
          (Nat.card K = 2 ∧ 3 ≤ r) := by
        rcases (by omega : f = 1 ∨ 2 ≤ f) with rfl | hf2
        · exact Or.inr (Or.inr ⟨by rw [hK, pow_one], by omega⟩)
        · refine Or.inl (Or.inr ?_)
          rw [hK]
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
      have := ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K r hr hcond
      obtain ⟨-, -, -, -, ⟨eProj⟩⟩ :=
        SymmetricLocal.small_standard_source_even_simple_symplectic_parameters_stated
          (X := StatedSp r K) hK hr ⟨MulEquiv.refl _⟩
      have hadm : StatedLieAdmissible .PSp r 2 f := ⟨Nat.prime_two, hf, hr2, fun h => by
        rw [Prod.mk.injEq] at h
        obtain ⟨rfl, h2⟩ := h
        exact h21 ⟨rfl, Nat.pow_right_injective le_rfl (h2.trans (pow_one 2).symm)⟩⟩
      exact evenPSpTypedConclusion_of_simple eProj.symm
        (Or.inl ⟨.PSp, r, f, hadm, Or.inl ⟨by decide, hadm, K, inferInstance, inferInstance, hK,
          ⟨MulEquiv.refl _⟩⟩, Or.inl (by decide)⟩) hM

theorem even_sp_field_PSpTyped {τ : StatedLieTag} {N F : ℕ} {r : ℕ} {K : Type} [Field K]
    {f : ℕ} (hr : 2 ≤ r) (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    {a : MulAut (StatedProj (StatedSp r K))} (ha : a * a = 1) (g : StatedSp r K)
    (σ : K ≃+* K) (hag : a = spInner r K g * fieldAut r K σ) (hσ : σ ≠ 1)
    (M : Subgroup (fixedSubgroup a)) (hM : IsPComponent 2 M) :
    EvenOuterTypedConclusion τ N F M := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : NeZero r := ⟨by omega⟩
  obtain ⟨hfe, hσx, hk, -, -, -, -, -, -, -, h, hah⟩ :=
    even_symplectic_quadratic_involution_descent (by omega : 1 ≤ r) hf hK ha g σ hag hσ
  have hf2 : 2 ≤ f := by
    obtain ⟨t, ht⟩ := hfe
    omega
  obtain ⟨hNinn, -, hιjinj, ⟨act, -, Θ, hΘ⟩, -, -⟩ :=
    even_symplectic_field_centralizers_and_intermediate_odd_cores hr hf2 hfe hK σ hσx
  have hN : inner (StatedProj (StatedSp r K)) ⊓ centralizer {fieldAut r K σ} =
      ((spInner r K).comp (subfieldSpHom r (descentField σ))).range := by
    apply le_antisymm
    · intro x hx
      have hxE : x ∈ spSemilinearAutGroup r K ⊓ centralizer {fieldAut r K σ} :=
        ⟨inner_le_spSemilinearAutGroup hx.1, hx.2⟩
      obtain ⟨⟨g', φ⟩, hg'⟩ := Θ.surjective ⟨x, hxE⟩
      have hx' : x = spInner r K (subfieldSpHom r (descentField σ) g') * fieldAut r K φ := by
        rw [← hΘ, hg']
      have hφ : φ = 1 := by
        by_contra hφ
        refine (spInner_mul_fieldAut_not_mem_inner_iff
          (subfieldSpHom r (descentField σ) g') φ).mpr hφ ?_
        rw [← hx']
        exact hx.1
      subst hφ
      refine ⟨g', ?_⟩
      rw [hx', map_one, mul_one]
      rfl
    · rintro _ ⟨g', rfl⟩
      refine ⟨hNinn ⟨g', rfl⟩, ?_⟩
      have h1 := (Θ ⟨g', 1⟩).2.2
      rw [hΘ, map_one, mul_one] at h1
      exact h1
  have hc : MulAut.congr (conjAut r K ⟨h, statedSp_le_gsp h.2⟩) (fieldAut r K σ) = a :=
    (MulEquiv.ext fun _ => rfl : MulAut.congr (conjAut r K ⟨h, statedSp_le_gsp h.2⟩)
      (fieldAut r K σ) = _).trans hah.symm
  have hcj := conj_injective_statedProj_statedSp_charTwo (r := r) (K := K)
  let Φ : fixedSubgroup a ≃* StatedSp r (descentField σ) :=
    (MulEquiv.subgroupCongr (congrArg fixedSubgroup hc)).symm.trans
      ((fixedSubgroupCongrEquiv _ _).symm.trans
        ((fixedInnerEquiv hcj _).trans
          ((MulEquiv.subgroupCongr hN).trans (MonoidHom.ofInjective hιjinj).symm)))
  exact evenPSpTypedConclusion_of_mulEquiv (τ := τ) (n := N) (f := F) Φ
    (fun M' hM' => evenPSpTypedConclusion_statedSp (by omega) hk (by omega) M' hM') hM

theorem even_sp_suzuki_PSpTyped {τ : StatedLieTag} {N F : ℕ}
    {K : Type} [Field K] {m : ℕ} (hm : 1 ≤ m) [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ (2 * m + 1))
    {a : MulAut (StatedProj (StatedSp 2 K))} (ha : a * a = 1) (s : StatedSp 2 K)
    (has : a = spInner 2 K s * exceptionalAut K ^ (2 * m + 1))
    (M : Subgroup (fixedSubgroup a)) (hM : IsPComponent 2 M) :
    EvenOuterTypedConclusion τ N F M := by
  subst has
  obtain ⟨χ, -, hχ⟩ := OutcomeLocal.exists_inner_conj_eta hK ha
  obtain ⟨ψ, -, hψinj, -, hrange, -⟩ :=
    even_symplectic_two_suzuki_full_centralizer_odd_core hm hK (exceptionalAut K)
      exceptionalAut_proj
  obtain ⟨-, -, hSz⟩ := LieType.Ree.suzuki_simple hm hK
  have hcj := conj_injective_statedProj_statedSp_charTwo (r := 2) (K := K)
  have hc : MulAut.congr χ (exceptionalAut K ^ (2 * m + 1)) =
      spInner 2 K s * exceptionalAut K ^ (2 * m + 1) :=
    (MulEquiv.ext fun _ => rfl : MulAut.congr χ (exceptionalAut K ^ (2 * m + 1)) = _).trans
      hχ.symm
  let Φ : fixedSubgroup (spInner 2 K s * exceptionalAut K ^ (2 * m + 1)) ≃*
      Blueprint.suzukiGroup m K :=
    (MulEquiv.subgroupCongr (congrArg fixedSubgroup hc)).symm.trans
      ((fixedSubgroupCongrEquiv _ _).symm.trans
        ((fixedInnerEquiv hcj _).trans
          ((MulEquiv.subgroupCongr hrange.symm).trans (MonoidHom.ofInjective hψinj).symm)))
  have hadm : StatedLieAdmissible .twistedB2 0 2 (2 * m + 1) :=
    ⟨Nat.prime_two, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩
  exact evenPSpTypedConclusion_of_simple Φ (Or.inl ⟨.twistedB2, 0, 2 * m + 1, hadm,
    Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, m, hm, K, inferInstance, inferInstance, rfl, hK,
      ⟨MulEquiv.refl _⟩⟩)), Or.inl (by decide)⟩) hM

theorem evenOuterTypedFamilyInput_PSp :
    EvenOuterTypedFamilyInput .PSp := by
  intro J _ n f hadm hm α hα hαo P hP
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_psp_of_lieModel hadm hm
  have hf : 1 ≤ f := hadm.2.1
  have hn : 2 ≤ n := hadm.2.2.1
  have hnf : (n, 2 ^ f) ≠ (2, 2) := hadm.2.2.2
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : NeZero n := ⟨by omega⟩
  have : Finite J := Finite.of_equiv _ e.symm.toEquiv
  have hβ : orderOf (MulAut.congr e α) = 2 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective α).trans hα
  have hβ2 : MulAut.congr e α * MulAut.congr e α = 1 := by
    rw [← sq, ← hβ, pow_orderOf_eq_one]
  have hβo : MulAut.congr e α ∉ inner (StatedProj (StatedSp n K)) := by
    rw [FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  refine evenPSpTypedConclusion_of_mulEquiv (fixedSubgroupCongrEquiv e α) ?_ hP
  have hE : MulAut.congr e α ∈ spSemilinearAutGroup n K →
      ∀ M : Subgroup (fixedSubgroup (MulAut.congr e α)), IsPComponent 2 M →
        EvenOuterTypedConclusion .PSp n f M := by
    intro hmem M hM
    obtain ⟨g, σ, hgσ⟩ := exists_eq_spInner_mul_fieldAut hmem
    have hσ : σ ≠ 1 := by
      rintro rfl
      rw [map_one, mul_one] at hgσ
      exact hβo (hgσ ▸ spInner_mem_inner g)
    exact even_sp_field_PSpTyped hn hf hK hβ2 g σ hgσ hσ M hM
  by_cases hn3 : 3 ≤ n
  · apply hE
    rw [(SymplecticHigher.automorphism_generation (K := K) hn3).1]
    exact mem_top _
  · obtain rfl : n = 2 := by omega
    obtain ⟨-, -, -, -, ⟨γ, hγ⟩, hall⟩ := even_symplectic_two_exterior_square_automorphism hf hK
    obtain ⟨-, -, -, -, -, -, -, -, -, -, heven, hodd⟩ := hall γ hγ
    rcases Nat.even_or_odd f with hfe | hfo
    · exact hE (heven hfe _ hβ)
    · obtain ⟨s, hs⟩ := hodd hfo _ hβ hβo
      obtain ⟨m, rfl⟩ := hfo
      have hm : 1 ≤ m := by
        by_contra h0
        obtain rfl : m = 0 := by omega
        exact hnf rfl
      rw [eq_exceptionalAut hγ] at hs
      exact fun M hM => even_sp_suzuki_PSpTyped hm hK hβ2 s hs M hM

end CFSG.ComponentClassification.CatFC
