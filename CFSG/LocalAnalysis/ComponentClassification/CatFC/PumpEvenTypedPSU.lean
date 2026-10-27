module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpEvenTyped
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenPSU

public section

namespace CFSG.ComponentClassification.CatFC

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.CatLeafProof
open CFSG.LocalAnalysis.ComponentInitial LinearFlag FourGroupEvenCanonical
open CFSG.ComponentClassification.UnbalancedCatalog

theorem evenOuterTypedConclusion_of_mulEquiv {τ : StatedLieTag} {n f : ℕ} {X Y : Type} [Group X]
    [Group Y] [Finite X] [Finite Y] (Φ : X ≃* Y)
    (h : ∀ M : Subgroup Y, IsPComponent 2 M → EvenOuterTypedConclusion τ n f M) {P : Subgroup X}
    (hP : IsPComponent 2 P) : EvenOuterTypedConclusion τ n f P := by
  have hM := LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 Φ hP
  obtain ⟨eZ⟩ := GrSLit.nonempty_fusionZStar_equiv_of_mulEquiv'
    (P.equivMapOfInjective Φ.toMonoidHom Φ.injective)
  rcases h _ hM with ⟨τ', n', f', hadm, hL, himp⟩ | ⟨⟨e⟩⟩ | hL
  · exact Or.inl ⟨τ', n', f', hadm, LieType.CurtisTits.lieModel_of_mulEquiv eZ.symm hL, himp⟩
  · exact Or.inr (Or.inl ⟨eZ.trans e⟩)
  · exact Or.inr (Or.inr (LieType.CurtisTits.lieModel_of_mulEquiv eZ.symm hL))

theorem evenOuterTypedConclusion_of_simple {τ : StatedLieTag} {n f : ℕ} {X Y : Type} [Group X]
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

theorem evenOuterTypedConclusion_statedSp {τ : StatedLieTag} {n₀ f₀ : ℕ} {K : Type} [Field K]
    [Finite K] {f r : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hr : 1 ≤ r)
    (M : Subgroup (StatedSp r K)) (hM : IsPComponent 2 M) :
    EvenOuterTypedConclusion τ n₀ f₀ M := by
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
      exact evenOuterTypedConclusion_of_simple
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
      exact evenOuterTypedConclusion_of_simple eProj.symm
        (Or.inl ⟨.PSp, r, f, hadm, Or.inl ⟨by decide, hadm, K, inferInstance, inferInstance, hK,
          ⟨MulEquiv.refl _⟩⟩, Or.inl (by decide)⟩) hM

theorem evenOuterTypedFamilyInput_PSU : EvenOuterTypedFamilyInput .PSU := by
  intro J _ n f hadm hm α hα hαo P hP
  obtain ⟨K, _, h, ⟨ψ⟩⟩ := nonempty_mulEquiv_primeFormP_of_lieModel hadm hm
  have : Finite K := h.finite
  have : Finite J := Finite.of_equiv _ ψ.symm.toEquiv
  rcases even_unitary_outer_fixed_cases hadm hm α hα hαo with
    hch | ⟨k, _, _, hk, r, hr, -, ⟨Φ⟩⟩
  · exact absurd hP (not_isPComponent_of_isCharacteristicP hch P)
  · have : Finite (GL (Fin r ⊕ Fin r) k) := Finite.of_injective Units.val Units.val_injective
    exact evenOuterTypedConclusion_of_mulEquiv Φ
      (fun M hM => evenOuterTypedConclusion_statedSp hadm.2.1 hk hr M hM) hP

end CFSG.ComponentClassification.CatFC
