module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenPSL
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCoordinateLinear
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoChar2C0Basic
public import CFSG.RankThree.SteinbergR3ECASymplecticPrimeSubfield
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.RootSp2
public import CFSG.RankThree.PartOne.KF.U4Model
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenE6
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTIUnitarySocleForms
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalEvenSymplecticSource

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LocalAnalysis.ComponentInitial LinearFlag FourGroupEvenCanonical
open CFSG.ComponentClassification.UnbalancedCatalog

theorem conj_map_fixedSubgroup_eq_inner {P : Type*} [Group P]
    (hcj : Function.Injective (MulAut.conj : P →* MulAut P)) (β : MulAut P) :
    (fixedSubgroup β).map MulAut.conj = inner P ⊓ centralizer {β} := by
  ext φ
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, rfl⟩, mem_centralizer_singleton_iff.mpr ?_⟩
    have hx' : β x = x := hx
    rw [RankThree.CASymplecticSubfield.mul_conj_eq β x, hx']
  · rintro ⟨⟨x, rfl⟩, hx⟩
    refine ⟨x, ?_, rfl⟩
    have h := mem_centralizer_singleton_iff.mp hx
    rw [RankThree.CASymplecticSubfield.mul_conj_eq β x] at h
    exact (hcj (mul_right_cancel h)).symm

@[expose] def fixedInnerEquiv {P : Type*} [Group P]
    (hcj : Function.Injective (MulAut.conj : P →* MulAut P)) (β : MulAut P) :
    fixedSubgroup β ≃* ↥(inner P ⊓ centralizer {β}) :=
  ((fixedSubgroup β).equivMapOfInjective MulAut.conj hcj).trans
    (MulEquiv.subgroupCongr (conj_map_fixedSubgroup_eq_inner hcj β))

variable {K : Type} [Field K] {n : ℕ}

theorem nonempty_fixed_canonical_equiv {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : 3 ≤ n) (C : GL (Fin n) K)
    (hC : (C : Matrix (Fin n) (Fin n) K) = 1 ∨
      ∃ r, n = 2 * r ∧ (C : Matrix (Fin n) (Fin n) K) = UnitaryHigher.blockSwapJ n r) :
    Nonempty (fixedSubgroup (conjAut n K C * dualAut n K) ≃*
      matrixIsometryGroup (C : Matrix (Fin n) (Fin n) K)) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have hCan : IsCanonicalGram (C : Matrix (Fin n) (Fin n) K) := by
    rcases hC with h1 | ⟨r, hr, hJ⟩
    · rw [h1]
      exact isCanonicalGram_one
    · rw [hJ]
      exact isCanonicalGram_blockSwapJ (by omega)
  obtain ⟨hinj, hNinn, -, -, hNC, -, -⟩ :=
    even_linear_canonical_graph_symplectic_centralizers hf hK hn C hC
  have hcj := ProjectivePlane.conj_injective_projectiveSL (F := K) hn
  have heq : inner (projectiveSL n K) ⊓ centralizer {conjAut n K C * dualAut n K} =
      (matrixIsometryGroup (C : Matrix (Fin n) (Fin n) K)).map (conjAut n K) := by
    refine le_antisymm ?_ (le_inf hNinn hNC)
    rintro φ ⟨⟨y, rfl⟩, hy⟩
    obtain ⟨g, rfl⟩ := LinearFlag.proj_surjective n K y
    rw [← LinearFlag.conjAut_toGL] at hy ⊢
    obtain ⟨g', hg', hgg'⟩ :=
      (commute_pureGraph_conjAut_iff hCan hn _).mp (mem_centralizer_singleton_iff.mp hy).symm
    exact ⟨g', hg', hgg'.symm⟩
  exact ⟨((fixedInnerEquiv hcj _).trans (MulEquiv.subgroupCongr heq)).trans
    ((MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, range_subtype])).trans
      (MonoidHom.ofInjective hinj).symm)⟩

theorem isCharacteristicP_fixed_dualAut {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : 4 ≤ n) (hev : Even n) : IsCharacteristicP 2 (fixedSubgroup (dualAut n K)) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  obtain ⟨r, hr⟩ := hev
  have hcj := ProjectivePlane.conj_injective_projectiveSL (F := K) (by omega : 3 ≤ n)
  obtain ⟨-, -, -, -, -, -, -, -, -, hRinn, hRC, hRn, hCR, hQ, -⟩ :=
    even_linear_nonalternating_graph_radical hf hK (show n = 2 * r by omega) hn
      (⟨0, by omega⟩ : Fin n)
  have hX : IsCharacteristicP 2 ↥(inner (projectiveSL n K) ⊓ centralizer {dualAut n K}) :=
    RankTwoChar2C0.isCharacteristicP_of_le_normalizer (le_inf hRinn hRC)
      (hQ.to_le le_sup_left)
      (fun x hx => (normal_subgroupOf_iff_le_normalizer hRC).1 hRn hx.2)
      (fun c hc hcR => by
        have hc' := mem_inf.2 ⟨hc.2, hcR⟩
        rw [hCR] at hc'
        obtain ⟨k, hk⟩ := hQ ⟨c, hc'⟩
        exact ⟨k, by simpa using congrArg Subtype.val hk⟩)
  exact LocalAnalysis.ComponentInitial.isCharacteristicP_of_mulEquiv (fixedInnerEquiv hcj _).symm
    hX

theorem evenLieConclusion_of_simple {X Y : Type} [Group X] [Finite X] [Group Y]
    [IsSimpleGroup Y] (e : X ≃* Y)
    (hY : (∃ (τ' : StatedLieTag) (n' f' : ℕ), StatedLieAdmissible τ' n' 2 f' ∧
        Blueprint.LieModel Y τ' n' 2 f') ∨ Nonempty (Y ≃* alternatingGroup (Fin 6)) ∨
      Blueprint.LieModel Y .PSU 3 3 1)
    {P : Subgroup X} (hP : IsPComponent 2 P) : EvenLieConclusion P := by
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
  rcases hY with ⟨τ', n', f', hadm, hm⟩ | ⟨⟨eA⟩⟩ | hm
  · exact Or.inl ⟨τ', n', f', hadm, LieType.CurtisTits.lieModel_of_mulEquiv eZ.symm hm⟩
  · exact Or.inr (Or.inl ⟨eZ.trans eA⟩)
  · exact Or.inr (Or.inr (LieType.CurtisTits.lieModel_of_mulEquiv eZ.symm hm))

theorem evenLieConclusion_statedSp [Finite K] {f r : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hr : 1 ≤ r) (M : Subgroup (StatedSp r K)) (hM : IsPComponent 2 M) : EvenLieConclusion M := by
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
      exact evenLieConclusion_of_simple
        ((ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne K).symm.trans e₂)
        (Or.inl ⟨.PSL, 2, f, hadm, Or.inl ⟨by decide, hstated⟩⟩) hM
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
      exact evenLieConclusion_of_simple eProj.symm
        (Or.inl ⟨.PSp, r, f, hadm, Or.inl ⟨by decide, hadm, K, inferInstance, inferInstance, hK,
          ⟨MulEquiv.refl _⟩⟩⟩) hM

theorem evenPSLGraphInput_holds : EvenPSLGraphInput := by
  intro n K _ _ f hf hK hn A hα _ P hP
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have hc := CatalogueBLinearHigherB.congr_pureGraph (n := n) (K := K) A
  have hsq : CatalogueBGraphForm.pureGraphAction n K A ^ 2 = 1 := hα ▸ pow_orderOf_eq_one _
  have hα2 : (conjAut n K A * dualAut n K) ^ 2 = 1 := by
    apply (MulAut.congr (CatalogueBLinearHigherB.nativeEquiv n K)).injective
    rw [map_pow, hc, hsq, map_one]
  obtain ⟨-, ⟨H, C, -, hconj, hCcase⟩, -⟩ :=
    UnitaryHigher.even_linear_pure_graph_involution_normal_forms hf hK hn A hα2
  have hc2 : MulAut.congr (conjAut n K H) (conjAut n K C * dualAut n K) =
      conjAut n K A * dualAut n K :=
    (MulEquiv.ext fun _ => rfl : MulAut.congr (conjAut n K H) (conjAut n K C * dualAut n K) =
      _).trans hconj.symm
  let Ψ : fixedSubgroup (CatalogueBGraphForm.pureGraphAction n K A) ≃*
      fixedSubgroup (conjAut n K C * dualAut n K) :=
    ((MulEquiv.subgroupCongr (congrArg fixedSubgroup hc)).symm.trans
      (fixedSubgroupCongrEquiv _ _).symm).trans
    ((MulEquiv.subgroupCongr (congrArg fixedSubgroup hc2)).symm.trans
      (fixedSubgroupCongrEquiv _ _).symm)
  have hC' : (C : Matrix (Fin n) (Fin n) K) = 1 ∨
      ∃ r, n = 2 * r ∧ (C : Matrix (Fin n) (Fin n) K) = UnitaryHigher.blockSwapJ n r := by
    rcases hCcase with ⟨h1, -⟩ | ⟨r, hr, hJ, -⟩
    · exact Or.inl h1
    · exact Or.inr ⟨r, hr, hJ⟩
  obtain ⟨Φ⟩ := nonempty_fixed_canonical_equiv hf hK hn C hC'
  by_cases heven : (C : Matrix (Fin n) (Fin n) K) = 1 ∧ Even n
  · exfalso
    obtain ⟨h1, hev⟩ := heven
    have hβ : conjAut n K C * dualAut n K = dualAut n K := by
      rw [show C = 1 from Units.ext h1, map_one, one_mul]
    have hch : IsCharacteristicP 2 (fixedSubgroup (conjAut n K C * dualAut n K)) := by
      rw [hβ]
      exact isCharacteristicP_fixed_dualAut hf hK (by obtain ⟨r, hr⟩ := hev; omega) hev
    exact not_isPComponent_of_isCharacteristicP
      (LocalAnalysis.ComponentInitial.isCharacteristicP_of_mulEquiv Ψ.symm hch) P hP
  obtain ⟨r, hr1, ⟨eSp⟩⟩ : ∃ r, 1 ≤ r ∧
      Nonempty (matrixIsometryGroup (C : Matrix (Fin n) (Fin n) K) ≃* StatedSp r K) := by
    rcases hC' with h1 | ⟨r, hr, hJ⟩
    · have hodd : Odd n := by
        rcases Nat.even_or_odd n with hev | hodd
        · exact absurd ⟨h1, hev⟩ heven
        · exact hodd
      obtain ⟨r, hr⟩ := hodd
      have hC1 : (C : Matrix (Fin n) (Fin n) K) =
          ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by rw [h1, Units.val_one]
      obtain ⟨e₂⟩ := OutcomeLocal.nonempty_altIsometry_mulEquiv_statedSp _
        (OutcomeLocal.dotForm_restrict_isAlt (k := K) (n := n))
        (OutcomeLocal.dotForm_restrict_nondegenerate hr) (OutcomeLocal.finrank_dotForm_ker hr)
      exact ⟨r, by omega, ⟨((MulEquiv.subgroupCongr (congrArg matrixIsometryGroup hC1)).trans
        (OutcomeLocal.oneRestrictEquiv hr)).trans e₂⟩⟩
    · exact ⟨r, by omega, ⟨(MulEquiv.subgroupCongr (congrArg matrixIsometryGroup hJ)).trans
        (OutcomeLocal.blockSwapIsometryEquivStatedSp (by omega))⟩⟩
  have : Finite (GL (Fin r ⊕ Fin r) K) := Finite.of_injective Units.val Units.val_injective
  exact evenLieConclusion_of_mulEquiv ((Ψ.trans Φ).trans eSp)
    (fun M hM => evenLieConclusion_statedSp hf hK hr1 M hM) hP

theorem evenOuterFamilyInput_PSL_holds : EvenOuterFamilyInput .PSL :=
  evenOuterFamilyInput_PSL evenPSLGraphInput_holds

end CFSG.ComponentClassification.CatLeafProof
