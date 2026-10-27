module

public import CFSG.LocalAnalysis.AGLEmbedding.UnitaryFacts
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryModel
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherRankOneSchreier

public section

namespace CFSG.AGLEmbedding.UnitaryModel

open CFSG.BenderSuzuki.MatrixGroups CFSG.UnitaryThreeRecognition.Model
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem isSolvable_of_stabilizer {Γ : Type*} [Group Γ] (U : Subgroup Γ)
    (hB : Group.IsSolvable ↥(Subgroup.normalizer (U : Set Γ)))
    (hO : Group.IsSolvable (Outer Γ)) (A : Subgroup (MulAut Γ))
    (hA : ∀ α ∈ A, U.map α.toMonoidHom = U) : Group.IsSolvable A := by
  set S₀ : Subgroup Γ := A.comap (MulAut.conj : Γ →* MulAut Γ) with hS₀
  have hle : S₀ ≤ Subgroup.normalizer (U : Set Γ) := by
    intro x hx
    have h1 := hA _ hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h2 : (MulAut.conj x) y ∈ U ↔ y ∈ U := by
      conv_lhs => rw [← h1]
      rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
    rw [← h2]
    simp [MulAut.conj_apply]
  have : Group.IsSolvable S₀ :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  let f : S₀ →* A := ((MulAut.conj : Γ →* MulAut Γ).comp S₀.subtype).codRestrict A fun x => x.2
  let g : A →* Outer Γ := (QuotientGroup.mk' (inner Γ)).comp A.subtype
  refine Group.isSolvable_of_ker_le_range f g ?_
  intro α hα
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hα
  obtain ⟨x, hx⟩ := hα
  refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
  show (MulAut.conj : Γ →* MulAut Γ) x ∈ A
  rw [hx]
  exact α.2

section Borel

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {p f : ℕ}
  (hK : Nat.card K = (p ^ f) ^ 2) (hfix : Nat.card {x : K // J.conj x = x} = p ^ f)

include hK hfix

theorem isSolvable_stabilizer_pinf [Fact p.Prime] :
    Group.IsSolvable
      (MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) (pinf J hJ)) := by
  set S := MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) (pinf J hJ) with hS
  have hRS : rootGroup J hJ ≤ S := rootGroup_le_stabilizer J hJ
  have : ((rootGroup J hJ).subgroupOf S).Normal :=
    rootGroup_subgroupOf_stabilizer_normal J hJ (p ^ f) hK hfix
  have hRsolv : Group.IsSolvable ↥(rootGroup J hJ) := by
    have := (isPGroup_rootGroup J hJ hK hfix).isNilpotent
    infer_instance
  have hRSsolv : Group.IsSolvable ↥((rootGroup J hJ).subgroupOf S) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hRS).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hRS).injective
  have hmk : ∀ s : S, ∃ t ∈ torusGroup J hJ, ∃ ht : t ∈ S,
      (QuotientGroup.mk s : S ⧸ (rootGroup J hJ).subgroupOf S) = QuotientGroup.mk ⟨t, ht⟩ := by
    intro s
    have hgmem : (s : ProjectiveSpecialUnitaryMatrixGroup J) ∈
        ((rootGroup J hJ ⊔ torusGroup J hJ : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) :
          Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
      rw [rootGroup_sup_torusGroup J hJ (p ^ f) hK hfix]
      exact s.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _
      (torusGroup_le_normalizer_rootGroup J hJ)] at hgmem
    obtain ⟨r, hr, t, ht, hrt⟩ := hgmem
    have htS : t ∈ S := torusGroup_le_stabilizer_pinf J hJ ht
    refine ⟨t, ht, htS, ?_⟩
    have hs : s = ⟨r, hRS hr⟩ * ⟨t, htS⟩ := Subtype.ext hrt.symm
    have hr1 : (QuotientGroup.mk ⟨r, hRS hr⟩ : S ⧸ (rootGroup J hJ).subgroupOf S) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hr)
    rw [hs, QuotientGroup.mk_mul, hr1, one_mul]
  have hquot : Group.IsSolvable (S ⧸ (rootGroup J hJ).subgroupOf S) := by
    apply Group.isSolvable_of_comm
    intro a b
    induction a using QuotientGroup.induction_on with
    | H s =>
      induction b using QuotientGroup.induction_on with
      | H s' =>
        obtain ⟨t, ht, htS, h1⟩ := hmk s
        obtain ⟨t', ht', htS', h2⟩ := hmk s'
        rw [h1, h2, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        congr 1
        apply Subtype.ext
        obtain ⟨k, rfl⟩ := ht
        obtain ⟨k', rfl⟩ := ht'
        show torus J hJ k * torus J hJ k' = torus J hJ k' * torus J hJ k
        rw [← map_mul, ← map_mul, mul_comm]
  exact Group.isSolvable_of_ker_le_range ((rootGroup J hJ).subgroupOf S).subtype
    (QuotientGroup.mk' ((rootGroup J hJ).subgroupOf S)) (by
      rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem normalizer_rootGroup_eq_stabilizer [Fact p.Prime] (hq : 2 < p ^ f) :
    Subgroup.normalizer (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) =
      MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) (pinf J hJ) := by
  have h2 := isMultiplyPretransitive_two J hJ (p ^ f) hK hfix
  have : MulAction.IsPretransitive (ProjectiveSpecialUnitaryMatrixGroup J) (IsoPoint J) :=
    MulAction.isPretransitive_of_is_two_pretransitive
  have : Nontrivial (IsoPoint J) := by
    rw [← Finite.one_lt_card_iff_nontrivial, card_isoPoint J hJ (p ^ f) hK hfix]
    have : 0 < (p ^ f) ^ 3 := pow_pos (by omega) _
    omega
  have hprim := MulAction.isPreprimitive_of_is_two_pretransitive h2
  have hco := MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive
    (ProjectiveSpecialUnitaryMatrixGroup J) (pinf J hJ)
  have hle := stabilizer_pinf_le_normalizer_rootGroup J hJ (p ^ f) hK hfix
  rcases hco.le_iff.mp hle with h | h
  · exact absurd h (isCoatom_normalizer_rootGroup J hJ hK hfix hq).1
  · exact h

end Borel

end CFSG.AGLEmbedding.UnitaryModel

namespace CFSG.AGLEmbedding

open CFSG.UnitaryThreeRecognition.Model (rootGroup)
open CFSG.BenderSuzuki.MatrixGroups (ProjectiveSpecialUnitaryMatrixGroup)

theorem kFactUnitarySylowNormalizerSolvable : KFactUnitarySylowNormalizerSolvable := by
  intro L _ _ p _ d hd h U A hA
  have hmodel := UnitaryModel.statedClassicalModel hd h
  obtain ⟨-, hf, hq, K, _, _, J, hJ, hK, hfix, ⟨e⟩⟩ := UnitaryModel.exists_equiv_psu hmodel
  obtain ⟨S, hS⟩ := UnitaryModel.exists_sylow_eq_rootGroup J hJ hK hfix hf
  obtain ⟨e', he'⟩ := UnitaryModel.exists_equiv_map_eq e U S
  have hN : (Subgroup.normalizer ((U : Subgroup L) : Set L)).map e'.toMonoidHom =
      Subgroup.normalizer (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
    rw [Subgroup.map_equiv_normalizer_eq, he', hS]
  have hsolv : Group.IsSolvable ↥(Subgroup.normalizer
      (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J))) := by
    rw [UnitaryModel.normalizer_rootGroup_eq_stabilizer J hJ hK hfix hq]
    exact UnitaryModel.isSolvable_stabilizer_pinf J hJ hK hfix
  have hB : Group.IsSolvable ↥(Subgroup.normalizer ((U : Subgroup L) : Set L)) :=
    Group.isSolvable_of_isSolvable_injective
      (f := ((Subgroup.equivMapOfInjective _ e'.toMonoidHom e'.injective).trans
        (MulEquiv.subgroupCongr hN)).toMonoidHom)
      ((Subgroup.equivMapOfInjective _ e'.toMonoidHom e'.injective).trans
        (MulEquiv.subgroupCongr hN)).injective
  exact UnitaryModel.isSolvable_of_stabilizer (U : Subgroup L) hB
    (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.unitary_rank_one_classical_model_schreier
      hmodel).2 A hA

end CFSG.AGLEmbedding
