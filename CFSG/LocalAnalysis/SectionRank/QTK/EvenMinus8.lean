module

public import CFSG.LocalAnalysis.SectionRank.QTK.EvenMinus8M
public import CFSG.LocalAnalysis.SectionRank.QTK.EvenExt

public section

namespace CFSG.SectionRank.QTK

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (localRank)
open scoped commutatorElement

theorem isPGroup_sup_zpowers {G : Type*} [Group G] {a b : G} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (hab : Commute a b) : IsPGroup 2 (Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup G) :=
  IsPGroup.to_sup_of_normal_left' (isPGroup_zpowers_of_sq ha) (isPGroup_zpowers_of_sq hb)
    (Subgroup.zpowers_le.2 (mem_normalizer_zpowers hab.symm))

variable (K : Type) [Field K] [CharP K 2]

theorem castGLι_isometry_minus {M : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2)}
    (hM : MinusBasisIsom (M : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2)))
    (v : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K) :
    StatedQuadMinus 4 K 1 1
        ((castGLι K M : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K) *ᵥ v) =
      StatedQuadMinus 4 K 1 1 v := by
  rw [coe_castGLι, ← CFSG.LieType.Universal.Spin.coe_quadMinus 4 K 1 1]
  exact isometry_castMat_of_basis (CFSG.LieType.Universal.Spin.quadMinus 4 K 1 1)
    (StatedQuadMinus 4 (ZMod 2) 1 1) (fun w => by
      rw [CFSG.LieType.Universal.Spin.coe_quadMinus]
      exact statedQuadMinus_comp_cast w) _ hM.1 hM.2 v

theorem three_le_localRank_statedOmegaMinus_four_one [Finite K] :
    3 ≤ localRank 3 ↥(StatedOmega (StatedQuadMinus 4 K 1 1)) := by
  obtain ⟨h3, h1, h2, hZA, hZZ, hAZ⟩ := minus_relations
  obtain ⟨hE1, hE2, hE12, hc1, hc2, hE1c, hn1, hn2, hn1', hn2', hl1, hl2, hr1, hr2⟩ :=
    minus_fourGroup
  obtain ⟨hZ, hA, hI2, hI3⟩ := minus_basisIsom
  set π := castGLι K (ι := Fin 3 ⊕ Fin 3 ⊕ Fin 2)
  have hcomm : ∀ {a b : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2)},
      MinusBasisIsom (a : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2)) →
      MinusBasisIsom (b : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2)) →
      π ⁅a, b⁆ ∈ StatedOmega (StatedQuadMinus 4 K 1 1) := fun ha hb => by
    rw [map_commutatorElement]
    exact Subgroup.commutator_mem_commutator
      (Subgroup.subset_closure (castGLι_isometry_minus K ha))
      (Subgroup.subset_closure (castGLι_isometry_minus K hb))
  have hP1 : mE₁ ∈ Subgroup.zpowers mE₁ ⊔ Subgroup.zpowers mE₂ :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hP2 : mE₂ ∈ Subgroup.zpowers mE₁ ⊔ Subgroup.zpowers mE₂ :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  refine le_localRank_of_witness π ?_ minusZ minusA h3 h1 h2 hZA hZZ
    (P := Subgroup.zpowers mE₁ ⊔ Subgroup.zpowers mE₂) (isPGroup_sup_zpowers hE1 hE2 hE12) ?_
    ?_ ?_ ?_
  · rw [(MonoidHom.ker_eq_bot_iff π).2 (castGLι_injective K)]
    exact bot_le
  · intro h
    exact hE1c (Subgroup.mem_center_iff.1 (h hP1) mOm).symm
  · intro i
    fin_cases i
    · exact mem_normalizer_sup_of_commute hl1 hl2
    · exact mem_normalizer_sup_of_commute hr1 hr2
    · refine mem_normalizer_sup_zpowers ?_ ?_ ?_ ?_
      · change mOm * mE₁ * mOm⁻¹ ∈ _
        rw [hn1]
        exact hP2
      · change mOm * mE₂ * mOm⁻¹ ∈ _
        rw [hn2]
        exact Subgroup.mul_mem _ hP1 hP2
      · change mOm⁻¹ * mE₁ * mOm ∈ _
        rw [hn1']
        exact Subgroup.mul_mem _ hP1 hP2
      · change mOm⁻¹ * mE₂ * mOm ∈ _
        rw [hn2']
        exact hP1
  · intro i
    rw [← hAZ i]
    exact hcomm (hA i) (hZ i)
  · rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
    · rw [← hc1]
      exact hcomm (hZ 2) hI2
    · rw [← hc2]
      exact hcomm (hZ 2) hI3

variable {K}

omit [CharP K 2] in
theorem eq_zero_or_eq_one_of_card_two [Finite K] (hK : Nat.card K = 2) (x : K) :
    x = 0 ∨ x = 1 := by
  have : Fintype K := Fintype.ofFinite K
  have h := FiniteField.pow_card x
  rw [Fintype.card_eq_nat_card, hK] at h
  have h' : x * (x - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.1 h' with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.1 h1)

theorem eq_one_of_irreducible_of_card_two [Finite K] (hK : Nat.card K = 2) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : b = 1 ∧ c = 1 := by
  have hc : c = 1 := (eq_zero_or_eq_one_of_card_two hK c).resolve_left fun h0 =>
    hirr 0 (by rw [h0]; ring)
  refine ⟨(eq_zero_or_eq_one_of_card_two hK b).resolve_left fun h0 => hirr 1 ?_, hc⟩
  rw [h0, hc]
  linear_combination (CharP.cast_eq_zero K 2 : ((2 : ℕ) : K) = 0)

theorem three_le_localRank_statedProj_statedOmegaMinus_four_two [Finite K]
    (hK : Nat.card K = 2) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    3 ≤ localRank 3 (StatedProj (StatedOmega (StatedQuadMinus 4 K b c))) := by
  obtain ⟨rfl, rfl⟩ := eq_one_of_irreducible_of_card_two hK hirr
  have hv : CFSG.LieType.Universal.Spin.quadMinus 4 K 1 1 (Pi.single (.inr (.inr 0)) 1) ≠ 0 := by
    rw [CFSG.LieType.Universal.Spin.coe_quadMinus]
    simp [StatedQuadMinus]
  rw [← CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv
    (CFSG.RankThree.PartOne.KFU.equivProjOfScalarsBot _
      (statedScalars_subgroupOf_statedOmega_eq_bot _
        (CFSG.LieType.Universal.Spin.coe_quadMinus 4 K 1 1) hv)) Nat.prime_three]
  exact three_le_localRank_statedOmegaMinus_four_one K

end CFSG.SectionRank.QTK
