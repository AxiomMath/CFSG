module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1OutFinal
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.ComponentClassification.InnAutDerivedOrthogonal
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxSymplectic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open TauCeti CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.HardMathSupport.Timmesfeld.Tables.T1b
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
  (statedProjectiveReindexEquiv)

theorem inner_of_pow_three_pomegaOdd {n ℓ f : ℕ} {G : Type} [Group G] [Finite G]
    (hG : StatedClassicalModel G .POmegaOdd n ℓ f) {β : MulAut G}
    (hβ : β ∈ innAutDerived G) (hβ3 : β ^ 3 = 1) : β ∈ inner G := by
  have hG0 := hG
  obtain ⟨hadm, K, hfield, hfinite, hK, ⟨e⟩⟩ := hG
  letI := hfield
  letI := hfinite
  have hn : 3 ≤ n := hadm.2.2.1
  have hℓ2 : ℓ ≠ 2 := hadm.2.2.2
  have hchar : ringChar K = ℓ :=
    CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hadm.1 hadm.2.1 hK
  have h2 : ringChar K ≠ 2 := by rw [hchar]; exact hℓ2
  haveI : Finite (matrixProjectiveDerived (coordinateQuadOdd n K)) :=
    Finite.of_equiv G (coordinateOddWitnessEquiv K e).toEquiv
  have hmodel : ∀ β' : MulAut (matrixProjectiveDerived (coordinateQuadOdd n K)),
      β' ∈ innAutDerived (matrixProjectiveDerived (coordinateQuadOdd n K)) →
        β' ^ 3 = 1 → β' ∈ inner (matrixProjectiveDerived (coordinateQuadOdd n K)) := by
    intro β' hβmem hβp
    obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_odd hG0 K hK e
    have hQ : ∃ v, coordinateQuadOdd n K v ≠ 0 :=
      CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT
    have hab := card_abelianization_two_pow_of_bound (oddIndexEquiv n) (quadOdd n K)
      (orthogonal_model_isometry_abelianization_order_bound G .POmegaOdd (Or.inl rfl) n ℓ f hG0 K
        hK (quadOdd n K) (coe_quadOdd n K) e)
    have htop : matrixProjectiveImage (coordinateQuadOdd n K) = ⊤ :=
      CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_odd K n hn h2
    exact mem_inner_of_mem_innAutDerived_of_pow_eq_one (coordinateQuadOdd n K) hQ hab
      Nat.prime_three (by norm_num) htop hβmem hβp
  have hβM : MulAut.congr (coordinateOddWitnessEquiv K e) β ∈
      innAutDerived (matrixProjectiveDerived (coordinateQuadOdd n K)) :=
    (mem_innAutDerived_congr (coordinateOddWitnessEquiv K e)).2 hβ
  have hβMp : (MulAut.congr (coordinateOddWitnessEquiv K e) β) ^ 3 = 1 := by
    rw [← map_pow, hβ3, map_one]
  have hin := hmodel _ hβM hβMp
  rw [← inner_map_congr (coordinateOddWitnessEquiv K e)] at hin
  obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.mp hin
  have hb' : b = β := (MulAut.congr (coordinateOddWitnessEquiv K e)).injective hba
  rw [hb'] at hb
  exact hb

theorem inner_of_pow_three_pomegaPlus {n ℓ f : ℕ} {G : Type} [Group G] [Finite G]
    (hG : StatedClassicalModel G .POmegaPlus n ℓ f) (hn : 5 ≤ n) {β : MulAut G}
    (hβ : β ∈ innAutDerived G) (hβ3 : β ^ 3 = 1) : β ∈ inner G := by
  have hG0 := hG
  obtain ⟨hadm, K, hfield, hfinite, hK, ⟨e⟩⟩ := hG
  letI := hfield
  letI := hfinite
  have hn4 : 4 ≤ n := hadm.2.2
  have hchar : ringChar K = ℓ :=
    CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hadm.1 hadm.2.1 hK
  haveI : Finite (matrixProjectiveDerived (coordinateQuadPlus n K)) :=
    Finite.of_equiv G (coordinatePlusWitnessEquiv K e).toEquiv
  have hmodel : ∀ β' : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K)),
      β' ∈ innAutDerived (matrixProjectiveDerived (coordinateQuadPlus n K)) →
        β' ^ 3 = 1 → β' ∈ inner (matrixProjectiveDerived (coordinateQuadPlus n K)) := by
    intro β' hβmem hβp
    obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_plus hG0 K hK e
    have hQ : ∃ v, coordinateQuadPlus n K v ≠ 0 :=
      CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT
    have hab := card_abelianization_two_pow_of_bound (plusIndexEquiv n) (quadPlus n K)
      (orthogonal_model_isometry_abelianization_order_bound G .POmegaPlus (Or.inr (Or.inl rfl))
        n ℓ f hG0 K hK (quadPlus n K) (coe_quadPlus n K) e)
    have htop : matrixProjectiveImage (coordinateQuadPlus n K) = ⊤ :=
      CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_plus K n hn
    exact mem_inner_of_mem_innAutDerived_of_pow_eq_one (coordinateQuadPlus n K) hQ hab
      Nat.prime_three (by norm_num) htop hβmem hβp
  have hβM : MulAut.congr (coordinatePlusWitnessEquiv K e) β ∈
      innAutDerived (matrixProjectiveDerived (coordinateQuadPlus n K)) :=
    (mem_innAutDerived_congr (coordinatePlusWitnessEquiv K e)).2 hβ
  have hβMp : (MulAut.congr (coordinatePlusWitnessEquiv K e) β) ^ 3 = 1 := by
    rw [← map_pow, hβ3, map_one]
  have hin := hmodel _ hβM hβMp
  rw [← inner_map_congr (coordinatePlusWitnessEquiv K e)] at hin
  obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.mp hin
  have hb' : b = β := (MulAut.congr (coordinatePlusWitnessEquiv K e)).injective hba
  rw [hb'] at hb
  exact hb

theorem inner_of_pow_three_pomegaMinus {n ℓ f : ℕ} {G : Type} [Group G] [Finite G]
    (hG : StatedClassicalModel G .POmegaMinus n ℓ f) {β : MulAut G}
    (hβ : β ∈ innAutDerived G) (hβ3 : β ^ 3 = 1) : β ∈ inner G := by
  have hG0 := hG
  obtain ⟨hadm, K, hfield, hfinite, hK, b, c, hirr, ⟨e⟩⟩ := hG
  letI := hfield
  letI := hfinite
  have hn4 : 4 ≤ n := hadm.2.2
  have hn1 : 1 ≤ n := by omega
  haveI : Finite (matrixProjectiveDerived (coordinateQuadMinus n K hn1 b c)) :=
    Finite.of_equiv G (coordinateMinusWitnessEquiv K hn1 b c e).toEquiv
  have hmodel : ∀ β' : MulAut (matrixProjectiveDerived (coordinateQuadMinus n K hn1 b c)),
      β' ∈ innAutDerived (matrixProjectiveDerived (coordinateQuadMinus n K hn1 b c)) →
        β' ^ 3 = 1 → β' ∈ inner (matrixProjectiveDerived (coordinateQuadMinus n K hn1 b c)) := by
    intro β' hβmem hβp
    obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_minus hG0 K hK b c hirr e
    have hQ : ∃ v, coordinateQuadMinus n K hn1 b c v ≠ 0 :=
      CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT
    have hab := card_abelianization_two_pow_of_bound (minusIndexEquiv n hn1) (quadMinus n K b c)
      (orthogonal_model_isometry_abelianization_order_bound G .POmegaMinus (Or.inr (Or.inr rfl))
        n ℓ f hG0 K hK b c hirr (quadMinus n K b c) (coe_quadMinus n K b c) e)
    have htop : matrixProjectiveImage (coordinateQuadMinus n K hn1 b c) = ⊤ :=
      CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_minus K n hn4 b c hirr
    exact mem_inner_of_mem_innAutDerived_of_pow_eq_one (coordinateQuadMinus n K hn1 b c) hQ hab
      Nat.prime_three (by norm_num) htop hβmem hβp
  have hβM : MulAut.congr (coordinateMinusWitnessEquiv K hn1 b c e) β ∈
      innAutDerived (matrixProjectiveDerived (coordinateQuadMinus n K hn1 b c)) :=
    (mem_innAutDerived_congr (coordinateMinusWitnessEquiv K hn1 b c e)).2 hβ
  have hβMp : (MulAut.congr (coordinateMinusWitnessEquiv K hn1 b c e) β) ^ 3 = 1 := by
    rw [← map_pow, hβ3, map_one]
  have hin := hmodel _ hβM hβMp
  rw [← inner_map_congr (coordinateMinusWitnessEquiv K hn1 b c e)] at hin
  obtain ⟨b', hb, hba⟩ := Subgroup.mem_map.mp hin
  have hb' : b' = β := (MulAut.congr (coordinateMinusWitnessEquiv K hn1 b c e)).injective hba
  rw [hb'] at hb
  exact hb

theorem inner_of_pow_three_symplectic (d : TauCeti.ValidLieTypeIndex)
    [Finite (TauCeti.CFSGIndex.lie d).Group] (hd : isSymplecticIdx d.1)
    {a : MulAut (TauCeti.CFSGIndex.lie d).Group}
    (ha : a ∈ innAutDerived (TauCeti.CFSGIndex.lie d).Group) (ha3 : a ^ 3 = 1) :
    a ∈ inner (TauCeti.CFSGIndex.lie d).Group := by
  obtain ⟨r, hr2, hne, hcard, ⟨e⟩⟩ := exists_mulEquiv_statedProj_of_isSymplecticIdx hd
  haveI : Finite d.fixedField := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField d
  have hK : Nat.card d.fixedField = d.characteristic ^ d.fieldExponent := by
    rw [TauCeti.ValidLieTypeIndex.card_fixedField,
      TauCeti.ValidLieTypeIndex.fieldOrder_eq_characteristic_pow]
  have hne' : ¬ (r = 2 ∧ d.characteristic ^ d.fieldExponent = 2) := by
    rw [← hK, hcard]
    exact hne
  have hβ : MulAut.congr e.symm a ∈ innAutDerived (StatedProj (StatedSp r d.fixedField)) :=
    (mem_innAutDerived_congr e.symm).2 ha
  have hβp : (MulAut.congr e.symm a) ^ 3 = 1 := by
    rw [← map_pow, ha3, map_one]
  have hin := mem_inner_of_mem_innAutDerived_statedSp (p := 3) Nat.prime_three (by norm_num)
    d.characteristic_prime d.fieldExponent_pos hK hr2 hne' hβ hβp
  rw [← inner_map_congr e.symm] at hin
  obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.mp hin
  have hb' : b = a := (MulAut.congr e.symm).injective hba
  rw [hb'] at hb
  exact hb

theorem kd264Y1OutOS_holds : KD264Y1OutOS := by
  intro d hfin hP hns hk2 hk3 hpR a ha ha3
  rcases d with ⟨e, hv⟩
  rcases hP with ⟨r, q, rfl⟩ | ⟨r, q, rfl⟩ | ⟨r, q, hr5, rfl⟩ | ⟨r, q, rfl⟩
  ·
    by_cases hB : r = 2 ∨ q.p = 2
    · exact inner_of_pow_three_symplectic ⟨_, hv⟩ (by simp [isSymplecticIdx, hB]) ha ha3
    · push Not at hB
      have hstd := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
        ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
      have hn3 : 3 ≤ r := by
        have := hstd.1
        omega
      have hSC : StatedClassicalModel (TauCeti.CFSGIndex.lie ⟨.B r q, hv⟩).Group
          .POmegaOdd r q.p q.exponent :=
        ⟨⟨q.prime_p, q.exponent_pos, hn3, hB.2⟩, _, inferInstance,
          CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _,
          CFSG.Models.card_fixedField_of (TauCeti.LieTypeIndex.characteristic_B r q)
            (TauCeti.LieTypeIndex.fieldExponent_B r q),
          ⟨CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj_odd r q hv hB.2
            hn3⟩⟩
      exact inner_of_pow_three_pomegaOdd hSC ha ha3
  ·
    exact inner_of_pow_three_symplectic ⟨_, hv⟩ trivial ha ha3
  ·
    obtain ⟨-, hSC | ⟨h0, -⟩⟩ := CFSG.Models.lieModel_D r q hv (MulEquiv.refl _)
    · exact inner_of_pow_three_pomegaPlus hSC hr5 ha ha3
    · omega
  ·
    obtain ⟨hadm, hSC | ⟨h0, -⟩⟩ := CFSG.Models.lieModel_twistedD r q hv (MulEquiv.refl _)
    · exact inner_of_pow_three_pomegaMinus hSC ha ha3
    · have := hadm.2.2
      omega

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
