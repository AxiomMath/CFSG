module

public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.OutFixed
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.OutSp
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.Chev2Split
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxSymplectic
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCSpComm
  CFSG.RankThree.PartTwo.KFacts
  CFSG.RankThree.CASymplecticSubfield CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.HardMathSupport.Dickson.Sec6.I923
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.PartOne.Sec66T (lieModel_classical_iff)

theorem not_upD42Pumpup_fieldAut_psp {r f : ℕ} (hr : 2 ≤ r) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ f)
    {σ : K ≃+* K} (hσ : orderOf σ = 3) :
    ¬ UpD42Pumpup (StatedProj (StatedSp r K)) (fieldAut r K σ) := by
  intro hx
  haveI : NeZero r := ⟨by omega⟩
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  obtain ⟨h3f, hkcard⟩ := card_semilinearFixedSubfield Nat.prime_two hf hK hσ
  let k := descentField σ
  have hkcard' : Nat.card k = 2 ^ (f / 3) := hkcard
  have hf0 : 1 ≤ f / 3 := by
    have h3 : 3 ≤ f := Nat.le_of_dvd (by omega) h3f
    omega
  have hinj := subfieldSpProj_injective (K := K) (r := r) (by omega) k
  have hfix : fixSubgroup (fieldAut r K σ) = (subfieldSpProj r k).range := by
    ext x
    have h1 := fixed_iff_mem_range (r := r) (p := 3) (by decide) hσ3 x
    have h2 : (subfieldProj σ).range = (subfieldSpProj r k).range := by
      ext y
      constructor
      · rintro ⟨g, rfl⟩
        exact ⟨proj r k g, subfieldSpProj_proj k g⟩
      · rintro ⟨z, rfl⟩
        obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective z
        exact ⟨g, (subfieldSpProj_proj k g).symm⟩
    exact h1.trans (Iff.of_eq (congrArg (x ∈ ·) h2))
  let eD : ↥(fixSubgroup (fieldAut r K σ)) ≃* StatedProj (StatedSp r ↥k) :=
    (MulEquiv.subgroupCongr hfix).trans (MonoidHom.ofInjective hinj).symm
  by_cases hex : r = 2 ∧ Nat.card k = 2
  · obtain ⟨rfl, hk2⟩ := hex
    have hc : Nat.card (StatedSp 2 ↥k) = 720 := by
      rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp_two, hk2]
      norm_num
    have hdvd : 174182400 ∣ Nat.card (StatedProj (StatedSp 2 ↥k)) := by
      rw [← Nat.card_congr eD.toEquiv]
      exact hx.card_d42_dvd_fixed
    have hquot : Nat.card (StatedProj (StatedSp 2 ↥k)) ∣ Nat.card (StatedSp 2 ↥k) :=
      Subgroup.card_quotient_dvd_card _
    have hbad := hdvd.trans hquot
    rw [hc] at hbad
    norm_num at hbad
  · have hadm : StatedLieAdmissible .PSp r 2 (f / 3) :=
      ⟨Nat.prime_two, hf0, hr, fun hc => hex
        ⟨(Prod.mk.inj hc).1, hkcard'.trans (Prod.mk.inj hc).2⟩⟩
    have hmodel : LieModel (StatedProj (StatedSp r ↥k)) .PSp r 2 (f / 3) :=
      (lieModel_classical_iff (by decide)).mpr
        ⟨hadm, ↥k, inferInstance, inferInstance, hkcard', ⟨MulEquiv.refl _⟩⟩
    have hs : IsSimpleGroup (StatedProj (StatedSp r ↥k)) :=
      CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp
        _ r 2 (f / 3) ((lieModel_classical_iff (by decide)).mp hmodel)
    have hnab : ∃ a b : StatedProj (StatedSp r ↥k), a * b ≠ b * a := by
      by_contra hcon
      push Not at hcon
      letI : CommGroup (StatedProj (StatedSp r ↥k)) :=
        { (inferInstance : Group (StatedProj (StatedSp r ↥k))) with mul_comm := hcon }
      exact hx.not_solvable_fixed
        (Group.isSolvable_of_isSolvable_injective (f := eD.toMonoidHom) eD.injective)
    have hD := isD42Type_of_upD42Pumpup_of_fixEquiv_simple hx eD hs hnab
    have ht := (classical_type_of_isD42 (by decide) hmodel hD).1
    cases ht

theorem upD42Chev2Out_symplectic_holds : UpD42Chev2Out isSymplecticIdx := by
  intro S _ _ _ _ d hd hc ⟨e⟩ α hout hx
  obtain ⟨r, hr, -, -, ⟨eP⟩⟩ := exists_mulEquiv_statedProj_of_isSymplecticIdx hd
  haveI : Finite ↥d.fixedField := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField d
  let e' : S ≃* StatedProj (StatedSp r ↥d.fixedField) := e.trans eP.symm
  have hc' : d.1.characteristic = 2 := by
    rcases d with ⟨idx, hv⟩
    cases idx <;> simpa [IsCharTwoLieIndex] using hc
  have hK : Nat.card ↥d.fixedField = 2 ^ d.fieldExponent := by
    rw [TauCeti.ValidLieTypeIndex.card_fixedField,
      TauCeti.ValidLieTypeIndex.fieldOrder_eq_characteristic_pow]
    change d.1.characteristic ^ d.fieldExponent = 2 ^ d.fieldExponent
    rw [hc']
  have hx' := hx.congr e'
  have hninn : ¬ IsInnerAut (MulAut.congr e' α) := fun hin =>
    hout ((congr_mem_inner_iff_of_equiv e' α).mp hin)
  obtain ⟨γ, σ, hσ, hβ⟩ := Up34Chev2.psp_field_descent hr Nat.prime_two
    d.fieldExponent_pos hK hx'.1 hninn
  have he : MulAut.congr γ⁻¹ (MulAut.congr e' α) = fieldAut r ↥d.fixedField σ := by
    rw [hβ]
    ext x
    simp [MulAut.congr_apply, MulAut.mul_apply]
  have hx'' := hx'.congr γ⁻¹
  rw [he] at hx''
  exact (not_upD42Pumpup_fieldAut_psp hr d.fieldExponent_pos hK hσ hx'').elim

end CFSG.HardMathSupport.Dickson.Sec6

end
