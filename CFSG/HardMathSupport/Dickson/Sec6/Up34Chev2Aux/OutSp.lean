module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.ExcOuter
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.LayerMore
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.OrthOuterThreeAux.SympPrimeSubfieldOdd
public import CFSG.RankThree.PartOne.KC.OrthogonalNoninnerPlaneModel
public import CFSG.RankThree.PartOne.KC.SymplecticSubfieldFixed
public import CFSG.RankThree.PartOne.S11c.Sec66ClassCommon
public import CFSG.RankThree.PartOne.S11d.OutLinear

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.PartOne.KCSpComm
  CFSG.RankThree.CASymplecticSubfield CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.CatLeaf CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
  (symplectic_prime_subfield_fixed_group_and_full_centralizer_odd)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.HardMathSupport.Dickson.Sec6.I923
open Up34Chev2

namespace Up34Chev2

theorem psp_field_descent {r : ℕ} (hr : 2 ≤ r) {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f)
    {ψ : MulAut (StatedProj (StatedSp r K))} (hψ3 : ψ ^ 3 = 1) (hninn : ¬ IsInnerAut ψ) :
    ∃ (γ : MulAut (StatedProj (StatedSp r K))) (σ : K ≃+* K), orderOf σ = 3 ∧
      ψ = γ * fieldAut r K σ * γ⁻¹ := by
  obtain ⟨-, -, -, -, -, -, -, hidx, hrel, hdesc⟩ :=
    CFSG.RankThree.Classical.SteinbergBY.symplectic_prime_semilinear_field_descent hp hf hr hK
  have hidx' : (spSemilinearAutGroup r K).index ≤ 2 := Nat.le_of_dvd (by norm_num) hidx
  have hE : ψ ∈ spSemilinearAutGroup r K :=
    OutStructure.mem_of_pow_mem_of_index_le_two _ hidx' (by decide : Odd 3)
      (by rw [hψ3]; exact Subgroup.one_mem _)
  have hD : ψ ∉ spLinearAutGroup r K := by
    intro hD
    have hrel2 : (inner (StatedProj (StatedSp r K))).relIndex (spLinearAutGroup r K) ∣ 2 :=
      hrel.trans (Nat.gcd_dvd_left _ _)
    haveI := inner_normal (StatedProj (StatedSp r K))
    have hmem : ψ ∈ inner (StatedProj (StatedSp r K)) := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hrel2 with hk | hk
      · exact KCOrthogonalNoninner.mem_of_pow_eq_one_of_relIndex_eq_two_pow
          (H := inner (StatedProj (StatedSp r K))) (k := 0) (by rw [hk]; rfl) Nat.prime_three
          (by norm_num) hD hψ3
      · exact KCOrthogonalNoninner.mem_of_pow_eq_one_of_relIndex_eq_two_pow
          (H := inner (StatedProj (StatedSp r K))) (k := 1) (by rw [hk]; rfl) Nat.prime_three
          (by norm_num) hD hψ3
    exact hninn hmem
  have hψord : orderOf ψ = 3 := by
    refine orderOf_eq_prime hψ3 ?_
    intro h1
    exact hninn (h1 ▸ ⟨1, by simp⟩)
  obtain ⟨h3f, σ, hσ, -, h, hhD, hψh⟩ := hdesc 3 Nat.prime_three ψ hE hD hψord
  exact ⟨h, σ, hσ, hψh⟩

section Field


theorem noL34Layer_fieldAut_psp_two_eight {K : Type} [Field K] [Finite K] (hK : Nat.card K = 8)
    {σ : K ≃+* K} (hσ : orderOf σ = 3) : NoL34Layer (fieldAut 2 K σ) := by
  have hK' : Nat.card K = 2 ^ 3 := by rw [hK]; norm_num
  obtain ⟨-, -, -, -, -, hfixiff, -, -, hA6, -⟩ :=
    symplectic_prime_subfield_fixed_group_and_full_centralizer_odd
      (K := K) (r := 2) Nat.prime_two Nat.prime_three (by norm_num) (by norm_num) (by norm_num)
      le_rfl hK' σ hσ
  obtain ⟨-, ⟨eA⟩, -⟩ := hA6 ⟨rfl, by norm_num⟩
  have hD : fixSubgroup (fieldAut 2 K σ) = subfieldFixedGroup K 2 σ :=
    Subgroup.ext fun x => (hfixiff x).symm
  have h5 : 5 ≤ Nat.card (Fin 6) := by rw [Nat.card_fin]; norm_num
  haveI hsA : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup h5
  have hcardA : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide
  set S : Subgroup (StatedProj (StatedSp 2 K)) :=
    ⁅subfieldFixedGroup K 2 σ, subfieldFixedGroup K 2 σ⁆ with hS
  haveI hs : IsSimpleGroup ↥S := eA.isSimpleGroup
  have hcardS : Nat.card ↥S = 360 := by rw [Nat.card_congr eA.toEquiv, hcardA]
  have hnab : ∃ a b : ↥S, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    letI : CommGroup ↥S := { (inferInstance : Group ↥S) with mul_comm := fun a b => hcon a b }
    have hprime : (Nat.card ↥S).Prime := IsSimpleGroup.prime_card
    rw [hcardS] at hprime
    exact absurd hprime (by norm_num)
  refine noL34Layer_of_simple_commutator _ S (by rw [hD]) hs hnab fun hT => ?_
  have := card_eq_of_isLThreeFour hT
  rw [hcardS] at this
  exact absurd this (by norm_num)

theorem noL34Layer_fieldAut_psp {r : ℕ} (hr : 2 ≤ r) {K : Type} [Field K] [Finite K]
    {σ : K ≃+* K} (hσ : orderOf σ = 3) {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) :
    NoL34Layer (fieldAut r K σ) := by
  by_cases hex : r = 2 ∧ Nat.card K = 8
  · obtain ⟨rfl, h8⟩ := hex
    exact noL34Layer_fieldAut_psp_two_eight h8 hσ
  have : NeZero r := ⟨by omega⟩
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  obtain ⟨h3f, hkcard⟩ := card_semilinearFixedSubfield Nat.prime_two hf hK hσ
  set k := descentField σ with hkdef
  have hkcard' : Nat.card k = 2 ^ (f / 3) := hkcard
  have hf0 : 1 ≤ f / 3 := by
    have : 3 ≤ f := Nat.le_of_dvd (by omega) h3f
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
  have hadm : StatedLieAdmissible .PSp r 2 (f / 3) :=
    ⟨Nat.prime_two, hf0, hr, fun hc => by
      have h1 := (Prod.mk.inj hc).1
      have h2 := (Prod.mk.inj hc).2
      apply hex
      refine ⟨h1, ?_⟩
      have : Nat.card K = Nat.card k ^ 3 := by
        rw [hkcard', ← pow_mul, mul_comm, Nat.mul_div_cancel' h3f]; exact hK
      rw [this, hkcard', h2]; norm_num⟩
  have hmodelk : StatedClassicalModel (StatedProj (StatedSp r ↥k)) .PSp r 2 (f / 3) :=
    ⟨hadm, ↥k, inferInstance, inferInstance, hkcard', ⟨MulEquiv.refl _⟩⟩
  haveI hsk : IsSimpleGroup (StatedProj (StatedSp r ↥k)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp _ r 2 (f / 3)
      hmodelk
  have hmodel : LieModel (StatedProj (StatedSp r ↥k)) .PSp r 2 (f / 3) :=
    (lieModel_classical_iff (by decide)).mpr hmodelk
  obtain ⟨-, hM, -⟩ := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput _ .PSp r 2
    (f / 3) hadm hmodel
  have hnab := exists_noncomm_of_simple_of_order hadm hM (by
    show 2 ≤ (f / 3) * (r ^ 2)
    nlinarith)
  exact noL34Layer_of_fixed_equiv _ eD hsk hnab fun h =>
    not_isLThreeFour_of_lieModel_two hmodel (by decide) h

end Field

end Up34Chev2

section Family


theorem up34C2Out_B : Up34Chev2Out FamB := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ α hα hp
  cases d with
  | B r q =>
    exfalso
    have hq2 : q.p = 2 := hc
    have hr2 : 2 ≤ r := (((TauCeti.LieTypeIndex.inStandardRange_iff _).mp
      ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1)).1
    have hm := blueprintLieModel_B r q hv hq2 e
    have hC : StatedClassicalModel S .PSp r q.p q.exponent :=
      (lieModel_classical_iff (by decide)).mp hm
    obtain ⟨hadm, K, _, _, hK, ⟨e0⟩⟩ := hC
    rw [hq2] at hK hadm
    have hψ3 : MulAut.congr e0 α ^ 3 = 1 := by rw [← map_pow, ((up34Pumpup_iff α).1 hp).1, map_one]
    have hninn : ¬ IsInnerAut (MulAut.congr e0 α) := fun h =>
      hα ((congr_mem_inner_iff_of_equiv e0 α).mp h)
    obtain ⟨γ, σ, hσ, hψγ⟩ := psp_field_descent hr2 Nat.prime_two hadm.2.1 hK hψ3 hninn
    have h1 : NoL34Layer (MulAut.congr e0 α) := by
      rw [hψγ]
      exact noL34Layer_conj γ (noL34Layer_fieldAut_psp hr2 hσ hadm.2.1 hK)
    exact ((up34Pumpup_iff α).1 hp).2.2 (noL34Layer_congr e0 h1)
  | _ => exact hF.elim

end Family

end CFSG.HardMathSupport.Dickson.Sec6
