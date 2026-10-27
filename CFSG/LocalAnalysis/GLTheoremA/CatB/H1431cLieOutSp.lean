module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieOutCharTwo
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.OutSp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.Yardstones.Md0ec50421ce4
  CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.PartOne.KCSpComm
  CFSG.RankThree.CASymplecticSubfield CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.CatLeaf CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
  (symplectic_prime_subfield_fixed_group_and_full_centralizer_odd)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.HardMathSupport.Dickson.Sec6.I923
open CFSG.HardMathSupport.Dickson.Sec6 (FamB)
open scoped commutatorElement

section Field

variable {T : TauCeti.CFSGIndex → Prop} {tm tf tN : ℕ}


theorem typeLayer_fieldAut_psp_two_eight (hD : LieSOutType T tm tf tN) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 8) {σ : K ≃+* K} (hσ : orderOf σ = 3) {G : Prop} :
    TypeLayer T (fieldAut 2 K σ) G := by
  have hK' : Nat.card K = 2 ^ 3 := by rw [hK]; norm_num
  obtain ⟨-, -, -, -, -, hfixiff, -, -, hA6, -⟩ :=
    symplectic_prime_subfield_fixed_group_and_full_centralizer_odd
      (K := K) (r := 2) Nat.prime_two Nat.prime_three (by norm_num) (by norm_num) (by norm_num)
      le_rfl hK' σ hσ
  obtain ⟨-, ⟨eA⟩, -⟩ := hA6 ⟨rfl, by norm_num⟩
  have hD' : fixSubgroup (fieldAut 2 K σ) = subfieldFixedGroup K 2 σ :=
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
  refine typeLayer_of_simple_commutator _ S (by rw [hD']) hs hnab fun hT => ?_
  have h1 := hD.card_eq hT
  rw [hcardS] at h1
  exact absurd ⟨1, by omega⟩ hD.ord.not_dvd_360

theorem typeLayer_fieldAut_psp (hD : LieSOutType T tm tf tN) {r : ℕ} (hr : 2 ≤ r) {K : Type}
    [Field K] [Finite K] {σ : K ≃+* K} (hσ : orderOf σ = 3) {g : ℕ} (hg : 1 ≤ g)
    (hK : Nat.card K = 2 ^ g) : TypeLayer T (fieldAut r K σ) (r = tm ∧ g = 3 * tf) := by
  by_cases hex : r = 2 ∧ Nat.card K = 8
  · obtain ⟨rfl, h8⟩ := hex
    exact typeLayer_fieldAut_psp_two_eight hD h8 hσ
  have : NeZero r := ⟨by omega⟩
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  obtain ⟨h3f, hkcard⟩ := card_semilinearFixedSubfield Nat.prime_two hg hK hσ
  set k := descentField σ with hkdef
  have hkcard' : Nat.card k = 2 ^ (g / 3) := hkcard
  have hf0 : 1 ≤ g / 3 := by
    have : 3 ≤ g := Nat.le_of_dvd (by omega) h3f
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
  have hadm : StatedLieAdmissible .PSp r 2 (g / 3) :=
    ⟨Nat.prime_two, hf0, hr, fun hc => by
      have h1 := (Prod.mk.inj hc).1
      have h2 := (Prod.mk.inj hc).2
      apply hex
      refine ⟨h1, ?_⟩
      have : Nat.card K = Nat.card k ^ 3 := by
        rw [hkcard', ← pow_mul, mul_comm, Nat.mul_div_cancel' h3f]; exact hK
      rw [this, hkcard', h2]; norm_num⟩
  have hmodelk : StatedClassicalModel (StatedProj (StatedSp r ↥k)) .PSp r 2 (g / 3) :=
    ⟨hadm, ↥k, inferInstance, inferInstance, hkcard', ⟨MulEquiv.refl _⟩⟩
  haveI hsk : IsSimpleGroup (StatedProj (StatedSp r ↥k)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp _ r 2 (g / 3)
      hmodelk
  have hmodel : Blueprint.LieModel (StatedProj (StatedSp r ↥k)) .PSp r 2 (g / 3) :=
    (lieModel_classical_iff (by decide)).mpr hmodelk
  obtain ⟨-, hM, -⟩ := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput _ .PSp r 2
    (g / 3) hadm hmodel
  have hnab := exists_noncomm_of_simple_of_order hadm hM (by
    show 2 ≤ (g / 3) * (r ^ 2)
    nlinarith)
  refine typeLayer_of_fixed_equiv _ eD hsk hnab fun h => ?_
  obtain ⟨-, hrm, hgf⟩ := hD.det h hmodel
  exact ⟨hrm, by omega⟩

theorem lieSOut_B (hD : LieSOutType T tm tf tN) :
    TypeOuterAt T (isBIdx tm (2 ^ (3 * tf))) FamB := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ α hα hp
  cases d with
  | B r q =>
    have hq2 : q.p = 2 := hc
    have hr2 : 2 ≤ r := (((TauCeti.LieTypeIndex.inStandardRange_iff _).mp
      ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1)).1
    have hm := CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_B r q hv hq2 e
    have hC : StatedClassicalModel S .PSp r q.p q.exponent :=
      (lieModel_classical_iff (by decide)).mp hm
    obtain ⟨hadm, K, _, _, hK, ⟨e0⟩⟩ := hC
    rw [hq2] at hK hadm
    have hψ3 : MulAut.congr e0 α ^ 3 = 1 := by rw [← map_pow, hp.1, map_one]
    have hninn : ¬ IsInnerAut (MulAut.congr e0 α) := fun h =>
      hα ((mem_innAutDerived_congr e0).mp (inner_le_innAutDerived _ h))
    obtain ⟨γ, σ, hσ, hψγ⟩ :=
      CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2.psp_field_descent hr2 Nat.prime_two hadm.2.1 hK
        hψ3 hninn
    have h1 : TypeLayer T (MulAut.congr e0 α) (r = tm ∧ q.exponent = 3 * tf) := by
      rw [hψγ]
      exact typeLayer_conj γ (typeLayer_fieldAut_psp hD hr2 hσ hadm.2.1 hK)
    obtain ⟨hrm, hqe⟩ := hp.apply (typeLayer_congr e0 h1)
    show r = tm ∧ q.card = 2 ^ (3 * tf)
    refine ⟨hrm, ?_⟩
    rw [TauCeti.PrimePower.card_def, hq2, hqe]
  | _ => exact hF.elim

end Field

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
