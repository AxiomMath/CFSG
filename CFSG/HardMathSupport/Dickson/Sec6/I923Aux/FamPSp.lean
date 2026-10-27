module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.Split
public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.LieArith
public import CFSG.RankThree.PartOne.KC.SymplecticSubfieldFixed
public import CFSG.RankThree.PartOne.KC.OrthogonalNoninnerPlaneModel
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartOne.S11c.Sec66ClassCommon
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.OrthOuterThreeAux.SympPrimeSubfieldOdd

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.PartOne.KCSpComm
  CFSG.RankThree.CASymplecticSubfield CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.CatLeaf
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross (symplectic_prime_subfield_fixed_group_and_full_centralizer_odd)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

theorem noL2Layer_fieldAut_psp (hO : LieOrderFormulasInput) {r : ℕ} (hr : 2 ≤ r) {K : Type}
    [Field K] [Finite K] {σ : K ≃+* K} (hσ : orderOf σ = 3) {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) (hex : ¬ (r = 2 ∧ Nat.card K = 8)) :
    NoL2Layer (fieldAut r K σ) := by
  have : NeZero r := ⟨by omega⟩
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  obtain ⟨h3f, hkcard⟩ := card_semilinearFixedSubfield hp hf hK hσ
  set k := descentField σ with hkdef
  have hkcard' : Nat.card k = p ^ (f / 3) := hkcard
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
  have hadm : StatedLieAdmissible .PSp r p (f / 3) :=
    ⟨hp, hf0, hr, fun hc => by
      have h1 := (Prod.mk.inj hc).1
      have h2 := (Prod.mk.inj hc).2
      apply hex
      refine ⟨h1, ?_⟩
      have : Nat.card K = Nat.card k ^ 3 := by
        rw [hkcard', ← pow_mul, mul_comm, Nat.mul_div_cancel' h3f]; exact hK
      rw [this, hkcard', h2]; norm_num⟩
  have hmodelk : StatedClassicalModel (StatedProj (StatedSp r ↥k)) .PSp r p (f / 3) :=
    ⟨hadm, ↥k, inferInstance, inferInstance, hkcard', ⟨MulEquiv.refl _⟩⟩
  haveI hsk : IsSimpleGroup (StatedProj (StatedSp r ↥k)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp _ r p (f / 3)
      hmodelk
  have hs : IsSimpleGroup ↥(fixSubgroup (fieldAut r K σ)) := eD.isSimpleGroup
  have hmodel : LieModel ↥(fixSubgroup (fieldAut r K σ)) .PSp r p (f / 3) :=
    (lieModel_classical_iff (by decide)).mpr ⟨hadm, ↥k, inferInstance, inferInstance, hkcard',
      ⟨eD⟩⟩
  haveI : Finite ↥(fixSubgroup (fieldAut r K σ)) := Finite.of_equiv _ eD.symm.toEquiv
  obtain ⟨-, hM, -⟩ := hO _ .PSp r p (f / 3) hadm hmodel
  have hnab := exists_noncomm_of_simple_of_order hadm hM (by
    show 2 ≤ (f / 3) * (r ^ 2)
    nlinarith)
  refine noL2_of_simple_fixed _ hs hnab fun r' hr' hT => ?_
  exact not_typeL2_of_lieModel hO hadm hmodel (by decide) (by simp)
    (center_eq_bot_of_simple hnab) hr' hT

theorem famOK_psp_of_field {r : ℕ} (hr : 2 ≤ r) {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f)
    (hnoL2 : ∀ σ : K ≃+* K, orderOf σ = 3 → NoL2Layer (fieldAut r K σ)) :
    FamOK (StatedProj (StatedSp r K)) := by
  intro ψ hψ3 hninn
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
  exact ⟨h, fieldAut r K σ, hψh, hnoL2 σ hσ⟩

theorem famOK_psp (hO : LieOrderFormulasInput) {r : ℕ} (hr : 2 ≤ r) {K : Type} [Field K]
    [Finite K] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f)
    (hex : ¬ (r = 2 ∧ Nat.card K = 8)) : FamOK (StatedProj (StatedSp r K)) :=
  famOK_psp_of_field hr hp hf hK fun _ hσ => noL2Layer_fieldAut_psp hO hr hσ hp hf hK hex

theorem y923_lieRestAt_psp (hO : LieOrderFormulasInput) : Y923_LieRestAt FamPsp := by
  intro Y _ _ hq hcore hL2 t n p f hadm ht hF hm α h3 hnot J hJ r hr
  obtain ⟨rfl, hn2, hex⟩ := hF
  have hC : StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSp n p f :=
    (lieModel_classical_iff (by decide)).mp hm
  obtain ⟨-, K, _, _, hK, ⟨e0⟩⟩ := hC
  rw [← hK] at hex
  exact noL2_of_famOK hq e0 (famOK_psp hO hn2 hadm.1 hadm.2.1 hK hex) h3 hnot hJ hr

theorem noL2Layer_fieldAut_psp_two_eight {K : Type} [Field K] [Finite K] (hK : Nat.card K = 8)
    {σ : K ≃+* K} (hσ : orderOf σ = 3) : NoL2Layer (fieldAut 2 K σ) := by
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
  refine noL2_of_simple_commutator_fixed _ S (by rw [hD]) hs hnab fun r hr hT => ?_
  obtain ⟨-, hodd, heven⟩ := CFSG.HardMathSupport.Solomon.Proving.typeL2_card (↥S) hT
  have hcen := center_eq_bot_of_simple hnab
  have hcard : Nat.card (↥S ⧸ Subgroup.center ↥S) = 360 := by
    rw [hcen]
    rw [Nat.card_congr (QuotientGroup.quotientBot (G := ↥S)).toEquiv, hcardS]
  have h100 : 100 ≤ r * r := by nlinarith
  have hr3 : 100 * r ≤ r ^ 3 := by nlinarith
  rcases Nat.even_or_odd r with hev | hod
  · have := (heven hev).1
    rw [hcard] at this
    omega
  · have := hodd hod
    rw [hcard] at this
    omega

theorem y923_lieRestAt_pspTwoEight : Y923_LieRestAt FamPspTwoEight := by
  intro Y _ _ hq hcore hL2 t n p f hadm ht hF hm α h3 hnot J hJ r hr
  obtain ⟨rfl, rfl, hq8⟩ := hF
  have hC : StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSp 2 p f :=
    (lieModel_classical_iff (by decide)).mp hm
  obtain ⟨-, K, _, _, hK, ⟨e0⟩⟩ := hC
  exact noL2_of_famOK hq e0
    (famOK_psp_of_field le_rfl hadm.1 hadm.2.1 hK
      fun σ hσ => noL2Layer_fieldAut_psp_two_eight (hK.trans hq8) hσ) h3 hnot hJ hr

end CFSG.HardMathSupport.Dickson.Sec6.I923
