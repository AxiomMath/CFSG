module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H1429SubSymp
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.SporthOrth

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1429Sub

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Dickson.DefCharOuter.Export
open CFSG.HardMathSupport.Dickson.DefCharOuter.Export.Sporth
open CFSG.HardMathSupport.Dickson.I271 (isChevSimple_of_mulEquiv isLTwoTwentySeven_of_mulEquiv)
open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.RankThree.Classical.SteinbergBY
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCOrthogonalSubfield
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.HardMathSupport.Lang.Proving
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

section Generic

variable {K : Type} [Field K] [Finite K] {k : Subfield K} {d : ℕ}
  {Q₀ : QuadraticForm k (Fin d → k)} {Q : QuadraticForm K (Fin d → K)} {σ : K ≃+* K}

theorem exists_equiv_fieldAutT (S : SubfieldSetup k Q₀ Q σ 3)
    (hE : ∀ γ : MulAut (matrixProjectiveDerived Q),
      (∀ t ∈ subfieldDerivedImage k S.hext, γ t = t) → γ ∈ matrixProjectiveImage Q)
    (hdvd : 3 ∣ Nat.card (matrixProjectiveDerived Q₀)) {I : Subgroup (matrixProjectiveDerived Q)}
    (hI : GLAPComponent 3 (fixSubgroup (fieldAutT Q σ S.hQσ)) I) :
    Nonempty (PSimple 3 I ≃* matrixProjectiveDerived Q₀) := by
  have hd : 0 < d := three_le_of_totallySingular k S.hT₀
  have hconc := subfield_conclusion orthogonal_high_Witt_subfield_pointwise_centralizer S hE
  obtain ⟨⟨-, hsimp, hnab⟩, hordy, hfixN, hJN, hJnorm, hquot, -, -, hfixJ, -⟩ := hconc
  haveI := hJnorm
  have hfix' : fixSubgroup (fieldAutT Q σ S.hQσ) = subfieldFixedGroup k Q₀ Q :=
    Subgroup.ext fun t => hfixN t
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := IsPGroup.isNilpotent (hquot : IsPGroup 2 _)
  rw [hfix'] at hI
  have hIJ := eq_of_component hJN inferInstance hsimp hI
  rw [hIJ]
  have hdvd' : 3 ∣ Nat.card ↥(subfieldDerivedImage k S.hext) := by
    rw [← Nat.card_congr (inclEquiv k S.hext hd).toEquiv]
    exact hdvd
  exact ⟨(pSimple_equiv_self hsimp hnab hdvd').trans (inclEquiv k S.hext hd).symm⟩

theorem exists_equiv_of_fieldDescent {G : Type} [Group G] [Finite G]
    {Q' : QuadraticForm K (Fin d → K)} {Q₀' : QuadraticForm k (Fin d → k)}
    (S : SubfieldSetup k Q₀' Q' σ 3)
    (hE : ∀ γ : MulAut (matrixProjectiveDerived Q'),
      (∀ t ∈ subfieldDerivedImage k S.hext, γ t = t) → γ ∈ matrixProjectiveImage Q')
    (e : G ≃* matrixProjectiveDerived Q) (β : MulAut G) (U : similarityPairs Q)
    (hUβ : matrixProjectiveConjugationHom Q U = MulAut.congr e β)
    (Θ : matrixProjectiveDerived Q ≃* matrixProjectiveDerived Q') (g' : similarityPairs Q')
    (hl : g'.val.left = 1) (hr : g'.val.right = σ)
    (hΘ : ∀ x, Θ (matrixProjectiveConjugationHom Q U x) =
      matrixProjectiveConjugationHom Q' g' (Θ x))
    (hdvd : 3 ∣ Nat.card (matrixProjectiveDerived Q₀')) {I : Subgroup G}
    (hI : GLAPComponent 3 (fixSubgroup β) I) :
    Nonempty (PSimple 3 I ≃* matrixProjectiveDerived Q₀') := by
  have hg' : g' = fieldPair Q' σ S.hQσ := Subtype.ext (SemidirectProduct.ext hl hr)
  have hcongr : MulAut.congr (e.trans Θ) β = fieldAutT Q' σ S.hQσ := by
    refine MulEquiv.ext fun x => ?_
    have h1 : (MulAut.congr (e.trans Θ) β) x = Θ ((MulAut.congr e β) (Θ.symm x)) := rfl
    rw [h1, ← hUβ, hΘ, MulEquiv.apply_symm_apply, hg']
    rfl
  obtain ⟨hI', ⟨eI⟩⟩ := component_transport (e.trans Θ) hcongr hI
  obtain ⟨e2⟩ := exists_equiv_fieldAutT S hE hdvd hI'
  exact ⟨eI.trans e2⟩

end Generic

section Odd

open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
  (statedProjectiveReindexEquiv)
open CFSG.LieType.Universal.Spin (quadOdd coe_quadOdd)
open CFSG.RankThree.PartOne.KCOrthogonalAut (matrixProjectiveImage_eq_top_odd)

theorem exists_fixModel_pomegaOdd {G : Type} [Group G] [Finite G] {n f : ℕ}
    (hG : StatedClassicalModel G .POmegaOdd n 3 f) {β : MulAut G} (hβ : β ^ 3 = 1)
    (hout : β ∉ (MulAut.conj : G →* MulAut G).range) {I : Subgroup G}
    (hI : GLAPComponent 3 (fixSubgroup β) I) :
    ∃ a : ℕ, 1 ≤ a ∧ f = 3 * a ∧ StatedClassicalModel (PSimple 3 I) .POmegaOdd n 3 a := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨-, hf, hn3, -⟩ := hG.1
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hG.2
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaOdd
    (Or.inl rfl) n 3 f hG K hK e
  obtain ⟨hchar, -⟩ := coordinate_model_witness_odd hG K hK e
  have h2K : ringChar K ≠ 2 := by rw [hchar]; exact hp2
  have htop : matrixProjectiveImage (coordinateQuadOdd n K) = ⊤ :=
    matrixProjectiveImage_eq_top_odd K n hn3 h2K
  obtain ⟨hD, hord⟩ := outer_order_prime (coordinateOddWitnessEquiv K e) hgates hp hp2 hβ hout
  have hE : MulAut.congr (coordinateOddWitnessEquiv K e) β ∈
      matrixProjectiveImage (coordinateQuadOdd n K) := by
    rw [htop]
    exact Subgroup.mem_top _
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' G .POmegaOdd (Or.inl rfl)
    n 3 f 3 hG hp hp2 K hK e _ hE hD hord
  obtain ⟨g, hgE⟩ := hE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord', hcard, U, _, _, hUκ, hUr, _, hDisp⟩ := hrest g.val.right ⟨g, hgE, rfl⟩
  obtain ⟨_, _, -, -, hT'⟩ := hDisp
  obtain ⟨_, _, -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT'
  have hord'' : orderOf U.val.right = 3 := by
    rw [hUr]
    exact hord'
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = 3 ^ (f / 3) := by
    rw [hUr]
    exact hcard
  have hσk : ∀ x, x ∈ semilinearFixedSubfield U.val.right ↔ U.val.right x = x := fun x =>
    RingHom.mem_eqLocusField
  have hfp : 1 ≤ f / 3 := Nat.div_pos (Nat.le_of_dvd hf hpf) (by norm_num)
  have hmodelk : StatedClassicalModel (matrixProjectiveDerived
      (coordinateQuadOdd n (semilinearFixedSubfield U.val.right))) .POmegaOdd n 3 (f / 3) :=
    ⟨⟨hp, hfp, hn3, hp2⟩, _, inferInstance, inferInstance, hcard',
      ⟨(statedProjectiveReindexEquiv (oddIndexEquiv n) (quadOdd n _) (coe_quadOdd n _)).symm⟩⟩
  have ht : (StatedLieTag.POmegaOdd = .PSp ∧ 2 ≤ n) ∨
      (StatedLieTag.POmegaOdd = .POmegaOdd ∧ 3 ≤ n) ∨
      (StatedLieTag.POmegaOdd = .POmegaPlus ∧ 4 ≤ n) ∨
      (StatedLieTag.POmegaOdd = .POmegaMinus ∧ 4 ≤ n) := Or.inr (Or.inl ⟨rfl, hn3⟩)
  obtain ⟨eI⟩ := exists_equiv_of_fieldDescent
    (subfieldSetup_odd (semilinearFixedSubfield U.val.right) hσk hp hp2 hord'' hn3
      (Ring.two_ne_zero h2K))
    (fun γ _ => by rw [htop]; exact Subgroup.mem_top γ) (coordinateOddWitnessEquiv K e) β U hUκ Θ
    g' hg'l hg'r hΘ (dvd_card hmodelk ht) hI
  exact ⟨f / 3, hfp, by omega, CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv eI.symm hmodelk⟩

end Odd

section Minus

open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
  (statedProjectiveReindexEquiv)
open CFSG.LieType.Universal.Spin (quadMinus coe_quadMinus)
open CFSG.RankThree.PartOne.KCOrthogonalAut (matrixProjectiveImage_eq_top_minus)

theorem exists_fixModel_pomegaMinus {G : Type} [Group G] [Finite G] {n f : ℕ}
    (hG : StatedClassicalModel G .POmegaMinus n 3 f) {β : MulAut G} (hβ : β ^ 3 = 1)
    (hout : β ∉ (MulAut.conj : G →* MulAut G).range) {I : Subgroup G}
    (hI : GLAPComponent 3 (fixSubgroup β) I) :
    ∃ a : ℕ, 1 ≤ a ∧ f = 3 * a ∧ StatedClassicalModel (PSimple 3 I) .POmegaMinus n 3 a := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨-, hf, hn4⟩ := hG.1
  obtain ⟨K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hG.2
  have hn1 : 1 ≤ n := by omega
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaMinus
    (Or.inr (Or.inr rfl)) n 3 f hG hn1 K hK b c hirr e
  obtain ⟨hD, hord⟩ := outer_order_prime (coordinateMinusWitnessEquiv K hn1 b c e) hgates hp hp2
    hβ hout
  have htop : matrixProjectiveImage (coordinateQuadMinus n K hn1 b c) = ⊤ :=
    matrixProjectiveImage_eq_top_minus K n hn4 b c hirr
  have hE : MulAut.congr (coordinateMinusWitnessEquiv K hn1 b c e) β ∈
      matrixProjectiveImage (coordinateQuadMinus n K hn1 b c) := by
    rw [htop]
    exact Subgroup.mem_top _
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' G .POmegaMinus
    (Or.inr (Or.inr rfl)) n 3 f 3 hG hp hp2 hn1 K hK b c hirr e _ hE hD hord
  obtain ⟨g, hgE⟩ := hE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord', hcard, U, _, _, hUκ, hUr, _, hDisp⟩ := hrest g.val.right ⟨g, hgE, rfl⟩
  obtain ⟨b', c', hirr', _, _, -, -, hT'⟩ := hDisp
  obtain ⟨_, _, -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT'
  have hord'' : orderOf U.val.right = 3 := by
    rw [hUr]
    exact hord'
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = 3 ^ (f / 3) := by
    rw [hUr]
    exact hcard
  have hσk : ∀ x, x ∈ semilinearFixedSubfield U.val.right ↔ U.val.right x = x := fun x =>
    RingHom.mem_eqLocusField
  have hfp : 1 ≤ f / 3 := Nat.div_pos (Nat.le_of_dvd hf hpf) (by norm_num)
  obtain ⟨m, hm⟩ := hpf
  have hdiv : f / 3 = m := by rw [hm]; exact Nat.mul_div_cancel_left m (by norm_num)
  have hcardm : Nat.card (semilinearFixedSubfield U.val.right) = 3 ^ m := by
    rw [hcard', hdiv]
  have hm1 : 1 ≤ m := by
    rw [hdiv] at hfp
    exact hfp
  have hK' : Nat.card K = 3 ^ (m * 3) := by rw [hK, hm, mul_comm]
  have hdeg := finrank_subfield_eq (semilinearFixedSubfield U.val.right) hp hm1 hcardm hK'
  have hirrK := rootFree_of_odd_degree (semilinearFixedSubfield U.val.right) hp hp2 hdeg b' c' hirr'
  have hmodelk : StatedClassicalModel (matrixProjectiveDerived
      (coordinateQuadMinus n (semilinearFixedSubfield U.val.right) hn1 b' c')) .POmegaMinus n 3
      (f / 3) :=
    ⟨⟨hp, hfp, hn4⟩, _, inferInstance, inferInstance, hcard', b', c', hirr',
      ⟨(statedProjectiveReindexEquiv (minusIndexEquiv n hn1) (quadMinus n _ b' c')
        (coe_quadMinus n _ b' c')).symm⟩⟩
  have ht : (StatedLieTag.POmegaMinus = .PSp ∧ 2 ≤ n) ∨
      (StatedLieTag.POmegaMinus = .POmegaOdd ∧ 3 ≤ n) ∨
      (StatedLieTag.POmegaMinus = .POmegaPlus ∧ 4 ≤ n) ∨
      (StatedLieTag.POmegaMinus = .POmegaMinus ∧ 4 ≤ n) := Or.inr (Or.inr (Or.inr ⟨rfl, hn4⟩))
  obtain ⟨eI⟩ := exists_equiv_of_fieldDescent
    (subfieldSetup_minus (semilinearFixedSubfield U.val.right) hσk hp hp2 hord'' hn4 hdeg b' c'
      hirr')
    (fun γ _ => by
      rw [matrixProjectiveImage_eq_top_minus K n hn4 _ _ hirrK]
      exact Subgroup.mem_top γ)
    (coordinateMinusWitnessEquiv K hn1 b c e) β U hUκ Θ g' hg'l hg'r hΘ (dvd_card hmodelk ht) hI
  exact ⟨f / 3, hfp, by omega, CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv eI.symm hmodelk⟩

end Minus

section Plus

open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
  (statedProjectiveReindexEquiv)
open CFSG.LieType.Universal.Spin (quadPlus coe_quadPlus)
open CFSG.RankThree.PartOne.KCOrthogonalAut (matrixProjectiveImage_eq_top_plus)

theorem exists_fixModel_pomegaPlus {G : Type} [Group G] [Finite G] {n f : ℕ} (hn5 : 5 ≤ n)
    (hG : StatedClassicalModel G .POmegaPlus n 3 f) {β : MulAut G} (hβ : β ^ 3 = 1)
    (hout : β ∉ (MulAut.conj : G →* MulAut G).range) {I : Subgroup G}
    (hI : GLAPComponent 3 (fixSubgroup β) I) :
    ∃ a : ℕ, 1 ≤ a ∧ f = 3 * a ∧ StatedClassicalModel (PSimple 3 I) .POmegaPlus n 3 a := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨-, hf, hn4⟩ := hG.1
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hG.2
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaPlus
    (Or.inr (Or.inl rfl)) n 3 f hG K hK e
  obtain ⟨hD, hord⟩ := outer_order_prime (coordinatePlusWitnessEquiv K e) hgates hp hp2 hβ hout
  have hE : MulAut.congr (coordinatePlusWitnessEquiv K e) β ∈
      matrixProjectiveImage (coordinateQuadPlus n K) := by
    rw [matrixProjectiveImage_eq_top_plus K n hn5]
    exact Subgroup.mem_top _
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' G .POmegaPlus
    (Or.inr (Or.inl rfl)) n 3 f 3 hG hp hp2 K hK e _ hE hD hord
  obtain ⟨g, hgE⟩ := hE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord', hcard, U, _, _, hUκ, hUr, _, hDisp⟩ := hrest g.val.right ⟨g, hgE, rfl⟩
  obtain ⟨_, _, -, -, hT'⟩ := hDisp
  obtain ⟨_, _, -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT'
  have hord'' : orderOf U.val.right = 3 := by
    rw [hUr]
    exact hord'
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = 3 ^ (f / 3) := by
    rw [hUr]
    exact hcard
  have hσk : ∀ x, x ∈ semilinearFixedSubfield U.val.right ↔ U.val.right x = x := fun x =>
    RingHom.mem_eqLocusField
  have hfp : 1 ≤ f / 3 := Nat.div_pos (Nat.le_of_dvd hf hpf) (by norm_num)
  have hmodelk : StatedClassicalModel (matrixProjectiveDerived
      (coordinateQuadPlus n (semilinearFixedSubfield U.val.right))) .POmegaPlus n 3 (f / 3) :=
    ⟨⟨hp, hfp, hn4⟩, _, inferInstance, inferInstance, hcard',
      ⟨(statedProjectiveReindexEquiv (plusIndexEquiv n) (quadPlus n _) (coe_quadPlus n _)).symm⟩⟩
  have ht : (StatedLieTag.POmegaPlus = .PSp ∧ 2 ≤ n) ∨
      (StatedLieTag.POmegaPlus = .POmegaOdd ∧ 3 ≤ n) ∨
      (StatedLieTag.POmegaPlus = .POmegaPlus ∧ 4 ≤ n) ∨
      (StatedLieTag.POmegaPlus = .POmegaMinus ∧ 4 ≤ n) := Or.inr (Or.inr (Or.inl ⟨rfl, hn4⟩))
  have S := subfieldSetup_plus (semilinearFixedSubfield U.val.right) hσk hp hp2 hord''
    (by omega : 3 ≤ n)
  obtain ⟨eI⟩ := exists_equiv_of_fieldDescent S (fun γ _ => by
      rw [matrixProjectiveImage_eq_top_plus K n hn5]
      exact Subgroup.mem_top γ)
    (coordinatePlusWitnessEquiv K e) β U hUκ Θ g' hg'l hg'r hΘ (dvd_card hmodelk ht) hI
  exact ⟨f / 3, hfp, by omega, CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv eI.symm hmodelk⟩

end Plus

end CFSG.LocalAnalysis.GLTheoremA.H1429Sub

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.GLTheoremA.H1429Sub

theorem i1429SubOrth_holds : I1429SubLieAt SubIsOrth := by
  intro S _ _ hS hnc d hchar hP ⟨e⟩ β hβ hout I hI hU
  have hord : orderOf β = 3 := orderOf_three_of_not_inner hβ hout
  obtain ⟨d, hv⟩ := d
  rcases hP with ⟨n, q, hd, hn⟩ | ⟨n, q, hd, hn⟩ | ⟨n, q, hd⟩
  · cases hd
    have hq3 : q.p = 3 := by simpa using hchar
    have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
      ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
    rcases CFSG.Models.lieModel_B n q hv e with hm | hm
    · have hm' : StatedClassicalModel S .PSp n q.p q.exponent :=
        hm.statedClassicalModel_of_ne_zero (by omega)
      rw [hq3] at hm'
      obtain ⟨a, ha, hf, hmI⟩ := exists_fixModel_psp hm' hord hout hI
      obtain ⟨-, hn2, -⟩ := finish_classical hmI hU
      omega
    · have hm' : StatedClassicalModel S .POmegaOdd n q.p q.exponent :=
        hm.statedClassicalModel_of_ne_zero (by omega)
      rw [hq3] at hm'
      obtain ⟨a, ha, hf, hmI⟩ := exists_fixModel_pomegaOdd hm' hβ hout hI
      obtain ⟨ht, -, -⟩ := finish_classical hmI hU
      exact absurd ht (by decide)
  · cases hd
    have hq3 : q.p = 3 := by simpa using hchar
    have hm' : StatedClassicalModel S .POmegaPlus n q.p q.exponent :=
      (CFSG.Models.lieModel_D n q hv e).statedClassicalModel_of_ne_zero (by omega)
    rw [hq3] at hm'
    obtain ⟨a, ha, hf, hmI⟩ := exists_fixModel_pomegaPlus hn hm' hβ hout hI
    obtain ⟨ht, -, -⟩ := finish_classical hmI hU
    exact absurd ht (by decide)
  · cases hd
    have hq3 : q.p = 3 := by simpa using hchar
    have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
      ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
    have hm' : StatedClassicalModel S .POmegaMinus n q.p q.exponent :=
      (CFSG.Models.lieModel_twistedD n q hv e).statedClassicalModel_of_ne_zero (by omega)
    rw [hq3] at hm'
    obtain ⟨a, ha, hf, hmI⟩ := exists_fixModel_pomegaMinus hm' hβ hout hI
    obtain ⟨ht, -, -⟩ := finish_classical hmI hU
    exact absurd ht (by decide)

end CFSG.LocalAnalysis.GLTheoremA

end
