module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.SporthChev
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldBY
public import CFSG.HardMathSupport.Lang.Proving.OrthogonalFieldDescentOdd
import CFSG.RankThree.PartOne.KC.OrthogonalNoninnerPlaneModel
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.SporthGeneric

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.Export.Sporth

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Dickson.DefCharOuter.Export
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
open CFSG.ComponentClassification (OuterAutomorphisms.inner OuterAutomorphisms.inner_normal
  OuterAutomorphisms.congr_conj)

section Field

variable {K : Type} [Field K] [Finite K] {k : Subfield K} {d : ℕ}
  {Q₀ : QuadraticForm k (Fin d → k)} {Q : QuadraticForm K (Fin d → K)} {σ : K ≃+* K} {p : ℕ}

theorem outerCentData_of_fieldAutT (S : SubfieldSetup k Q₀ Q σ p)
    (hE : ∀ γ : MulAut (matrixProjectiveDerived Q),
      (∀ t ∈ subfieldDerivedImage k S.hext, γ t = t) → γ ∈ matrixProjectiveImage Q)
    (hout : fieldAutT Q σ S.hQσ ∉ innerAut (matrixProjectiveDerived Q))
    (hchev : IsChevSimple p (matrixProjectiveDerived Q₀))
    (hdvd : p ∣ Nat.card (matrixProjectiveDerived Q₀))
    (hL27 : ¬ IsLTwoTwentySeven (matrixProjectiveDerived Q₀)) :
    OuterCentData p (fieldAutT Q σ S.hQσ) := by
  have hd : 0 < d := three_le_of_totallySingular k S.hT₀
  have hconc := subfield_conclusion orthogonal_high_Witt_subfield_pointwise_centralizer S hE
  obtain ⟨⟨-, hsimp, hnab⟩, hordy, hfixN, hJN, hJnorm, hquot, -, -, hfixJ, -⟩ := hconc
  haveI := hJnorm
  have hap : fieldAutT Q σ S.hQσ ^ p = 1 := by
    have h := pow_orderOf_eq_one (fieldAutT Q σ S.hQσ)
    rwa [hordy] at h
  have hZ := center_matrix_eq_bot hd S.hnd S.hT
  have hfix' : fixSubgroup (fieldAutT Q σ S.hQσ) = subfieldFixedGroup k Q₀ Q :=
    Subgroup.ext fun t => hfixN t
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := IsPGroup.isNilpotent (hquot : IsPGroup 2 _)
  have hfix : ∀ w : MulAut (matrixProjectiveDerived Q),
      (∀ x ∈ subfieldDerivedImage k S.hext, w x = x) →
        w ∈ Subgroup.zpowers (fieldAutT Q σ S.hQσ) := by
    intro w hw
    rw [← hfixJ]
    exact (mem_fixingSubgroup_iff _).mpr fun t ht => by simpa using hw t ht
  exact OuterCentData.of_fieldType_of_fix_eq S.hp hap hout hZ hfix' hJN hJnorm inferInstance hsimp
    hnab (isChevSimple_of_mulEquiv (inclEquiv k S.hext hd) hchev)
    (by rw [← Nat.card_congr (inclEquiv k S.hext hd).toEquiv]; exact hdvd)
    (fun h => hL27 (isLTwoTwentySeven_of_mulEquiv (inclEquiv k S.hext hd).symm h)) hfix

theorem outerCentData_of_fieldDescent {G : Type} [Group G] [Finite G]
    {Q' : QuadraticForm K (Fin d → K)} {Q₀' : QuadraticForm k (Fin d → k)}
    (S : SubfieldSetup k Q₀' Q' σ p)
    (hE : ∀ γ : MulAut (matrixProjectiveDerived Q'),
      (∀ t ∈ subfieldDerivedImage k S.hext, γ t = t) → γ ∈ matrixProjectiveImage Q')
    (e : G ≃* matrixProjectiveDerived Q) (β : MulAut G) (U : similarityPairs Q)
    (hUβ : matrixProjectiveConjugationHom Q U = MulAut.congr e β)
    (Θ : matrixProjectiveDerived Q ≃* matrixProjectiveDerived Q') (g' : similarityPairs Q')
    (hl : g'.val.left = 1) (hr : g'.val.right = σ)
    (hΘ : ∀ x, Θ (matrixProjectiveConjugationHom Q U x) =
      matrixProjectiveConjugationHom Q' g' (Θ x))
    (hout : β ∉ innerAut G)
    (hchev : IsChevSimple p (matrixProjectiveDerived Q₀'))
    (hdvd : p ∣ Nat.card (matrixProjectiveDerived Q₀'))
    (hL27 : ¬ IsLTwoTwentySeven (matrixProjectiveDerived Q₀')) :
    OuterCentData p β := by
  have hg' : g' = fieldPair Q' σ S.hQσ := Subtype.ext (SemidirectProduct.ext hl hr)
  have hcongr : MulAut.congr (e.trans Θ) β = fieldAutT Q' σ S.hQσ := by
    refine MulEquiv.ext fun x => ?_
    have h1 : (MulAut.congr (e.trans Θ) β) x = Θ ((MulAut.congr e β) (Θ.symm x)) := rfl
    rw [h1, ← hUβ, hΘ, MulEquiv.apply_symm_apply, hg']
    rfl
  refine OuterCentData.of_congr S.hp (e.trans Θ) ?_
  rw [hcongr]
  refine outerCentData_of_fieldAutT S hE ?_ hchev hdvd hL27
  rw [← hcongr]
  intro hin
  exact hout ((congr_mem_innerAut_iff (e.trans Θ) β).1 hin)

end Field

section Gates

variable {K : Type} [Field K] [Finite K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {f p : ℕ}

theorem mem_E_of_pow_eq_one_of_three_lt (hg : OrthogonalGates Q f) (hp : p.Prime) (hp3 : 3 < p)
    {β : MulAut (matrixProjectiveDerived Q)} (hβp : β ^ p = 1) : β ∈ matrixProjectiveImage Q := by
  have hpg : IsPGroup p (Subgroup.zpowers β) := by
    intro g
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp g.2
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, ← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hβp, one_zpow]
    rfl
  have hK0 := hg.2.2.2.2.2.2.1 p hp hp3 _ hpg
  have h1 : β ∈ projectivePointFamilyAut Q := hg.2.2.2.2.1 (hK0 (Subgroup.mem_zpowers β))
  rw [hg.2.2.2.2.2.1] at h1
  exact h1

theorem exists_conj_of_mem_D_of_pow_eq_one (hg : OrthogonalGates Q f) (hp : p.Prime)
    (hp2 : p ≠ 2) {β : MulAut (matrixProjectiveDerived Q)}
    (hβD : β ∈ (linearConjugationHom Q).range) (hβp : β ^ p = 1) :
    ∃ t : matrixProjectiveDerived Q, MulAut.conj t = β := by
  obtain ⟨-, k, hk⟩ := hg.2.2.1
  have : (OuterAutomorphisms.inner (matrixProjectiveDerived Q)).Normal :=
    OuterAutomorphisms.inner_normal _
  exact CFSG.RankThree.PartOne.KCOrthogonalNoninner.mem_of_pow_eq_one_of_relIndex_eq_two_pow hk hp
    hp2 hβD hβp

theorem outer_order_prime {G : Type} [Group G] (e : G ≃* matrixProjectiveDerived Q)
    (hg : OrthogonalGates Q f) (hp : p.Prime) (hp2 : p ≠ 2) {β : MulAut G} (hβ : β ^ p = 1)
    (hout : β ∉ innerAut G) :
    MulAut.congr e β ∉ (linearConjugationHom Q).range ∧ orderOf (MulAut.congr e β) = p := by
  have hβ' : MulAut.congr e β ^ p = 1 := by rw [← map_pow, hβ, map_one]
  have hD : MulAut.congr e β ∉ (linearConjugationHom Q).range := by
    intro hD
    obtain ⟨t, ht⟩ := exists_conj_of_mem_D_of_pow_eq_one hg hp hp2 hD hβ'
    refine hout ⟨e.symm t, (MulAut.congr e).injective ?_⟩
    rw [OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply, ht]
  refine ⟨hD, ?_⟩
  have hne1 : MulAut.congr e β ≠ 1 := fun h => hD (h ▸ one_mem _)
  haveI : Fact p.Prime := ⟨hp⟩
  exact orderOf_eq_prime hβ' hne1

end Gates

section Odd

open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
  (statedProjectiveReindexEquiv)
open CFSG.LieType.Universal.Spin (quadOdd coe_quadOdd)
open CFSG.RankThree.PartOne.KCOrthogonalAut (matrixProjectiveImage_eq_top_odd)

theorem outerCentData_pomegaOdd {G : Type} [Group G] [Finite G] {n ℓ f : ℕ}
    (hG : StatedClassicalModel G .POmegaOdd n ℓ f) {p : ℕ} (hp : p.Prime) (hpℓ : p = ℓ)
    {β : MulAut G} (hβ : β ^ p = 1) (hout : β ∉ innerAut G) : OuterCentData p β := by
  subst hpℓ
  obtain ⟨-, hf, hn3, hp2⟩ := hG.1
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hG.2
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaOdd
    (Or.inl rfl) n p f hG K hK e
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
    n p f p hG hp hp2 K hK e _ hE hD hord
  obtain ⟨g, hgE⟩ := hE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord', hcard, U, _, _, hUκ, hUr, _, hDisp⟩ := hrest g.val.right ⟨g, hgE, rfl⟩
  obtain ⟨_, _, -, -, hT'⟩ := hDisp
  obtain ⟨_, _, -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT'
  have hord'' : orderOf U.val.right = p := by
    rw [hUr]
    exact hord'
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = p ^ (f / p) := by
    rw [hUr]
    exact hcard
  have hσk : ∀ x, x ∈ semilinearFixedSubfield U.val.right ↔ U.val.right x = x := fun x =>
    RingHom.mem_eqLocusField
  have hfp : 1 ≤ f / p := Nat.div_pos (Nat.le_of_dvd hf hpf) hp.pos
  have hmodelk : StatedClassicalModel (matrixProjectiveDerived
      (coordinateQuadOdd n (semilinearFixedSubfield U.val.right))) .POmegaOdd n p (f / p) :=
    ⟨⟨hp, hfp, hn3, hp2⟩, _, inferInstance, inferInstance, hcard',
      ⟨(statedProjectiveReindexEquiv (oddIndexEquiv n) (quadOdd n _) (coe_quadOdd n _)).symm⟩⟩
  have ht : (StatedLieTag.POmegaOdd = .PSp ∧ 2 ≤ n) ∨
      (StatedLieTag.POmegaOdd = .POmegaOdd ∧ 3 ≤ n) ∨
      (StatedLieTag.POmegaOdd = .POmegaPlus ∧ 4 ≤ n) ∨
      (StatedLieTag.POmegaOdd = .POmegaMinus ∧ 4 ≤ n) := Or.inr (Or.inl ⟨rfl, hn3⟩)
  exact outerCentData_of_fieldDescent
    (subfieldSetup_odd (semilinearFixedSubfield U.val.right) hσk hp hp2 hord'' hn3
      (Ring.two_ne_zero h2K))
    (fun γ _ => by rw [htop]; exact Subgroup.mem_top γ) (coordinateOddWitnessEquiv K e) β U hUκ Θ
    g' hg'l hg'r hΘ hout (isChevSimple_of_pomegaOdd hmodelk) (dvd_card hmodelk ht)
    (not_isLTwoTwentySeven hmodelk ht)

end Odd

section Minus

open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
  (statedProjectiveReindexEquiv)
open CFSG.LieType.Universal.Spin (quadMinus coe_quadMinus)
open CFSG.RankThree.PartOne.KCOrthogonalAut (matrixProjectiveImage_eq_top_minus)

theorem outerCentData_pomegaMinus {G : Type} [Group G] [Finite G] {n ℓ f : ℕ}
    (hG : StatedClassicalModel G .POmegaMinus n ℓ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpℓ : p = ℓ) {β : MulAut G} (hβ : β ^ p = 1) (hout : β ∉ innerAut G) :
    OuterCentData p β := by
  subst hpℓ
  obtain ⟨-, hf, hn4⟩ := hG.1
  obtain ⟨K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hG.2
  have hn1 : 1 ≤ n := by omega
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaMinus
    (Or.inr (Or.inr rfl)) n p f hG hn1 K hK b c hirr e
  obtain ⟨hD, hord⟩ := outer_order_prime (coordinateMinusWitnessEquiv K hn1 b c e) hgates hp hp2
    hβ hout
  have htop : matrixProjectiveImage (coordinateQuadMinus n K hn1 b c) = ⊤ :=
    matrixProjectiveImage_eq_top_minus K n hn4 b c hirr
  have hE : MulAut.congr (coordinateMinusWitnessEquiv K hn1 b c e) β ∈
      matrixProjectiveImage (coordinateQuadMinus n K hn1 b c) := by
    rw [htop]
    exact Subgroup.mem_top _
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' G .POmegaMinus
    (Or.inr (Or.inr rfl)) n p f p hG hp hp2 hn1 K hK b c hirr e _ hE hD hord
  obtain ⟨g, hgE⟩ := hE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord', hcard, U, _, _, hUκ, hUr, _, hDisp⟩ := hrest g.val.right ⟨g, hgE, rfl⟩
  obtain ⟨b', c', hirr', _, _, -, -, hT'⟩ := hDisp
  obtain ⟨_, _, -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT'
  have hord'' : orderOf U.val.right = p := by
    rw [hUr]
    exact hord'
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = p ^ (f / p) := by
    rw [hUr]
    exact hcard
  have hσk : ∀ x, x ∈ semilinearFixedSubfield U.val.right ↔ U.val.right x = x := fun x =>
    RingHom.mem_eqLocusField
  have hfp : 1 ≤ f / p := Nat.div_pos (Nat.le_of_dvd hf hpf) hp.pos
  obtain ⟨m, hm⟩ := hpf
  have hdiv : f / p = m := by rw [hm]; exact Nat.mul_div_cancel_left m hp.pos
  have hcardm : Nat.card (semilinearFixedSubfield U.val.right) = p ^ m := by
    rw [hcard', hdiv]
  have hm1 : 1 ≤ m := by
    rw [hdiv] at hfp
    exact hfp
  have hK' : Nat.card K = p ^ (m * p) := by rw [hK, hm, mul_comm]
  have hdeg := finrank_subfield_eq (semilinearFixedSubfield U.val.right) hp hm1 hcardm hK'
  have hirrK := rootFree_of_odd_degree (semilinearFixedSubfield U.val.right) hp hp2 hdeg b' c' hirr'
  have hmodelk : StatedClassicalModel (matrixProjectiveDerived
      (coordinateQuadMinus n (semilinearFixedSubfield U.val.right) hn1 b' c')) .POmegaMinus n p
      (f / p) :=
    ⟨⟨hp, hfp, hn4⟩, _, inferInstance, inferInstance, hcard', b', c', hirr',
      ⟨(statedProjectiveReindexEquiv (minusIndexEquiv n hn1) (quadMinus n _ b' c')
        (coe_quadMinus n _ b' c')).symm⟩⟩
  have ht : (StatedLieTag.POmegaMinus = .PSp ∧ 2 ≤ n) ∨
      (StatedLieTag.POmegaMinus = .POmegaOdd ∧ 3 ≤ n) ∨
      (StatedLieTag.POmegaMinus = .POmegaPlus ∧ 4 ≤ n) ∨
      (StatedLieTag.POmegaMinus = .POmegaMinus ∧ 4 ≤ n) := Or.inr (Or.inr (Or.inr ⟨rfl, hn4⟩))
  exact outerCentData_of_fieldDescent
    (subfieldSetup_minus (semilinearFixedSubfield U.val.right) hσk hp hp2 hord'' hn4 hdeg b' c'
      hirr')
    (fun γ _ => by
      rw [matrixProjectiveImage_eq_top_minus K n hn4 _ _ hirrK]
      exact Subgroup.mem_top γ)
    (coordinateMinusWitnessEquiv K hn1 b c e) β U hUκ Θ g' hg'l hg'r hΘ hout
    (isChevSimple_of_pomegaMinus hmodelk) (dvd_card hmodelk ht)
    (not_isLTwoTwentySeven hmodelk ht)

end Minus

section Plus

open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
  (statedProjectiveReindexEquiv)
open CFSG.LieType.Universal.Spin (quadPlus coe_quadPlus)
open CFSG.RankThree.PartOne.KCOrthogonalAut (matrixProjectiveImage_eq_top_plus)

theorem outerCentData_pomegaPlus_of_mem_E {G : Type} [Group G] [Finite G] {n ℓ f : ℕ}
    (hG : StatedClassicalModel G .POmegaPlus n ℓ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ f) (e : G ≃* StatedProj (StatedOmega (StatedQuadPlus n K))) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p = ℓ) {β : MulAut G} (hβ : β ^ p = 1)
    (hout : β ∉ innerAut G)
    (hE : MulAut.congr (coordinatePlusWitnessEquiv K e) β ∈
      matrixProjectiveImage (coordinateQuadPlus n K)) :
    OuterCentData p β := by
  subst hpℓ
  obtain ⟨-, hf, hn4⟩ := hG.1
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaPlus
    (Or.inr (Or.inl rfl)) n p f hG K hK e
  obtain ⟨hD, hord⟩ := outer_order_prime (coordinatePlusWitnessEquiv K e) hgates hp hp2 hβ hout
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' G .POmegaPlus
    (Or.inr (Or.inl rfl)) n p f p hG hp hp2 K hK e _ hE hD hord
  obtain ⟨g, hgE⟩ := hE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord', hcard, U, _, _, hUκ, hUr, _, hDisp⟩ := hrest g.val.right ⟨g, hgE, rfl⟩
  obtain ⟨_, _, -, -, hT'⟩ := hDisp
  obtain ⟨_, _, -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT'
  have hord'' : orderOf U.val.right = p := by
    rw [hUr]
    exact hord'
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = p ^ (f / p) := by
    rw [hUr]
    exact hcard
  have hσk : ∀ x, x ∈ semilinearFixedSubfield U.val.right ↔ U.val.right x = x := fun x =>
    RingHom.mem_eqLocusField
  have hfp : 1 ≤ f / p := Nat.div_pos (Nat.le_of_dvd hf hpf) hp.pos
  have hmodelk : StatedClassicalModel (matrixProjectiveDerived
      (coordinateQuadPlus n (semilinearFixedSubfield U.val.right))) .POmegaPlus n p (f / p) :=
    ⟨⟨hp, hfp, hn4⟩, _, inferInstance, inferInstance, hcard',
      ⟨(statedProjectiveReindexEquiv (plusIndexEquiv n) (quadPlus n _) (coe_quadPlus n _)).symm⟩⟩
  have ht : (StatedLieTag.POmegaPlus = .PSp ∧ 2 ≤ n) ∨
      (StatedLieTag.POmegaPlus = .POmegaOdd ∧ 3 ≤ n) ∨
      (StatedLieTag.POmegaPlus = .POmegaPlus ∧ 4 ≤ n) ∨
      (StatedLieTag.POmegaPlus = .POmegaMinus ∧ 4 ≤ n) := Or.inr (Or.inr (Or.inl ⟨rfl, hn4⟩))
  have S := subfieldSetup_plus (semilinearFixedSubfield U.val.right) hσk hp hp2 hord''
    (by omega : 3 ≤ n)
  refine outerCentData_of_fieldDescent S ?_ (coordinatePlusWitnessEquiv K e) β U hUκ Θ g' hg'l
    hg'r hΘ hout (isChevSimple_of_pomegaPlus hmodelk) (dvd_card hmodelk ht)
    (not_isLTwoTwentySeven hmodelk ht)
  rcases (show n = 4 ∨ 5 ≤ n by omega) with h4 | h5
  · subst h4
    intro γ hγ
    have hmodelK : StatedClassicalModel (matrixProjectiveDerived (coordinateQuadPlus 4 K))
        .POmegaPlus 4 p f :=
      ⟨⟨hp, hf, hn4⟩, K, inferInstance, inferInstance, hK, ⟨(statedProjectiveReindexEquiv
        (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K)).symm⟩⟩
    exact mem_matrixProjectiveImage_plus_four _ hK hmodelK (statedProjectiveReindexEquiv
      (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K)).symm S.hext S.hnd₀ S.hT₀ γ hγ
  · intro γ _
    rw [matrixProjectiveImage_eq_top_plus K n h5]
    exact Subgroup.mem_top γ

theorem outerCentData_pomegaPlus {G : Type} [Group G] [Finite G] {n ℓ f : ℕ}
    (hG : StatedClassicalModel G .POmegaPlus n ℓ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpℓ : p = ℓ) (hD4 : n = 4 → p ≠ 3) {β : MulAut G} (hβ : β ^ p = 1)
    (hout : β ∉ innerAut G) : OuterCentData p β := by
  obtain ⟨-, -, hn4⟩ := hG.1
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hG.2
  refine outerCentData_pomegaPlus_of_mem_E hG K hK e hp hp2 hpℓ hβ hout ?_
  rcases (show n = 4 ∨ 5 ≤ n by omega) with h4 | h5
  · have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaPlus
      (Or.inr (Or.inl rfl)) n ℓ f hG K hK e
    have hp3 : 3 < p := by
      have := hp.two_le
      have := hD4 h4
      omega
    exact mem_E_of_pow_eq_one_of_three_lt hgates hp hp3 (by rw [← map_pow, hβ, map_one])
  · rw [matrixProjectiveImage_eq_top_plus K n h5]
    exact Subgroup.mem_top _

end Plus

end CFSG.HardMathSupport.Dickson.DefCharOuter.Export.Sporth
