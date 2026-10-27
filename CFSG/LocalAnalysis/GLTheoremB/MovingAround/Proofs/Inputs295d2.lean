module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs295d
import CFSG.HardMathSupport.Lang.Proving.OrthogonalFieldDescentOdd
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsL33d
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Field
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAll
import CFSG.HardMathSupport.Timmesfeld.CrossChar.G2LongFrame
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPReduction
import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CatTw
import CFSG.HardMathSupport.Malle.E27Lie.Cross.SymplecticPSp
import CFSG.HardMathSupport.Malle.E27Lie.Cross.UnitaryPSU
import CFSG.HardMathSupport.Malle.E27Lie.Cross.OrthOddModel
import CFSG.LieType.SeitzGeneration.SubfieldPairSUBridge
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToral

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs295d

open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.RankThree.Classical.SteinbergBY
open CFSG.RankThree.PartOne.KCOrthogonalSubfield
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.HardMathSupport.Lang.Proving
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.RankThree.PartOne.KCOrthogonalNoninner (mem_of_pow_eq_one_of_relIndex_eq_two_pow)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal
  (isPSolvable_of_mulEquiv)
open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure (isPSolvable_of_le)

section Field

open QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.OmMinus
open CFSG.RankThree.Classical2 (orthDerived ProjOrthDerived)

theorem three_dvd_card_matrixProjectiveDerived {k : Type} [Field k] [Finite k]
    (h3 : (3 : k) ≠ 0) {d : ℕ} {Q : QuadraticForm k (Fin d → k)}
    (hnd : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule k (Fin d → k), Module.finrank k U = 3 ∧ ∀ u ∈ U, Q u = 0) :
    3 ∣ Nat.card (matrixProjectiveDerived Q) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdim : 3 ≤ Module.finrank k (Fin d → k) := by
    obtain ⟨U, hU, -⟩ := hT
    rw [← hU]
    exact Submodule.finrank_le U
  obtain ⟨c, u, v, hr, -, -⟩ := exists_rotPair_of_polarNondegOn (polarNondegOn_top hnd)
    (by rwa [finrank_top])
  have hrO := hr.rotAut_mem_orthogonalGroup
  have hr3 := hr.rotAut_pow_three
  obtain ⟨-, -, -, -, -, -, hodd, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hnd hT
  have hrΩ : hr.rotAut ∈ orthDerived Q := hodd _ hrO
    ((by decide : Odd 3).of_dvd_nat (orderOf_dvd_of_pow_eq_one hr3))
  set y : ProjOrthDerived Q := QuotientGroup.mk ⟨hr.rotAut, hrΩ⟩ with hy
  have hy3 : y ^ 3 = 1 := by
    rw [hy, ← QuotientGroup.mk_pow]
    have : (⟨hr.rotAut, hrΩ⟩ : orthDerived Q) ^ 3 = 1 := Subtype.ext (by simpa using hr3)
    rw [this, QuotientGroup.mk_one]
  have hy1 : y ≠ 1 := by
    intro h1
    rw [hy, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    obtain ⟨a, ha⟩ := mem_scalars.1 h1
    have hQu : Q u ≠ 0 := by rw [hr.Q_u]; exact hr.c_ne
    have hu0 : u ≠ 0 := fun h => hQu (by rw [h, QuadraticMap.map_zero])
    have ha2 : a * a = 1 := by
      have h1 := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 hrO u
      rw [ha, QuadraticMap.map_smul, smul_eq_mul] at h1
      exact mul_right_cancel₀ hQu (by rw [one_mul]; exact h1)
    have hau : a • u = u := by
      have h1 := congrArg (fun f : (Fin d → k) ≃ₗ[k] (Fin d → k) => f u) hr3
      have hone : (1 : (Fin d → k) ≃ₗ[k] (Fin d → k)) u = u := rfl
      simp only [pow_succ, pow_zero, one_mul, LinearEquiv.mul_apply, ha, smul_smul, hone] at h1
      rwa [ha2, mul_one] at h1
    have ha1 : a = 1 := by
      have h0 : (a - 1) • u = 0 := by rw [sub_smul, one_smul, hau, sub_self]
      rcases smul_eq_zero.1 h0 with h | h
      · exact sub_eq_zero.1 h
      · exact absurd h hu0
    apply hr.rotAut_ne h3
    rw [ha, ha1, one_smul]
  have hord : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  rw [Nat.card_congr (CFSG.RankThree.PartOne.KCOrthComm.matrixProjEquiv Q).toEquiv, ← hord]
  exact orderOf_dvd_natCard y

theorem not_isPSolvable_fixSubgroup_fieldAutT {K : Type} [Field K] [Finite K] {k : Subfield K}
    {d : ℕ} {Q₀ : QuadraticForm k (Fin d → k)} {Q : QuadraticForm K (Fin d → K)} {σ : K ≃+* K}
    {p : ℕ} (h3 : (3 : K) ≠ 0) (S : SubfieldSetup k Q₀ Q σ p) :
    ¬ CFSG.HallHigman.IsPSolvable 3 ↥(fixSubgroup (fieldAutT Q σ S.hQσ)) := by
  have hd : 0 < d := three_le_of_totallySingular k S.hT₀
  obtain ⟨hsimp, hnonab⟩ := matrix_simple_nonabelian hd S.hnd₀ S.hT₀
  have h3k : (3 : k) ≠ 0 := fun h => h3 (by
    have h' : ((3 : k) : K) = ((0 : k) : K) := by rw [h]
    push_cast at h'
    exact h')
  have hcard := three_dvd_card_matrixProjectiveDerived h3k S.hnd₀ S.hT₀
  have hfix : fixSubgroup (fieldAutT Q σ S.hQσ) = subfieldFixedGroup k Q₀ Q :=
    Subgroup.ext fun t => fieldAutT_apply_iff S t
  have e : matrixProjectiveDerived Q₀ ≃* ↥(subfieldDerivedImage k S.hext) := inclEquiv k S.hext hd
  have hJs : IsSimpleGroup ↥(subfieldDerivedImage k S.hext) := by
    haveI := hsimp
    exact e.symm.isSimpleGroup
  have hJnc : ¬ IsMulCommutative ↥(subfieldDerivedImage k S.hext) := by
    rintro ⟨hc⟩
    obtain ⟨a, b, hab⟩ := hnonab
    apply hab
    apply e.injective
    rw [map_mul, map_mul]
    exact hc.comm _ _
  have hJ3 : 3 ∣ Nat.card ↥(subfieldDerivedImage k S.hext) := by
    rwa [← Nat.card_congr e.toEquiv]
  intro hs
  rw [hfix] at hs
  exact CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.not_isPSolvable_three_of_simple hJs
    hJnc hJ3 (isPSolvable_of_le hs (subfieldDerivedImage_le k S.hext))

theorem not_isPSolvable_of_fieldDescent {K : Type} [Field K] [Finite K] {k : Subfield K} {d : ℕ}
    {Q Q' : QuadraticForm K (Fin d → K)} {Q₀' : QuadraticForm k (Fin d → k)} {σ : K ≃+* K}
    {p : ℕ} (h3 : (3 : K) ≠ 0) (S : SubfieldSetup k Q₀' Q' σ p) (U : similarityPairs Q)
    (Θ : matrixProjectiveDerived Q ≃* matrixProjectiveDerived Q') (g' : similarityPairs Q')
    (hl : g'.val.left = 1) (hr : g'.val.right = σ)
    (hΘ : ∀ x, Θ (matrixProjectiveConjugationHom Q U x) =
      matrixProjectiveConjugationHom Q' g' (Θ x)) :
    ¬ CFSG.HallHigman.IsPSolvable 3 ↥(fixSubgroup (matrixProjectiveConjugationHom Q U)) := by
  have hg' : g' = fieldPair Q' σ S.hQσ := Subtype.ext (SemidirectProduct.ext hl hr)
  have hcongr : MulAut.congr Θ (matrixProjectiveConjugationHom Q U) = fieldAutT Q' σ S.hQσ := by
    refine MulEquiv.ext fun x => ?_
    have h1 : (MulAut.congr Θ (matrixProjectiveConjugationHom Q U)) x =
        Θ (matrixProjectiveConjugationHom Q U (Θ.symm x)) := rfl
    rw [h1, hΘ, MulEquiv.apply_symm_apply, hg']
    rfl
  intro hs
  apply not_isPSolvable_fixSubgroup_fieldAutT h3 S
  rw [← hcongr, Inputs295c.fixSubgroup_congr]
  exact isPSolvable_of_mulEquiv
    ((fixSubgroup (matrixProjectiveConjugationHom Q U)).equivMapOfInjective _ Θ.injective) hs

end Field

section Gates

variable {K : Type} [Field K] [Finite K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {f : ℕ}

theorem mem_E_of_top_omega (hg : OrthogonalGates Q f) (htop : projectivePointFamilyAut Q = ⊤)
    (β : MulAut (matrixProjectiveDerived Q)) : β ∈ matrixProjectiveImage Q := by
  have h1 : β ∈ projectivePointFamilyAut Q := htop ▸ Subgroup.mem_top β
  rwa [hg.2.2.2.2.2.1] at h1

theorem not_isPSolvable_of_gates_omega {G : Type} [Group G]
    (e : G ≃* matrixProjectiveDerived Q) (hg : OrthogonalGates Q f) (β : MulAut G)
    (hβ : β ^ 3 = 1) (hout : β ∉ (MulAut.conj : G →* MulAut G).range)
    (hE : MulAut.congr e β ∈ matrixProjectiveImage Q)
    (hdesc : ∀ a ∈ matrixProjectiveImage Q, a ∉ (linearConjugationHom Q).range →
      orderOf a = 3 → ¬ CFSG.HallHigman.IsPSolvable 3 ↥(fixSubgroup a)) :
    ¬ CFSG.HallHigman.IsPSolvable 3 ↥(fixSubgroup β) := by
  have hβ' : MulAut.congr e β ^ 3 = 1 := by rw [← map_pow, hβ, map_one]
  by_cases hD : MulAut.congr e β ∈ (linearConjugationHom Q).range
  · exfalso
    obtain ⟨-, k, hk⟩ := hg.2.2.1
    have : (CFSG.ComponentClassification.OuterAutomorphisms.inner
        (matrixProjectiveDerived Q)).Normal :=
      CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
    obtain ⟨t, ht⟩ := mem_of_pow_eq_one_of_relIndex_eq_two_pow hk Nat.prime_three (by norm_num)
      hD hβ'
    apply hout
    refine ⟨e.symm t, (MulAut.congr e).injective ?_⟩
    rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply, ht]
  · have hne1 : MulAut.congr e β ≠ 1 := fun h => hD (h ▸ one_mem _)
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hord : orderOf (MulAut.congr e β) = 3 := orderOf_eq_prime hβ' hne1
    intro hs
    apply hdesc _ hE hD hord
    rw [Inputs295c.fixSubgroup_congr]
    exact isPSolvable_of_mulEquiv ((fixSubgroup β).equivMapOfInjective _ e.injective) hs

end Gates

section Types

theorem three_ne_zero_of_card' {K : Type} [Field K] [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hℓ3 : ℓ ≠ 3) (hK : Nat.card K = ℓ ^ f) : (3 : K) ≠ 0 :=
  Inputs295c.three_ne_zero_of_card hℓ hℓ3 hK

theorem not_isPSolvable_omega_odd {G : Type} [Group G] {n ℓ f : ℕ}
    (hG : StatedClassicalModel G .POmegaOdd n ℓ f) (hℓ3 : ℓ ≠ 3) (β : MulAut G) (hβ : β ^ 3 = 1)
    (hout : β ∉ (MulAut.conj : G →* MulAut G).range) :
    ¬ CFSG.HallHigman.IsPSolvable 3 ↥(fixSubgroup β) := by
  obtain ⟨hℓ, -, hn3, hℓ2⟩ := hG.1
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hG.2
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaOdd
    (Or.inl rfl) n ℓ f hG K hK e
  have htop : projectivePointFamilyAut (coordinateQuadOdd n K) = ⊤ :=
    ((orthogonal_geometry_tail_model_point_family_invariant G .POmegaOdd
      (.inl rfl) n ℓ f hG) K hK).2
  obtain ⟨hchar, -, -, -⟩ := coordinate_model_witness_odd hG K hK e
  have h2 : (2 : K) ≠ 0 := by
    have hprime : (ringChar K).Prime := hchar ▸ hℓ
    rw [Ne, CFSG.ClassicalGroups.Orthogonal.two_eq_zero_iff_ringChar_eq_two hprime, hchar]
    exact hℓ2
  have h3 := three_ne_zero_of_card' hℓ hℓ3 hK
  refine not_isPSolvable_of_gates_omega (coordinateOddWitnessEquiv K e) hgates β hβ hout
    (mem_E_of_top_omega hgates htop _) ?_
  intro a haE haD hap
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' G .POmegaOdd (Or.inl rfl)
    n ℓ f 3 hG Nat.prime_three (by norm_num) K hK e a haE haD hap
  obtain ⟨g, hgE⟩ := haE
  obtain ⟨-, hrest⟩ := hdesc
  obtain ⟨hord, -, U, _, _, hUκ, hUr, _, hDisp⟩ := hrest g.val.right ⟨g, hgE, rfl⟩
  obtain ⟨_, _, -, -, hT'⟩ := hDisp
  obtain ⟨_, _, -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT'
  have hord' : orderOf U.val.right = 3 := by
    rw [hUr]
    exact hord
  have hσk : ∀ x, x ∈ semilinearFixedSubfield U.val.right ↔ U.val.right x = x := fun x =>
    RingHom.mem_eqLocusField
  rw [← hUκ]
  exact not_isPSolvable_of_fieldDescent h3
    (subfieldSetup_odd (semilinearFixedSubfield U.val.right) hσk Nat.prime_three (by norm_num)
      hord' hn3 h2) U Θ g' hg'l hg'r hΘ

theorem not_isPSolvable_omega_plus {G : Type} [Group G] {n ℓ f : ℕ}
    (hG : StatedClassicalModel G .POmegaPlus n ℓ f) (hℓ3 : ℓ ≠ 3) (hn5 : 5 ≤ n) (β : MulAut G)
    (hβ : β ^ 3 = 1) (hout : β ∉ (MulAut.conj : G →* MulAut G).range) :
    ¬ CFSG.HallHigman.IsPSolvable 3 ↥(fixSubgroup β) := by
  obtain ⟨hℓ, -, -⟩ := hG.1
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hG.2
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaPlus
    (Or.inr (Or.inl rfl)) n ℓ f hG K hK e
  have htop : projectivePointFamilyAut (coordinateQuadPlus n K) = ⊤ :=
    (CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit.orthogonal_geometry_plus_point_family_orbit
      hG hK e).2.2.2.2.1 hn5
  have h3 := three_ne_zero_of_card' hℓ hℓ3 hK
  refine not_isPSolvable_of_gates_omega (coordinatePlusWitnessEquiv K e) hgates β hβ hout
    (mem_E_of_top_omega hgates htop _) ?_
  intro a haE haD hap
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' G .POmegaPlus
    (Or.inr (Or.inl rfl)) n ℓ f 3 hG Nat.prime_three (by norm_num) K hK e a haE haD hap
  obtain ⟨g, hgE⟩ := haE
  obtain ⟨-, hrest⟩ := hdesc
  obtain ⟨hord, -, U, _, _, hUκ, hUr, _, hDisp⟩ := hrest g.val.right ⟨g, hgE, rfl⟩
  obtain ⟨_, _, -, -, hT'⟩ := hDisp
  obtain ⟨_, _, -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT'
  have hord' : orderOf U.val.right = 3 := by
    rw [hUr]
    exact hord
  have hσk : ∀ x, x ∈ semilinearFixedSubfield U.val.right ↔ U.val.right x = x := fun x =>
    RingHom.mem_eqLocusField
  rw [← hUκ]
  exact not_isPSolvable_of_fieldDescent h3
    (subfieldSetup_plus (semilinearFixedSubfield U.val.right) hσk Nat.prime_three (by norm_num)
      hord' (by omega : 3 ≤ n)) U Θ g' hg'l hg'r hΘ

theorem not_isPSolvable_omega_minus {G : Type} [Group G] {n ℓ f : ℕ}
    (hG : StatedClassicalModel G .POmegaMinus n ℓ f) (hℓ3 : ℓ ≠ 3) (β : MulAut G)
    (hβ : β ^ 3 = 1) (hout : β ∉ (MulAut.conj : G →* MulAut G).range) :
    ¬ CFSG.HallHigman.IsPSolvable 3 ↥(fixSubgroup β) := by
  obtain ⟨hℓ, hf, hn4⟩ := hG.1
  obtain ⟨K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hG.2
  have hn1 : 1 ≤ n := by omega
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaMinus
    (Or.inr (Or.inr rfl)) n ℓ f hG hn1 K hK b c hirr e
  have htop : projectivePointFamilyAut (coordinateQuadMinus n K hn1 b c) = ⊤ :=
    ((orthogonal_geometry_tail_model_point_family_invariant G .POmegaMinus (.inr rfl) n ℓ f hG)
      hn1 K hK b c hirr).2
  have h3 := three_ne_zero_of_card' hℓ hℓ3 hK
  refine not_isPSolvable_of_gates_omega (coordinateMinusWitnessEquiv K hn1 b c e) hgates β hβ
    hout (mem_E_of_top_omega hgates htop _) ?_
  intro a haE haD hap
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' G .POmegaMinus
    (Or.inr (Or.inr rfl)) n ℓ f 3 hG Nat.prime_three (by norm_num) hn1 K hK b c hirr e a haE
    haD hap
  obtain ⟨g, hgE⟩ := haE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord, hcard, U, _, _, hUκ, hUr, _, hDisp⟩ := hrest g.val.right ⟨g, hgE, rfl⟩
  obtain ⟨b', c', hirr', _, _, -, -, hT'⟩ := hDisp
  obtain ⟨_, _, -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT'
  have hord' : orderOf U.val.right = 3 := by
    rw [hUr]
    exact hord
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = ℓ ^ (f / 3) := by
    rw [hUr]
    exact hcard
  have hσk : ∀ x, x ∈ semilinearFixedSubfield U.val.right ↔ U.val.right x = x := fun x =>
    RingHom.mem_eqLocusField
  obtain ⟨m, hm⟩ := hpf
  have hdiv : f / 3 = m := by rw [hm]; exact Nat.mul_div_cancel_left m (by norm_num)
  rw [hdiv] at hcard'
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, mul_zero] at hm
      omega
    · exact h
  have hK' : Nat.card K = ℓ ^ (m * 3) := by rw [hK, hm, mul_comm]
  have hdeg := finrank_subfield_eq (semilinearFixedSubfield U.val.right) hℓ hm1 hcard' hK'
  rw [← hUκ]
  exact not_isPSolvable_of_fieldDescent h3
    (subfieldSetup_minus (semilinearFixedSubfield U.val.right) hσk Nat.prime_three (by norm_num)
      hord' hn4 hdeg b' c' hirr') U Θ g' hg'l hg'r hΘ

end Types

section OrthIndex

theorem outer295At_typeB_odd {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.B r q).Valid) (hp2 : q.p ≠ 2) (hp3 : q.p ≠ 3) (hr : 3 ≤ r) :
    Inputs295c.Outer295At ⟨.B r q, hv⟩ := by
  intro K _ _ _ _ ⟨e⟩ _ _ _ α hα hout
  exact Or.inr (Or.inr (not_isPSolvable_omega_odd
    (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r q hv hp2 hr e) hp3 α hα hout))

theorem outer295At_typeD {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.D r q).Valid) (hp3 : q.p ≠ 3) (hr : 5 ≤ r) :
    Inputs295c.Outer295At ⟨.D r q, hv⟩ := by
  intro K _ _ _ _ ⟨e⟩ _ _ _ α hα hout
  exact Or.inr (Or.inr (not_isPSolvable_omega_plus
    (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv e) hp3 hr α hα hout))

theorem outer295At_typeTwistedD {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedD r q).Valid) (hp3 : q.p ≠ 3) :
    Inputs295c.Outer295At ⟨.twistedD r q, hv⟩ := by
  intro K _ _ _ _ ⟨e⟩ _ _ _ α hα hout
  exact Or.inr (Or.inr (not_isPSolvable_omega_minus
    (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv e) hp3 α hα hout))

end OrthIndex

theorem isPSolvable_centralizer_of_mulEquiv {G H : Type} [Group G] [Group H] [Finite G]
    [Finite H] (e : G ≃* H) (x : G)
    (h : CFSG.HallHigman.IsPSolvable 3 ↥(Subgroup.centralizer ({x} : Set G))) :
    CFSG.HallHigman.IsPSolvable 3 ↥(Subgroup.centralizer ({e x} : Set H)) := by
  rw [← Inputs295.map_centralizer_singleton e x]
  exact isPSolvable_of_mulEquiv ((Subgroup.centralizer ({x} : Set G)).equivMapOfInjective _
    e.injective) h

section Exceptional

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL33d (exists_mem_componentRoots
  le_pow_orbit exists_weyl_smul_eq_of_mem_componentRoots exists_untwist_root)
open CFSG.HardMathSupport.Dickson.Sec6.Up34Exc (two_suN_exists_hom two_suN_exists_equiv)
open scoped MatrixGroups


theorem exists_kernelRoot_of_chain {τ : Tag} {L : Type} [Field L] (a : Fin τ.rank → Lˣ)
    (hap : ∀ l, a l ^ 3 = 1) {i j k : Fin τ.rank} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (h1 : IsRoot τ (Pi.single i 1 + Pi.single j 1)) (h2 : IsRoot τ (Pi.single j 1 + Pi.single k 1))
    (h3 : IsRoot τ (Pi.single i 1 + Pi.single j 1 + Pi.single k 1)) :
    ∃ γ, γ ∈ kernelRoots (rootCharHom a) := by
  classical
  have hsingle : ∀ l : Fin τ.rank, rootChar a (Pi.single l 1) = a l := by
    intro l
    rw [rootChar, Finset.prod_eq_single l]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · intro h
      exact absurd (Finset.mem_univ l) h
  have hval : ∀ v : Fin τ.rank → ℤ, rootCharHom a (Multiplicative.ofAdd v) = rootChar a v :=
    fun v => rfl
  have e1 : rootCharHom a (Multiplicative.ofAdd (Pi.single i 1)) = a i := by rw [hval, hsingle]
  have e2 : rootCharHom a (Multiplicative.ofAdd (Pi.single j 1)) = a j := by rw [hval, hsingle]
  have e3 : rootCharHom a (Multiplicative.ofAdd (Pi.single k 1)) = a k := by rw [hval, hsingle]
  have e12 : rootCharHom a (Multiplicative.ofAdd (Pi.single i 1 + Pi.single j 1)) = a i * a j := by
    rw [hval, rootChar_add, hsingle, hsingle]
  have e23 : rootCharHom a (Multiplicative.ofAdd (Pi.single j 1 + Pi.single k 1)) = a j * a k := by
    rw [hval, rootChar_add, hsingle, hsingle]
  have e123 : rootCharHom a (Multiplicative.ofAdd (Pi.single i 1 + Pi.single j 1 +
      Pi.single k 1)) = a i * a j * a k := by
    rw [hval, rootChar_add, rootChar_add, hsingle, hsingle, hsingle]
  by_contra hno
  push Not at hno
  have n1 : a i ≠ 1 := fun h => hno _ ⟨isRoot_single τ i, by rw [e1, h]⟩
  have n2 : a j ≠ 1 := fun h => hno _ ⟨isRoot_single τ j, by rw [e2, h]⟩
  have n3 : a k ≠ 1 := fun h => hno _ ⟨isRoot_single τ k, by rw [e3, h]⟩
  have n12 : a i * a j ≠ 1 := fun h => hno _ ⟨h1, by rw [e12, h]⟩
  have n23 : a j * a k ≠ 1 := fun h => hno _ ⟨h2, by rw [e23, h]⟩
  have n123 : a i * a j * a k ≠ 1 := fun h => hno _ ⟨h3, by rw [e123, h]⟩
  have hq : ∀ u : Lˣ, u ^ 3 = 1 → u ≠ 1 → (u : L) ^ 2 + u + 1 = 0 := by
    intro u hu3 hu1
    have h0 : ((u : L) - 1) * ((u : L) ^ 2 + u + 1) = 0 := by
      have : (u : L) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hu3, Units.val_one]
      linear_combination this
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd (Units.ext (sub_eq_zero.1 h)) hu1
    · exact h
  have heq : ∀ u v : Lˣ, u ^ 3 = 1 → v ^ 3 = 1 → u ≠ 1 → v ≠ 1 → u * v ≠ 1 → v = u := by
    intro u v hu hv hu1 hv1 huv
    have hu' := hq u hu hu1
    have hv' := hq v hv hv1
    have h0 : ((v : L) - u) * ((v : L) + u + 1) = 0 := by linear_combination hv' - hu'
    rcases mul_eq_zero.1 h0 with h | h
    · exact Units.ext (sub_eq_zero.1 h)
    · exfalso
      apply huv
      apply Units.ext
      have hv2 : (v : L) = -(u : L) - 1 := by linear_combination h
      have hu3 : (u : L) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]
      rw [Units.val_mul, Units.val_one, hv2]
      linear_combination (-1 : L) * hu'
  have hji : a j = a i := heq _ _ (hap i) (hap j) n1 n2 n12
  have hkj : a k = a j := heq _ _ (hap j) (hap k) n2 n3 n23
  apply n123
  rw [hkj, hji, ← pow_three', hap i]

theorem not_isPSolvable_fixSubgroup_of_qs {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    {p₀ : ℕ} (S : LangSetup τ L p₀) {C : Type} [Group C] [Finite C] (ι : C →* ModGL τ L)
    (hι : Function.Injective ι) (hrange : ι.range = S.Γ) (β : MulAut C)
    {a : Fin τ.rank → Lˣ} (hβ : ∀ c, ι (β c) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹)
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    {J : Type} [Group J] [Finite J] (hq : CFSG.IsQuasisimple J) (h3 : 3 ∣ Nat.card J)
    (g : J →* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (hgker : g.ker ≤ Subgroup.center J) :
    ¬ CFSG.HallHigman.IsPSolvable 3 ↥(fixSubgroup β) := by
  classical
  have hle := (langSubnormal_of_mem_torus S hT i).1
  have hfix : (fixSubgroup β).map ι = S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} := by
    rw [CFSG.HardMathSupport.Solomon.Coordinator.LieComp.map_fixSubgroup_eq_of_conj ι hι β _ hβ,
      hrange]
  have hle' : rationalComponent S.ρ S.Γ (rootCharHom a) i ≤ (fixSubgroup β).map ι :=
    hle.trans hfix.ge
  let eF := (fixSubgroup β).equivMapOfInjective ι hι
  let φ : J →* C := (fixSubgroup β).subtype.comp
    (eF.symm.toMonoidHom.comp ((Subgroup.inclusion hle').comp g))
  have hφker : φ.ker ≤ Subgroup.center J := by
    intro A hA
    apply hgker
    rw [MonoidHom.mem_ker] at hA ⊢
    have h1 : eF.symm (Subgroup.inclusion hle' (g A)) = 1 :=
      (fixSubgroup β).subtype_injective (hA.trans (map_one _).symm)
    have h2 : Subgroup.inclusion hle' (g A) = 1 := by
      rw [← map_one eF.symm] at h1
      exact eF.symm.injective h1
    exact Subgroup.inclusion_injective hle' (h2.trans (map_one _).symm)
  have hπ : ∃ b : J, φ b ≠ 1 := by
    by_contra hall
    push Not at hall
    obtain ⟨u, v, huv⟩ := Inputs295c.exists_noncomm_of_isQuasisimple hq
    have hu : u ∈ Subgroup.center J := hφker (hall u)
    exact huv (Subgroup.mem_center_iff.1 hu v).symm
  have hns := Inputs295c.not_isPSolvable_range_of_quasisimple hq h3 φ hπ
  have hrangeφ : φ.range ≤ fixSubgroup β := by
    rintro _ ⟨A, rfl⟩
    exact (eF.symm (Subgroup.inclusion hle' (g A))).2
  intro hs
  exact hns (isPSolvable_of_le hs hrangeφ)

theorem not_isPSolvable_fixSubgroup_of_sl2 {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    {p₀ : ℕ} (S : LangSetup τ L p₀) {C : Type} [Group C] [Finite C] (ι : C →* ModGL τ L)
    (hι : Function.Injective ι) (hrange : ι.range = S.Γ) (β : MulAut C)
    {a : Fin τ.rank → Lˣ} (hβ : ∀ c, ι (β c) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹)
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    {E : Type} [Field E] [Finite E] (hE4 : 4 ≤ Nat.card E)
    (g : SL(2, E) →* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (hgker : g.ker ≤ Subgroup.center SL(2, E)) :
    ¬ CFSG.HallHigman.IsPSolvable 3 ↥(fixSubgroup β) :=
  not_isPSolvable_fixSubgroup_of_qs S ι hι hrange β hβ hT i
    (CFSG.SeitzReduction.LinearPilot.isQuasisimple_specialLinearGroup_of_le le_rfl (Or.inr hE4))
    (Inputs295c.three_dvd_card_sl (F := E) (m := 2) le_rfl) g hgker

theorem exists_sl2_hom_simplyLaced {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ} (hτ : SimplyLacedTag τ) (hq4 : 4 ≤ S.D.q)
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a)) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E), 4 ≤ Nat.card E ∧
      ∃ g : SL(2, E) →* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i),
        g.ker ≤ Subgroup.center SL(2, E) := by
  classical
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  haveI : NeZero s := ⟨hs0.ne'⟩
  obtain ⟨θ, hθ⟩ := exists_mem_componentRoots i
  have hθr : IsRoot τ θ := isRoot_of_mem_componentRoots hθ
  have hneg : -θ ∈ componentRoots (rootCharHom a) i :=
    (isRootComponent_componentRoots i).neg_mem θ hθ
  have hρθ : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] θ ∈ componentRoots (rootCharHom a) i := by
    rw [← hs]
    exact ⟨θ, hθ, rfl⟩
  obtain ⟨w, hw, hwθ⟩ := exists_weyl_smul_eq_of_mem_componentRoots hτ hθ hρθ
  obtain ⟨σ, z, hσ, hnorm, hz⟩ := exists_untwist_root S hτ hT i hs0 hθ hw hwθ.symm
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : CharP L r := hchar
  have hσ' : ∀ c, σ c = c ^ (r ^ (e * s)) := fun c => by rw [hσ, hq, ← pow_mul]
  have hQ4 : 4 ≤ r ^ (e * s) := by
    calc 4 ≤ S.D.q := hq4
      _ = r ^ e := hq
      _ ≤ r ^ (e * s) := le_pow_orbit hr.pos hs0
  obtain ⟨hfinK, hKcard⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.finite_card_fixSubfield (L := L) (r := r)
      (n := e * s) (Nat.mul_pos he hs0) σ hσ'
  let ι : SL(2, ↥(fixSubfield σ)) →* SL(2, L) :=
    Matrix.SpecialLinearGroup.map (fixSubfield σ).subtype
  let θ₁ : SL(2, ↥(fixSubfield σ)) →* ModGL τ L :=
    (MulAut.conj z).toMonoidHom.comp ((rootSL2 τ L θ).comp ι)
  have hθ₁ : ∀ A, θ₁ A = z * rootSL2 τ L θ (ι A) * z⁻¹ := fun A => rfl
  have hpair : rootSpan τ L {θ, -θ} = rootSubgroup τ L θ ⊔ rootSubgroup τ L (-θ) := by
    simp only [rootSpan, iSup_insert, iSup_singleton]
  have hρmem : ∀ B, rootSL2 τ L θ B ∈ rootSpan τ L {θ, -θ} := by
    intro B
    have h1 : rootSL2 τ L θ B ∈ (rootSL2 τ L θ).range := ⟨B, rfl⟩
    rw [CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot hθr, ← hpair] at h1
    exact h1
  have hpairS : rootSpan τ L {θ, -θ} ≤ rootSpan τ L (componentRoots (rootCharHom a) i) := by
    refine rootSpan_mono fun γ hγ => ?_
    rcases hγ with rfl | hγ
    · exact hθ
    · rw [Set.mem_singleton_iff.1 hγ]
      exact hneg
  have hθS : ∀ A, θ₁ A ∈ rootSpan τ L (componentRoots (rootCharHom a) i) := fun A => by
    rw [hθ₁]
    exact (hnorm i _).1 (hpairS (hρmem (ι A)))
  have hθfix : ∀ A, iterHom S.D.step s (θ₁ A) = θ₁ A := by
    intro A
    rw [hθ₁, hz _ (hρmem (ι A)), frobGL_rootSL2 σ hθr]
    congr 3
    ext j k
    exact (A j k).2
  have hθinj : Function.Injective θ₁ := by
    intro A B hAB
    rw [hθ₁, hθ₁] at hAB
    have h1 : rootSL2 τ L θ (ι A) = rootSL2 τ L θ (ι B) := by
      have := congrArg (fun x => z⁻¹ * x * z) hAB
      simpa [mul_assoc] using this
    have h2 := CFSG.RankThree.Chevalley.rootSL2_injective_of_field θ h1
    ext j k
    exact congrArg (fun M : SL(2, L) => (M : Matrix (Fin 2) (Fin 2) L) j k) h2
  set P := outerOrbitFamily S hT i hs hmin with hP
  have hP0 : P.S 0 = rootSpan τ L (componentRoots (rootCharHom a) i) := by
    rw [hP, outerOrbitFamily_S, ZMod.val_zero]
    simp only [Function.iterate_zero, id_eq, Set.image_id']
  let θ₀ : SL(2, ↥(fixSubfield σ)) →* P.S 0 :=
    θ₁.codRestrict (P.S 0) fun A => by rw [hP0]; exact hθS A
  have hfix0 : ∀ A, iterHom S.D.step s ((θ₀ A : P.S 0) : ModGL τ L) = θ₀ A := fun A => hθfix A
  have hperf : Group.IsPerfect SL(2, ↥(fixSubfield σ)) :=
    (CFSG.SeitzReduction.LinearPilot.isQuasisimple_specialLinearGroup_of_le le_rfl
      (Or.inr (by rw [hKcard]; omega))).1
  have hfR : ∀ A, P.norm (θ₀ A) ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i :=
    outer_norm_mem_rationalComponent S hT i hs hmin hperf θ₀ hfix0
  let g : SL(2, ↥(fixSubfield σ)) →* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    (P.norm.comp θ₀).codRestrict _ hfR
  have hgker : g.ker ≤ Subgroup.center SL(2, ↥(fixSubfield σ)) := by
    intro A hA
    have h1 : P.norm (θ₀ A) = 1 := congrArg Subtype.val hA
    have h2 := P.mem_Z_of_norm_eq_one h1
    rw [Subgroup.mem_center_iff]
    intro B
    have h3 := P.mem_Z.1 h2 (θ₁ B) (P.S_le_A 0 (by rw [hP0]; exact hθS B))
    exact hθinj (by rw [map_mul, map_mul]; exact h3)
  exact ⟨↥(fixSubfield σ), inferInstance, hfinK, by rw [hKcard]; exact hQ4, g, hgker⟩

theorem isRoot_chain_E6 :
    IsRoot .E6 (Pi.single (⟨0, by decide⟩ : Fin Tag.E6.rank) 1 + Pi.single ⟨2, by decide⟩ 1) ∧
    IsRoot .E6 (Pi.single (⟨2, by decide⟩ : Fin Tag.E6.rank) 1 + Pi.single ⟨3, by decide⟩ 1) ∧
    IsRoot .E6 (Pi.single (⟨0, by decide⟩ : Fin Tag.E6.rank) 1 + Pi.single ⟨2, by decide⟩ 1 +
      Pi.single ⟨3, by decide⟩ 1) := by
  have e1 : reflect .E6 ⟨0, by decide⟩ (Pi.single ⟨2, by decide⟩ 1) =
      Pi.single (⟨0, by decide⟩ : Fin Tag.E6.rank) 1 + Pi.single ⟨2, by decide⟩ 1 := by decide
  have e2 : reflect .E6 ⟨2, by decide⟩ (Pi.single ⟨3, by decide⟩ 1) =
      Pi.single (⟨2, by decide⟩ : Fin Tag.E6.rank) 1 + Pi.single ⟨3, by decide⟩ 1 := by decide
  have e3 : reflect .E6 ⟨0, by decide⟩
      (Pi.single (⟨2, by decide⟩ : Fin Tag.E6.rank) 1 + Pi.single ⟨3, by decide⟩ 1) =
      Pi.single (⟨0, by decide⟩ : Fin Tag.E6.rank) 1 + Pi.single ⟨2, by decide⟩ 1 +
        Pi.single ⟨3, by decide⟩ 1 := by decide
  have r2 := IsRoot.reflect (τ := .E6) ⟨2, by decide⟩ (IsRoot.basis ⟨3, by decide⟩)
  rw [e2] at r2
  have r1 := IsRoot.reflect (τ := .E6) ⟨0, by decide⟩ (IsRoot.basis ⟨2, by decide⟩)
  rw [e1] at r1
  have r3 := IsRoot.reflect (τ := .E6) ⟨0, by decide⟩ r2
  rw [e3] at r3
  exact ⟨r1, r2, r3⟩

theorem isRoot_chain_E7 :
    IsRoot .E7 (Pi.single (⟨0, by decide⟩ : Fin Tag.E7.rank) 1 + Pi.single ⟨2, by decide⟩ 1) ∧
    IsRoot .E7 (Pi.single (⟨2, by decide⟩ : Fin Tag.E7.rank) 1 + Pi.single ⟨3, by decide⟩ 1) ∧
    IsRoot .E7 (Pi.single (⟨0, by decide⟩ : Fin Tag.E7.rank) 1 + Pi.single ⟨2, by decide⟩ 1 +
      Pi.single ⟨3, by decide⟩ 1) := by
  have e1 : reflect .E7 ⟨0, by decide⟩ (Pi.single ⟨2, by decide⟩ 1) =
      Pi.single (⟨0, by decide⟩ : Fin Tag.E7.rank) 1 + Pi.single ⟨2, by decide⟩ 1 := by decide
  have e2 : reflect .E7 ⟨2, by decide⟩ (Pi.single ⟨3, by decide⟩ 1) =
      Pi.single (⟨2, by decide⟩ : Fin Tag.E7.rank) 1 + Pi.single ⟨3, by decide⟩ 1 := by decide
  have e3 : reflect .E7 ⟨0, by decide⟩
      (Pi.single (⟨2, by decide⟩ : Fin Tag.E7.rank) 1 + Pi.single ⟨3, by decide⟩ 1) =
      Pi.single (⟨0, by decide⟩ : Fin Tag.E7.rank) 1 + Pi.single ⟨2, by decide⟩ 1 +
        Pi.single ⟨3, by decide⟩ 1 := by decide
  have r2 := IsRoot.reflect (τ := .E7) ⟨2, by decide⟩ (IsRoot.basis ⟨3, by decide⟩)
  rw [e2] at r2
  have r1 := IsRoot.reflect (τ := .E7) ⟨0, by decide⟩ (IsRoot.basis ⟨2, by decide⟩)
  rw [e1] at r1
  have r3 := IsRoot.reflect (τ := .E7) ⟨0, by decide⟩ r2
  rw [e3] at r3
  exact ⟨r1, r2, r3⟩

theorem isRoot_chain_E8 :
    IsRoot .E8 (Pi.single (⟨0, by decide⟩ : Fin Tag.E8.rank) 1 + Pi.single ⟨2, by decide⟩ 1) ∧
    IsRoot .E8 (Pi.single (⟨2, by decide⟩ : Fin Tag.E8.rank) 1 + Pi.single ⟨3, by decide⟩ 1) ∧
    IsRoot .E8 (Pi.single (⟨0, by decide⟩ : Fin Tag.E8.rank) 1 + Pi.single ⟨2, by decide⟩ 1 +
      Pi.single ⟨3, by decide⟩ 1) := by
  have e1 : reflect .E8 ⟨0, by decide⟩ (Pi.single ⟨2, by decide⟩ 1) =
      Pi.single (⟨0, by decide⟩ : Fin Tag.E8.rank) 1 + Pi.single ⟨2, by decide⟩ 1 := by decide
  have e2 : reflect .E8 ⟨2, by decide⟩ (Pi.single ⟨3, by decide⟩ 1) =
      Pi.single (⟨2, by decide⟩ : Fin Tag.E8.rank) 1 + Pi.single ⟨3, by decide⟩ 1 := by decide
  have e3 : reflect .E8 ⟨0, by decide⟩
      (Pi.single (⟨2, by decide⟩ : Fin Tag.E8.rank) 1 + Pi.single ⟨3, by decide⟩ 1) =
      Pi.single (⟨0, by decide⟩ : Fin Tag.E8.rank) 1 + Pi.single ⟨2, by decide⟩ 1 +
        Pi.single ⟨3, by decide⟩ 1 := by decide
  have r2 := IsRoot.reflect (τ := .E8) ⟨2, by decide⟩ (IsRoot.basis ⟨3, by decide⟩)
  rw [e2] at r2
  have r1 := IsRoot.reflect (τ := .E8) ⟨0, by decide⟩ (IsRoot.basis ⟨2, by decide⟩)
  rw [e1] at r1
  have r3 := IsRoot.reflect (τ := .E8) ⟨0, by decide⟩ r2
  rw [e3] at r3
  exact ⟨r1, r2, r3⟩

theorem exists_kernelComponent_E {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {L : Type}
    [Field L] (a : Fin τ.rank → Lˣ) (hap : ∀ l, a l ^ 3 = 1) :
    Nonempty (KernelComponent (rootCharHom a)) := by
  rcases hτ with rfl | rfl | rfl
  · obtain ⟨r1, r2, r3⟩ := isRoot_chain_E6
    obtain ⟨γ, hγ⟩ := exists_kernelRoot_of_chain a hap (by decide) (by decide) (by decide) r1 r2 r3
    exact ⟨⟦⟨γ, hγ⟩⟧⟩
  · obtain ⟨r1, r2, r3⟩ := isRoot_chain_E7
    obtain ⟨γ, hγ⟩ := exists_kernelRoot_of_chain a hap (by decide) (by decide) (by decide) r1 r2 r3
    exact ⟨⟦⟨γ, hγ⟩⟧⟩
  · obtain ⟨r1, r2, r3⟩ := isRoot_chain_E8
    obtain ⟨γ, hγ⟩ := exists_kernelRoot_of_chain a hap (by decide) (by decide) (by decide) r1 r2 r3
    exact ⟨⟦⟨γ, hγ⟩⟧⟩

theorem not_isPSolvable_centralizer_untw {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] (hK3 : ¬ 3 ∣ Nat.card K) (hK4 : 4 ≤ Nat.card K)
    (y : ↥(adjointGroup τ K)) (hy : orderOf y = 3) :
    ¬ CFSG.HallHigman.IsPSolvable 3
      ↥(Subgroup.centralizer ({y} : Set ↥(adjointGroup τ K))) := by
  classical
  have hτ' : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with h | h | h <;> simp [h]
  have hy3 : y ^ 3 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have hy1 : y ≠ 1 := fun h => by rw [h, orderOf_one] at hy; norm_num at hy
  set β : MulAut ↥(adjointGroup τ K) := MulAut.conj y with hβdef
  have hβ : ∀ c, (β c : ModGL τ K) = (y : ModGL τ K) * c * (y : ModGL τ K)⁻¹ := fun c => by
    rw [hβdef, MulAut.conj_apply]
    simp
  have hhL := baseChange_mem_adjointGroup_of_mem_inndiag
    (CFSG.StandardType.RecipeExcLang.adjointGroup_le_inndiagGroup y.2)
  have hperf : commutator ↥(adjointGroup τ K) = ⊤ :=
    single_edge_perfect τ K (by rcases hτ with h | h | h <;> simp [h])
  have hmon : MonomialToralAt τ 3 :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five
      (by rcases hτ with h | h | h <;> simp [h]) Nat.prime_three (by norm_num)
  have hp1 : (y : ModGL τ K) ^ 3 = 1 := by rw [← Subgroup.coe_pow, hy3]; rfl
  have hh1 : (y : ModGL τ K) ≠ 1 := fun h => hy1 (Subtype.ext h)
  obtain ⟨S', a, ι, hSq, -, hT, hap, -, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inner_untw hτ' Nat.prime_three hK3 (Or.inr hK4) hmon hperf β
      (y : ModGL τ K) hhL hβ hp1 hh1
  obtain ⟨i⟩ := exists_kernelComponent_E hτ a hap
  have hsl : SimplyLacedTag τ := by
    rcases hτ with h | h | h <;> simp [SimplyLacedTag, h]
  obtain ⟨E, _, _, hE4, g, hgker⟩ :=
    exists_sl2_hom_simplyLaced S' hsl (by rw [hSq]; exact hK4) hT i
  have h := not_isPSolvable_fixSubgroup_of_sl2 S' ι hinj hrange β hconj hT i hE4 g hgker
  rwa [hβdef, CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup_conj] at h

theorem not_isPSolvable_centralizer_twE6 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hℓ3 : ℓ ≠ 3)
    (hq4 : 4 ≤ ℓ ^ f) {K : Type} [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (y : ↥(twistedE6RootGroup K σ)) (hy : orderOf y = 3) :
    ¬ CFSG.HallHigman.IsPSolvable 3
      ↥(Subgroup.centralizer ({y} : Set ↥(twistedE6RootGroup K σ))) := by
  classical
  haveI : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have hy3 : y ^ 3 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have hy1 : y ≠ 1 := fun h => by rw [h, orderOf_one] at hy; norm_num at hy
  set β : MulAut ↥(twistedE6RootGroup K σ) := MulAut.conj y with hβdef
  have hβ : ∀ c, (β c : ModGL TwistTag.E6.tag K) =
      (y : ModGL TwistTag.E6.tag K) * c * (y : ModGL TwistTag.E6.tag K)⁻¹ := fun c => by
    rw [hβdef, MulAut.conj_apply]
    simp
  have hmon : MonomialToralAt Tag.E6 3 :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five (by simp)
      Nat.prime_three (by norm_num)
  have hp1 : (y : ModGL TwistTag.E6.tag K) ^ 3 = 1 := by rw [← Subgroup.coe_pow, hy3]; rfl
  have hh1 : (y : ModGL TwistTag.E6.tag K) ≠ 1 := fun h => hy1 (Subtype.ext h)
  have hh : (y : ModGL TwistTag.E6.tag K) ∈ twistedE6InndiagGL K σ := by
    rw [twistedE6InndiagGL]
    exact Subgroup.mem_sup_left y.2
  have h3ℓ : (3 : ℕ) ≠ ℓ := fun h => hℓ3 h.symm
  obtain ⟨S', a, ι, hSq, -, hT, hap, -, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inndiag_twE6_of_prime hℓ hf hK σ hσ Nat.prime_three h3ℓ Nat.prime_three
      h3ℓ (Or.inr hq4) hmon β (y : ModGL TwistTag.E6.tag K) hh hβ hp1 hh1
  obtain ⟨i⟩ := exists_kernelComponent_E (Or.inl rfl) a hap
  obtain ⟨E, _, _, hE4, g, hgker⟩ :=
    exists_sl2_hom_simplyLaced S' (Or.inr (Or.inl rfl)) (by rw [hSq]; exact hq4) hT i
  have h := not_isPSolvable_fixSubgroup_of_sl2 S' ι hinj hrange β hconj hT i hE4 g hgker
  rwa [hβdef, CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup_conj] at h

theorem inner295At_untwE {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {c : TauCeti.PrimePower → TauCeti.LieTypeIndex}
    (hB : CFSG.TauCetiBridge.Even.UntwistedBridgeAll τ c) (q : TauCeti.PrimePower)
    (hv : (c q).Valid) (hp3 : q.p ≠ 3) (hq2 : q.card ≠ 2) :
    Inputs295c.Inner295At ⟨c q, hv⟩ := by
  intro S _ _ _ _ ⟨e⟩ _ _ _ x hx
  obtain ⟨K, _, _, hK, -, ⟨eK⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup hB q hv
  let e' : S ≃* ↥(adjointGroup τ K) := e.trans eK
  haveI : Finite ↥(adjointGroup τ K) := Finite.of_equiv S e'.toEquiv
  have hK3 : ¬ 3 ∣ Nat.card K := by
    rw [hK]
    exact CFSG.LieType.SeitzGeneration.not_dvd_card_of_ne Nat.prime_three (Ne.symm hp3)
  have hK4 : 4 ≤ Nat.card K := by rw [hK]; exact Inputs295c.four_le_card_of hp3 hq2
  have hy : orderOf (e' x) = 3 := by rw [MulEquiv.orderOf_eq]; exact hx
  exact Or.inr (Or.inr fun hs => not_isPSolvable_centralizer_untw hτ hK3 hK4 (e' x) hy
    (isPSolvable_centralizer_of_mulEquiv e' x hs))

theorem inner295At_twistedE6 (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid) (hp3 : q.p ≠ 3) (hq2 : q.card ≠ 2) :
    Inputs295c.Inner295At ⟨.twistedE6 q, hv⟩ := by
  intro S _ _ _ _ ⟨e⟩ _ _ _ x hx
  obtain ⟨K, _, σ, hK, hσ, ⟨eK⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_twistedE6 q hv
  let e' : S ≃* ↥(twistedE6RootGroup K σ) := e.trans eK
  haveI : Finite ↥(twistedE6RootGroup K σ) := Finite.of_equiv S e'.toEquiv
  have hq4 : 4 ≤ q.p ^ q.exponent := by
    rw [← TauCeti.PrimePower.card_def]
    exact Inputs295c.four_le_card_of hp3 hq2
  have hy : orderOf (e' x) = 3 := by rw [MulEquiv.orderOf_eq]; exact hx
  exact Or.inr (Or.inr fun hs => not_isPSolvable_centralizer_twE6 q.prime_p q.exponent_pos hp3 hq4
    hK σ hσ (e' x) hy (isPSolvable_centralizer_of_mulEquiv e' x hs))

theorem three_dvd_card_adjointGroup (τ : Tag) (k : Type) [Field k] [Finite k] :
    3 ∣ Nat.card ↥(adjointGroup τ k) := by
  haveI : Finite (ModGL τ k) := finite_modGL
  let f : SL(2, k) →* ↥(adjointGroup τ k) :=
    (rootSL2 τ k 0).codRestrict _ fun A => CFSG.LieType.Chevalley.rootSL2_mem_adjointGroup 0 A
  have hf : Function.Injective f := fun A B h =>
    CFSG.RankThree.Chevalley.rootSL2_injective_of_field (τ := τ) (K := k) 0
      (congrArg Subtype.val h)
  exact (Inputs295c.three_dvd_card_sl (F := k) (m := 2) le_rfl).trans
    (Subgroup.card_dvd_of_injective f hf)

theorem not_isPSolvable_fixSubgroup_entrywise (τ : Tag) {K : Type} [Field K] [Finite K]
    (σ : K ≃+* K) (hk : τ = .G2 → 3 ≤ Nat.card (fixSubfield σ)) :
    ¬ CFSG.HallHigman.IsPSolvable 3 ↥(fixSubgroup (entrywiseAdjointAut τ σ)) := by
  classical
  haveI : Finite (fixSubfield σ) := Subtype.finite
  haveI : Finite (ModGL τ K) := finite_modGL
  obtain ⟨ι, hι, hJC, -, -⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ExcCopy.exists_fixed_structure τ σ
  have hperf := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ExcCopy.isPerfect_adjointGroup τ
    (fixSubfield σ) hk
  obtain ⟨hs, hnc⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ExcCopy.isSimpleGroup_adjointGroup_of_perfect
      τ (fixSubfield σ) hperf
  let e : ↥(adjointGroup τ (fixSubfield σ)) ≃* ι.range := MonoidHom.ofInjective hι
  haveI := hs
  have hJs : IsSimpleGroup ι.range := e.symm.isSimpleGroup
  have hJnc : ¬ IsMulCommutative ι.range := by
    rintro ⟨hc⟩
    obtain ⟨x, y, hxy⟩ := hnc
    exact hxy (e.injective (by rw [map_mul, map_mul]; exact hc.comm _ _))
  haveI : Finite (ModGL τ (fixSubfield σ)) := finite_modGL
  have hJ3 : 3 ∣ Nat.card ι.range := by
    rw [← Nat.card_congr e.toEquiv]
    exact three_dvd_card_adjointGroup τ _
  intro hsolv
  exact CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.not_isPSolvable_three_of_simple hJs
    hJnc hJ3 (isPSolvable_of_le hsolv hJC)

theorem not_isPSolvable_fixSubgroup_untwE {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] (hK3 : ¬ 3 ∣ Nat.card K) (hK4 : 4 ≤ Nat.card K)
    (β : MulAut ↥(adjointGroup τ K)) (hβ : β ^ 3 = 1) (hβ1 : β ≠ 1) :
    ¬ CFSG.HallHigman.IsPSolvable 3 ↥(fixSubgroup β) := by
  classical
  have hτ' : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with h | h | h <;> simp [h]
  rcases CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_field_or_inndiag_E hτ
      Nat.prime_three (by norm_num) β hβ hβ1 with ⟨σ, ψ, -, hψ⟩ | ⟨h, hh, hβh, hp1, hh1⟩
  ·
    intro hs
    apply not_isPSolvable_fixSubgroup_entrywise τ σ (fun h => by rcases hτ with h' | h' | h' <;>
      simp [h'] at h)
    rw [← hψ, Inputs295c.fixSubgroup_conj]
    exact isPSolvable_of_mulEquiv ((fixSubgroup β).equivMapOfInjective _ ψ.injective) hs
  ·
    have hhL := baseChange_mem_adjointGroup_of_mem_inndiag hh
    have hperf : commutator ↥(adjointGroup τ K) = ⊤ :=
      single_edge_perfect τ K (by rcases hτ with h | h | h <;> simp [h])
    have hmon : MonomialToralAt τ 3 :=
      monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five
        (by rcases hτ with h | h | h <;> simp [h]) Nat.prime_three (by norm_num)
    obtain ⟨S', a, ι, hSq, -, hT, hap, -, hinj, hrange, hconj⟩ :=
      exists_langSetup_of_inner_untw hτ' Nat.prime_three hK3 (Or.inr hK4) hmon hperf β h hhL hβh
        hp1 hh1
    obtain ⟨i⟩ := exists_kernelComponent_E hτ a hap
    have hsl : SimplyLacedTag τ := by
      rcases hτ with h | h | h <;> simp [SimplyLacedTag, h]
    obtain ⟨E, _, _, hE4, g, hgker⟩ :=
      exists_sl2_hom_simplyLaced S' hsl (by rw [hSq]; exact hK4) hT i
    exact not_isPSolvable_fixSubgroup_of_sl2 S' ι hinj hrange β hconj hT i hE4 g hgker

theorem outer295At_untwE {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {c : TauCeti.PrimePower → TauCeti.LieTypeIndex}
    (hB : CFSG.TauCetiBridge.Even.UntwistedBridgeAll τ c) (q : TauCeti.PrimePower)
    (hv : (c q).Valid) (hp3 : q.p ≠ 3) (hq2 : q.card ≠ 2) :
    Inputs295c.Outer295At ⟨c q, hv⟩ := by
  intro S _ _ _ _ ⟨e⟩ _ _ _ α hα hout
  obtain ⟨K, _, _, hK, -, ⟨eK⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup hB q hv
  let e' : S ≃* ↥(adjointGroup τ K) := e.trans eK
  haveI : Finite ↥(adjointGroup τ K) := Finite.of_equiv S e'.toEquiv
  have hK3 : ¬ 3 ∣ Nat.card K := by
    rw [hK]
    exact CFSG.LieType.SeitzGeneration.not_dvd_card_of_ne Nat.prime_three (Ne.symm hp3)
  have hK4 : 4 ≤ Nat.card K := by rw [hK]; exact Inputs295c.four_le_card_of hp3 hq2
  have hβ : MulAut.congr e' α ^ 3 = 1 := congr_pow_three_eq_one e' hα
  have hβ1 : MulAut.congr e' α ≠ 1 := by
    intro h1
    apply hout
    refine ⟨1, ?_⟩
    rw [map_one]
    exact ((MulAut.congr e').injective (h1.trans (map_one _).symm)).symm
  refine Or.inr (Or.inr fun hs => not_isPSolvable_fixSubgroup_untwE hτ hK3 hK4 _ hβ hβ1 ?_)
  rw [Inputs295c.fixSubgroup_congr]
  exact isPSolvable_of_mulEquiv ((fixSubgroup α).equivMapOfInjective _ e'.injective) hs

theorem exists_sl2_hom_inner {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ} (hq4 : 4 ≤ S.D.q)
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E), 4 ≤ Nat.card E ∧
      ∃ g : SL(2, E) →* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i),
        g.ker ≤ Subgroup.center SL(2, E) := by
  classical
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  have : NeZero s := ⟨hs0.ne'⟩
  obtain ⟨σ, z, hσ, hnorm, hz⟩ := exists_untwistT S hT i hs0 hinner
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  haveI : Fact r.Prime := ⟨hr⟩
  have hσ' : ∀ c, σ c = c ^ (r ^ (e * s)) := fun c => by rw [hσ, hq, ← pow_mul]
  have hQ4 : 4 ≤ r ^ (e * s) := by
    calc 4 ≤ S.D.q := hq4
      _ = r ^ e := hq
      _ ≤ r ^ (e * s) := le_pow_orbit hr.pos hs0
  obtain ⟨t, ht⟩ := exists_unit_sq_ne_one (L := L) σ hσ' (Nat.mul_pos he hs0) (by omega)
  have hsL : ∃ u : Lˣ, u ^ 2 ≠ 1 := by
    refine ⟨Units.map (fixSubfield σ).subtype.toMonoidHom t, fun h => ht ?_⟩
    apply Units.ext
    apply Subtype.ext
    simpa using congrArg (fun x : Lˣ => (x : L)) h
  obtain ⟨hfinK, hKcard⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.finite_card_fixSubfield (L := L) (r := r)
      (n := e * s) (Nat.mul_pos he hs0) σ hσ'
  have hperfC := isPerfect_componentRootSpan_of_sq_ne_one (K := fixSubfield σ)
    (χ := rootCharHom a) ht i
  obtain ⟨f, hf1, hker, hf2⟩ :=
    rationalComponent_eq_range_componentRootSpanT S hT i hs hmin σ z hnorm hz hsL
  have hRf : f.range = rationalComponent S.ρ S.Γ (rootCharHom a) i :=
    le_antisymm (hf2 (Subgroup.isPerfect_iff.1 hperfC)) hf1
  obtain ⟨γ, hγ⟩ := exists_mem_componentRoots i
  have hγr : IsRoot τ γ := isRoot_of_mem_componentRoots hγ
  have hneg : -γ ∈ componentRoots (rootCharHom a) i :=
    (isRootComponent_componentRoots i).neg_mem γ hγ
  have hle : (rootSL2 τ (fixSubfield σ) γ).range ≤
      componentRootSpan (fixSubfield σ) (rootCharHom a) i := by
    rw [CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot hγr]
    exact sup_le (le_iSup₂_of_le γ hγ le_rfl) (le_iSup₂_of_le (-γ) hneg le_rfl)
  let ι : SL(2, ↥(fixSubfield σ)) →* ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i) :=
    (rootSL2 τ (fixSubfield σ) γ).codRestrict _ (fun A => hle ⟨A, rfl⟩)
  have hι : Function.Injective ι := fun A B h =>
    CFSG.RankThree.Chevalley.rootSL2_injective_of_field γ (congrArg Subtype.val h)
  let g : SL(2, ↥(fixSubfield σ)) →* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    (f.comp ι).codRestrict _ (fun A => hRf ▸ ⟨ι A, rfl⟩)
  have hgker : g.ker ≤ Subgroup.center SL(2, ↥(fixSubfield σ)) := by
    intro A hA
    have hA' : ι A ∈ f.ker := by
      rw [MonoidHom.mem_ker] at hA ⊢
      exact congrArg Subtype.val hA
    have hAZ := hker hA'
    rw [Subgroup.mem_center_iff] at hAZ ⊢
    intro B
    exact hι (by rw [map_mul, map_mul]; exact hAZ (ι B))
  exact ⟨↥(fixSubfield σ), inferInstance, hfinK, by rw [hKcard]; exact hQ4, g, hgker⟩

theorem three_dvd_sq_sub_one {Q : ℕ} (hQ : ¬ 3 ∣ Q) : (3 : ℤ) ∣ (Q : ℤ) ^ 2 - 1 := by
  have hne : Q % 3 ≠ 0 := fun h0 => hQ (Nat.dvd_of_mod_eq_zero h0)
  rcases (show Q % 3 = 1 ∨ Q % 3 = 2 by omega) with h1 | h2
  · obtain ⟨k, hk⟩ : ∃ k, Q = 3 * k + 1 := ⟨Q / 3, by omega⟩
    rw [hk]
    push_cast
    exact ⟨3 * (k : ℤ) ^ 2 + 2 * k, by ring⟩
  · obtain ⟨k, hk⟩ : ∃ k, Q = 3 * k + 2 := ⟨Q / 3, by omega⟩
    rw [hk]
    push_cast
    exact ⟨3 * (k : ℤ) ^ 2 + 4 * k + 1, by ring⟩

theorem three_dvd_card_statedSU {r f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData r f F)
    (hr3 : r ≠ 3) {ν : ℕ} (hν : 2 ≤ ν) : 3 ∣ Nat.card ↥(StatedSU ν (r ^ f) F) := by
  have hcard := CFSG.GH74.GLS.Stage2.Final.ModelOrd.card_statedSU_int h (n := ν) (by omega)
  have hQ3 : ¬ 3 ∣ r ^ f := fun hd => hr3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three h.prime).1
    (Nat.prime_three.dvd_of_dvd_pow hd)).symm
  have h2 : (3 : ℤ) ∣ ∏ i ∈ Finset.Icc 2 ν, (((r ^ f : ℕ) : ℤ) ^ i - (-1) ^ i) := by
    refine (dvd_trans ?_ (Finset.dvd_prod_of_mem _ (Finset.mem_Icc.2 ⟨le_rfl, hν⟩)))
    have := three_dvd_sq_sub_one hQ3
    simpa using this
  have h3 : (3 : ℤ) ∣ (Nat.card ↥(StatedSU ν (r ^ f) F) : ℤ) := by
    rw [hcard]
    exact Dvd.dvd.mul_left h2 _
  exact_mod_cast h3

theorem exists_qs_hom_F4 {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.F4 L p₀) {a : Fin Tag.F4.rank → Lˣ} (hq4 : 4 ≤ S.D.q)
    (hT : rootDiagUnit Tag.F4 a ∈ S.D.torus) (hap : ∀ i, a i ^ 3 = 1)
    (h1 : rootDiagUnit Tag.F4 a ≠ 1) (i : KernelComponent (rootCharHom a)) :
    ∃ (J : Type) (_ : Group J) (_ : Finite J), CFSG.IsQuasisimple J ∧ 3 ∣ Nat.card J ∧
      ∃ g : J →* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i),
        g.ker ≤ Subgroup.center J := by
  classical
  have hℓp : ringChar L ≠ 3 :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_ne_of_pow_eq_one Nat.prime_three hap
      h1
  have hpL : ((3 : ℕ) : L) ≠ 0 :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.natCast_ne_zero_of_ringChar_ne
      Nat.prime_three hℓp
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])
  · obtain ⟨E, _, _, hE4, g, hgker⟩ := exists_sl2_hom_inner S hq4 hT i hinner
    exact ⟨SL(2, E), inferInstance, inferInstance,
      CFSG.SeitzReduction.LinearPilot.isQuasisimple_specialLinearGroup_of_le le_rfl (Or.inr hE4),
      Inputs295c.three_dvd_card_sl (F := E) (m := 2) le_rfl, g, hgker⟩
  by_cases hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)
  · have h2 : 2 ≤ compRank (componentRoots (rootCharHom a) i) := by
      by_contra hlt
      have hr1 : compRank (componentRoots (rootCharHom a) i) = 1 := by omega
      exact hinner (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.twistInner_of_shape S hT i 1 2
        hr1 (by rw [hA.2, hr1]) (by omega) (by omega) (by omega) (by omega))
    obtain ⟨ν, ψ, σ, κ, hν, hψ, hκ, hnorm, hΨ⟩ := exists_frame_of_typeA_tag_T_of_prime
      g2LongA2Frame_proved S Nat.prime_three hpL hTp i h2 hA.2
    obtain ⟨hs0, hs, -⟩ := outer_componentOrbitLength_spec S hT i
    set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
    have hmaps : ∀ x y, x ≠ y → (S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[s] (σ x y) ∈ frameRoots σ := by
      intro x y hxy
      have h1' : σ x y ∈ componentRoots (rootCharHom a) i := by
        rw [hΨ]
        exact ⟨x, y, hxy, rfl⟩
      have h2' : (S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[s] (σ x y) ∈
          (S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i :=
        ⟨_, h1', rfl⟩
      rw [hs, hΨ] at h2'
      exact h2'
    have hneg : ∀ (n : ℕ) (γ : Fin Tag.F4.rank → ℤ),
        (S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[n] (-γ) = -(S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[n] γ := by
      intro n
      induction n with
      | zero => exact fun γ => rfl
      | succ n ih =>
        intro γ
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, S.frob.neg_eq]
    obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
    haveI : Fact r.Prime := ⟨hr⟩
    haveI : CharP L r := hchar
    have hr3 : r ≠ 3 := fun h => hℓp (by rw [ringChar.eq L r, h])
    have hes : 0 < e * s := Nat.mul_pos he hs0
    have hQ4 : 4 ≤ r ^ (e * s) := by
      calc 4 ≤ S.D.q := hq4
        _ = r ^ e := hq
        _ ≤ _ := le_pow_orbit hr.pos hs0
    rcases hψ.aut_cases hν hκ hnorm ((S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[s]) hmaps (hneg s)
        (iform_rho_iterate S s) with ⟨π, hπ⟩ | ⟨π, hπ⟩
    ·
      obtain ⟨σQ, hσc, f, hf1, hfker, hf2⟩ :=
        CFSG.HardMathSupport.Solomon.Coordinator.LieComp.split_exists_hom S hT i hν hψ hΨ π hπ hr
          hchar he hq
      obtain ⟨hfinK, hKcard⟩ :=
        CFSG.HardMathSupport.Solomon.Coordinator.LieComp.finite_card_fixSubfield (L := L) (r := r)
          (n := e * s) hes σQ hσc
      have hperf : Group.IsPerfect SL(ν, ↥(fixSubfield σQ)) :=
        CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect hν
      have hRf : f.range = rationalComponent S.ρ S.Γ (rootCharHom a) i :=
        le_antisymm (hf2 hperf) hf1
      let g : SL(ν, ↥(fixSubfield σQ)) →* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
        f.codRestrict _ (fun c => hRf ▸ ⟨c, rfl⟩)
      have hgker : g.ker ≤ Subgroup.center SL(ν, ↥(fixSubfield σQ)) := by
        intro c hc
        apply hfker
        rw [MonoidHom.mem_ker] at hc ⊢
        exact congrArg Subtype.val hc
      exact ⟨SL(ν, ↥(fixSubfield σQ)), inferInstance, inferInstance,
        CFSG.SeitzReduction.LinearPilot.isQuasisimple_specialLinearGroup_of_le (by omega)
          (Or.inl hν),
        Inputs295c.three_dvd_card_sl (F := ↥(fixSubfield σQ)) (m := ν) (by omega), g, hgker⟩
    ·
      obtain ⟨σQ, hσc, f, hf1, hfker, hf2⟩ := two_suN_exists_hom S hT i hν hψ hΨ π hπ hr hchar he hq
      obtain ⟨hfin, hqsC, -⟩ := stdUnitary_fixSubgroup (ν := ν) hr hes σQ hσc hν
      have h32 : (ν, r ^ (e * s)) ≠ (3, 2) := fun h => by
        have := congrArg Prod.snd h
        simp only at this
        omega
      have hRf : f.range = rationalComponent S.ρ S.Γ (rootCharHom a) i :=
        le_antisymm (hf2 (hqsC h32).1) hf1
      let g : ↥(CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)) →*
          ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
        f.codRestrict _ (fun c => hRf ▸ ⟨c, rfl⟩)
      have hgker : g.ker ≤ Subgroup.center
          ↥(CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)) := by
        intro c hc
        apply hfker
        rw [MonoidHom.mem_ker] at hc ⊢
        exact congrArg Subtype.val hc
      obtain ⟨F, hFcard, ⟨eC⟩⟩ := two_suN_exists_equiv hr hes σQ hσc hν
      have hU : UnitaryFieldData r (e * s) F :=
        ⟨hr, hes, by rw [hFcard, ← pow_mul, mul_comm]⟩
      have h3 : 3 ∣ Nat.card
          ↥(CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)) := by
        rw [← Nat.card_congr eC.toEquiv]
        exact three_dvd_card_statedSU hU hr3 (by omega)
      exact ⟨↥(CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)), inferInstance,
        hfin, hqsC h32, h3, g, hgker⟩
  ·
    exfalso
    have hp2' : 3 % 2 = 1 := by norm_num
    rcases CFSG.HardMathSupport.Solomon.Coordinator.LieComp.f4_nonA_casesP Nat.prime_three hp2' S
        hpL hTp h1 i hA with ⟨hr, hn⟩ | ⟨v, J, -, -, hr, hn⟩
    · exact hinner (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.twistInner_of_shape S hT i 2 8
        hr hn (by omega) (by omega) (by omega) (by omega))
    · exact hinner (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.twistInner_of_shape S hT i 3
        18 hr hn (by omega) (by omega) (by omega) (by omega))

theorem isRoot_chain_F4 :
    IsRoot .F4 (Pi.single (⟨0, by decide⟩ : Fin Tag.F4.rank) 1 + Pi.single ⟨1, by decide⟩ 1) ∧
    IsRoot .F4 (Pi.single (⟨1, by decide⟩ : Fin Tag.F4.rank) 1 + Pi.single ⟨2, by decide⟩ 1) ∧
    IsRoot .F4 (Pi.single (⟨0, by decide⟩ : Fin Tag.F4.rank) 1 + Pi.single ⟨1, by decide⟩ 1 +
      Pi.single ⟨2, by decide⟩ 1) := by
  have e1 : reflect .F4 ⟨0, by decide⟩ (Pi.single ⟨1, by decide⟩ 1) =
      Pi.single (⟨0, by decide⟩ : Fin Tag.F4.rank) 1 + Pi.single ⟨1, by decide⟩ 1 := by decide
  have e2 : reflect .F4 ⟨1, by decide⟩ (Pi.single ⟨2, by decide⟩ 1) =
      Pi.single (⟨1, by decide⟩ : Fin Tag.F4.rank) 1 + Pi.single ⟨2, by decide⟩ 1 := by decide
  have e3 : reflect .F4 ⟨0, by decide⟩
      (Pi.single (⟨1, by decide⟩ : Fin Tag.F4.rank) 1 + Pi.single ⟨2, by decide⟩ 1) =
      Pi.single (⟨0, by decide⟩ : Fin Tag.F4.rank) 1 + Pi.single ⟨1, by decide⟩ 1 +
        Pi.single ⟨2, by decide⟩ 1 := by decide
  have r2 := IsRoot.reflect (τ := .F4) ⟨1, by decide⟩ (IsRoot.basis ⟨2, by decide⟩)
  rw [e2] at r2
  have r1 := IsRoot.reflect (τ := .F4) ⟨0, by decide⟩ (IsRoot.basis ⟨1, by decide⟩)
  rw [e1] at r1
  have r3 := IsRoot.reflect (τ := .F4) ⟨0, by decide⟩ r2
  rw [e3] at r3
  exact ⟨r1, r2, r3⟩

theorem not_isPSolvable_fixSubgroup_F4 {K : Type} [Field K] [Finite K] (hK3 : ¬ 3 ∣ Nat.card K)
    (hK4 : 4 ≤ Nat.card K) (β : MulAut ↥(adjointGroup .F4 K)) (hβ : β ^ 3 = 1) (hβ1 : β ≠ 1) :
    ¬ CFSG.HallHigman.IsPSolvable 3 ↥(fixSubgroup β) := by
  classical
  rcases CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_field_or_inndiag_FG (Or.inl rfl)
      (fun h => absurd h (by decide)) Nat.prime_three (by norm_num) β hβ hβ1 with
    ⟨σ, ψ, -, hψ⟩ | ⟨h, hh, hβh, hp1, hh1⟩
  · intro hs
    apply not_isPSolvable_fixSubgroup_entrywise .F4 σ (fun h => absurd h (by decide))
    rw [← hψ, Inputs295c.fixSubgroup_conj]
    exact isPSolvable_of_mulEquiv ((fixSubgroup β).equivMapOfInjective _ ψ.injective) hs
  · have hhL := baseChange_mem_adjointGroup_of_mem_inndiag hh
    have hperf : commutator ↥(adjointGroup .F4 K) = ⊤ := single_edge_perfect .F4 K (by decide)
    have hmon : MonomialToralAt .F4 3 :=
      monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five (by simp)
        Nat.prime_three (by norm_num)
    obtain ⟨S', a, ι, hSq, -, hT, hap, ha1, hinj, hrange, hconj⟩ :=
      exists_langSetup_of_inner_untw (Or.inr (Or.inl rfl)) Nat.prime_three hK3 (Or.inr hK4) hmon
        hperf β h hhL hβh hp1 hh1
    obtain ⟨r1, r2, r3⟩ := isRoot_chain_F4
    obtain ⟨γ, hγ⟩ := exists_kernelRoot_of_chain a hap (by decide) (by decide) (by decide) r1 r2 r3
    obtain ⟨J, _, _, hJq, hJ3, g, hgker⟩ :=
      exists_qs_hom_F4 S' (by rw [hSq]; exact hK4) hT hap ha1 ⟦⟨γ, hγ⟩⟧
    exact not_isPSolvable_fixSubgroup_of_qs S' ι hinj hrange β hconj hT _ hJq hJ3 g hgker

theorem at_F4 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.F4 q).Valid) (hp3 : q.p ≠ 3)
    (hq2 : q.card ≠ 2) :
    Inputs295c.Outer295At ⟨.F4 q, hv⟩ ∧ Inputs295c.Inner295At ⟨.F4 q, hv⟩ := by
  have key : ∀ (S : Type) [Group S] [Finite S],
      (S ≃* (TauCeti.CFSGIndex.lie ⟨.F4 q, hv⟩).Group) → ∀ α : MulAut S, α ^ 3 = 1 → α ≠ 1 →
        ¬ CFSG.HallHigman.IsPSolvable 3 ↥(fixSubgroup α) := by
    intro S _ _ e α hα hα1
    obtain ⟨K, _, _, hK, -, ⟨eK⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4 q hv
    let e' : S ≃* ↥(adjointGroup .F4 K) := e.trans eK
    haveI : Finite ↥(adjointGroup .F4 K) := Finite.of_equiv S e'.toEquiv
    have hK3 : ¬ 3 ∣ Nat.card K := by
      rw [hK]
      exact CFSG.LieType.SeitzGeneration.not_dvd_card_of_ne Nat.prime_three (Ne.symm hp3)
    have hK4 : 4 ≤ Nat.card K := by rw [hK]; exact Inputs295c.four_le_card_of hp3 hq2
    have hβ : MulAut.congr e' α ^ 3 = 1 := congr_pow_three_eq_one e' hα
    have hβ1 : MulAut.congr e' α ≠ 1 := fun h1 =>
      hα1 ((MulAut.congr e').injective (h1.trans (map_one _).symm))
    intro hs
    apply not_isPSolvable_fixSubgroup_F4 hK3 hK4 _ hβ hβ1
    rw [Inputs295c.fixSubgroup_congr]
    exact isPSolvable_of_mulEquiv ((fixSubgroup α).equivMapOfInjective _ e'.injective) hs
  refine ⟨fun S _ _ _ _ ⟨e⟩ _ _ _ α hα hout => Or.inr (Or.inr (key S e α hα fun h => hout
    ⟨1, by rw [map_one, h]⟩)), fun S _ _ _ hnab ⟨e⟩ _ _ _ x hx => Or.inr (Or.inr ?_)⟩
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hc1 : MulAut.conj x ≠ 1 := by
    intro h
    have hxz : x ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun φ : MulAut S => φ g) h
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc g * x = x * g * x⁻¹ * x := by rw [this]
        _ = x * g := by group
    have hZ : Subgroup.center S = ⊥ := GL83.I713.center_eq_bot_of_simple hnab
    rw [hZ, Subgroup.mem_bot] at hxz
    rw [hxz, orderOf_one] at hx
    norm_num at hx
  rw [← CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup_conj]
  exact key S e (MulAut.conj x) (by rw [← map_pow, hx3, map_one]) hc1

theorem units_subsingleton_of_card_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    Subsingleton Kˣ := by
  classical
  have := Fintype.ofFinite K
  have hc : Fintype.card Kˣ = 1 := by
    rw [Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
  exact Fintype.card_le_one_iff_subsingleton.1 hc.le

theorem eq_zero_or_eq_one_of_card_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (x : K) : x = 0 ∨ x = 1 := by
  by_cases hx : x = 0
  · exact Or.inl hx
  · right
    haveI := units_subsingleton_of_card_two hK
    have := Subsingleton.elim (Units.mk0 x hx) 1
    simpa using congrArg Units.val this

theorem ringEquiv_eq_one_of_card_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (σ : K ≃+* K) : σ = 1 := by
  ext x
  rcases eq_zero_or_eq_one_of_card_two hK x with rfl | rfl
  · rw [map_zero, map_zero]
  · rw [map_one, map_one]

theorem mem_range_conj_of_inndiag_card_two {τ : Tag} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) (β : MulAut ↥(adjointGroup τ K)) (b : Fin τ.rank → Kˣ)
    {j : ModGL τ K} (hj : j ∈ adjointGroup τ K)
    (hβh : ∀ c : adjointGroup τ K, (β c : ModGL τ K) =
      (rootDiagUnit τ b * j) * c * (rootDiagUnit τ b * j)⁻¹) :
    β ∈ (MulAut.conj : ↥(adjointGroup τ K) →* MulAut ↥(adjointGroup τ K)).range := by
  have hb : b = 1 := by
    haveI := units_subsingleton_of_card_two hK
    exact Subsingleton.elim _ _
  subst hb
  have hd1 : rootDiagUnit τ (1 : Fin τ.rank → Kˣ) = 1 := Units.ext rootDiag_one
  refine ⟨⟨j, hj⟩, MulEquiv.ext fun c => Subtype.ext ?_⟩
  rw [hβh c, hd1, one_mul]
  rfl

theorem mem_range_conj_of_card_two_E {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = 2) (β : MulAut ↥(adjointGroup τ K))
    (hβ : β ^ 3 = 1) :
    β ∈ (MulAut.conj : ↥(adjointGroup τ K) →* MulAut ↥(adjointGroup τ K)).range := by
  by_cases hβ1 : β = 1
  · exact ⟨1, by rw [hβ1, map_one]⟩
  rcases CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_field_or_inndiag_E hτ
      Nat.prime_three (by norm_num) β hβ hβ1 with ⟨σ, -, hσ, -⟩ | ⟨h, hh, hβh, -, -⟩
  · exact absurd (ringEquiv_eq_one_of_card_two hK σ) hσ
  · obtain ⟨b, j, hj, rfl⟩ := hh
    exact mem_range_conj_of_inndiag_card_two hK β b hj hβh

theorem mem_range_conj_of_card_two_F4 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (β : MulAut ↥(adjointGroup .F4 K)) (hβ : β ^ 3 = 1) :
    β ∈ (MulAut.conj : ↥(adjointGroup .F4 K) →* MulAut ↥(adjointGroup .F4 K)).range := by
  by_cases hβ1 : β = 1
  · exact ⟨1, by rw [hβ1, map_one]⟩
  rcases CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_field_or_inndiag_FG (Or.inl rfl)
      (fun h => absurd h (by decide)) Nat.prime_three (by norm_num) β hβ hβ1 with
    ⟨σ, -, hσ, -⟩ | ⟨h, hh, hβh, -, -⟩
  · exact absurd (ringEquiv_eq_one_of_card_two hK σ) hσ
  · obtain ⟨b, j, hj, rfl⟩ := hh
    exact mem_range_conj_of_inndiag_card_two hK β b hj hβh

theorem outer295At_untwE_two {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {c : TauCeti.PrimePower → TauCeti.LieTypeIndex}
    (hB : CFSG.TauCetiBridge.Even.UntwistedBridgeAll τ c) (q : TauCeti.PrimePower)
    (hv : (c q).Valid) (hq2 : q.card = 2) : Inputs295c.Outer295At ⟨c q, hv⟩ := by
  intro S _ _ _ _ ⟨e⟩ _ _ _ α hα hout
  obtain ⟨K, _, _, hK, -, ⟨eK⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup hB q hv
  have hK2 : Nat.card K = 2 := hK.trans hq2
  exact absurd (mem_range_conj_of_card_two_E hτ hK2 _ (congr_pow_three_eq_one (e.trans eK) hα))
    (congr_not_mem_range_conj (e.trans eK) hout)

theorem outer295At_F4_two (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.F4 q).Valid)
    (hq2 : q.card = 2) : Inputs295c.Outer295At ⟨.F4 q, hv⟩ := by
  intro S _ _ _ _ ⟨e⟩ _ _ _ α hα hout
  obtain ⟨K, _, _, hK, -, ⟨eK⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4 q hv
  have hK2 : Nat.card K = 2 := hK.trans hq2
  exact absurd (mem_range_conj_of_card_two_F4 hK2 _ (congr_pow_three_eq_one (e.trans eK) hα))
    (congr_not_mem_range_conj (e.trans eK) hout)

theorem three_dvd_orderTwistedE6 {q : ℕ} (hq : ¬ 3 ∣ q) (hq1 : 1 ≤ q) :
    3 ∣ CFSG.Open.orderTwistedE6 q := by
  unfold CFSG.Open.orderTwistedE6
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq1
  have h2 : 3 ∣ q ^ 2 - 1 := by
    have h := three_dvd_sq_sub_one hq
    have e : ((q ^ 2 - 1 : ℕ) : ℤ) = (q : ℤ) ^ 2 - 1 := by
      rw [Nat.cast_sub hq2]
      push_cast
      ring
    rw [← e] at h
    exact_mod_cast h
  have h6 : 3 ∣ q ^ 6 - 1 := by
    refine h2.trans ?_
    have := Nat.sub_one_dvd_pow_sub_one (q ^ 2) 3
    rwa [← pow_mul] at this
  have h9 : 3 * 3 ∣ (q ^ 6 - 1) * (q ^ 2 - 1) := Nat.mul_dvd_mul h6 h2
  have hN : (q ^ 6 - 1) * (q ^ 2 - 1) ∣ q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) *
      (q ^ 6 - 1) * (q ^ 5 + 1) * (q ^ 2 - 1) := by
    refine Nat.mul_dvd_mul ?_ dvd_rfl
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left dvd_rfl _) _
  apply Nat.dvd_div_of_mul_dvd
  have hg : Nat.gcd 3 (q + 1) * 3 ∣ 3 * 3 := Nat.mul_dvd_mul_right (Nat.gcd_dvd_left _ _) 3
  exact hg.trans (h9.trans hN)

theorem not_isPSolvable_fixSubgroup_twE6 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hℓ3 : ℓ ≠ 3)
    (hq4 : 4 ≤ ℓ ^ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (β : MulAut ↥(twistedE6RootGroup K σ))
    (hβ : β ^ 3 = 1) (hβ1 : β ≠ 1) :
    ¬ CFSG.HallHigman.IsPSolvable 3 ↥(fixSubgroup β) := by
  classical
  have h3ℓ : (3 : ℕ) ≠ ℓ := fun h => hℓ3 h.symm
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -, hker, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hK σ hσ
  by_cases hΘβ : Θ β = 1
  ·
    have hmem : β ∈ (twistedE6InndiagConj K σ).range := by
      rw [range_twistedE6InndiagConj, ← hker, MonoidHom.mem_ker]
      exact hΘβ
    obtain ⟨h, hh⟩ := hmem
    have hp1 : h ^ 3 = 1 :=
      twistedE6InndiagConj_injective hℓ hf hK σ hσ (by rw [map_pow, hh, hβ, map_one])
    have hh1 : h ≠ 1 := fun h' => hβ1 (by rw [← hh, h', map_one])
    have hmon : MonomialToralAt Tag.E6 3 :=
      monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five (by simp)
        Nat.prime_three (by norm_num)
    obtain ⟨S', a, ι, hSq, -, hT, hap, -, hinj, hrange, hconj⟩ :=
      exists_langSetup_of_inndiag_twE6_of_prime hℓ hf hK σ hσ Nat.prime_three h3ℓ
        Nat.prime_three h3ℓ (Or.inr hq4) hmon (twistedE6InndiagConj K σ h)
        (h : ModGL TwistTag.E6.tag K) h.2 (twistedE6InndiagConj_apply h)
        (by rw [← Subgroup.coe_pow, hp1]; rfl) (fun h' => hh1 (Subtype.ext h'))
    rw [← hh]
    obtain ⟨i⟩ := exists_kernelComponent_E (Or.inl rfl) a hap
    obtain ⟨E, _, _, hE4, g, hgker⟩ :=
      exists_sl2_hom_simplyLaced S' (Or.inr (Or.inl rfl)) (by rw [hSq]; exact hq4) hT i
    exact not_isPSolvable_fixSubgroup_of_sl2 S' ι hinj hrange _ hconj hT i hE4 g hgker
  ·
    have hK2f : Nat.card K = ℓ ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
    obtain ⟨d, hd, hd1, r, s, T, ε, hT, hε, hrs, ψ, hψ, -⟩ :=
      CFSG.HardMathSupport.Lang.Coordinator.twisted_E6_field_descent_data_of_prime_order hℓ hf K
        hK2f σ hσ Θ hΘ Nat.prime_three (by norm_num) β hβ hΘβ
    have hdp : d * 3 = f := by rw [hd, mul_comm]
    obtain ⟨fr, hfr, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hℓ
        (by omega : 1 ≤ 2 * f) hK2f
    obtain ⟨κ, hκ⟩ : ∃ κ : K ≃+* K, ∀ c, κ c = c ^ ℓ ^ (2 * d) :=
      ⟨fr ^ (2 * d), fun c => CFSG.LieType.Chevalley.ringAut_pow_apply_of_frobenius hfr (2 * d) c⟩
    have hKdp : Nat.card K = ℓ ^ (2 * d * 3) := by rw [hK2f, mul_assoc, hdp]
    have hσdp : ∀ c, σ c = c ^ ℓ ^ (d * 3) := fun c => by rw [hσ, hdp]
    have hσ₀ : ∀ c : fixSubfield κ,
        (CFSG.LieType.Chevalley.fixSubfieldRestrict T κ c : K) = (c : K) ^ ℓ ^ d :=
      fun c => by rw [CFSG.LieType.Chevalley.coe_fixSubfieldRestrict, hT]
    obtain ⟨-, hcardk, hJC, -, hder, hsimpleJ, hncJ, -⟩ :=
      CFSG.RankThree.Chevalley.twisted_E6_canonical_odd_field_derived_subgroup_and_pointwise_centralizer
        hℓ hd1 le_rfl (by decide) K hKdp κ hκ σ hσdp
        (CFSG.LieType.Chevalley.fixSubfieldRestrict T κ) hσ₀ ε hε
    set C := graphFixedRootGroup TwistTag.E6 K σ.toRingHom with hC
    set Jf := CFSG.RankThree.Chevalley.subfieldRootGroupImage TwistTag.E6 (fixSubfield κ)
      (CFSG.LieType.Chevalley.fixSubfieldRestrict T κ) with hJdef
    set δ := fieldActor (t := TwistTag.E6) σ ε with hδdef
    haveI : Finite (fixSubfield κ) := Subtype.finite
    haveI : Finite C := Subtype.finite
    have hJδ : Jf.subgroupOf C ≤ fixSubgroup δ := by
      rw [← hder]
      intro x hx
      have hx' := Subgroup.commutator_le_self _ hx
      exact hx'
    have eJC : Jf.subgroupOf C ≃* Jf := Subgroup.subgroupOfEquivOfLe hJC
    haveI := hsimpleJ
    have hJs : IsSimpleGroup (Jf.subgroupOf C) := eJC.isSimpleGroup
    have hJnc : ¬ IsMulCommutative (Jf.subgroupOf C) := by
      rintro ⟨hc⟩
      apply hncJ
      intro a b
      apply eJC.symm.injective
      rw [map_mul, map_mul]
      exact hc.comm _ _
    let q' : TauCeti.PrimePower := ⟨ℓ, d, hℓ, hd1⟩
    have hv' : (TauCeti.LieTypeIndex.twistedE6 q').Valid := TauCeti.LieTypeIndex.valid_twistedE6 q'
    have hcardk' : Nat.card (fixSubfield κ) = q'.card ^ 2 := by
      rw [hcardk, TauCeti.PrimePower.card_def, ← pow_mul, mul_comm]
    have hσ₀k : ∀ c, (CFSG.LieType.Chevalley.fixSubfieldRestrict T κ) c = c ^ q'.card := fun c =>
      Subtype.ext (by rw [hσ₀ c, TauCeti.PrimePower.card_def]; rfl)
    obtain ⟨eCat⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.catEquiv_twistedE6_of_field q' hv'
        (fixSubfield κ) hcardk' (CFSG.LieType.Chevalley.fixSubfieldRestrict T κ) hσ₀k
    let eXJ : ↥(graphFixedRootGroup TwistTag.E6 (fixSubfield κ)
        (CFSG.LieType.Chevalley.fixSubfieldRestrict T κ).toRingHom) ≃* ↥Jf :=
      (graphFixedRootGroup TwistTag.E6 (fixSubfield κ)
        (CFSG.LieType.Chevalley.fixSubfieldRestrict T κ).toRingHom).equivMapOfInjective
        (baseChangeGL (fixSubfield κ).subtype) (baseChangeGL_injective _)
    haveI : Finite ↥(graphFixedRootGroup TwistTag.E6 (fixSubfield κ)
        (CFSG.LieType.Chevalley.fixSubfieldRestrict T κ).toRingHom) :=
      Finite.of_equiv _ (eXJ.trans eJC.symm).toEquiv.symm
    have hJ3 : 3 ∣ Nat.card ↥(Jf.subgroupOf C) := by
      rw [Nat.card_congr eJC.toEquiv, ← Nat.card_congr eXJ.toEquiv,
        CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨.twistedE6 q', hv'⟩ _
          ⟨eCat.symm⟩]
      have hq3 : ¬ 3 ∣ q'.card := by
        rw [TauCeti.PrimePower.card_def]
        exact fun h => hℓ3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1
          (Nat.prime_three.dvd_of_dvd_pow h)).symm
      exact three_dvd_orderTwistedE6 hq3 (Nat.one_le_iff_ne_zero.2 (by
        rw [TauCeti.PrimePower.card_def]
        exact pow_ne_zero _ hℓ.ne_zero))
    have hδ : ¬ CFSG.HallHigman.IsPSolvable 3 ↥(fixSubgroup δ) := fun hs =>
      CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.not_isPSolvable_three_of_simple hJs
        hJnc hJ3 (isPSolvable_of_le hs hJδ)
    have hfixr : fixSubgroup (β ^ r) = fixSubgroup β :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_pow_eq_of_pow_pow' hrs
    intro hs
    apply hδ
    rw [← hψ, Inputs295c.fixSubgroup_conj, hfixr]
    exact isPSolvable_of_mulEquiv ((fixSubgroup β).equivMapOfInjective _ ψ.injective) hs

theorem outer295At_twistedE6 (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid) (hp3 : q.p ≠ 3) (hq2 : q.card ≠ 2) :
    Inputs295c.Outer295At ⟨.twistedE6 q, hv⟩ := by
  intro S _ _ _ _ ⟨e⟩ _ _ _ α hα hout
  obtain ⟨K, _, σ, hK, hσ, ⟨eK⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_twistedE6 q hv
  haveI : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero))
  let e' : S ≃* ↥(twistedE6RootGroup K σ) := e.trans eK
  haveI : Finite ↥(twistedE6RootGroup K σ) := Finite.of_equiv S e'.toEquiv
  have hq4 : 4 ≤ q.p ^ q.exponent := by
    rw [← TauCeti.PrimePower.card_def]
    exact Inputs295c.four_le_card_of hp3 hq2
  have hβ : MulAut.congr e' α ^ 3 = 1 := congr_pow_three_eq_one e' hα
  have hβ1 : MulAut.congr e' α ≠ 1 := by
    intro h1
    apply hout
    refine ⟨1, ?_⟩
    rw [map_one]
    exact ((MulAut.congr e').injective (h1.trans (map_one _).symm)).symm
  refine Or.inr (Or.inr fun hs => not_isPSolvable_fixSubgroup_twE6 q.prime_p q.exponent_pos hp3
    hq4 hK σ hσ _ hβ hβ1 ?_)
  rw [Inputs295c.fixSubgroup_congr]
  exact isPSolvable_of_mulEquiv ((fixSubgroup α).equivMapOfInjective _ e'.injective) hs

end Exceptional

section BlocksQS

theorem not_isPSolvable_of_quasisimple_le {G : Type} [Group G] [Finite G] {R C : Subgroup G}
    (hR : CFSG.IsQuasisimple ↥R) (h3 : 3 ∣ Nat.card R) (hRC : R ≤ C) :
    ¬ CFSG.HallHigman.IsPSolvable 3 ↥C := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hs
  exact Inputs295c.not_three_dvd_card_of_isPSolvable hR (isPSolvable_of_le hs hRC) h3

section Symplectic

open Polynomial Module Matrix CFSG.RankThree.Classical CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCSpIsotypic
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Malle.E27Lie
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

open scoped Classical in
theorem not_isPSolvable_centralizer_psp {r ℓ f : ℕ} {K : Type} [Field K] [Finite K]
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hℓ3 : ℓ ≠ 3) (hq4 : 4 ≤ ℓ ^ f)
    (hr : 2 ≤ r) {a : StatedProj (StatedSp r K)} (ha : orderOf a = 3) :
    ¬ CFSG.HallHigman.IsPSolvable 3
      ↥(Subgroup.centralizer ({a} : Set (StatedProj (StatedSp r K)))) := by
  have : Finite (StatedProj (StatedSp r K)) :=
    CFSG.ClassicalGroups.Symplectic.finite_statedProj_statedSp r K
  have hrq : ¬ (r = 2 ∧ ℓ ^ f = 2) := by omega
  obtain ⟨-, -, hinj⟩ := spProj_facts hℓ hf hK hr hrq
  have hcharK : CharP K ℓ := by
    have := Fintype.ofFinite K
    have : Fact ℓ.Prime := ⟨hℓ⟩
    exact charP_of_card_eq_prime_pow (f := f) (by rw [Fintype.card_eq_nat_card, hK])
  have hpK : ((3 : ℕ) : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K ℓ]
    intro hd
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 hd)
  obtain ⟨⟨x, ⟨hxa, hxo⟩, -⟩, hblocks⟩ := symplectic_cross_prime_primary_centralizer_blocks hℓ hf
    hK Nat.prime_three (by norm_num) (Ne.symm hℓ3) (by omega) a ha
  have blocks0 := hblocks x hxa hxo
  subst hxa
  have blocks := blocks0
  have hcent := blocks.centralizer_eq
  have hker : (proj r K).ker ≤ Subgroup.center (StatedSp r K) := by
    rw [SymplecticHigher.ker_proj]
    exact SymplecticHigher.spScalars_le_center
  have hx3 : x ^ 3 = 1 := by rw [← hxo]; exact pow_orderOf_eq_one x
  have hsq : Squarefree (minpoly K (spEnd x)) := (altPrimaryData_spLin hpK hx3).squarefree
  have hdeg : (minpoly K (spEnd x)).natDegree ≤ 3 := by
    have hdvd : minpoly K (spEnd x) ∣ (X ^ 3 - C (1 : K) : K[X]) := by
      refine minpoly.dvd K _ ?_
      have h1 : spEnd x ^ 3 = 1 := by
        have : (spLin r K x) ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
        have h2 := congrArg (fun u : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K) =>
          (u : Module.End K (Fin r ⊕ Fin r → K))) this
        simpa [Units.val_pow_eq_pow_val] using h2
      simp [h1]
    have hne0 : (X ^ 3 - C (1 : K) : K[X]) ≠ 0 := (monic_X_pow_sub_C _ (by norm_num)).ne_zero
    have h4 := Polynomial.natDegree_le_of_dvd hdvd hne0
    rwa [natDegree_X_pow_sub_C] at h4
  have hfr : Module.finrank K (Fin r ⊕ Fin r → K) = 2 * r := by
    rw [Module.finrank_fintype_fun_eq_card]; simp [two_mul]
  obtain ⟨h, hm⟩ := exists_primaryMultiplicity_gt (M := 1) hsq hdeg (by omega)
  by_cases h1 : (h : K[X]) = X - 1
  ·
    have hd : 2 ≤ spFixedDim x := by
      have h2 : 2 ≤ primaryMultiplicity (spEnd x) (X - 1) := by rw [← h1]; exact hm
      rw [show (X - 1 : K[X]) = X - C 1 by rw [C_1], primaryMultiplicity_X_sub_C_eq] at h2
      exact h2
    have hl : SpFixedListed x := ⟨hd, by omega⟩
    have h42 : ¬ (spFixedDim x = 4 ∧ Nat.card K = 2) := by omega
    have hqs := spFixedFactor_isQuasisimple hK hℓ hf blocks hl h42
    have hperf : ⁅spFixedFactor x, spFixedFactor x⁆ = spFixedFactor x :=
      commutator_eq_of_isPerfect hqs.1
    have hnd : ¬ 3 ∣ Nat.card K := by
      rw [hK]
      intro hd3
      exact hℓ3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1
        (Nat.prime_three.dvd_of_dvd_pow hd3)).symm
    refine not_isPSolvable_of_quasisimple_le
      (CFSG.LocalCores.isQuasisimple_map hqs (proj r K) (not_le_ker_proj_of_isQuasisimple hqs))
      (three_dvd_card_map_of_perfect (proj r K) hker hperf
        (three_dvd_card_spFixedFactor blocks hd hnd)) ?_
    rw [hcent]
    exact Subgroup.map_mono (spFixedFactor_le_centralizer x)
  ·
    have hm2 : 2 ≤ primaryMultiplicity (spEnd x) (h : K[X]) := by omega
    have facts := spBlockFacts_nontrivial_three hq4 blocks h h1
    have hqs := spPull_isQuasisimple facts hm2
    obtain ⟨hle, hqm, -⟩ := spListed_facts (p := 3) Nat.prime_three
      (B := ⊤) le_top hinj hcent (spPull_le_centralizer x _) (spPull_normalized x _) hqs
    have h3 := dvd_card_spBlockImage (K := K) (r := r) (by omega) Nat.prime_three (by norm_num)
      blocks h h1 hm2
    rw [spBlockImage_eq] at h3
    exact not_isPSolvable_of_quasisimple_le hqm h3 hle

theorem inner295At_of_projSp_four {d : TauCeti.ValidLieTypeIndex} {r : ℕ} (hr : 2 ≤ r)
    (h : ∀ (K : Type) [Group K], (K ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∃ (F : Type) (_ : Field F) (ℓ f : ℕ), ℓ.Prime ∧ 1 ≤ f ∧ Nat.card F = ℓ ^ f ∧ ℓ ≠ 3 ∧
        4 ≤ ℓ ^ f ∧ Nonempty (K ≃* StatedProj (StatedSp r F))) :
    Inputs295c.Inner295At d := by
  intro K _ _ _ _ ⟨e⟩ _ _ _ x hx
  obtain ⟨F, _, ℓ, f, hℓ, hf, hF, hℓ3, hq4, ⟨g⟩⟩ := h K e
  haveI : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; positivity)
  haveI : Finite (StatedProj (StatedSp r F)) :=
    CFSG.ClassicalGroups.Symplectic.finite_statedProj_statedSp r F
  have hgx : orderOf (g x) = 3 := by rw [MulEquiv.orderOf_eq]; exact hx
  exact Or.inr (Or.inr fun hs => not_isPSolvable_centralizer_psp hℓ hf hF hℓ3 hq4 hr hgx
    (isPSolvable_centralizer_of_mulEquiv g x hs))

theorem inner295At_typeC_three {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.C 3 q).Valid) (hp3 : q.p ≠ 3) :
    Inputs295c.Inner295At ⟨.C 3 q, hv⟩ := by
  have hp2 : q.p ≠ 2 := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).2
  have hq4 : 4 ≤ q.p ^ q.exponent := by
    have h5 : 5 ≤ q.p := by
      have := q.prime_p.two_le
      have h4 : q.p ≠ 4 := fun h4 => by
        have := q.prime_p
        rw [h4] at this
        norm_num at this
      omega
    exact h5.trans' (by norm_num) |>.trans (Nat.le_self_pow q.exponent_pos.ne' _)
  refine inner295At_of_projSp_four (r := 3) (by norm_num) fun K _ e => ?_
  obtain ⟨-, F, _, _, hF, hf⟩ := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC 3 q hv e
  exact ⟨F, inferInstance, q.p, q.exponent, q.prime_p, q.exponent_pos, hF, hp3, hq4, hf⟩

theorem inner295At_typeB_even_three {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.B 3 q).Valid) (hp2 : q.p = 2) (hq2 : q.card ≠ 2) :
    Inputs295c.Inner295At ⟨.B 3 q, hv⟩ := by
  have hq4 : 4 ≤ q.p ^ q.exponent := by
    rw [← TauCeti.PrimePower.card_def]
    exact Inputs295c.four_le_card_of (by rw [hp2]; norm_num) hq2
  refine inner295At_of_projSp_four (r := 3) (by norm_num) fun K _ e => ?_
  obtain ⟨-, F, _, _, hF, hf⟩ :=
    CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even 3 q hv hp2 le_rfl e
  exact ⟨F, inferInstance, q.p, q.exponent, q.prime_p, q.exponent_pos, hF,
    by rw [hp2]; norm_num, hq4, hf⟩

end Symplectic

section Unitary

open Polynomial Module Matrix CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.FOC CFSG.RankThree.PartOne
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.HardMathSupport.Curtis.Coordinator
  CFSG.HardMathSupport.Curtis.Coordinator.SPLCell.Uni CFSG.HardMathSupport.Malle.E27Lie

theorem three_dvd_natCard_of_one_le_pRank {G : Type} [Group G] [Finite G]
    (h : 1 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G)) : 3 ∣ Nat.card G := by
  obtain ⟨E, -, -, hcard⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) (⊤ : Subgroup G)
  have h1 : 3 ∣ Nat.card E := by
    rw [hcard]
    exact dvd_pow_self 3 (by omega)
  exact h1.trans (Subgroup.card_subgroup_dvd_card E)

open scoped Classical in
theorem not_isPSolvable_fixSubgroup_primeFormConjHom {ℓ f n : ℕ} {K : Type} [Field K]
    [Finite K] {h : UnitaryFieldData ℓ f K} (hℓ3 : ℓ ≠ 3) (y : primeFormUnitary h (idGram K n))
    {c : Kˣ} (hyp : (y : GL (Fin n) K) ^ 3 = GeneralLinearGroup.scalar (Fin n) c)
    (hq : (4 ≤ ℓ ^ f ∧ 4 ≤ n) ∨ (ℓ ^ f = 2 ∧ 10 ≤ n) ∨ (4 ≤ n ∧ ∀ μ : K, μ ^ 3 ≠ c)) :
    ¬ CFSG.HallHigman.IsPSolvable 3 ↥(fixSubgroup (primeFormConjHom h (idGram K n) y)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hℓ := h.prime
  have : CharP K ℓ := h.charP
  have h3K : ((3 : ℕ) : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K ℓ]
    intro hd
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 hd)
  have hx := squarefree_minpoly_toLinU_of_pow_scalar y h3K hyp
  have hX : ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) = Matrix.toLin' ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    (Matrix.toLin'_apply' _).symm
  have hdvd : minpoly K ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) ∣ (X ^ 3 - C (c : K) : K[X]) := by
    refine minpoly.dvd K _ ?_
    rw [hX]
    exact SPLCell.aeval_linEnd_X_pow_sub_C c hyp
  have hdeg : (minpoly K ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K))).natDegree ≤ 3 := by
    have hne0 : (X ^ 3 - C (c : K) : K[X]) ≠ 0 := (monic_X_pow_sub_C _ (by norm_num)).ne_zero
    have h4 := Polynomial.natDegree_le_of_dvd hdvd hne0
    rwa [natDegree_X_pow_sub_C] at h4
  have hfr : Module.finrank K (Fin n → K) = n := Module.finrank_fin_fun K
  have hgood : ∃ a : primaryFactors ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)), IsGoodBlock h (toLinU h n y) a := by
    rcases hq with ⟨hq4, hn4⟩ | ⟨hq2, hn10⟩ | ⟨hn4, hc⟩
    · obtain ⟨a, ha⟩ := exists_primaryMultiplicity_gt (M := 1) hx hdeg (by omega)
      exact ⟨a, isGoodBlock_of_numeric a (by omega) (fun _ => hq4) (fun _ => by omega)⟩
    · obtain ⟨a, ha⟩ := exists_primaryMultiplicity_gt (M := 3) hx hdeg (by omega)
      exact ⟨a, isGoodBlock_of_numeric a (by omega) (fun e => by omega) (fun e => by omega)⟩
    ·
      obtain ⟨a, ha⟩ := exists_primaryMultiplicity_gt (M := 1) hx hdeg (by omega)
      have ha2 : 2 ≤ (a : K[X]).natDegree := by
        by_contra hlt
        have hpos := (irreducible_of_mem_primaryFactors a.2).natDegree_pos
        have h1 : (a : K[X]).natDegree = 1 := by omega
        have hmon := monic_of_mem_primaryFactors a.2
        have hdvd' : (a : K[X]) ∣ (X ^ 3 - C (c : K) : K[X]) :=
          ((mem_primaryFactors.mp a.2).2.2).trans hdvd
        rw [hmon.eq_X_add_C h1, show (X + C ((a : K[X]).coeff 0) : K[X]) =
          X - C (-(a : K[X]).coeff 0) by rw [map_neg, sub_neg_eq_add]] at hdvd'
        have hroot := Polynomial.dvd_iff_isRoot.mp hdvd'
        apply hc (-(a : K[X]).coeff 0)
        simpa [sub_eq_zero] using hroot
      have hbound : 4 ≤ ℓ ^ (f * (a : K[X]).natDegree) := by
        have hℓ2 := hℓ.two_le
        have hf1 := h.one_le
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ ℓ ^ 2 := Nat.pow_le_pow_left hℓ2 2
          _ ≤ ℓ ^ (f * (a : K[X]).natDegree) := Nat.pow_le_pow_right (by omega) (by nlinarith)
      exact ⟨a, isGoodBlock_of_numeric' a (by omega) (fun _ => hbound) (fun _ => by omega)⟩
  obtain ⟨a, ha⟩ := hgood
  obtain ⟨Q, hQc, hQd, hQ, hQ3⟩ := exists_quasisimple_three_dvd_block h3K hℓ3 hx a ha
  have hrange : Q ≤ (phiS h (n := n)).range := by
    intro g hg
    exact mem_range_phiS (mem_sesqSpecialUnitaryGroup.mpr
      ⟨(mem_unitaryCentralizer.mp (hQc hg)).1, hQd g hg⟩)
  set Bq : Subgroup ↥(gramSU h (idGram K n)) := Q.comap (phiS h) with hBq
  have hmap : Bq.map (phiS h) = Q := Subgroup.map_comap_eq_self hrange
  have eB : ↥Bq ≃* ↥Q := (Subgroup.equivMapOfInjective Bq (phiS h) phiS_injective).trans
    (MulEquiv.subgroupCongr hmap)
  have hBqq : CFSG.IsQuasisimple ↥Bq := CFSG.LocalCores.isQuasisimple_of_mulEquiv eB.symm hQ
  have h3Bq : 3 ∣ Nat.card Bq := by rwa [Nat.card_congr eB.toEquiv]
  set π : ↥(gramSU h (idGram K n)) →* primeFormP h (idGram K n) :=
    QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n) with hπdef
  have hker : π.ker ≤ Subgroup.center ↥(gramSU h (idGram K n)) := by
    intro g hg
    rw [Subgroup.mem_center_iff]
    intro g'
    have hg' : g ∈ normOneScalars h (gramSU h (idGram K n)) n := by
      rwa [hπdef, QuotientGroup.ker_mk'] at hg
    obtain ⟨c, -, -, hc⟩ := hg'
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hc]
    exact (GeneralLinearGroup.scalar_commute c _).symm
  have hπ : ∃ b : Bq, (π.comp Bq.subtype) b ≠ 1 := by
    by_contra hall
    push Not at hall
    obtain ⟨u, v, huv⟩ := Inputs295c.exists_noncomm_of_isQuasisimple hBqq
    have hu : (u : gramSU h (idGram K n)) ∈ Subgroup.center _ := hker (hall u)
    exact huv (Subtype.ext (Subgroup.mem_center_iff.1 hu (v : gramSU h (idGram K n))).symm)
  have hns := Inputs295c.not_isPSolvable_range_of_quasisimple hBqq h3Bq (π.comp Bq.subtype) hπ
  have hfix : (π.comp Bq.subtype).range ≤ fixSubgroup (primeFormConjHom h (idGram K n) y) := by
    rintro _ ⟨g, rfl⟩
    rw [mem_fixSubgroup]
    change primeFormConjHom h (idGram K n) y ((g : gramSU h (idGram K n)) :
      primeFormP h (idGram K n)) = ((g : gramSU h (idGram K n)) : primeFormP h (idGram K n))
    rw [primeFormConjHom_mk]
    congr 1
    apply Subtype.ext
    have hcomm := (mem_unitaryCentralizer.mp (hQc (show phiS h g ∈ Q from g.2))).2
    have hc : (y : GL (Fin n) K) * ((g : gramSU h (idGram K n)) : GL (Fin n) K) =
        ((g : gramSU h (idGram K n)) : GL (Fin n) K) * y := by
      apply Matrix.GeneralLinearGroup.toLin.injective
      rw [map_mul, map_mul]
      exact Units.ext hcomm.eq.symm
    change (y : GL (Fin n) K) * ((g : gramSU h (idGram K n)) : GL (Fin n) K) *
      (y : GL (Fin n) K)⁻¹ = ((g : gramSU h (idGram K n)) : GL (Fin n) K)
    rw [hc, mul_inv_cancel_right]
  intro hs
  exact hns (isPSolvable_of_le hs hfix)

theorem not_isPSolvable_centralizer_primeFormP {ℓ f n : ℕ} {K : Type} [Field K] [Finite K]
    {h : UnitaryFieldData ℓ f K} (hℓ3 : ℓ ≠ 3) (hq : (4 ≤ ℓ ^ f ∧ 4 ≤ n) ∨ (ℓ ^ f = 2 ∧ 10 ≤ n))
    {z : primeFormP h (idGram K n)} (hz : z ^ 3 = 1) :
    ¬ CFSG.HallHigman.IsPSolvable 3
      ↥(Subgroup.centralizer ({z} : Set (primeFormP h (idGram K n)))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective z
  set y : primeFormUnitary h (idGram K n) :=
    ⟨((s : gramSU h (idGram K n)) : GL (Fin n) K), s.2.1⟩ with hy
  have hs3 : s ^ 3 ∈ normOneScalars h (gramSU h (idGram K n)) n := by
    rw [← QuotientGroup.eq_one_iff]
    simpa using hz
  obtain ⟨c, -, -, hc⟩ := hs3
  have hyp : (y : GL (Fin n) K) ^ 3 = GeneralLinearGroup.scalar (Fin n) c := by
    have e1 : (y : GL (Fin n) K) = ((s : gramSU h (idGram K n)) : GL (Fin n) K) := rfl
    rw [e1, ← Subgroup.coe_pow, hc]
  have hle : fixSubgroup (primeFormConjHom h (idGram K n) y) ≤
      Subgroup.centralizer ({(QuotientGroup.mk' _ s : primeFormP h (idGram K n))} :
        Set (primeFormP h (idGram K n))) := by
    intro r hr
    obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective r
    have h1 : primeFormConjHom h (idGram K n) y ((t : gramSU h (idGram K n)) :
        primeFormP h (idGram K n)) = (t : primeFormP h (idGram K n)) := by
      rw [mem_fixSubgroup] at hr
      exact hr
    rw [primeFormConjHom_mk] at h1
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h2 : (⟨(y : GL (Fin n) K) * (t : GL (Fin n) K) * (y : GL (Fin n) K)⁻¹,
        conj_mem_gramSU h (idGram K n) y.2 t.2⟩ : gramSU h (idGram K n)) = s * t * s⁻¹ :=
      Subtype.ext rfl
    rw [h2] at h1
    change ((s * t * s⁻¹ : gramSU h (idGram K n)) : primeFormP h (idGram K n)) = _ at h1
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  intro hs
  exact not_isPSolvable_fixSubgroup_primeFormConjHom hℓ3 y hyp (hq.imp_right Or.inl)
    (isPSolvable_of_le hs hle)

theorem fixSubgroup_primeFormConjHom_le_centralizer {ℓ f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData ℓ f K} (s : gramSU h (idGram K n)) :
    fixSubgroup (primeFormConjHom h (idGram K n)
      ⟨((s : gramSU h (idGram K n)) : GL (Fin n) K), s.2.1⟩) ≤
      Subgroup.centralizer ({(QuotientGroup.mk' _ s : primeFormP h (idGram K n))} :
        Set (primeFormP h (idGram K n))) := by
  intro r hr
  obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective r
  have h1 : primeFormConjHom h (idGram K n) ⟨((s : gramSU h (idGram K n)) : GL (Fin n) K), s.2.1⟩
      ((t : gramSU h (idGram K n)) : primeFormP h (idGram K n)) =
      (t : primeFormP h (idGram K n)) := by
    rw [mem_fixSubgroup] at hr
    exact hr
  rw [primeFormConjHom_mk] at h1
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h2 : (⟨((s : gramSU h (idGram K n)) : GL (Fin n) K) * (t : GL (Fin n) K) *
      ((s : gramSU h (idGram K n)) : GL (Fin n) K)⁻¹,
      conj_mem_gramSU h (idGram K n) s.2.1 t.2⟩ : gramSU h (idGram K n)) = s * t * s⁻¹ :=
    Subtype.ext rfl
  rw [h2] at h1
  change ((s * t * s⁻¹ : gramSU h (idGram K n)) : primeFormP h (idGram K n)) = _ at h1
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1
  exact (mul_inv_eq_iff_eq_mul.mp h1).symm

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LocalAnalysis.RankFourTheoremC.TorusU
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.CrossUni in
theorem four_le_pRank_fixSubgroup_primeFormConjHom {ℓ f n : ℕ} {K : Type} [Field K] [Finite K]
    {h : UnitaryFieldData ℓ f K} (h3q : 3 ∣ ℓ ^ f + 1) (hn : 5 ≤ n)
    (y : primeFormUnitary h (idGram K n)) (hy3 : (y : GL (Fin n) K) ^ 3 = 1) :
    4 ≤ CFSG.Open.pRank 3 (fixSubgroup (primeFormConjHom h (idGram K n) y)) := by
  classical
  haveI : Fact ℓ.Prime := ⟨h.prime⟩
  haveI : CharP K ℓ := h.charP
  have hK : Nat.card K = (ℓ ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  set σ := unitaryInvolution K ℓ f with hσdef
  have hσ : IsUnitaryInvolution σ := isUnitaryInvolution_unitaryInvolution hK
  have hq : 1 < ℓ ^ f := one_lt_pow_of_card hK
  have hcard : 3 ∣ Nat.card Kˣ := by
    rw [card_units_of_card hK, sq_sub_one_eq _ hq.le]
    exact Dvd.dvd.mul_right h3q _
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_three hcard
  have hσζ : σ ζ = ζ⁻¹ := by
    rw [hσdef, unitaryInvolution_apply]
    have h1 : ζ ^ (ℓ ^ f + 1) = 1 := (hζ.pow_eq_one_iff_dvd _).2 h3q
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact h1)
  have hsiso : conjTr σ ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    have hy := y.2
    change (((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * idGram K n *
      ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = idGram K n at hy
    rw [conjTr, hσdef, ← CFSG.LieType.SeitzGeneration.SUPair.bar_funext h]
    simpa [idGram] using hy
  obtain ⟨F, hFi, hFc, hFs⟩ := exists_torusHom_rank4 hσ Nat.prime_three (by norm_num) hζ hσζ hn
    (y : GL (Fin n) K) hsiso hy3
  have hFS : ∀ a, ((F a : SUid σ n) : GL (Fin n) K) ∈ gramSU h (idGram K n) := by
    intro a
    rw [idGram, CFSG.LieType.SeitzGeneration.SUPair.gramSU_one_eq h n]
    exact (F a).2
  let F' : (Fin 4 → Multiplicative (ZMod 3)) →* gramSU h (idGram K n) :=
    ((SUid σ n).subtype.comp F).codRestrict _ hFS
  let ψ : (Fin 4 → Multiplicative (ZMod 3)) →* primeFormP h (idGram K n) :=
    (QuotientGroup.mk' _).comp F'
  have hψ : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at ha
    obtain ⟨c, -, -, hc⟩ := ha
    have hsc : ((F a : SUid σ n) : GL (Fin n) K) ∈ StatedScalars (Fin n) K := ⟨c, hc.symm⟩
    exact (Subgroup.mem_bot).2 (hFi (by rw [hFs a hsc, map_one]))
  have hA : Nat.card (Fin 4 → Multiplicative (ZMod 3)) = 3 ^ 4 := by
    simp [Nat.card_eq_fintype_card]
  refine CFSG.SectionRank.le_pRank_of_injective (p := 3) (by norm_num) (fun a b => mul_comm a b)
    (fun a => funext fun i => pow_prime_eq_one_zmod (a i)) hA ψ hψ ?_
  rintro _ ⟨a, rfl⟩
  rw [mem_fixSubgroup]
  change primeFormConjHom h (idGram K n) y ((F' a : gramSU h (idGram K n)) :
    primeFormP h (idGram K n)) = ((F' a : gramSU h (idGram K n)) : primeFormP h (idGram K n))
  rw [primeFormConjHom_mk]
  congr 1
  apply Subtype.ext
  change (y : GL (Fin n) K) * ((F a : SUid σ n) : GL (Fin n) K) * (y : GL (Fin n) K)⁻¹ =
    ((F a : SUid σ n) : GL (Fin n) K)
  rw [hFc a, mul_inv_cancel_right]

theorem no_cube_root_of_card_four {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    {c : Kˣ} (hc1 : c ≠ 1) (μ : K) : μ ^ 3 ≠ c := by
  intro hμ
  by_cases hμ0 : μ = 0
  · rw [hμ0] at hμ
    exact c.ne_zero (by rw [← hμ]; norm_num)
  · have hcard : Nat.card Kˣ = 3 := by
      have := Fintype.ofFinite K
      classical
      rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
    have h1 : (Units.mk0 μ hμ0) ^ 3 = 1 := by
      rw [← hcard]
      exact pow_card_eq_one'
    apply hc1
    apply Units.ext
    rw [← hμ]
    simpa using congrArg Units.val h1

theorem eq_two_of_pow_eq_two {ℓ f : ℕ} (hℓ : ℓ.Prime) (h : ℓ ^ f = 2) : ℓ = 2 ∧ f = 1 := by
  have hf : f ≠ 0 := by
    rintro rfl
    norm_num at h
  have hdvd : ℓ ∣ 2 := by
    rw [← h]
    exact dvd_pow_self ℓ hf
  have hℓ2 : ℓ = 2 := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 hdvd
  refine ⟨hℓ2, ?_⟩
  rw [hℓ2] at h
  have h' : 2 ^ f = 2 ^ 1 := by rw [h, pow_one]
  exact Nat.pow_right_injective le_rfl h'

theorem excl295At_primeFormP_two {ℓ f n : ℕ} {K : Type} [Field K] [Finite K]
    {h : UnitaryFieldData ℓ f K} (hq : ℓ ^ f = 2) (hn : 5 ≤ n)
    {z : primeFormP h (idGram K n)} (hz : orderOf z = 3) : Inputs295.Excl295At z := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hz3 : z ^ 3 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  obtain ⟨hℓ2, hf1⟩ := eq_two_of_pow_eq_two h.prime hq
  have hℓ3 : ℓ ≠ 3 := by omega
  have hK4 : Nat.card K = 4 := by rw [h.card, hℓ2, hf1]; norm_num
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective z
  set y : primeFormUnitary h (idGram K n) :=
    ⟨((s : gramSU h (idGram K n)) : GL (Fin n) K), s.2.1⟩ with hy
  have hs3 : s ^ 3 ∈ normOneScalars h (gramSU h (idGram K n)) n := by
    rw [← QuotientGroup.eq_one_iff]
    simpa using hz3
  obtain ⟨c, -, -, hc⟩ := hs3
  have hyp : (y : GL (Fin n) K) ^ 3 = GeneralLinearGroup.scalar (Fin n) c := by
    have e1 : (y : GL (Fin n) K) = ((s : gramSU h (idGram K n)) : GL (Fin n) K) := rfl
    rw [e1, ← Subgroup.coe_pow, hc]
  have hle := fixSubgroup_primeFormConjHom_le_centralizer (h := h) s
  by_cases hc1 : c = 1
  · refine Or.inr (Or.inl ((four_le_pRank_fixSubgroup_primeFormConjHom (by rw [hq]) hn y
      (by rw [hyp, hc1, map_one])).trans (CFSG.SectionRank.pRank_mono (by norm_num) hle)))
  · exact Or.inr (Or.inr fun hs => not_isPSolvable_fixSubgroup_primeFormConjHom hℓ3 y hyp
      (Or.inr (Or.inr ⟨by omega, no_cube_root_of_card_four hK4 hc1⟩)) (isPSolvable_of_le hs hle))

theorem outerExcl295_primeFormP_two {ℓ f n : ℕ} {K : Type} [Field K] [Finite K]
    (h : UnitaryFieldData ℓ f K) (hq : ℓ ^ f = 2) (hn : 5 ≤ n)
    (β : MulAut (primeFormP h (idGram K n))) (hβ3 : β ^ 3 = 1) : Inputs295c.OuterExcl295 β := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hℓ2, hf1⟩ := eq_two_of_pow_eq_two h.prime hq
  have hℓ3 : ℓ ≠ 3 := by omega
  have hK4 : Nat.card K = 4 := by rw [h.card, hℓ2, hf1]; norm_num
  have hn3 : 3 ≤ n := by omega
  have hne : ¬ (n = 3 ∧ ℓ ^ f = 2) := by omega
  set σ := primeFormFieldFactor h isPrimeFormGram_one hn3 hne β with hσdef
  have hσ3 : σ ^ 3 = 1 := by rw [hσdef, ← map_pow, hβ3, map_one]
  have hσ2 : σ ^ 2 = 1 := by
    have hcardA : Nat.card (RingAut K) = 2 := by
      rw [(CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic h.prime K h.card).1, hf1]
    have := pow_card_eq_one' (x := (σ : RingAut K))
    rwa [hcardA] at this
  have hσ1 : σ = 1 := by
    calc σ = σ ^ 3 * (σ ^ 2)⁻¹ := by group
      _ = 1 := by rw [hσ3, hσ2]; group
  have hD : β ∈ primeFormD h (idGram K n) := by
    rw [← ker_primeFormFieldFactor h isPrimeFormGram_one hn3 hne]
    exact hσ1
  obtain ⟨A, rfl⟩ := hD
  have hA3 : primeFormConjHom h (idGram K n) (A ^ 3) = 1 := by rw [map_pow]; exact hβ3
  obtain ⟨c, -, hc⟩ := (primeFormConjHom_eq_one_iff_of_ne hn3 hne (A ^ 3)).1 hA3
  have hyp : (A : GL (Fin n) K) ^ 3 = GeneralLinearGroup.scalar (Fin n) c := by
    rw [← Subgroup.coe_pow]; exact hc
  by_cases hc1 : c = 1
  · exact Or.inr (Or.inl (le_trans (by norm_num) (four_le_pRank_fixSubgroup_primeFormConjHom
      (by rw [hq]) hn A (by rw [hyp, hc1, map_one]))))
  · exact Or.inr (Or.inr (not_isPSolvable_fixSubgroup_primeFormConjHom hℓ3 A hyp
      (Or.inr (Or.inr ⟨by omega, no_cube_root_of_card_four hK4 hc1⟩))))

theorem at_typeTwistedA_two {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid) (hq2 : q.card = 2) (hr : 4 ≤ r) :
    Inputs295c.Outer295At ⟨.twistedA r q, hv⟩ ∧ Inputs295c.Inner295At ⟨.twistedA r q, hv⟩ := by
  have hqc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  refine ⟨fun K _ _ _ _ ⟨e⟩ _ _ _ α hα _ => ?_, fun K _ _ _ _ ⟨e⟩ _ _ _ x hx => ?_⟩
  · obtain ⟨-, -, -, -, F, _, h, ⟨θ⟩⟩ :=
      CFSG.RankThree.PartOne.exists_primeFormP_of_statedClassicalModel_PSU
        (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e)
    haveI := h.finite
    have hβ := outerExcl295_primeFormP_two h (by rw [← hqc]; exact hq2) (by omega)
      (MulAut.congr θ α) (congr_pow_three_eq_one θ hα)
    rcases hβ with ⟨P, hP, hPp, hPc⟩ | hβ | hβ
    · refine Or.inl ⟨P.comap θ.toMonoidHom, ?_, ?_, ?_⟩
      · intro g hg
        have : θ g ∈ fixSubgroup (MulAut.congr θ α) := hP hg
        rw [Inputs295c.fixSubgroup_congr] at this
        obtain ⟨g', hg', hgg⟩ := this
        rw [θ.injective hgg] at hg'
        exact hg'
      · exact hPp.comap_of_injective θ.toMonoidHom θ.injective
      · have hmap : (P.comap θ.toMonoidHom).map θ.toMonoidHom = P :=
          Subgroup.map_comap_eq_self_of_surjective θ.surjective P
        rw [← hmap] at hPc
        rwa [Nat.card_congr ((P.comap θ.toMonoidHom).equivMapOfInjective θ.toMonoidHom
          θ.injective).toEquiv]
    · rw [Inputs295c.fixSubgroup_congr, pRank_map_mulEquiv] at hβ
      exact Or.inr (Or.inl hβ)
    · rw [Inputs295c.fixSubgroup_congr] at hβ
      refine Or.inr (Or.inr fun hs => hβ ?_)
      exact isPSolvable_of_mulEquiv ((fixSubgroup α).equivMapOfInjective _ θ.injective) hs
  · obtain ⟨-, -, -, -, F, _, h, ⟨θ⟩⟩ :=
      CFSG.RankThree.PartOne.exists_primeFormP_of_statedClassicalModel_PSU
        (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e)
    haveI := h.finite
    have hθx : orderOf (θ x) = 3 := by rw [MulEquiv.orderOf_eq]; exact hx
    exact Inputs295.Excl295At.of_equiv θ
      (excl295At_primeFormP_two (by rw [← hqc]; exact hq2) (by omega) hθx)

theorem inner295At_typeTwistedA_four {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid) (hp3 : q.p ≠ 3)
    (hq : (4 ≤ q.card ∧ 3 ≤ r) ∨ (q.card = 2 ∧ 9 ≤ r)) :
    Inputs295c.Inner295At ⟨.twistedA r q, hv⟩ := by
  intro K _ _ _ _ ⟨e⟩ _ _ _ x hx
  obtain ⟨-, -, -, -, F, _, h, ⟨θ⟩⟩ :=
    CFSG.RankThree.PartOne.exists_primeFormP_of_statedClassicalModel_PSU
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e)
  haveI := h.finite
  have hqc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  have hθx : (θ x) ^ 3 = 1 := by rw [← map_pow, ← hx, pow_orderOf_eq_one, map_one]
  exact Or.inr (Or.inr fun hs => not_isPSolvable_centralizer_primeFormP hp3
    (by rw [← hqc]; omega) hθx (isPSolvable_centralizer_of_mulEquiv θ x hs))

open CFSG.RankThree.Classical in
theorem not_isPSolvable_fixSubgroup_primeFormP_of_dvd {ℓ f n : ℕ} {K : Type} [Field K]
    [Finite K] (h : UnitaryFieldData ℓ f K) (hℓ3 : ℓ ≠ 3)
    (hq : (4 ≤ ℓ ^ f ∧ 4 ≤ n) ∨ (ℓ ^ f = 2 ∧ 10 ≤ n)) (h3q : 3 ∣ ℓ ^ f + 1)
    (β : MulAut (primeFormP h (idGram K n))) (hβ3 : β ^ 3 = 1) :
    ¬ CFSG.HallHigman.IsPSolvable 3 ↥(fixSubgroup β) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn4 : 4 ≤ n := by omega
  have hn3 : 3 ≤ n := by omega
  have hne : ¬ (n = 3 ∧ ℓ ^ f = 2) := by omega
  set σ := primeFormFieldFactor h isPrimeFormGram_one hn3 hne β with hσdef
  have hσ3 : σ ^ 3 = 1 := by rw [hσdef, ← map_pow, hβ3, map_one]
  by_cases hσ1 : σ = 1
  ·
    have hD : β ∈ primeFormD h (idGram K n) := by
      rw [← ker_primeFormFieldFactor h isPrimeFormGram_one hn3 hne]
      exact hσ1
    obtain ⟨A, rfl⟩ := hD
    have hA3 : primeFormConjHom h (idGram K n) (A ^ 3) = 1 := by rw [map_pow]; exact hβ3
    obtain ⟨c, -, hc⟩ := (primeFormConjHom_eq_one_iff_of_ne hn3 hne (A ^ 3)).1 hA3
    exact not_isPSolvable_fixSubgroup_primeFormConjHom hℓ3 A (c := c)
      (by rw [← Subgroup.coe_pow]; exact hc) (hq.imp_right Or.inl)
  ·
    have hσord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
    have hβ1 : β ≠ 1 := fun h1 => hσ1 (by rw [hσdef, h1, map_one])
    have hβord : orderOf β = 3 := orderOf_eq_prime hβ3 hβ1
    obtain ⟨hpf, -, -, -, -, M, hM⟩ :=
      CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent h hn3 hne
        Nat.prime_three (by norm_num) (Ne.symm hℓ3) β hβord σ rfl hσord
    have hβeq : β = primeFormConjHom h _ M * primeFormFieldHom h isPrimeFormGram_one σ *
        (primeFormConjHom h _ M)⁻¹ := by
      rw [← hM]
      group
    rw [hβeq, Inputs295c.fixSubgroup_conj]
    set h₀ := fixSubfield_unitaryFieldData h Nat.prime_three (by norm_num) hσord with hh₀
    have hbar := fixSubfield_unitaryFieldData_bar h Nat.prime_three (by norm_num) hσord
    haveI := h₀.finite
    have hinj := subfieldPSU_injective h h₀ hbar n (by omega)
    have hJle : (subfieldPSU h h₀ hbar n).range ≤
        fixSubgroup (primeFormFieldHom h isPrimeFormGram_one σ) := by
      intro y hy
      exact range_subfieldPSU_le h n h₀ hbar hy
    have hmod : StatedClassicalModel (primeFormP h₀ ((1 : GL (Fin n)
        (CFSG.LieType.Chevalley.fixSubfield σ)) : Matrix (Fin n) (Fin n)
          (CFSG.LieType.Chevalley.fixSubfield σ))) .PSU n ℓ (f / 3) := by
      refine ⟨⟨h.prime, h₀.one_le, hn3, fun he => by simp only [Prod.mk.injEq] at he; omega⟩,
        CFSG.LieType.Chevalley.fixSubfield σ, inferInstance, inferInstance, ?_,
        ⟨(CFSG.LocalAnalysis.unitaryPSUEquivPrimeFormOne h₀ n).symm.trans
          (unitaryPSUEquiv h₀ (by omega))⟩⟩
      rw [h₀.card, ← pow_mul, mul_comm]
    obtain ⟨-, k, _, _, hk, ⟨ek⟩⟩ := hmod
    have hq0 : ℓ ^ f = (ℓ ^ (f / 3)) ^ 3 := by
      rw [← pow_mul, Nat.div_mul_cancel hpf]
    have hmod3 : (ℓ ^ (f / 3) + 1) % 3 = (ℓ ^ f + 1) % 3 := by
      have := mod_three_cube (ℓ ^ (f / 3))
      rw [hq0]
      omega
    have hQ3 : ¬ 3 ∣ ℓ ^ (f / 3) := fun hd => hℓ3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three
      h.prime).1 (Nat.prime_three.dvd_of_dvd_pow hd)).symm
    have hrk := three_le_pRank_top_projSU (n := n) hk hQ3 (by omega)
    have h3P : 3 ∣ Nat.card (primeFormP h₀ ((1 : GL (Fin n)
        (CFSG.LieType.Chevalley.fixSubfield σ)) : Matrix (Fin n) (Fin n)
          (CFSG.LieType.Chevalley.fixSubfield σ))) := by
      rw [Nat.card_congr ek.toEquiv]
      exact three_dvd_natCard_of_one_le_pRank (by omega)
    have hq₀ : ¬ (n = 3 ∧ ℓ ^ (f / 3) = 2) := by omega
    let eJ := MonoidHom.ofInjective hinj
    have hJs : IsSimpleGroup ↥(subfieldPSU h h₀ hbar n).range := by
      haveI := isSimpleGroup_primeFormP_one h₀ hn3 hq₀
      exact eJ.symm.isSimpleGroup
    have hJnc : ¬ IsMulCommutative ↥(subfieldPSU h h₀ hbar n).range := by
      rintro ⟨hc⟩
      apply not_commute_primeFormP_one h₀ hn3 hq₀
      intro a b
      apply eJ.injective
      rw [map_mul, map_mul]
      exact hc.comm _ _
    have hJ3 : 3 ∣ Nat.card ↥(subfieldPSU h h₀ hbar n).range := by
      rwa [← Nat.card_congr eJ.toEquiv]
    intro hs
    have hs' := isPSolvable_of_mulEquiv ((fixSubgroup (primeFormFieldHom h isPrimeFormGram_one
      σ)).equivMapOfInjective _ (primeFormConjHom h _ M).injective).symm hs
    exact CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.not_isPSolvable_three_of_simple hJs
      hJnc hJ3 (isPSolvable_of_le hs' hJle)

theorem outer295At_typeTwistedA_dvd {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid) (hp3 : q.p ≠ 3) (h3q : 3 ∣ q.card + 1)
    (hq : (4 ≤ q.card ∧ 3 ≤ r) ∨ (q.card = 2 ∧ 9 ≤ r)) :
    Inputs295c.Outer295At ⟨.twistedA r q, hv⟩ := by
  intro K _ _ _ _ ⟨e⟩ _ _ _ α hα _
  obtain ⟨-, -, -, -, F, _, h, ⟨θ⟩⟩ :=
    CFSG.RankThree.PartOne.exists_primeFormP_of_statedClassicalModel_PSU
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e)
  haveI := h.finite
  have hqc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  have hns := not_isPSolvable_fixSubgroup_primeFormP_of_dvd h hp3 (by rw [← hqc]; omega)
    (by rwa [← hqc]) (MulAut.congr θ α) (congr_pow_three_eq_one θ hα)
  rw [Inputs295c.fixSubgroup_congr] at hns
  refine Or.inr (Or.inr fun hs => hns ?_)
  exact isPSolvable_of_mulEquiv ((fixSubgroup α).equivMapOfInjective _ θ.injective) hs

end Unitary

section Orthogonal

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.LocalAnalysis.ComponentInitial CFSG.AGLEmbedding.ToralCensus
  CFSG.HardMathSupport.Malle.E27Lie

theorem qs_range_of_injective {J G : Type*} [Group J] [Group G] (hJ : CFSG.IsQuasisimple J)
    (h3 : 3 ∣ Nat.card J) (φ : J →* G) (hφ : Function.Injective φ) :
    CFSG.IsQuasisimple ↥φ.range ∧ 3 ∣ Nat.card φ.range := by
  let e := MonoidHom.ofInjective hφ
  exact ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e hJ, by rwa [← Nat.card_congr e.toEquiv]⟩

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}

theorem exists_qs_of_fixed_sl2 (hx : OddOrderIsometry Q 3 x) (hK : 4 ≤ Nat.card K)
    (ψ : Matrix.SpecialLinearGroup (Fin 2) K →* (fixedSpace x ≃ₗ[K] fixedSpace x))
    (hψ : Function.Injective ψ)
    (hψO : ∀ A, ψ A ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)) :
    ∃ J : Subgroup (V ≃ₗ[K] V), J ≤ isometryCentralizer Q x ∧ CFSG.IsQuasisimple ↥J ∧
      3 ∣ Nat.card J := by
  let ι₁ : Matrix.SpecialLinearGroup (Fin 2) K →*
      ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)) :=
    ψ.codRestrict _ hψO
  have hι₁ : Function.Injective ι₁ := fun A B hAB => hψ (congrArg Subtype.val hAB)
  let φ := ((supportedBlock Q x (X - 1)).subtype.comp (fixedBlockEquiv hx).symm.toMonoidHom).comp ι₁
  have hφ : Function.Injective φ :=
    ((Subgroup.subtype_injective _).comp (fixedBlockEquiv hx).symm.injective).comp hι₁
  obtain ⟨hq, h3⟩ := qs_range_of_injective
    (CFSG.SeitzReduction.LinearPilot.isQuasisimple_specialLinearGroup_of_le le_rfl (Or.inr hK))
    (Inputs295c.three_dvd_card_sl (F := K) (m := 2) le_rfl) φ hφ
  refine ⟨φ.range, ?_, hq, h3⟩
  rintro _ ⟨A, rfl⟩
  exact (supportedBlock_le_isometryCentralizer _) ((fixedBlockEquiv hx).symm (ι₁ A)).2

theorem exists_qs_of_factor (hx : OddOrderIsometry Q 3 x) (hK : 4 ≤ Nat.card K) {h : K[X]}
    [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap) (hX : h ≠ X - 1)
    (hdeg : h.natDegree ≤ 2) (hm : 2 ≤ primaryMultiplicity x.toLinearMap h) :
    ∃ J : Subgroup (V ≃ₗ[K] V), J ≤ isometryCentralizer Q x ∧ CFSG.IsQuasisimple ↥J ∧
      3 ∣ Nat.card J := by
  classical
  by_cases hself : h = reciprocalPolynomial h
  ·
    obtain ⟨ℓ, f, d, hU, B, hd, hqK, hBs, hBl, hbar, ⟨φs⟩⟩ :=
      exists_selfDual_unitary hx hh hX hself
    have hpos := (irreducible_of_mem_primaryFactors hh).natDegree_pos
    have hd1 : d = 1 := by omega
    subst hd1
    have : Finite (AdjoinRoot h) := hU.finite
    obtain ⟨e, he⟩ := hU.exists_orthonormal_basis hBs hBl
    have hm' : 2 ≤ Module.finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h) := hm
    have hq4 : 4 ≤ ℓ ^ (f * 1) := by rw [mul_one, ← hqK]; exact hK
    have hSU := CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_sesqSpecialUnitaryGroup_of_two_le
      hU hBs hBl hm' ⟨fun _ => hq4, fun _ => by omega⟩
    obtain ⟨ν, hνμ, hν3, hν1⟩ := exists_unit_of_orderOf_eq_three (orderOf_root_eq_three hx hh hX)
    have hbar' : hU.bar (ν : AdjoinRoot h) = (ν : AdjoinRoot h)⁻¹ := by rw [hνμ]; exact hbar
    have h01 : (⟨0, by omega⟩ : Fin (Module.finrank (AdjoinRoot h)
        (primaryComponent x.toLinearMap h))) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
    set ψ := (Matrix.GeneralLinearGroup.toLin' e).toMonoidHom with hψ
    have hψi : Function.Injective ψ := (Matrix.GeneralLinearGroup.toLin' e).injective
    have hu := toLin'_diagGL_mem e he ⟨0, by omega⟩ ⟨1, by omega⟩ hbar'
    let u : ↥(sesqSpecialUnitaryGroup B) := ⟨_, hu⟩
    have hu3 : u ^ 3 = 1 := by
      apply Subtype.ext
      change (ψ (diagGL _ _ (twoDiag ⟨0, by omega⟩ ⟨1, by omega⟩ ν))) ^ 3 = 1
      rw [← map_pow, ← map_pow, twoDiag_pow_three hν3, map_one, map_one]
    have hu1 : u ≠ 1 := by
      intro h1
      have h1' : ψ (diagGL _ _ (twoDiag ⟨0, by omega⟩ ⟨1, by omega⟩ ν)) = 1 :=
        congrArg Subtype.val h1
      exact twoDiag_ne_one h01 hν1 (diagGL_injective (hψi (h1'.trans (map_one ψ).symm)))
    have h3SU : 3 ∣ Nat.card ↥(sesqSpecialUnitaryGroup B) := by
      rw [← orderOf_eq_prime hu3 hu1]
      exact orderOf_dvd_natCard u
    let φ := ((supportedBlock Q x h).subtype.comp φs.symm.toMonoidHom).comp
      (Subgroup.inclusion (sesqSpecialUnitaryGroup_le B))
    have hφ : Function.Injective φ :=
      ((Subgroup.subtype_injective _).comp φs.symm.injective).comp
        (Subgroup.inclusion_injective _)
    obtain ⟨hq, h3⟩ := qs_range_of_injective hSU h3SU φ hφ
    refine ⟨φ.range, ?_, hq, h3⟩
    rintro _ ⟨A, rfl⟩
    exact (supportedBlock_le_isometryCentralizer _) (φs.symm _).2
  ·
    have := finite_adjoinRoot (K := K) (h := h)
    set b : Module.Basis (Fin (primaryMultiplicity x.toLinearMap h)) (AdjoinRoot h)
      (primaryComponent x.toLinearMap h) := Module.finBasisOfFinrankEq _ _ rfl
    set φp := pairedBlockEquiv hx hh hself
    let φ := (((supportedBlock Q x h).subtype.comp φp.symm.toMonoidHom).comp
      (Matrix.GeneralLinearGroup.toLin' b).toMonoidHom).comp
        (Matrix.SpecialLinearGroup.toGL (n := Fin (primaryMultiplicity x.toLinearMap h))
          (R := AdjoinRoot h))
    have hφ : Function.Injective φ :=
      (((Subgroup.subtype_injective _).comp φp.symm.injective).comp
        (Matrix.GeneralLinearGroup.toLin' b).injective).comp
          Matrix.SpecialLinearGroup.toGL_injective
    obtain ⟨hq, h3⟩ := qs_range_of_injective
      (CFSG.SeitzReduction.LinearPilot.isQuasisimple_specialLinearGroup_of_le hm
        (Or.inr (four_le_card_adjoinRoot hK)))
      (Inputs295c.three_dvd_card_sl hm) φ hφ
    refine ⟨φ.range, ?_, hq, h3⟩
    rintro _ ⟨A, rfl⟩
    exact (supportedBlock_le_isometryCentralizer _) (φp.symm _).2

theorem exists_qs_isometryCentralizer (hx : OddOrderIsometry Q 3 x) (hx1 : x ≠ 1)
    (hdim : ((2 : K) ≠ 0 ∧ 7 ≤ finrank K V) ∨ ((2 : K) = 0 ∧ 8 ≤ finrank K V))
    (hK : 4 ≤ Nat.card K) :
    ∃ J : Subgroup (V ≃ₗ[K] V), J ≤ isometryCentralizer Q x ∧ CFSG.IsQuasisimple ↥J ∧
      3 ∣ Nat.card J := by
  classical
  by_cases hfx : ((2 : K) ≠ 0 ∧ 5 ≤ finrank K (fixedSpace x)) ∨
      ((2 : K) = 0 ∧ 6 ≤ finrank K (fixedSpace x))
  · rcases hfx with ⟨h2, h5⟩ | ⟨h2, h6⟩
    · obtain ⟨P, hP⟩ := exists_two_hypPairs_odd h2 hx.polarBilin_fixed_nondegenerate h5
      exact exists_qs_of_fixed_sl2 hx hK (pairLmulOdd hP) (pairLmulOdd_injective hP)
        fun A => pairLmulOdd_range_le hP ⟨A, rfl⟩
    · have : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
      obtain ⟨P, hP⟩ := exists_two_hypPairs hx.polarBilin_fixed_nondegenerate h6
      exact exists_qs_of_fixed_sl2 hx hK (pairLmul hP) (pairLmul_injective hP)
        fun A => pairLmul_range_le hP ⟨A, rfl⟩
  · obtain ⟨h, hh, hX, hrecX, hdeg, hdeg1, hsum⟩ :=
      exists_orth_factor hx (finrank_fixedSpace_lt hx1)
    have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
    have hm : 2 ≤ primaryMultiplicity x.toLinearMap h := by
      rcases hdim with ⟨h2, h7⟩ | ⟨h2, h8⟩
      · have : ¬ 5 ≤ finrank K (fixedSpace x) := fun h5 => hfx (Or.inl ⟨h2, h5⟩)
        omega
      · have : ¬ 6 ≤ finrank K (fixedSpace x) := fun h6 => hfx (Or.inr ⟨h2, h6⟩)
        omega
    exact exists_qs_of_factor hx hK hh hX hdeg hm

end Orthogonal

section Omega

open CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.AGLEmbedding.ToralCensus QuadraticMap CFSG.HardMathSupport.Malle.E27Lie

theorem not_isPSolvable_centralizer_pomega {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] [Finite K] {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K} (hQ0 : ⇑Q = Q₀)
    (hQ : (polarBilin Q).Nondegenerate) (h3 : ((3 : ℕ) : K) ≠ 0)
    (hn : ((2 : K) ≠ 0 ∧ 7 ≤ Fintype.card ι) ∨ ((2 : K) = 0 ∧ 8 ≤ Fintype.card ι))
    (hK : 4 ≤ Nat.card K) {a : StatedProj (StatedOmega Q₀)} (ha : orderOf a = 3) :
    ¬ CFSG.HallHigman.IsPSolvable 3
      ↥(Subgroup.centralizer ({a} : Set (StatedProj (StatedOmega Q₀)))) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hΩ := statedOmega_eq_comap hQ0
  have hne : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  have hdim : ((2 : K) ≠ 0 ∧ 7 ≤ Module.finrank K (ι → K)) ∨
      ((2 : K) = 0 ∧ 8 ≤ Module.finrank K (ι → K)) := by
    rw [Module.finrank_fintype_fun_eq_card]; exact hn
  let π : StatedOmega Q₀ →* StatedProj (StatedOmega Q₀) := QuotientGroup.mk' _
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
  have ha' : orderOf (π g) = 3 := ha
  have hker : π.ker ≤ Subgroup.center (StatedOmega Q₀) := by
    rw [QuotientGroup.ker_mk']
    exact scalars_subgroupOf_le_center _
  have hO : ∀ u : StatedOmega Q₀, toLinEquiv ι K (u : GL ι K) ∈
      TauCeti.QuadraticMap.orthogonalGroup Q := fun u => by
    have h : (u : GL ι K) ∈ (⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆).comap (toLinEquiv ι K).toMonoidHom := by
      rw [← hΩ]; exact u.2
    exact Subgroup.commutator_le_self _ (Subgroup.mem_comap.mp h)
  have hg3 : (g ^ 3 : StatedOmega Q₀) ∈ π.ker := by
    have h1 : π g ^ 3 = 1 := by
      have := pow_orderOf_eq_one (π g)
      rwa [ha'] at this
    rw [MonoidHom.mem_ker, map_pow]
    exact h1
  rw [QuotientGroup.ker_mk', Subgroup.mem_subgroupOf] at hg3
  obtain ⟨c, hc⟩ := hg3
  have hsq : (c : K) * c = 1 := by
    obtain ⟨v, hv⟩ := exists_quadratic_ne_zero (K := K) (Q := Q) hQ
    have hcv := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (hO (g ^ 3)) v
    rw [toLinEquiv_apply, ← hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at hcv
    have hsmul : Matrix.mulVec (Matrix.diagonal fun _ => (c : K)) v = (c : K) • v := by
      funext i
      simp [Matrix.mulVec_diagonal]
    rw [hsmul, QuadraticMap.map_smul, smul_eq_mul] at hcv
    have h1 : ((c : K) * c - 1) * Q v = 0 := by rw [sub_mul, hcv, one_mul, sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right hv)
  have hcc : c * c = 1 := Units.ext hsq
  have hg6 : (g : GL ι K) ^ 6 = 1 := by
    have h3' : (g : GL ι K) ^ 3 = Matrix.GeneralLinearGroup.scalar ι c := by
      rw [hc]; rfl
    have h6 : (g : GL ι K) ^ 6 = ((g : GL ι K) ^ 3) ^ 2 := by rw [← pow_mul]
    rw [h6, h3', ← map_pow, _root_.sq, hcc, map_one]
  set w : StatedOmega Q₀ := g ^ 4 with hw
  have hw3 : w ^ 3 = 1 := by
    apply Subtype.ext
    show ((g : GL ι K) ^ 4) ^ 3 = 1
    have h12 : ((g : GL ι K) ^ 4) ^ 3 = ((g : GL ι K) ^ 6) ^ 2 := by rw [← pow_mul, ← pow_mul]
    rw [h12, hg6, one_pow]
  have hπ3 : π g ^ 3 = 1 := by
    have := pow_orderOf_eq_one (π g)
    rwa [ha'] at this
  have hπw : π w = π g := by
    rw [hw, map_pow, show (4 : ℕ) = 3 + 1 from rfl, pow_succ, hπ3, one_mul]
  have hw1 : w ≠ 1 := by
    intro h
    rw [h, map_one] at hπw
    have h1 : π g = 1 := hπw.symm
    rw [h1, orderOf_one] at ha'
    omega
  have hx : OddOrderIsometry Q 3 (toLinEquiv ι K (w : GL ι K)) := by
    refine ⟨hO w, ?_, h3, fun v hv => hQ.1 v fun w' => ?_⟩
    · rw [← map_pow]
      have : (w : GL ι K) ^ 3 = 1 := congrArg Subtype.val hw3
      rw [this, map_one]
    · simpa [polarBilin_apply_apply] using hv w'
  have hx1 : toLinEquiv ι K (w : GL ι K) ≠ 1 := fun h =>
    hw1 (Subtype.ext ((toLinEquiv ι K).injective (h.trans (map_one _).symm)))
  obtain ⟨V, hVC, hVq, hV3⟩ := exists_qs_isometryCentralizer hx hx1 hdim hK
  have hVp : ⁅V, V⁆ = V := CFSG.RankThree.PartOne.KCUnitary.commutator_eq_of_isPerfect hVq.1
  have hVO : V ≤ TauCeti.QuadraticMap.orthogonalGroup Q := hVC.trans inf_le_left
  have hVD : V ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ :=
    calc V = ⁅V, V⁆ := hVp.symm
      _ ≤ _ := Subgroup.commutator_mono hVO hVO
  set e := toLinEquiv ι K with he
  set V' : Subgroup (GL ι K) := V.comap e.toMonoidHom with hV'
  have hV'G : V' ≤ StatedOmega Q₀ := by
    rw [hΩ]
    exact Subgroup.comap_mono hVD
  have hmapV' : V' = V.map e.symm.toMonoidHom := Subgroup.comap_equiv_eq_map_symm e V
  set B : Subgroup (StatedOmega Q₀) := V'.subgroupOf (StatedOmega Q₀) with hB
  have eV : ↥V ≃* ↥V' := (V.equivMapOfInjective _ e.symm.injective).trans
    (MulEquiv.subgroupCongr hmapV'.symm)
  have eB : ↥B ≃* ↥V := (Subgroup.subgroupOfEquivOfLe hV'G).trans eV.symm
  have hBq : CFSG.IsQuasisimple ↥B := CFSG.LocalCores.isQuasisimple_of_mulEquiv eB.symm hVq
  have h3B : 3 ∣ Nat.card B := by rw [Nat.card_congr eB.toEquiv]; exact hV3
  have hBc : ∀ b ∈ B, b * w = w * b := by
    intro b hb
    have hb' : e (b : GL ι K) ∈ V := Subgroup.mem_comap.mp (Subgroup.mem_subgroupOf.mp hb)
    have hcomm := (mem_isometryCentralizer.mp (hVC hb')).2
    apply Subtype.ext
    apply e.injective
    rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact LinearEquiv.ext fun v => hcomm v
  have hπ : ∃ b : B, (π.comp B.subtype) b ≠ 1 := by
    by_contra hall
    push Not at hall
    obtain ⟨u, v, huv⟩ := Inputs295c.exists_noncomm_of_isQuasisimple hBq
    have hu : (u : StatedOmega Q₀) ∈ Subgroup.center _ := hker (hall u)
    exact huv (Subtype.ext (Subgroup.mem_center_iff.1 hu (v : StatedOmega Q₀)).symm)
  have hns := Inputs295c.not_isPSolvable_range_of_quasisimple hBq h3B (π.comp B.subtype) hπ
  have hle : (π.comp B.subtype).range ≤
      Subgroup.centralizer ({π g} : Set (StatedProj (StatedOmega Q₀))) := by
    rintro _ ⟨b, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    change π b * π g = π g * π b
    rw [← hπw, ← map_mul, ← map_mul, hBc b b.2]
  intro hs
  exact hns (isPSolvable_of_le hs hle)

theorem inner295At_of_statedOmega_four {d : TauCeti.ValidLieTypeIndex}
    (h : ∀ (K : Type) [Group K], (K ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (F : Type) (_ : Field F) (_ : Finite F)
        (Q : QuadraticForm F (ι → F)) (Q₀ : (ι → F) → F), ((3 : ℕ) : F) ≠ 0 ∧
        (((2 : F) ≠ 0 ∧ 7 ≤ Fintype.card ι) ∨ ((2 : F) = 0 ∧ 8 ≤ Fintype.card ι)) ∧
        4 ≤ Nat.card F ∧ ⇑Q = Q₀ ∧ (polarBilin Q).Nondegenerate ∧
        Nonempty (K ≃* StatedProj (StatedOmega Q₀))) :
    Inputs295c.Inner295At d := by
  intro K _ _ _ _ ⟨e⟩ _ _ _ x hx
  obtain ⟨ι, _, _, F, _, _, Q, Q₀, h3, hdim, hK, hQ0, hnd, ⟨f⟩⟩ := h K e
  have hfx : orderOf (f x) = 3 := by rw [MulEquiv.orderOf_eq]; exact hx
  exact Or.inr (Or.inr fun hs => not_isPSolvable_centralizer_pomega hQ0 hnd h3 hdim hK hfx
    (isPSolvable_centralizer_of_mulEquiv f x hs))

theorem odd_field_facts' {F : Type} [Field F] [Finite F] {q : TauCeti.PrimePower}
    (hF : Nat.card F = q.p ^ q.exponent) (hp2 : q.p ≠ 2) (hp3 : q.p ≠ 3) :
    (2 : F) ≠ 0 ∧ ((3 : ℕ) : F) ≠ 0 ∧ 4 ≤ Nat.card F := by
  refine ⟨fun h => ?_, ?_, ?_⟩
  · have hc := CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq q.prime_p q.exponent_pos hF
    have hq : (ringChar F).Prime := hc ▸ q.prime_p
    exact hp2 (hc ▸ (CFSG.ClassicalGroups.Orthogonal.two_eq_zero_iff_ringChar_eq_two hq).1 h)
  · have := Inputs295c.three_ne_zero_of_card q.prime_p hp3 hF
    exact_mod_cast this
  · rw [hF]
    have h5 : 5 ≤ q.p := by
      have := q.prime_p.two_le
      have h4 : q.p ≠ 4 := fun h4 => by
        have := q.prime_p
        rw [h4] at this
        norm_num at this
      omega
    exact h5.trans' (by norm_num) |>.trans (Nat.le_self_pow q.exponent_pos.ne' _)

theorem inner295At_typeB_odd_three {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.B 3 q).Valid) (hp2 : q.p ≠ 2) (hp3 : q.p ≠ 3) :
    Inputs295c.Inner295At ⟨.B 3 q, hv⟩ := by
  refine inner295At_of_statedOmega_four fun K _ e => ?_
  obtain ⟨-, F, _, _, hF, hf⟩ :=
    CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd 3 q hv hp2 le_rfl e
  obtain ⟨h2, h3, hK⟩ := odd_field_facts' hF hp2 hp3
  obtain ⟨hnd, -⟩ := regular_quadOdd (K := F) (n := 3) h2 le_rfl
  exact ⟨Fin 3 ⊕ Fin 3 ⊕ Unit, inferInstance, inferInstance, F, inferInstance, inferInstance,
    CFSG.LieType.Universal.Spin.quadOdd 3 F, StatedQuadOdd 3 F, h3, Or.inl ⟨h2, by simp⟩, hK,
    CFSG.LieType.Universal.Spin.coe_quadOdd 3 F, hnd, hf⟩

theorem inner295At_typeTwistedD_four {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedD 4 q).Valid) (hp3 : q.p ≠ 3) (hq2 : q.card ≠ 2) :
    Inputs295c.Inner295At ⟨.twistedD 4 q, hv⟩ := by
  refine inner295At_of_statedOmega_four fun K _ e => ?_
  obtain ⟨-, F, _, _, hF, b, c, hirr, hf⟩ :=
    CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD 4 q hv e
  have hq4 : 4 ≤ Nat.card F := by
    rw [hF, ← TauCeti.PrimePower.card_def]
    exact Inputs295c.four_le_card_of hp3 hq2
  have h3 : ((3 : ℕ) : F) ≠ 0 := by
    have := Inputs295c.three_ne_zero_of_card q.prime_p hp3 hF
    exact_mod_cast this
  obtain ⟨hnd, -⟩ := regular_quadMinus (K := F) (n := 4) (b := b) (c := c) le_rfl hirr
  refine ⟨Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2, inferInstance, inferInstance, F, inferInstance,
    inferInstance, CFSG.LieType.Universal.Spin.quadMinus 4 F b c, StatedQuadMinus 4 F b c, h3,
    ?_, hq4, CFSG.LieType.Universal.Spin.coe_quadMinus 4 F b c, hnd, hf⟩
  by_cases h2 : (2 : F) = 0
  · exact Or.inr ⟨h2, by simp⟩
  · exact Or.inl ⟨h2, by simp⟩

end Omega

end BlocksQS

@[expose] def Input29_5'LieRest3 : Prop :=
  (∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.D 4 q).Valid), q.p ≠ 3 → q.card ≠ 2 →
    Inputs295c.Outer295At ⟨.D 4 q, hv⟩) ∧
  (∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid), q.card = 2 →
    Inputs295c.Outer295At ⟨.twistedE6 q, hv⟩) ∧
  (∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedA 3 q).Valid), q.card = 2 →
    Inputs295c.Inner295At ⟨.twistedA 3 q, hv⟩) ∧
  (∀ q : TauCeti.PrimePower, q.card = 2 →
    (∀ hv : (TauCeti.LieTypeIndex.F4 q).Valid, Inputs295c.Inner295At ⟨.F4 q, hv⟩) ∧
    (∀ hv : (TauCeti.LieTypeIndex.E6 q).Valid, Inputs295c.Inner295At ⟨.E6 q, hv⟩) ∧
    (∀ hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid, Inputs295c.Inner295At ⟨.twistedE6 q, hv⟩) ∧
    (∀ hv : (TauCeti.LieTypeIndex.E7 q).Valid, Inputs295c.Inner295At ⟨.E7 q, hv⟩) ∧
    (∀ hv : (TauCeti.LieTypeIndex.E8 q).Valid, Inputs295c.Inner295At ⟨.E8 q, hv⟩))

section Reduction

open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott (IsRankThreeIndex)

theorem p_eq_two_of_card_two {q : TauCeti.PrimePower} (h : q.card = 2) :
    q.p = 2 ∧ q.exponent = 1 := by
  have hp := q.prime_p
  have he := q.exponent_pos
  rw [TauCeti.PrimePower.card_def] at h
  have hdvd : q.p ∣ 2 := by
    rw [← h]
    exact dvd_pow_self q.p he.ne'
  have hp2 : q.p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hdvd
  refine ⟨hp2, ?_⟩
  rw [hp2] at h
  have h' : 2 ^ q.exponent = 2 ^ 1 := by rw [h, pow_one]
  exact Nat.pow_right_injective le_rfl h'

theorem three_le_of_big_B {r : ℕ} {q : TauCeti.PrimePower}
    (hb : Inputs295c.IsBig295Index (.B r q)) : 3 ≤ r := by
  rcases hb with h | h | h
  · change r = 3 at h
    omega
  · change 4 ≤ r at h
    omega
  · exact h.elim

theorem inner295At_twistedA_of_not_open {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid)
    (hch : (TauCeti.LieTypeIndex.twistedA r q).characteristic ≠ 3)
    (hb : Inputs295c.IsBig295Index (.twistedA r q))
    (hop : ¬ (q.card = 2 ∧ r = 3)) : Inputs295c.Inner295At ⟨.twistedA r q, hv⟩ := by
  have hp3 : q.p ≠ 3 := by simpa using hch
  have hr : 3 ≤ r := by
    rcases hb with h | h | h
    · change (r = 3 ∧ q.card % 3 = 2) ∨ ((r = 5 ∨ r = 6) ∧ q.card % 3 = 1) at h
      omega
    · change (4 ≤ r ∧ q.card % 3 = 2) ∨ (7 ≤ r ∧ q.card % 3 = 1) at h
      omega
    · exact h.elim
  by_cases hq2 : q.card = 2
  · exact (at_typeTwistedA_two hv hq2 (by omega)).2
  · exact inner295At_typeTwistedA_four hv hp3 (Or.inl ⟨Inputs295c.four_le_card_of hp3 hq2, hr⟩)

theorem outer295At_twistedA_of_big {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid)
    (hch : (TauCeti.LieTypeIndex.twistedA r q).characteristic ≠ 3)
    (hb : Inputs295c.IsBig295Index (.twistedA r q)) :
    Inputs295c.Outer295At ⟨.twistedA r q, hv⟩ := by
  have hp3 : q.p ≠ 3 := by simpa using hch
  have hq3 :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.card_mod_three_ne_zero hp3
  have hr : (3 ∣ q.card + 1 ∧ 3 ≤ r) ∨ (¬ 3 ∣ q.card + 1 ∧ 5 ≤ r) := by
    rcases hb with h | h | h
    · change (r = 3 ∧ q.card % 3 = 2) ∨ ((r = 5 ∨ r = 6) ∧ q.card % 3 = 1) at h
      omega
    · change (4 ≤ r ∧ q.card % 3 = 2) ∨ (7 ≤ r ∧ q.card % 3 = 1) at h
      omega
    · exact h.elim
  by_cases hg : 3 ∣ q.card + 1 ∧ 3 ∣ r + 1
  · obtain ⟨h3q, h3r⟩ := hg
    by_cases hq2 : q.card = 2
    · exact (at_typeTwistedA_two hv hq2 (by omega)).1
    · exact outer295At_typeTwistedA_dvd hv hp3 h3q
        (Or.inl ⟨Inputs295c.four_le_card_of hp3 hq2, by omega⟩)
  · refine outer295At_typeTwistedA hv hp3 (fun hd => hg ?_) hr
    exact ⟨Nat.dvd_trans hd (Nat.gcd_dvd_right _ _), Nat.dvd_trans hd (Nat.gcd_dvd_left _ _)⟩


theorem input29_5'LieRest2_of_rest3 (h : Input29_5'LieRest3) : Inputs295c.Input29_5'LieRest2 := by
  obtain ⟨hD4, hE6o, hU42, hExc⟩ := h
  refine ⟨?_, ?_, ?_⟩
  ·
    intro d h2 h42 hb hs ho hA
    have hch := Inputs295c.characteristic_ne_three_of_classicalTwo h2
    obtain ⟨dd, hv⟩ := d
    have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    cases dd with
    | twistedA r q =>
      refine ⟨outer295At_twistedA_of_big hv hch hb, ?_⟩
      by_cases hop : q.card = 2 ∧ r = 3
      · obtain ⟨hq2, rfl⟩ := hop
        exact hU42 q hv hq2
      · exact inner295At_twistedA_of_not_open hv hch hb hop
    | B r q =>
      have hq : q.card = 2 := h2
      obtain ⟨hp2, he1⟩ := p_eq_two_of_card_two hq
      have hr3 := three_le_of_big_B hb
      have hr4 : 4 ≤ r := by
        by_contra hlt
        obtain rfl : r = 3 := by omega
        exact hs ⟨q, hp2, he1, rfl⟩
      exact ⟨(at_typeB_even hv hp2 hr3).1, (at_typeB_even hv hp2 hr3).2 hr4⟩
    | D r q =>
      have hq : q.card = 2 := h2
      have hr4 : 4 ≤ r := hrange
      have hr5 : 5 ≤ r := by
        by_contra hlt
        obtain rfl : r = 4 := by omega
        exact h42 hq
      have hp3 : q.p ≠ 3 := by simpa using hch
      exact ⟨outer295At_typeD hv hp3 hr5, inner295At_typeD hv hp3 hr5⟩
    | twistedD r q =>
      have hq : q.card = 2 := h2
      obtain ⟨hp2, he1⟩ := p_eq_two_of_card_two hq
      have hr4 : 4 ≤ r := hrange
      have hr5 : 5 ≤ r := by
        by_contra hlt
        obtain rfl : r = 4 := by omega
        exact ho ⟨q, hp2, he1, rfl⟩
      have hp3 : q.p ≠ 3 := by simpa using hch
      exact ⟨outer295At_typeTwistedD hv hp3, inner295At_typeTwistedD hv hp3 hr5⟩
    | A r q => exact absurd rfl (hA r q)
    | C r q => exact h2.elim
    | E6 q => exact h2.elim
    | E7 q => exact h2.elim
    | E8 q => exact h2.elim
    | F4 q => exact h2.elim
    | G2 q => exact h2.elim
    | twistedE6 q => exact h2.elim
    | trialityD4 q => exact h2.elim
    | suzuki m => exact h2.elim
    | reeG2 m => exact h2.elim
    | reeF4 m => exact h2.elim
    | tits => exact h2.elim
  ·
    intro d hch h2 hb hA
    obtain ⟨dd, hv⟩ := d
    have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    cases dd with
    | twistedA r q => exact outer295At_twistedA_of_big hv hch hb
    | B r q =>
      have hr3 := three_le_of_big_B hb
      by_cases hp2 : q.p = 2
      · exact (at_typeB_even hv hp2 hr3).1
      · exact outer295At_typeB_odd hv hp2 (by simpa using hch) hr3
    | C r q => exact (at_typeC hv (by simpa using hch)).1
    | D r q =>
      have hr4 : 4 ≤ r := hrange
      by_cases hr : r = 4
      · subst hr
        exact hD4 q hv (by simpa using hch) h2
      · exact outer295At_typeD hv (by simpa using hch) (by omega)
    | twistedD r q => exact outer295At_typeTwistedD hv (by simpa using hch)
    | F4 q =>
      by_cases hq2 : q.card = 2
      · exact outer295At_F4_two q hv hq2
      · exact (at_F4 q hv (by simpa using hch) hq2).1
    | E6 q =>
      by_cases hq2 : q.card = 2
      · exact outer295At_untwE_two (τ := .E6) (Or.inl rfl) (c := TauCeti.LieTypeIndex.E6)
          CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv hq2
      · exact outer295At_untwE (τ := .E6) (Or.inl rfl) (c := TauCeti.LieTypeIndex.E6)
          CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv (by simpa using hch) hq2
    | twistedE6 q =>
      by_cases hq2 : q.card = 2
      · exact hE6o q hv hq2
      · exact outer295At_twistedE6 q hv (by simpa using hch) hq2
    | E7 q =>
      by_cases hq2 : q.card = 2
      · exact outer295At_untwE_two (τ := .E7) (Or.inr (Or.inl rfl)) (c := TauCeti.LieTypeIndex.E7)
          CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 q hv hq2
      · exact outer295At_untwE (τ := .E7) (Or.inr (Or.inl rfl)) (c := TauCeti.LieTypeIndex.E7)
          CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 q hv (by simpa using hch) hq2
    | E8 q =>
      by_cases hq2 : q.card = 2
      · exact outer295At_untwE_two (τ := .E8) (Or.inr (Or.inr rfl)) (c := TauCeti.LieTypeIndex.E8)
          CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 q hv hq2
      · exact outer295At_untwE (τ := .E8) (Or.inr (Or.inr rfl)) (c := TauCeti.LieTypeIndex.E8)
          CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 q hv (by simpa using hch) hq2
    | A r q => exact absurd rfl (hA r q)
    | G2 q => rcases hb with h | h | h <;> exact h.elim
    | trialityD4 q => rcases hb with h | h | h <;> exact h.elim
    | suzuki m => rcases hb with h | h | h <;> exact h.elim
    | reeG2 m => rcases hb with h | h | h <;> exact h.elim
    | reeF4 m => rcases hb with h | h | h <;> exact h.elim
    | tits => rcases hb with h | h | h <;> exact h.elim
  ·
    intro d hch h2 hb hD4 hA
    obtain ⟨dd, hv⟩ := d
    have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    cases dd with
    | twistedA r q =>
      by_cases hop : q.card = 2 ∧ r = 3
      · obtain ⟨hq2, rfl⟩ := hop
        exact hU42 q hv hq2
      · exact inner295At_twistedA_of_not_open hv hch hb hop
    | B r q =>
      have hr3 := three_le_of_big_B hb
      by_cases hr : r = 3
      · subst hr
        by_cases hp2 : q.p = 2
        · exact inner295At_typeB_even_three hv hp2 h2
        · exact inner295At_typeB_odd_three hv hp2 (by simpa using hch)
      · have hr4 : 4 ≤ r := by omega
        by_cases hp2 : q.p = 2
        · exact (at_typeB_even hv hp2 hr3).2 hr4
        · exact inner295At_typeB_odd hv hp2 (by simpa using hch) hr4
    | C r q =>
      have hr3 : 3 ≤ r := hrange.1
      by_cases hr : r = 3
      · subst hr
        exact inner295At_typeC_three hv (by simpa using hch)
      · exact (at_typeC hv (by simpa using hch)).2 (by omega)
    | D r q =>
      have hr4 : 4 ≤ r := hrange
      have hr5 : 5 ≤ r := by
        by_contra hlt
        obtain rfl : r = 4 := by omega
        exact hD4 q rfl
      exact inner295At_typeD hv (by simpa using hch) hr5
    | twistedD r q =>
      have hr4 : 4 ≤ r := hrange
      by_cases hr : r = 4
      · subst hr
        exact inner295At_typeTwistedD_four hv (by simpa using hch) h2
      · exact inner295At_typeTwistedD hv (by simpa using hch) (by omega)
    | F4 q =>
      by_cases hq2 : q.card = 2
      · exact (hExc q hq2).1 hv
      · exact (at_F4 q hv (by simpa using hch) hq2).2
    | E6 q =>
      by_cases hq2 : q.card = 2
      · exact (hExc q hq2).2.1 hv
      · exact inner295At_untwE (τ := .E6) (Or.inl rfl) (c := TauCeti.LieTypeIndex.E6)
          CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv (by simpa using hch) hq2
    | twistedE6 q =>
      by_cases hq2 : q.card = 2
      · exact (hExc q hq2).2.2.1 hv
      · exact inner295At_twistedE6 q hv (by simpa using hch) hq2
    | E7 q =>
      by_cases hq2 : q.card = 2
      · exact (hExc q hq2).2.2.2.1 hv
      · exact inner295At_untwE (τ := .E7) (Or.inr (Or.inl rfl)) (c := TauCeti.LieTypeIndex.E7)
          CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 q hv (by simpa using hch) hq2
    | E8 q =>
      by_cases hq2 : q.card = 2
      · exact (hExc q hq2).2.2.2.2 hv
      · exact inner295At_untwE (τ := .E8) (Or.inr (Or.inr rfl)) (c := TauCeti.LieTypeIndex.E8)
          CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 q hv (by simpa using hch) hq2
    | A r q => exact absurd rfl (hA r q)
    | G2 q => rcases hb with h | h | h <;> exact h.elim
    | trialityD4 q => rcases hb with h | h | h <;> exact h.elim
    | suzuki m => rcases hb with h | h | h <;> exact h.elim
    | reeG2 m => rcases hb with h | h | h <;> exact h.elim
    | reeF4 m => rcases hb with h | h | h <;> exact h.elim
    | tits => rcases hb with h | h | h <;> exact h.elim

end Reduction

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs295d
