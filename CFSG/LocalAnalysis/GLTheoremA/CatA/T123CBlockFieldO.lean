module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CBlockAbs
public import CFSG.Open.StatedDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3OrthFix
import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLie
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBaseIso
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FFix
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FSeitzB1
public import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
public import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim
public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
public import CFSG.LocalAnalysis.GLTheoremA.S9.Inputs95
public import CFSG.LocalAnalysis.GLTheoremA.S9.Lemma94
public import CFSG.LocalAnalysis.GLTheoremA.S9.Lemma95A
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Proof
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
import CFSG.CGT.Timmesfeld75.Derivations
import CFSG.CGT.Timmesfeld75.Main
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHighClassical
import CFSG.LargeExtraspecial.S3cMain
import CFSG.LargeExtraspecial.S3cOddCore
import CFSG.LargeExtraspecial.S3cSix
import CFSG.LargeExtraspecial.S4EightA
import CFSG.LargeExtraspecial.S4EightF4
import CFSG.LargeExtraspecial.S4SevenB3
import CFSG.LargeExtraspecial.S4Three
import CFSG.LargeExtraspecial.S4TwoA
import CFSG.LargeExtraspecial.S4TwoD
import CFSG.LargeExtraspecial.S4TwoG
import CFSG.LargeExtraspecial.S4TwoInput
import CFSG.LieType.SeitzGeneration.OuterLinearCat
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieOffCharOuterCubeUnitary
import CFSG.RankThree.PartOne.CTP.SeitzFineU5
import CFSG.RankThree.PartOne.CTP.StdSub
import CFSG.RankThree.PartOne.KF.SU5Model
import CFSG.RankThree.PartOne.S11d.PSLDescent
import CFSG.RankThree.PartOne.SEITZ2.Common
import CFSG.RankThree.PartOne.SEITZ2.OmegaSetup
import CFSG.RankThree.PartTwo.Sec4.E27.FixStandard

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T123CB

open CFSG.Open
open scoped commutatorElement

private theorem dvd_div_of_coprime {p N g : ℕ} (hg : g ∣ N) (hpN : p ∣ N)
    (hcop : Nat.Coprime p g) : p ∣ N / g := by
  obtain ⟨m, rfl⟩ := hg
  rcases Nat.eq_zero_or_pos g with rfl | hg0
  · simp
  · rw [Nat.mul_div_cancel_left m hg0]
    exact hcop.dvd_of_dvd_mul_left hpN

private theorem coprime_of_dvd_four {p g : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hg : g ∣ 4) :
    Nat.Coprime p g := by
  refine (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => hp2 ?_
  have h4 : p ∣ 2 ^ 2 := by
    norm_num
    exact h.trans hg
  exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h4)

private theorem dvd_prod_of_dvd_add_one {n q p : ℕ} (hn : 2 ≤ n) (hdvd : p ∣ q + 1) :
    p ∣ ∏ i ∈ Finset.Icc 1 (n - 1), (q ^ (2 * i) - 1) := by
  have h1 : q ^ (2 * 1) - 1 ∣ ∏ i ∈ Finset.Icc 1 (n - 1), (q ^ (2 * i) - 1) :=
    Finset.dvd_prod_of_mem (fun i => q ^ (2 * i) - 1) (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)
  rw [mul_one] at h1
  exact (hdvd.trans (EvenSmallLie.CatalogOrders.add_one_dvd_sq_sub_one q)).trans h1

theorem dvd_ordD_of_dvd_add_one {n q p : ℕ} (hn : 2 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : p ∣ q + 1) : p ∣ ordD n q :=
  dvd_div_of_coprime ((Nat.gcd_dvd_right _ _).trans (dvd_mul_of_dvd_left (dvd_mul_left _ _) _))
    (Dvd.dvd.mul_left (dvd_prod_of_dvd_add_one hn hdvd) _)
    (coprime_of_dvd_four hp hp2 (Nat.gcd_dvd_left _ _))

theorem dvd_ordTwistedD_of_dvd_add_one {n q p : ℕ} (hn : 2 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : p ∣ q + 1) : p ∣ ordTwistedD n q :=
  dvd_div_of_coprime ((Nat.gcd_dvd_right _ _).trans (dvd_mul_of_dvd_left (dvd_mul_left _ _) _))
    (Dvd.dvd.mul_left (dvd_prod_of_dvd_add_one hn hdvd) _)
    (coprime_of_dvd_four hp hp2 (Nat.gcd_dvd_left _ _))

private theorem dvd_pow_add_one_of_mul {ℓ e p : ℕ} (hp : p.Prime) (hdvd : p ∣ ℓ ^ (e * p) + 1) :
    p ∣ ℓ ^ e + 1 := by
  haveI := Fact.mk hp
  rw [pow_mul] at hdvd
  rw [← ZMod.natCast_eq_zero_iff] at hdvd ⊢
  push_cast at hdvd ⊢
  rwa [ZMod.pow_card] at hdvd

private theorem ne_of_dvd_pow_add_one {ℓ f p : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hdvd : p ∣ ℓ ^ f + 1) : p ≠ ℓ := by
  rintro rfl
  have h1 : p ∣ p ^ f := dvd_pow_self p (by omega)
  exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right h1).mp hdvd))

section Simple

variable {p : ℕ} {T : Type} [Group T]

private theorem center_eq_bot_of_simple_nonabelian {X : Type*} [Group X] [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a) : Subgroup.center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := hnab
    exact absurd ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a) hab

private theorem isQuasisimple_of_simple_nonabelian' {X : Type*} [Group X] [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a) : CFSG.Open.IsQuasisimple X := by
  refine ⟨?_, ((QuotientGroup.quotientMulEquivOfEq (center_eq_bot_of_simple_nonabelian hnab)).trans
    QuotientGroup.quotientBot).isSimpleGroup⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X) with h | h
  · obtain ⟨a, b, hab⟩ := hnab
    have h1 : ⁅a, b⁆ = 1 := by
      rw [← Subgroup.mem_bot, ← h]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    exact absurd (commutatorElement_eq_one_iff_mul_comm.mp h1) hab
  · exact h

@[expose] def FixSimple (p : ℕ) {T : Type} [Group T] (α : MulAut T) : Prop :=
  ∃ (X : Type) (_ : Group X), IsSimpleGroup X ∧ (∃ a b : X, a * b ≠ b * a) ∧ p ∣ Nat.card X ∧
    Nonempty (↥(fixSub α) ≃* X) ∧
    ∀ β : MulAut T, (∀ m ∈ fixSub α, β m = m) → β ∈ Subgroup.zpowers α

theorem FixSimple.fieldBlock {α : MulAut T} (h : FixSimple p α) :
    ∃ M : Subgroup T, IsComponentOf M (fixSub α) ∧ p ∣ Nat.card (↥M ⧸ Subgroup.center ↥M) ∧
      (∀ P : Subgroup T, P ≤ fixSub α → ⁅P, P⁆ = P → P ≤ M) ∧
      ∀ β : MulAut T, (∀ m ∈ M, β m = m) → β ∈ Subgroup.zpowers α := by
  obtain ⟨X, _, hs, ⟨a, b, hab⟩, hpX, ⟨e⟩, hfix⟩ := h
  haveI := hs
  haveI : IsSimpleGroup ↥(fixSub α) := e.isSimpleGroup
  have hnab : ∃ x y : ↥(fixSub α), x * y ≠ y * x :=
    ⟨e.symm a, e.symm b, fun h' => hab (by simpa using congrArg e h')⟩
  have hZ := center_eq_bot_of_simple_nonabelian hnab
  refine ⟨fixSub α, ⟨le_rfl, IsSubnormal.refl _, isQuasisimple_of_simple_nonabelian' hnab⟩, ?_,
    fun P hP _ => hP, hfix⟩
  rw [Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans
    QuotientGroup.quotientBot).toEquiv, Nat.card_congr e.toEquiv]
  exact hpX

theorem FixSimple.of_congr {T' : Type} [Group T'] (e : T ≃* T') {α : MulAut T}
    (h : FixSimple p (MulAut.congr e α)) : FixSimple p α := by
  obtain ⟨X, _, hs, hnab, hpX, ⟨f⟩, hfix⟩ := h
  have hmem : ∀ t : T, e t ∈ fixSub (MulAut.congr e α) ↔ t ∈ fixSub α := fun t => by
    rw [mem_fixSub, mem_fixSub, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, e.injective.eq_iff]
  have hmap : (fixSub α).map e.toMonoidHom = fixSub (MulAut.congr e α) := by
    ext x
    rw [Subgroup.mem_map_equiv, ← hmem, MulEquiv.apply_symm_apply]
  refine ⟨X, inferInstance, hs, hnab, hpX,
    ⟨((Subgroup.equivMapOfInjective (fixSub α) e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hmap)).trans f⟩, fun β hβ => ?_⟩
  have hβ' := hfix (MulAut.congr e β) fun m hm => by
    have h1 : e.symm m ∈ fixSub α := (hmem _).1 (by rwa [MulEquiv.apply_symm_apply])
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, hβ _ h1,
      MulEquiv.apply_symm_apply]
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hβ'
  exact Subgroup.mem_zpowers_iff.mpr ⟨j, (MulAut.congr e).injective (by rw [map_zpow, hj])⟩

theorem fixSimple_conj {X : Type} [Group X] [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a)
    (hpX : p ∣ Nat.card X) {ι : X →* T} (hι : Function.Injective ι) {F : MulAut T}
    (hF : ∀ t, F t = t ↔ t ∈ ι.range)
    (hfixF : fixingSubgroup (MulAut T) (ι.range : Set T) = Subgroup.zpowers F) (D : MulAut T) :
    FixSimple p (D * F * D⁻¹) := by
  have hmem : ∀ t, t ∈ fixSub (D * F * D⁻¹) ↔ D⁻¹ t ∈ ι.range := fun t => by
    rw [mem_fixSub, ← hF, MulAut.mul_apply, MulAut.mul_apply]
    constructor
    · intro h
      calc F (D⁻¹ t) = D⁻¹ (D (F (D⁻¹ t))) := by simp
        _ = D⁻¹ t := by rw [h]
    · intro h
      rw [h]
      simp
  let φ : X →* T := (D : MulAut T).toMonoidHom.comp ι
  have hφ : Function.Injective φ := D.injective.comp hι
  have hrange : φ.range = fixSub (D * F * D⁻¹) := by
    ext t
    rw [hmem, MonoidHom.mem_range, MonoidHom.mem_range]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, by simp [φ]⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, by simp [φ, hx]⟩
  refine ⟨X, inferInstance, inferInstance, hnab, hpX,
    ⟨(MulEquiv.subgroupCongr hrange.symm).trans (MonoidHom.ofInjective hφ).symm⟩,
    fun β hβ => ?_⟩
  have hβ' : D⁻¹ * β * D ∈ fixingSubgroup (MulAut T) (ι.range : Set T) := by
    rw [mem_fixingSubgroup_iff]
    intro y hy
    have h1 : β (D y) = D y := hβ (D y) ((hmem _).2 (by simpa using hy))
    change (D⁻¹ * β * D) y = y
    simp [MulAut.mul_apply, h1]
  rw [hfixF] at hβ'
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hβ'
  refine Subgroup.mem_zpowers_iff.mpr ⟨j, ?_⟩
  rw [conj_zpow, hj]
  group

end Simple

section Models

open Matrix CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.RankThree.Classical.SteinbergBY CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBHigherLinearField
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.Assembly.LowTwoRank (StatedProj StatedOmega StatedQuadPlus StatedQuadMinus
  StatedLieAdmissible StatedLieTag StatedClassicalModel)
open CFSG.HardMathSupport.Lang.Proving (orthogonal_prime_semilinear_actual_fixed_form_descent')
open CFSG.RankThree.PartOne.KCOrthogonalAut (matrixProjectiveImage_eq_top_plus
  matrixProjectiveImage_eq_top_minus)

private theorem isOuterOfOrder_of_pow {p : ℕ} {T : Type} [Group T] (hp : p.Prime)
    {α : MulAut T} (hαp : α ^ p = 1) (hαo : ∀ t : T, MulAut.conj t ≠ α) :
    IsOuterOfOrder p α := by
  haveI := Fact.mk hp
  exact ⟨orderOf_eq_prime hαp fun h => hαo 1 (by rw [h, map_one]), fun g h => hαo g h.symm⟩

private theorem fixSimple_coordPlus {n ℓ f p : ℕ} {K : Type} [Field K] [Finite K]
    (hadm : StatedLieAdmissible .POmegaPlus n ℓ f) (hn5 : 5 ≤ n) (hK : Nat.card K = ℓ ^ f)
    (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ ℓ ^ f + 1)
    {α : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K))} (hα : IsOuterOfOrder p α) :
    FixSimple p α := by
  classical
  obtain ⟨hℓ, hf, hn4⟩ := id hadm
  have hpℓ := ne_of_dvd_pow_add_one hp hf hdvd
  have hM : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus n K))) .POmegaPlus n ℓ
      f := ⟨hadm, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  have hg : OrthogonalGates (coordinateQuadPlus n K) f :=
    orthogonal_large_prime_semilinear_field_and_diagonal_gates _ .POmegaPlus (Or.inr (Or.inl rfl))
      n ℓ f hM K hK (MulEquiv.refl _)
  obtain ⟨hE, hD⟩ :=
    outer_mem_E_not_D_of_top hg (matrixProjectiveImage_eq_top_plus K n hn5) hp hp2 hα
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' _ .POmegaPlus
    (Or.inr (Or.inl rfl)) n ℓ f p hM hp hp2 K hK (MulEquiv.refl _) α hE hD hα.1
  obtain ⟨D, -, σ, hσ, hαD⟩ := exists_conj_fieldAutT_of_descent _ hE hdesc
    (fun σ _ => coordinateQuadPlus_fieldAut n σ)
    (fun U Q₀ _ hdisp => by
      obtain ⟨ν, S₀, -, -, S, ν', hSQ, -, hSA, -⟩ := hdisp
      exact ⟨S, ν', hSQ, hSA⟩)
  obtain ⟨hpf, hcardk⟩ := card_semilinearFixedSubfield hℓ hf hK hσ
  obtain ⟨e, rfl⟩ := hpf
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h0 | h0
    · rw [h0, mul_zero] at hf
      omega
    · exact h0
  rw [Nat.mul_div_cancel_left e hp.pos] at hcardk
  have hK' : Nat.card K = ℓ ^ (e * p) := by rw [hK, mul_comm]
  have hσk : ∀ x, x ∈ semilinearFixedSubfield σ ↔ σ x = x := fun x => RingHom.mem_eqLocusField
  have hadm0 : StatedLieAdmissible .POmegaPlus n ℓ e := ⟨hℓ, he, hn4⟩
  obtain ⟨-, hconc⟩ :=
    orthogonal_prime_subfield_fixed_group_and_full_centralizer_odd .POmegaPlus
      (Or.inr (Or.inl rfl)) n ℓ e p hadm0 hp hp2 hpℓ K (semilinearFixedSubfield σ) hcardk hK' σ
      hσ hσk
  have hNJ := subfieldFixedGroup_le_plus hadm0 hp hp2 (semilinearFixedSubfield σ) hcardk hK' σ
    hσ hσk
  obtain ⟨⟨hinj, -, -⟩, -, hfixiff, hJN, -, -, -, -, hfixJ, -⟩ := hconc
  set k := semilinearFixedSubfield σ with hkdef
  have hkfin : Finite k := inferInstance
  have hM0 : StatedClassicalModel (matrixProjectiveDerived (coordinateQuadPlus n k))
      .POmegaPlus n ℓ e :=
    ⟨hadm0, k, inferInstance, inferInstance, hcardk,
      ⟨(coordinatePlusWitnessEquiv (n := n) k (MulEquiv.refl _)).symm⟩⟩
  obtain ⟨-, hnt, hsimp0, hperf0⟩ := orth_facts_of_model (Or.inr (Or.inl rfl)) hM0
  have hnab0 : ∃ a b : matrixProjectiveDerived (coordinateQuadPlus n k), a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    exact Group.IsPerfect.not_isMulCommutative _ ⟨⟨fun a b => hcon a b⟩⟩
  have hdvd0 : p ∣ ℓ ^ e + 1 := dvd_pow_add_one_of_mul hp (by rwa [mul_comm] at hdvd)
  have hcard0 : p ∣ Nat.card (matrixProjectiveDerived (coordinateQuadPlus n k)) := by
    rw [EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_classical hM0]
    exact dvd_ordD_of_dvd_add_one (by omega) hp hp2 hdvd0
  rw [hαD]
  exact fixSimple_conj hnab0 hcard0 hinj
    (fun t => (hfixiff t).trans ⟨fun h => hNJ h, fun h => hJN h⟩) hfixJ D

private theorem fixSimple_coordMinus {n ℓ e p : ℕ} {K : Type} [Field K] [Finite K]
    (hn : 4 ≤ n) (hn1 : 1 ≤ n) (hℓ : ℓ.Prime) (he : 1 ≤ e) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpℓ : p ≠ ℓ) (hdvd : p ∣ ℓ ^ e + 1) {k : Subfield K} (hk : Nat.card k = ℓ ^ e)
    (hK : Nat.card K = ℓ ^ (e * p)) {σ₀ : K ≃+* K} (hσ₀ : orderOf σ₀ = p)
    (hfix : ∀ x, x ∈ k ↔ σ₀ x = x) (b c : k) (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0)
    {α : MulAut (matrixProjectiveDerived (coordinateQuadMinus n K hn1 (b : K) (c : K)))}
    (hα : IsOuterOfOrder p α) : FixSimple p α := by
  classical
  have hf : 1 ≤ e * p := Nat.mul_pos he hp.pos
  have hfixall := fun σ (h : orderOf σ = p) => fixed_of_orderOf_orth hℓ he hp hK hσ₀ hfix h
  have hirrK : ∀ s : K, s ^ 2 + (b : K) * s + (c : K) ≠ 0 :=
    rootFree_of_odd_degree k hp hp2 (finrank_subfield_eq k hℓ he hk hK) b c hirr
  have hM : StatedClassicalModel
      (StatedProj (StatedOmega (StatedQuadMinus n K (b : K) (c : K)))) .POmegaMinus n ℓ (e * p) :=
    ⟨⟨hℓ, hf, hn⟩, K, inferInstance, inferInstance, hK, b, c, hirrK, ⟨MulEquiv.refl _⟩⟩
  have hg : OrthogonalGates (coordinateQuadMinus n K hn1 (b : K) (c : K)) (e * p) :=
    orthogonal_large_prime_semilinear_field_and_diagonal_gates _ .POmegaMinus
      (Or.inr (Or.inr rfl)) n ℓ (e * p) hM hn1 K hK b c hirrK (MulEquiv.refl _)
  have htop := matrixProjectiveImage_eq_top_minus K n hn (b : K) (c : K) hirrK
  obtain ⟨hE, hD⟩ := outer_mem_E_not_D_of_top hg htop hp hp2 hα
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' _ .POmegaMinus
    (Or.inr (Or.inr rfl)) n ℓ (e * p) p hM hp hp2 hn1 K hK b c hirrK (MulEquiv.refl _) α hE hD
    hα.1
  obtain ⟨D, -, σ, hσ, hαD⟩ := exists_conj_fieldAutT_of_descent _ hE hdesc
    (fun σ h v => coordinateQuadMinus_fieldAut k n hn1 (hfixall σ h) b c v) (by
      intro U Q₀ hord hdisp
      obtain ⟨b', c', hirr', ν, S₀, -, -, S, ν', hSQ, -, hSA, -⟩ := hdisp
      have hfixV := hfixall U.val.right hord
      have hσk' : ∀ x, x ∈ semilinearFixedSubfield U.val.right ↔ U.val.right x = x :=
        fun x => RingHom.mem_eqLocusField
      have hb'k : (b' : K) ∈ k := (hfixV _).2 ((hσk' _).1 b'.2)
      have hc'k : (c' : K) ∈ k := (hfixV _).2 ((hσk' _).1 c'.2)
      have hirrkK : ∀ s ∈ k, s ^ 2 + (b : K) * s + (c : K) ≠ 0 := fun s hs hz =>
        hirr ⟨s, hs⟩ (Subtype.ext (by simpa using hz))
      have hirr'kK : ∀ s ∈ k, s ^ 2 + (b' : K) * s + (c' : K) ≠ 0 := by
        intro s hs hz
        have hsV : s ∈ KCOrthogonalDescent.fixedField U.val := (hσk' s).2 ((hfixV s).1 hs)
        exact hirr' ⟨s, hsV⟩ (Subtype.ext (by simpa using hz))
      obtain ⟨μ, hμk, hμQ⟩ :=
        SEITZ2.exists_tail_isometry k hn1 b.2 c.2 hb'k hc'k hirrkK hirr'kK
      have hμσ : glFieldAut (Fin (2 * n)) K U.val.right μ = μ :=
        Units.ext (Matrix.ext fun i j => (hfixV _).1 (hμk i j))
      refine ⟨μ * S, ν', fun v => ?_, ?_⟩
      · rw [Units.val_mul, ← Matrix.mulVec_mulVec]
        exact (hμQ _).trans (hSQ v)
      · rw [mul_assoc, hSA, map_mul, hμσ])
  obtain ⟨-, hconc⟩ :=
    orthogonal_prime_subfield_fixed_group_and_full_centralizer_odd .POmegaMinus
      (Or.inr (Or.inr rfl)) n ℓ e p ⟨hℓ, he, hn⟩ hp hp2 hpℓ hn1 K k hk hK σ hσ (hfixall σ hσ)
      b c hirr
  have hNJ := subfieldFixedGroup_le_minus ⟨hℓ, he, hn⟩ hp hp2 hn1 k hk hK σ hσ (hfixall σ hσ)
    b c hirr
  obtain ⟨⟨hinj, -, -⟩, -, hfixiff, hJN, -, -, -, -, hfixJ, -⟩ := hconc
  have hkfin : Finite k := inferInstance
  have hM0 : StatedClassicalModel (matrixProjectiveDerived (coordinateQuadMinus n k hn1 b c))
      .POmegaMinus n ℓ e :=
    ⟨⟨hℓ, he, hn⟩, k, inferInstance, inferInstance, hk, b, c, hirr,
      ⟨(coordinateMinusWitnessEquiv k hn1 b c (MulEquiv.refl _)).symm⟩⟩
  obtain ⟨-, hnt, hsimp0, hperf0⟩ := orth_facts_of_model (Or.inr (Or.inr rfl)) hM0
  have hnab0 : ∃ a b' : matrixProjectiveDerived (coordinateQuadMinus n k hn1 b c),
      a * b' ≠ b' * a := by
    by_contra hcon
    push Not at hcon
    exact Group.IsPerfect.not_isMulCommutative _ ⟨⟨fun a b' => hcon a b'⟩⟩
  have hcard0 : p ∣ Nat.card (matrixProjectiveDerived (coordinateQuadMinus n k hn1 b c)) := by
    rw [EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_classical hM0]
    exact dvd_ordTwistedD_of_dvd_add_one (by omega) hp hp2 hdvd
  rw [hαD]
  exact fixSimple_conj hnab0 hcard0 hinj
    (fun t => (hfixiff t).trans ⟨fun h => hNJ h, fun h => hJN h⟩) hfixJ D

theorem fieldBlockAt_of_omegaPlus_model {T : Type} [Group T] {n ℓ f p : ℕ}
    (hM : StatedClassicalModel T .POmegaPlus n ℓ f) (hn5 : 5 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : p ∣ ℓ ^ f + 1) : FieldBlockAt p T := by
  intro α hαp hαo
  obtain ⟨hadm, K, _, _, hK, ⟨e₀⟩⟩ := hM
  let θ : T ≃* matrixProjectiveDerived (coordinateQuadPlus n K) := coordinatePlusWitnessEquiv K e₀
  exact (FixSimple.of_congr θ (fixSimple_coordPlus hadm hn5 hK hp hp2 hdvd
    (isOuterOfOrder_congr θ (isOuterOfOrder_of_pow hp hαp hαo)))).fieldBlock

theorem fieldBlockAt_of_omegaMinus_model {T : Type} [Group T] {n ℓ f p : ℕ}
    (hM : StatedClassicalModel T .POmegaMinus n ℓ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : p ∣ ℓ ^ f + 1) : FieldBlockAt p T := by
  intro α hαp hαo
  obtain ⟨hℓ, hf, hn⟩ := id hM.1
  have hn1 : 1 ≤ n := by omega
  have hpℓ := ne_of_dvd_pow_add_one hp hf hdvd
  have hα := isOuterOfOrder_of_pow hp hαp hαo
  obtain ⟨e, K, _, _, k, σ, b, c, he, hfe, hk, hK, hσ, hfix, hirr, ⟨θ⟩⟩ :
      ∃ (e : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (k : Subfield K) (σ : K ≃+* K)
        (b c : k), 1 ≤ e ∧ f = p * e ∧ Nat.card k = ℓ ^ e ∧ Nat.card K = ℓ ^ (e * p) ∧
        orderOf σ = p ∧ (∀ x, x ∈ k ↔ σ x = x) ∧ (∀ s : k, s ^ 2 + b * s + c ≠ 0) ∧
        Nonempty (T ≃* matrixProjectiveDerived
          (coordinateQuadMinus n K hn1 (b : K) (c : K))) := by
    by_cases hp3 : p = 3
    · exact exists_rational_model_minus_three hn1 hM hp hp3 hα
    · have hp5 : 3 < p := by
        obtain ⟨j, hj⟩ := hp.odd_of_ne_two hp2
        have := hp.two_le
        omega
      exact exists_rational_model_minus hn1 hM hp hp5 hpℓ hα
  have hdvd0 : p ∣ ℓ ^ e + 1 := dvd_pow_add_one_of_mul hp (by rwa [hfe, mul_comm] at hdvd)
  exact (FixSimple.of_congr θ (fixSimple_coordMinus hn hn1 hℓ he hp hp2 hpℓ hdvd0 hk hK hσ hfix
    b c hirr (isOuterOfOrder_congr θ hα))).fieldBlock

end Models

end CFSG.LocalAnalysis.GLTheoremA.T123CB

end
