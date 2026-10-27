module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04D4Red
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04D4FSub
public import CFSG.HardMathSupport.Lang.Proving.OrthogonalFieldDescentOdd
public import CFSG.LieType.SeitzGeneration.OuterOrthThreeSubfield
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Exceptional.E6E7
public import CFSG.LieType.Steinberg.Families
public import CFSG.LieType.Steinberg.G2
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescent
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedLieTag StatedLieAdmissible StatedProj
  StatedOmega StatedQuadPlus)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.RankThree.PartOne (SubfieldConclusion)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (IsExtension fieldAutT fieldPair
  subfieldDerivedImage coordinateQuadPlus_fieldAut coordinateQuadPlus_isExtension)
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.HardMathSupport.Timmesfeld.DFour

local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

theorem d4_congr_trans_eq {T A B : Type*} [Group T] [Group A] [Group B] (φ : T ≃* A)
    (Θ : A ≃* B) (f₁ : MulAut T) (a : MulAut A) (b : MulAut B) (ha : MulAut.congr φ f₁ = a)
    (hΘ : ∀ x, Θ (a x) = b (Θ x)) : MulAut.congr (φ.trans Θ) f₁ = b := by
  ext y
  have h1 : MulAut.congr (φ.trans Θ) f₁ y = Θ (a (Θ.symm y)) := by
    rw [← ha, MulAut.congr_apply, MulAut.congr_apply]
    rfl
  rw [h1, hΘ, MulEquiv.apply_symm_apply]

theorem d4_congr_eq_fieldAutT {T : Type} [Group T] {K : Type} [Field K] {d : ℕ}
    {Q Q' : QuadraticForm K (Fin d → K)} (φ : T ≃* matrixProjectiveDerived Q)
    (Θ : matrixProjectiveDerived Q ≃* matrixProjectiveDerived Q') (f₁ : MulAut T)
    (U : similarityPairs Q) (hU : matrixProjectiveConjugationHom Q U = MulAut.congr φ f₁)
    (g' : similarityPairs Q') (hg'l : g'.val.left = 1) (hg'r : g'.val.right = U.val.right)
    (hΘ : ∀ x, Θ (matrixProjectiveConjugationHom Q U x) =
      matrixProjectiveConjugationHom Q' g' (Θ x))
    (hQσ : ∀ v, Q' (coordinateFieldMap d U.val.right v) = U.val.right (Q' v)) :
    MulAut.congr (φ.trans Θ) f₁ = fieldAutT Q' U.val.right hQσ := by
  have hg'eq : g' = fieldPair Q' U.val.right hQσ := Subtype.ext (SemidirectProduct.ext hg'l hg'r)
  refine d4_congr_trans_eq φ Θ f₁ (MulAut.congr φ f₁) (fieldAutT Q' U.val.right hQσ) rfl
    fun x => ?_
  have h1 := hΘ x
  rw [hU, hg'eq] at h1
  exact h1

theorem exists_outside_linear {S : Type} [Group S] [Finite S] (K : Type) [Field K] [Finite K]
    (φ : S ≃* matrixProjectiveDerived (coordinateQuadPlus 4 K))
    (hQ : coordinateQuadPlus 4 K ≠ 0)
    (hab : ∃ m : ℕ, Nat.card (Abelianization (matrixIsometries (coordinateQuadPlus 4 K))) = 2 ^ m)
    (hidx : (matrixProjectiveImage (coordinateQuadPlus 4 K)).index ≤ 3)
    (D : Subgroup (MulAut S)) (hD : CFSG.Open.IsElemAbelian 3 D) (hcard : Nat.card D = 3 ^ 2)
    (hinn : D ⊓ Inn S = ⊥) :
    ∃ y ∈ D, y ≠ 1 ∧ MulAut.congr φ y ∈ matrixProjectiveImage (coordinateQuadPlus 4 K) ∧
      MulAut.congr φ y ∉ (linearConjugationHom (coordinateQuadPlus 4 K)).range ∧
      orderOf (MulAut.congr φ y) = 3 := by
  have hXcard : Nat.card (D.map (MulAut.congr φ).toMonoidHom) = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective (MulAut.congr φ).injective, hcard]
  have hXexp : ∀ a ∈ D.map (MulAut.congr φ).toMonoidHom, a ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    change MulAut.congr φ x ^ 3 = 1
    rw [← map_pow, hD.2 x hx, map_one]
  have hXinn : ∀ a ∈ D.map (MulAut.congr φ).toMonoidHom,
      a ∈ Inn (matrixProjectiveDerived (coordinateQuadPlus 4 K)) → a = 1 := by
    rintro _ ⟨x, hx, rfl⟩ hI
    rw [← CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr φ] at hI
    obtain ⟨x', hx', hxx'⟩ := hI
    have hxe : x' = x := (MulAut.congr φ).injective hxx'
    have hmem : x ∈ D ⊓ Inn S := ⟨hx, hxe ▸ hx'⟩
    rw [hinn, Subgroup.mem_bot] at hmem
    rw [hmem, map_one]
  have hnt : ∃ a ∈ D.map (MulAut.congr φ).toMonoidHom,
      a ∈ matrixProjectiveImage (coordinateQuadPlus 4 K) ∧ a ≠ 1 := by
    by_contra hcon
    have hbot : (matrixProjectiveImage (coordinateQuadPlus 4 K)).subgroupOf
        (D.map (MulAut.congr φ).toMonoidHom) = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      rw [Subgroup.mem_subgroupOf] at hy
      rw [Subgroup.mem_bot]
      by_contra hne
      exact hcon ⟨(y : MulAut _), y.2, hy, fun h => hne (Subtype.ext h)⟩
    have h2 : ((matrixProjectiveImage (coordinateQuadPlus 4 K)).subgroupOf
        (D.map (MulAut.congr φ).toMonoidHom)).index ≤ 3 :=
      relIndex_le_three hidx _
    rw [hbot, Subgroup.index_bot, hXcard] at h2
    norm_num at h2
  obtain ⟨a, haX, haE, ha1⟩ := hnt
  obtain ⟨x, hxD, hxa⟩ := Subgroup.mem_map.mp haX
  have hxa' : MulAut.congr φ x = a := hxa
  have hx1 : x ≠ 1 := by
    rintro rfl
    apply ha1
    rw [← hxa']
    exact map_one _
  have ha3 : a ^ 3 = 1 := hXexp a haX
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  have hQv := exists_nonzero_value (coordinateQuadPlus 4 K) hQ
  have hnotlin : a ∉ (linearConjugationHom (coordinateQuadPlus 4 K)).range := fun hL =>
    ha1 (hXinn a haX (mem_inner_of_mem_linearRange (coordinateQuadPlus 4 K) hQv hab
      Nat.prime_three (by norm_num) hL ha3))
  refine ⟨x, hxD, hx1, ?_, ?_, ?_⟩
  · rw [hxa']
    exact haE
  · rw [hxa']
    exact hnotlin
  · rw [hxa']
    exact hord

theorem assemble_fixed {S P : Type} [Group S] [Group P] (ψ : S ≃* P) (y : MulAut S)
    (χ : MulAut P) (N J : Subgroup P) (hχ : ∀ t, χ t = t ↔ t ∈ N) (hJN : J ≤ N)
    (hnorm : (J.subgroupOf N).Normal) (hyψ : MulAut.congr ψ y = χ)
    (hJs : IsSimpleGroup ↥J) (hJn : ∃ a b : ↥J, a * b ≠ b * a) (hJ3 : 3 ∣ Nat.card ↥J) :
    ∃ L : Subgroup S, L ≤ CFSG.LocalAnalysis.GLTheoremA.fixSub y ∧ IsSimpleGroup ↥L ∧
      (∃ a b : ↥L, a * b ≠ b * a) ∧ 3 ∣ Nat.card ↥L ∧
      ∀ g ∈ CFSG.LocalAnalysis.GLTheoremA.fixSub y, ∀ x ∈ L, g * x * g⁻¹ ∈ L := by
  have hψy : ∀ s : S, ψ (y s) = χ (ψ s) := by
    intro s
    rw [← hyψ]
    change ψ (y s) = ψ (y (ψ.symm (ψ s)))
    rw [MulEquiv.symm_apply_apply]
  have hfix : ∀ s : S, s ∈ CFSG.LocalAnalysis.GLTheoremA.fixSub y ↔ ψ s ∈ N := by
    intro s
    rw [show s ∈ CFSG.LocalAnalysis.GLTheoremA.fixSub y ↔ y s = s from Iff.rfl,
      ← ψ.injective.eq_iff, hψy, hχ]
  have hmemL : ∀ s : S, s ∈ J.map ψ.symm.toMonoidHom ↔ ψ s ∈ J := by
    intro s
    constructor
    · rintro ⟨j, hj, rfl⟩
      simpa using hj
    · intro h
      exact ⟨ψ s, h, by simp⟩
  have eL : ↥(J.map ψ.symm.toMonoidHom) ≃* ↥J := (MulEquiv.subgroupMap ψ.symm J).symm
  refine ⟨J.map ψ.symm.toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    exact (hfix s).mpr (hJN ((hmemL s).mp hs))
  · exact eL.isSimpleGroup
  · obtain ⟨a, b, hab⟩ := hJn
    refine ⟨eL.symm a, eL.symm b, fun h => hab ?_⟩
    have h' := congrArg eL h
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h'
    exact h'
  · rw [Nat.card_congr eL.toEquiv]
    exact hJ3
  · intro g hg s hs
    have hgN : ψ g ∈ N := (hfix g).mp hg
    have hsJ : ψ s ∈ J := (hmemL s).mp hs
    have hsN : ψ s ∈ N := hJN hsJ
    have hconj := hnorm.conj_mem (⟨ψ s, hsN⟩ : N) (Subgroup.mem_subgroupOf.mpr hsJ)
      (⟨ψ g, hgN⟩ : N)
    have hconj' := Subgroup.mem_subgroupOf.mp hconj
    rw [hmemL]
    simpa [map_mul, map_inv] using hconj'

theorem field_core {S : Type} [Group S] [Finite S] {r f : ℕ}
    (hm : StatedClassicalModel S .POmegaPlus 4 r f) (hf3 : 3 ∣ f)
    (hsub : ∀ (K : Type) [Field K] [Finite K] (k : Subfield K), Nat.card k = r ^ (f / 3) →
      Nat.card K = r ^ (f / 3 * 3) → ∀ σ : K ≃+* K, orderOf σ = 3 →
      (∀ x, x ∈ k ↔ σ x = x) →
      SubfieldConclusion k (coordinateQuadPlus 4 k) (coordinateQuadPlus 4 K) σ 3
        (coordinateQuadPlus_isExtension k 4) (coordinateQuadPlus_fieldAut 4 σ))
    (D : Subgroup (MulAut S)) (hD : CFSG.Open.IsElemAbelian 3 D) (hcard : Nat.card D = 3 ^ 2)
    (hinn : D ⊓ Inn S = ⊥) :
    ∃ y ∈ D, y ≠ 1 ∧ ∃ L : Subgroup S, L ≤ CFSG.LocalAnalysis.GLTheoremA.fixSub y ∧
      IsSimpleGroup ↥L ∧ (∃ a b : ↥L, a * b ≠ b * a) ∧ 3 ∣ Nat.card L ∧
      ∀ g ∈ CFSG.LocalAnalysis.GLTheoremA.fixSub y, ∀ x ∈ L, g * x * g⁻¹ ∈ L := by
  have h0 := hm
  obtain ⟨⟨hr, hfpos, -⟩, K, _, _, hK, ⟨e⟩⟩ := h0
  obtain ⟨hQ, hab, hidx⟩ := coordinate_facts_four hm K hK e
  obtain ⟨y, hyD, hy1, hyE, hyD', hyord⟩ :=
    exists_outside_linear K (coordinatePlusWitnessEquiv K e) hQ hab hidx D hD hcard hinn
  have hdesc := CFSG.HardMathSupport.Lang.Proving.orthogonal_prime_semilinear_actual_fixed_form_descent'
    S .POmegaPlus
    (Or.inr (Or.inl rfl)) 4 r f 3 hm Nat.prime_three (by norm_num) K hK e
    (MulAut.congr (coordinatePlusWitnessEquiv K e) y) hyE hyD' hyord
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨g, hg⟩ := hyE
  have hrr := hrest g.val.right ⟨g, hg, rfl⟩
  obtain ⟨hord', hcardσ, U, _, _, hUκ, hUr, _, hDisp⟩ := hrr
  obtain ⟨ν, S₀, -, -, hT⟩ := hDisp
  obtain ⟨S', ν', -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT
  have hordσ : orderOf U.val.right = 3 := by
    rw [hUr]
    exact hord'
  have hcardk : Nat.card (semilinearFixedSubfield U.val.right) = r ^ (f / 3) := by
    rw [hUr]
    exact hcardσ
  have hK' : Nat.card K = r ^ (f / 3 * 3) := by
    rw [Nat.div_mul_cancel hf3]
    exact hK
  have hσk : ∀ x, x ∈ semilinearFixedSubfield U.val.right ↔ U.val.right x = x :=
    fun x => RingHom.mem_eqLocusField
  obtain ⟨⟨hinj, hsimp, hnonab⟩, -, hfix, hJN, hnorm, -⟩ :=
    hsub K (semilinearFixedSubfield U.val.right) hcardk hK' U.val.right hordσ hσk
  have hadm : StatedLieAdmissible .POmegaPlus 4 r (f / 3) :=
    ⟨hr, Nat.div_pos (Nat.le_of_dvd hfpos hf3) (by norm_num), le_rfl⟩
  have hJ3 := three_dvd_card_subfieldDerivedImage (semilinearFixedSubfield U.val.right) hadm
    hcardk (coordinateQuadPlus_isExtension (semilinearFixedSubfield U.val.right) 4) hinj
  have hΘy := d4_congr_eq_fieldAutT (coordinatePlusWitnessEquiv K e) Θ y U hUκ g' hg'l hg'r hΘ
    (coordinateQuadPlus_fieldAut 4 U.val.right)
  obtain ⟨L, hL1, hL2, hL3, hL4, hL5⟩ := assemble_fixed
    ((coordinatePlusWitnessEquiv K e).trans Θ) y
    (fieldAutT (coordinateQuadPlus 4 K) U.val.right (coordinateQuadPlus_fieldAut 4 U.val.right))
    _ _ hfix hJN hnorm hΘy hsimp hnonab hJ3
  exact ⟨y, hyD, hy1, L, hL1, hL2, hL3, hL4, hL5⟩

end CFSG.LocalAnalysis.GLTheoremA
