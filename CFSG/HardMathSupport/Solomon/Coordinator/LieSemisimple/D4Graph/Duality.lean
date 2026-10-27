module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27D4AmbientDescent
public import CFSG.LieType.Chevalley.TrialityFullAmbientFixedGroup
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4OutTorus
public import CFSG.HardMathSupport.Lang.D4Three.NormalForm
public import CFSG.LieType.Chevalley.LangAdjointDiagonalLift
public import CFSG.LieType.Chevalley.CLSOddE7RationalDerivedIndex
public import CFSG.LieType.Chevalley.OrdinaryEFieldGraphQuotient
public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism
public import CFSG.LieType.Chevalley.OddTrialityAutomorphismNormalForm
public import CFSG.LieType.Chevalley.EvenTrialityAutomorphismNormalForm
public import CFSG.RankThree.PartOne.KGD.D4T36Core
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.Transfer
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.Layer
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.ClassOne
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.ClassicalInvolution.Balance.LocalBalance.Faithful
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.Foundations
public import CFSG.HardMathSupport.Solomon.Coordinator.B3FamPC
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.TopScalarLiftSquare
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Lang.D4Three CFSG.GroupTheory
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.HardMathSupport.Lang.E6Descent
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)



theorem graphType_baseChange_normalForm {K : Type} [Field K] (L : Type) [Field L] (ι : K →+* L)
    (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (T : K ≃+* K) (ε : ℕ)
    (u : adjointGroup Tag.D4 K) :
    baseChangeGL ι ((MulAut.conj g * (exactNormalAut Tag.D4 K a T 0 * d4Graph K ε)) u :
        ModGL Tag.D4 K) =
      baseChangeGL ι ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a) *
        baseChangeGL ι (Subtype.val (twistedEntrywiseAut TwistTag.D4 (ε : ℤ) T u) :
          ModGL Tag.D4 K) *
          (baseChangeGL ι ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a))⁻¹ := by
  have hP : Units.map (entrywiseHom (τ := Tag.D4) T.toRingHom) (d4P K ^ ε) = d4P K ^ ε := by
    rw [map_pow]
    exact congrArg (· ^ ε) (units_map_entrywiseHom_diagramMap (t := TwistTag.D4) T.toRingHom)
  have h1 : (Subtype.val (twistedEntrywiseAut TwistTag.D4 (ε : ℤ) T u) : ModGL Tag.D4 K) =
      d4P K ^ ε * Units.map (entrywiseHom T.toRingHom) (u : ModGL Tag.D4 K) * (d4P K ^ ε)⁻¹ := by
    have h := coe_twistedEntrywiseAut TwistTag.D4 (ε : ℤ) T u
    rw [zpow_natCast] at h
    exact h
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv, coe_exactNormalAut, exactQ_zero, coe_d4Graph, h1]
  simp only [map_mul, map_inv, hP, mul_one, inv_one]
  group

theorem graphType_exists_ext {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ f) :
    ∃ (K₃ : Type) (_ : Field K₃) (_ : Finite K₃) (_ : CharP K₃ ℓ) (_ : Algebra K K₃),
      Nat.card K₃ = (ℓ ^ f) ^ 3 ∧ ∃ Fr : K₃ ≃+* K₃, ∀ c, Fr c = c ^ (ℓ ^ f) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ hf hK
  let _ : Algebra (ZMod ℓ) K := ZMod.algebra K ℓ
  have hfin : Module.finrank (ZMod ℓ) K = f := by
    have : Fintype K := Fintype.ofFinite K
    have h1 := Module.card_eq_pow_finrank (K := ZMod ℓ) (V := K)
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hK] at h1
    exact (Nat.pow_right_injective hℓ.two_le h1).symm
  have hf3 : f * 3 ≠ 0 := by omega
  have hdvd : Module.finrank (ZMod ℓ) K ∣ Module.finrank (ZMod ℓ) (GaloisField ℓ (f * 3)) := by
    rw [hfin, GaloisField.finrank ℓ hf3]
    exact Dvd.intro 3 rfl
  obtain ⟨φ⟩ := FiniteField.nonempty_algHom_of_finrank_dvd hdvd
  let _ : Algebra K (GaloisField ℓ (f * 3)) := φ.toRingHom.toAlgebra
  refine ⟨GaloisField ℓ (f * 3), inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · rw [GaloisField.card ℓ (f * 3) hf3, pow_mul]
  · have hinj : Function.Injective (iterateFrobenius (GaloisField ℓ (f * 3)) ℓ f) :=
      (iterateFrobenius (GaloisField ℓ (f * 3)) ℓ f).injective
    refine ⟨RingEquiv.ofBijective _ ⟨hinj, Finite.surjective_of_injective hinj⟩, fun c => ?_⟩
    exact iterateFrobenius_def ℓ f c

theorem graphType_baseChangeGL_d4P {K L : Type} [Field K] [Field L] (ι : K →+* L) :
    baseChangeGL ι (d4P K) = d4P L := baseChangeGL_diagramMap ι TwistTag.D4


section Cube

theorem graphType_cube_expand {G : Type*} [Group G] (x Q : G) :
    (x * Q) ^ 3 = x * (Q * x * Q⁻¹) * (Q * (Q * x * Q⁻¹) * Q⁻¹) * Q ^ 3 := by
  rw [pow_three']
  group

theorem graphType_cube_mem {F : Type} [Field F] (ε : ℕ) {x : ModGL Tag.D4 F}
    (hx : x ∈ adjointGroup Tag.D4 F) :
    (x * d4P F ^ ε) ^ 3 ∈ adjointGroup Tag.D4 F := by
  have hconj : ∀ y ∈ adjointGroup Tag.D4 F, d4P F ^ ε * y *
      (d4P F ^ ε)⁻¹ ∈ adjointGroup Tag.D4 F := fun y hy =>
    conj_mem_adjointGroup_of_map_eq (map_conj_pow_of_map_conj (d4P F)
      (map_conj_diagramMap TwistTag.D4 F (Or.inl rfl)) ε) y hy
  have hP3 : (d4P F ^ ε) ^ 3 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, show d4P F ^ 3 = 1 from
      diagramMap_pow_order TwistTag.D4 F, one_pow]
  rw [graphType_cube_expand, hP3, mul_one]
  exact mul_mem (mul_mem hx (hconj _ hx)) (hconj _ (hconj _ hx))

theorem graphType_cube_eq_one {K L : Type} [Field K] [Finite K] [Field L] (ι : K →+* L)
    (α : MulAut (adjointGroup Tag.D4 K)) (hα3 : α ^ 3 = 1) (g : adjointGroup Tag.D4 K)
    (a : Fin Tag.D4.rank → Kˣ) (ε : ℕ)
    (hx : baseChangeGL ι ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a) ∈ adjointGroup Tag.D4 L)
    (hM : ∀ u : adjointGroup Tag.D4 K, baseChangeGL ι (α u : ModGL Tag.D4 K) =
      (baseChangeGL ι ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a) * d4P L ^ ε) *
        baseChangeGL ι (u : ModGL Tag.D4 K) *
          (baseChangeGL ι ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a) *
            d4P L ^ ε)⁻¹) :
    (baseChangeGL ι ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a) *
      d4P L ^ ε) ^ 3 = 1 := by
  classical
  set M := baseChangeGL ι ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a) *
    d4P L ^ ε with hMdef
  have hcomm : ∀ w ∈ (adjointGroup Tag.D4 K).map (baseChangeGL ι), M ^ 3 * w = w * M ^ 3 := by
    rintro _ ⟨w', hw', rfl⟩
    set u : adjointGroup Tag.D4 K := ⟨w', hw'⟩ with hu
    have h3 : α (α (α u)) = u := by
      have : (α ^ 3) u = u := by rw [hα3]; rfl
      rwa [pow_three, MulAut.mul_apply, MulAut.mul_apply] at this
    have e' : M * (M * (M * baseChangeGL ι w' * M⁻¹) * M⁻¹) * M⁻¹ = baseChangeGL ι w' := by
      have := congrArg (fun y : adjointGroup Tag.D4 K => baseChangeGL ι (y : ModGL Tag.D4 K)) h3
      rw [hM (α (α u)), hM (α u), hM u] at this
      exact this
    have e'' : (M * M * M) * baseChangeGL ι w' * (M * M * M)⁻¹ = baseChangeGL ι w' := by
      calc (M * M * M) * baseChangeGL ι w' * (M * M * M)⁻¹ =
          M * (M * (M * baseChangeGL ι w' * M⁻¹) * M⁻¹) * M⁻¹ := by group
        _ = baseChangeGL ι w' := e'
    rw [pow_three']
    exact mul_inv_eq_iff_eq_mul.mp e''
  have hNad : M ^ 3 ∈ adjointGroup Tag.D4 L := graphType_cube_mem ε hx
  rcases lt_or_ge 2 (Nat.card K) with h2 | h2
  · obtain ⟨-, -, hfaith, -⟩ := Chevalley_large_finite_root_centralizer_faithfulness Tag.D4 K
      (by simpa using h2) L ι
    exact hfaith _ hNad hcomm
  ·
    have hK2 : Nat.card K = 2 := by
      have := Finite.one_lt_card (α := K)
      omega
    have : Fintype K := Fintype.ofFinite K
    have hu1 : ∀ u : Kˣ, u = 1 := by
      have h1 : Fintype.card Kˣ = 1 := by
        rw [Fintype.card_units, ← Nat.card_eq_fintype_card, hK2]
      intro u
      exact Fintype.card_le_one_iff.mp (le_of_eq h1) u 1
    have ha : a = 1 := funext fun i => hu1 (a i)
    rw [ha, rootDiagUnit_one, mul_one] at hMdef hx
    set n : ModGL Tag.D4 K := ((g : ModGL Tag.D4 K) * d4P K ^ ε) ^ 3 with hn
    have hMn : M ^ 3 = baseChangeGL ι n := by
      rw [hMdef, hn, map_pow, map_mul, map_pow, graphType_baseChangeGL_d4P]
    have hnad : n ∈ adjointGroup Tag.D4 K := graphType_cube_mem ε g.2
    have hcen : (⟨n, hnad⟩ : adjointGroup Tag.D4 K) ∈ Subgroup.center (adjointGroup Tag.D4 K) := by
      rw [Subgroup.mem_center_iff]
      intro u
      have := hcomm (baseChangeGL ι (u : ModGL Tag.D4 K)) ⟨u, u.2, rfl⟩
      rw [hMn, ← map_mul, ← map_mul] at this
      exact Subtype.ext (baseChangeGL_injective ι (by simpa using this.symm))
    rw [center_adjointGroup_eq_bot_field, Subgroup.mem_bot] at hcen
    have hn1 : n = 1 := congrArg Subtype.val hcen
    rw [hMn, hn1, map_one]

end Cube

section Inverse

variable {K : Type} [Field K]

theorem graphType_coe_normalForm (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (ε : ℕ)
    (u : adjointGroup Tag.D4 K) :
    ((MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K ε)) u : ModGL Tag.D4 K) =
      ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a * d4P K ^ ε) * (u : ModGL Tag.D4 K) *
        ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a * d4P K ^ ε)⁻¹ := by
  have h1 : ∀ w : ModGL Tag.D4 K, Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) w = w := by
    intro w
    have e1 : (1 : K ≃+* K).toRingHom = RingHom.id K := RingHom.ext fun _ => rfl
    rw [e1]
    exact Units.ext (entrywise_id (R := K) _)
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv, coe_exactNormalAut, exactQ_zero, coe_d4Graph, h1]
  group

theorem graphType_baseChange_normalForm_one {L : Type} [Field L] (ι : K →+* L)
    (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (ε : ℕ) (u : adjointGroup Tag.D4 K) :
    baseChangeGL ι ((MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K ε)) u :
        ModGL Tag.D4 K) =
      (baseChangeGL ι ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a) * d4P L ^ ε) *
        baseChangeGL ι (u : ModGL Tag.D4 K) *
          (baseChangeGL ι ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a) * d4P L ^ ε)⁻¹ := by
  rw [graphType_coe_normalForm]
  simp only [map_mul, map_inv, map_pow, graphType_baseChangeGL_d4P]

theorem graphType_inv_normalForm (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) :
    ∃ (g' : adjointGroup Tag.D4 K) (a' : Fin Tag.D4.rank → Kˣ),
      (MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K 2))⁻¹ =
        MulAut.conj g' * (exactNormalAut Tag.D4 K a' 1 0 * d4Graph K 1) := by
  set a' : Fin Tag.D4.rank → Kˣ := fun i => (a (d4Rho.symm i))⁻¹ with ha'
  set g' : adjointGroup Tag.D4 K := exactNormalAut Tag.D4 K a' 1 0 (d4Graph K 1 g⁻¹) with hg'
  refine ⟨g', a', ?_⟩
  have hP3 : d4P K ^ 3 = 1 := diagramMap_pow_order TwistTag.D4 K
  have hd : rootDiagUnit Tag.D4 a' = d4P K * (rootDiagUnit Tag.D4 a)⁻¹ * (d4P K)⁻¹ := by
    have hinv : rootDiagUnit Tag.D4 a⁻¹ = (rootDiagUnit Tag.D4 a)⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [← rootDiagUnit_mul, inv_mul_cancel, rootDiagUnit_one])
    have h : d4P K * rootDiagUnit Tag.D4 a⁻¹ = rootDiagUnit Tag.D4 a' * d4P K :=
      diagramMap_mul_rootDiagUnit (t := TwistTag.D4) (K := K) a⁻¹
    rw [hinv] at h
    calc rootDiagUnit Tag.D4 a' = (rootDiagUnit Tag.D4 a' * d4P K) * (d4P K)⁻¹ := by group
      _ = _ := by rw [← h]
  have hg'c : (g' : ModGL Tag.D4 K) =
      rootDiagUnit Tag.D4 a' * (d4P K * (g : ModGL Tag.D4 K)⁻¹ * (d4P K)⁻¹) *
        (rootDiagUnit Tag.D4 a')⁻¹ := by
    have h1 : ∀ w : ModGL Tag.D4 K, Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) w = w := by
      intro w
      have e1 : (1 : K ≃+* K).toRingHom = RingHom.id K := RingHom.ext fun _ => rfl
      rw [e1]
      exact Units.ext (entrywise_id (R := K) _)
    rw [hg', coe_exactNormalAut, exactQ_zero, coe_d4Graph, h1]
    simp only [Subgroup.coe_inv, pow_one, inv_one, mul_one]
  have hprod : ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a * d4P K ^ 2) *
      ((g' : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a' * d4P K ^ 1) = 1 := by
    rw [hg'c, hd]
    calc _ = (g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a * d4P K ^ 3 *
          (rootDiagUnit Tag.D4 a)⁻¹ * (g : ModGL Tag.D4 K)⁻¹ := by group
      _ = 1 := by rw [hP3]; group
  refine inv_eq_of_mul_eq_one_right (MulEquiv.ext fun u => Subtype.ext ?_)
  rw [MulAut.mul_apply, graphType_coe_normalForm, graphType_coe_normalForm, MulAut.one_apply]
  have hinv : ((g' : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a' * d4P K ^ 1) =
      ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a * d4P K ^ 2)⁻¹ :=
    eq_inv_of_mul_eq_one_right hprod
  rw [hinv]
  group

end Inverse


section FixedSubfield

variable {ℓ f : ℕ} [Fact ℓ.Prime] {K K₃ : Type} [Field K] [Finite K] [Field K₃] [Algebra K K₃]

theorem graphType_frobenius_algebraMap (hK : Nat.card K = ℓ ^ f) (Fr : K₃ ≃+* K₃)
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) (c : K) : Fr (algebraMap K K₃ c) = algebraMap K K₃ c := by
  have : Fintype K := Fintype.ofFinite K
  rw [hFr, ← map_pow, ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]

@[expose] def graphTypeFixedEquiv (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) [Finite K₃]
    (hK₃ : Nat.card K₃ = (ℓ ^ f) ^ 3) (Fr : K₃ ≃+* K₃) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) :
    K ≃+* fixSubfield Fr := by
  have hcard := CFSG.RankThree.PartOne.KGD.card_fixSubfield_cube (Fact.out : ℓ.Prime) hf hK₃ Fr hFr
  let φ : K →+* fixSubfield Fr := (algebraMap K K₃).codRestrict (fixSubfield Fr)
    fun c => (mem_fixSubfield Fr).2 (graphType_frobenius_algebraMap hK Fr hFr c)
  have hφ : Function.Injective φ := fun a b h => (algebraMap K K₃).injective
    (congrArg Subtype.val h)
  have : Finite (fixSubfield Fr) := Nat.finite_of_card_ne_zero (by
    rw [hcard]; exact (pow_pos (Fact.out : ℓ.Prime).pos f).ne')
  exact RingEquiv.ofBijective φ (hφ.bijective_of_nat_card_le (by rw [hcard, hK]))

theorem graphTypeFixedEquiv_apply (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) [Finite K₃]
    (hK₃ : Nat.card K₃ = (ℓ ^ f) ^ 3) (Fr : K₃ ≃+* K₃) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) (c : K) :
    ((graphTypeFixedEquiv hf hK hK₃ Fr hFr c : fixSubfield Fr) : K₃) = algebraMap K K₃ c := rfl

end FixedSubfield

section Group

variable {G : Type*} [Group G]

theorem graphType_commute_of_conj_eq (A B W : G) (h : A * W * A⁻¹ = B * W * B⁻¹) :
    A⁻¹ * B * W = W * (A⁻¹ * B) := by
  calc A⁻¹ * B * W = A⁻¹ * (B * W * B⁻¹) * B := by group
    _ = A⁻¹ * (A * W * A⁻¹) * B := by rw [h]
    _ = W * (A⁻¹ * B) := by group

theorem graphType_twisted_fixed (P a b c x : G) (hx : x = a⁻¹ * (P * b * P⁻¹))
    (hF : b⁻¹ * (P * c * P⁻¹) = x) : P * (b * c⁻¹) * P⁻¹ = a * b⁻¹ := by
  have h1 : P * c * P⁻¹ = b * (a⁻¹ * (P * b * P⁻¹)) := by
    rw [← hx, ← hF]; group
  calc P * (b * c⁻¹) * P⁻¹ = (P * b * P⁻¹) * (P * c * P⁻¹)⁻¹ := by group
    _ = (P * b * P⁻¹) * (b * (a⁻¹ * (P * b * P⁻¹)))⁻¹ := by rw [h1]
    _ = a * b⁻¹ := by group

end Group


section DualFacts

variable {K : Type} [Field K] [Finite K]

theorem sigma_ne_one {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hK : Nat.card K = (p ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) : σ ≠ 1 := by
  intro h
  have hc := CFSG.RankThree.PartOne.KGD.card_fixSubfield_cube hp hf hK σ hσ
  have htop : fixSubfield σ = ⊤ := by
    ext c
    simp [h]
  rw [htop] at hc
  have hc' : Nat.card K = p ^ f := by
    rw [← hc]
    exact (Nat.card_congr Subfield.topEquiv.toEquiv).symm
  have hp1 : 1 < p ^ f := Nat.one_lt_pow (by omega) hp.one_lt
  rw [hK] at hc'
  nlinarith [hp1, pow_pos (lt_trans Nat.zero_lt_one hp1) 2]

theorem sigma_cube {p f : ℕ} (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) : σ ^ 3 = 1 := by
  ext c
  exact ringEquiv_cube_apply_eq hK hσ c

theorem fieldActor_cube {σ : K ≃+* K} (hσ3 : σ ^ 3 = 1) :
    fieldActor (t := TwistTag.D4) σ σ ^ 3 = 1 := by
  have h1 : fieldActor (t := TwistTag.D4) σ (σ ^ 3) = fieldActor σ σ ^ 3 :=
    map_pow (fieldActorHom (t := TwistTag.D4) σ) σ 3
  rw [← h1, hσ3, fieldActor_one]

theorem exists_theta {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hK : Nat.card K = (p ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) :
    (∃ Θ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →* (K ≃+* K),
      (∀ α g δ, α = MulAut.conj g * fieldActor σ δ → Θ α = δ) ∧
      Θ.ker = (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range) ∧
    Nonempty (DerivedCentralQuotient (twistedFixedGroup TwistTag.D4 K σ.toRingHom) ≃*
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  by_cases hp2 : p = 2
  · subst hp2
    obtain ⟨-, -, ⟨Θ, hΘ, -, hker, -⟩, -, -, -, -, he⟩ :=
      even_triality_exact_automorphism_normal_form hf K hK σ hσ
    exact ⟨⟨Θ, hΘ, hker⟩, he⟩
  · obtain ⟨-, -, ⟨Θ, hΘ, -, hker, -⟩, -, -, -, -, he⟩ :=
      odd_triality_exact_automorphism_normal_form hp hp2 hf K hK σ hσ
    exact ⟨⟨Θ, hΘ, hker⟩, he⟩

theorem fieldActor_not_inner {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) :
    fieldActor (t := TwistTag.D4) σ σ ∉ inner (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  obtain ⟨⟨Θ, hΘ, hker⟩, -⟩ := exists_theta hp hf hK σ hσ
  intro hin
  have h1 : Θ (fieldActor (t := TwistTag.D4) σ σ) = σ :=
    hΘ _ 1 σ (by rw [map_one, one_mul])
  have h2 : fieldActor (t := TwistTag.D4) σ σ ∈ Θ.ker := by rw [hker]; exact hin
  rw [MonoidHom.mem_ker] at h2
  exact sigma_ne_one hp hf hK σ hσ (h1.symm.trans h2)

end DualFacts

theorem dual_fixEquiv_ambient {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f)
    (K₃ : Type) [Field K₃] [Finite K₃] [CharP K₃ ℓ] [Algebra K K₃]
    (hK₃ : Nat.card K₃ = (ℓ ^ f) ^ 3) (Fr : K₃ ≃+* K₃) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    (L : Type) [Field L] [CharP L ℓ] [Algebra K₃ L] [IsAlgClosure K₃ L]
    (x : ModGL TwistTag.D4.tag L) (hx : x ∈ adjointGroup TwistTag.D4.tag L)
    (hxF : Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x = x)
    (hxP : (x * diagramMap TwistTag.D4 L) ^ 3 = 1)
    (β : MulAut (adjointGroup TwistTag.D4.tag K₃))
    (hβ : ∀ u : adjointGroup TwistTag.D4.tag K₃,
      baseChangeGL (algebraMap K₃ L) (β u : ModGL TwistTag.D4.tag K₃) =
        x * baseChangeGL (algebraMap K₃ L)
          (twistedEntrywiseAut TwistTag.D4 1 Fr u : ModGL TwistTag.D4.tag K₃) * x⁻¹)
    (α : MulAut (adjointGroup TwistTag.D4.tag K))
    (hα : ∀ u : adjointGroup TwistTag.D4.tag K,
      baseChangeGL ((algebraMap K₃ L).comp (algebraMap K K₃)) (α u : ModGL TwistTag.D4.tag K) =
        x * (diagramMap TwistTag.D4 L *
          baseChangeGL ((algebraMap K₃ L).comp (algebraMap K K₃)) (u : ModGL TwistTag.D4.tag K) *
            (diagramMap TwistTag.D4 L)⁻¹) * x⁻¹) :
    ∃ φ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom), φ ^ 3 = 1 ∧
      φ ∉ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) →*
        MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)).range ∧
      Nonempty (↥(fixSubgroup α) ≃* ↥(fixSubgroup φ)) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have : Fintype K₃ := Fintype.ofFinite K₃
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K₃
  have hFr3 : ∀ c, Fr (Fr (Fr c)) = c := fun c => by
    rw [hFr, hFr, hFr, ← pow_mul, ← pow_mul, show ℓ ^ f * (ℓ ^ f * ℓ ^ f) = (ℓ ^ f) ^ 3 by ring,
      ← hK₃, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hK₃4 : 4 ≤ Nat.card K₃ := by
    rw [hK₃]
    have h2 : 2 ≤ ℓ ^ f := le_trans hℓ.two_le (Nat.le_self_pow (by omega) ℓ)
    calc 4 ≤ 2 ^ 3 := by norm_num
      _ ≤ (ℓ ^ f) ^ 3 := Nat.pow_le_pow_left h2 3
  obtain ⟨FrL, hFrLdef⟩ : ∃ FrL : L →+* L, FrL = iterateFrobenius L ℓ f := ⟨_, rfl⟩
  have hFrc : FrL.comp (algebraMap K₃ L) = (algebraMap K₃ L).comp Fr.toRingHom := by
    ext c
    simp [hFrLdef, iterateFrobenius_def, hFr, map_pow]
  have hFι : ∀ w : ModGL TwistTag.D4.tag K₃,
      Units.map (entrywiseHom FrL) (baseChangeGL (algebraMap K₃ L) w) =
        baseChangeGL (algebraMap K₃ L) (Units.map (entrywiseHom Fr.toRingHom) w) := fun w => by
    rw [units_map_entrywiseHom_eq_baseChangeGL, units_map_entrywiseHom_eq_baseChangeGL,
      baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL, hFrc]
  have hFP : Units.map (entrywiseHom FrL) (diagramMap TwistTag.D4 L) = diagramMap TwistTag.D4 L :=
    units_map_entrywiseHom_diagramMap (t := TwistTag.D4) FrL
  have hα₀ : ∀ w : adjointGroup TwistTag.D4.tag K₃,
      baseChangeGL (algebraMap K₃ L)
          (twistedEntrywiseAut TwistTag.D4 1 Fr w : ModGL TwistTag.D4.tag K₃) =
        diagramMap TwistTag.D4 L * Units.map (entrywiseHom FrL)
          (baseChangeGL (algebraMap K₃ L) (w : ModGL TwistTag.D4.tag K₃)) *
            (diagramMap TwistTag.D4 L)⁻¹ := by
    intro w
    rw [coe_twistedEntrywiseAut, zpow_one, map_mul, map_mul, map_inv, baseChangeGL_diagramMap, hFι]
  have hstep : ∀ w : adjointGroup TwistTag.D4.tag K₃,
      baseChangeGL (algebraMap K₃ L) (β w : ModGL TwistTag.D4.tag K₃) =
        (x * diagramMap TwistTag.D4 L) * Units.map (entrywiseHom FrL)
          (baseChangeGL (algebraMap K₃ L) (w : ModGL TwistTag.D4.tag K₃)) *
            (x * diagramMap TwistTag.D4 L)⁻¹ := by
    intro w
    rw [hβ, hα₀]
    group
  rw [← hFrLdef] at hxF
  have hMF : Units.map (entrywiseHom FrL) (x * diagramMap TwistTag.D4 L) =
      x * diagramMap TwistTag.D4 L := by
    rw [map_mul, hFP, hxF]
  have hFr3U : ∀ w : ModGL TwistTag.D4.tag K₃, Units.map (entrywiseHom Fr.toRingHom)
      (Units.map (entrywiseHom Fr.toRingHom) (Units.map (entrywiseHom Fr.toRingHom) w)) = w := by
    intro w
    rw [units_map_entrywiseHom_comp, units_map_entrywiseHom_comp]
    have h1 : (Fr.toRingHom.comp Fr.toRingHom).comp Fr.toRingHom = RingHom.id K₃ :=
      RingHom.ext hFr3
    rw [h1]
    exact Units.ext (entrywise_id (R := K₃) _)
  have hF3 : ∀ v : ModGL TwistTag.D4.tag K₃, Units.map (entrywiseHom FrL) (Units.map
      (entrywiseHom FrL) (Units.map (entrywiseHom FrL) (baseChangeGL (algebraMap K₃ L) v))) =
        baseChangeGL (algebraMap K₃ L) v := by
    intro v
    rw [hFι, hFι, hFι, hFr3U]
  have hM3 : (x * diagramMap TwistTag.D4 L) * (x * diagramMap TwistTag.D4 L) *
      (x * diagramMap TwistTag.D4 L) = 1 := by
    rw [← pow_three']
    exact hxP
  have hβ3 : β ^ 3 = 1 := by
    refine MulEquiv.ext fun w => Subtype.ext (baseChangeGL_injective (algebraMap K₃ L) ?_)
    have h3 : (β ^ 3) w = β (β (β w)) := by
      simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply]
    rw [h3, hstep, hstep, hstep]
    simp only [map_mul, map_inv, hMF, hF3]
    calc _ = ((x * diagramMap TwistTag.D4 L) * (x * diagramMap TwistTag.D4 L) *
          (x * diagramMap TwistTag.D4 L)) * baseChangeGL (algebraMap K₃ L) (w : ModGL TwistTag.D4.tag K₃) *
          ((x * diagramMap TwistTag.D4 L) * (x * diagramMap TwistTag.D4 L) *
          (x * diagramMap TwistTag.D4 L))⁻¹ := by group
      _ = _ := by rw [hM3]; simp
  have hK₃' : Nat.card K₃ = ℓ ^ (f * 3) := by rw [hK₃, ← pow_mul]
  obtain ⟨ψ, h, hhF, hψι, hψβ⟩ := exists_conj_eq_twistedEntrywiseAut_of_ambient TwistTag.D4 K₃ hK₃'
    hK₃4 hf (rfl : f * 3 = f * 3) Fr hFr 1 L x hx β hβ hβ3
  rw [← hFrLdef] at hhF
  have hFrL' : ∀ c, FrL c = c ^ (ℓ ^ f) := fun c => by rw [hFrLdef, iterateFrobenius_def]
  have hcomm : ∀ u, twistedEntrywiseAut TwistTag.D4 1 Fr (ψ u) = ψ (β u) := fun u => by
    have := congrArg (fun φ : MulAut (adjointGroup TwistTag.D4.tag K₃) => φ (ψ u)) hψβ
    simpa [MulAut.mul_apply, MulAut.inv_apply_self] using this.symm
  have hE : ∀ u : adjointGroup TwistTag.D4.tag K₃,
      (diagramMap TwistTag.D4 L * Units.map (entrywiseHom FrL) (h : ModGL TwistTag.D4.tag L) *
          (diagramMap TwistTag.D4 L)⁻¹) *
        baseChangeGL (algebraMap K₃ L) (twistedEntrywiseAut TwistTag.D4 1 Fr u : ModGL TwistTag.D4.tag K₃) *
          (diagramMap TwistTag.D4 L * Units.map (entrywiseHom FrL) (h : ModGL TwistTag.D4.tag L) *
            (diagramMap TwistTag.D4 L)⁻¹)⁻¹ =
        ((h : ModGL TwistTag.D4.tag L) * x) *
          baseChangeGL (algebraMap K₃ L) (twistedEntrywiseAut TwistTag.D4 1 Fr u : ModGL TwistTag.D4.tag K₃) *
            ((h : ModGL TwistTag.D4.tag L) * x)⁻¹ := by
    intro u
    have h1 := hα₀ (ψ u)
    rw [hcomm u, hψι (β u), hψι u] at h1
    simp only [map_mul, map_inv] at h1
    calc _ = diagramMap TwistTag.D4 L * (Units.map (entrywiseHom FrL) (h : ModGL TwistTag.D4.tag L) *
          Units.map (entrywiseHom FrL) (baseChangeGL (algebraMap K₃ L)
            (u : ModGL TwistTag.D4.tag K₃)) *
          (Units.map (entrywiseHom FrL) (h : ModGL TwistTag.D4.tag L))⁻¹) *
          (diagramMap TwistTag.D4 L)⁻¹ := by rw [hα₀ u]; group
      _ = (h : ModGL TwistTag.D4.tag L) * baseChangeGL (algebraMap K₃ L)
          (β u : ModGL TwistTag.D4.tag K₃) * (h : ModGL TwistTag.D4.tag L)⁻¹ := h1.symm
      _ = _ := by rw [hβ u]; group
  have hAad : diagramMap TwistTag.D4 L * Units.map (entrywiseHom FrL) (h : ModGL TwistTag.D4.tag L) *
      (diagramMap TwistTag.D4 L)⁻¹ ∈ adjointGroup TwistTag.D4.tag L := by
    have hconj := map_conj_diagramMap_zpow TwistTag.D4 L 1
    rw [zpow_one] at hconj
    refine conj_mem_adjointGroup_of_map_eq hconj _ ?_
    rw [hFrLdef]
    exact entrywiseFrobGL_mem ℓ f h.2
  have hN1 : (diagramMap TwistTag.D4 L * Units.map (entrywiseHom FrL)
      (h : ModGL TwistTag.D4.tag L) * (diagramMap TwistTag.D4 L)⁻¹)⁻¹ * ((h : ModGL TwistTag.D4.tag L) * x)
        = 1 := by
    obtain ⟨-, -, hfaith, -⟩ :=
      Chevalley_large_finite_root_centralizer_faithfulness_of_four_le TwistTag.D4.tag K₃ hK₃4 L
        (algebraMap K₃ L)
    refine hfaith _ (mul_mem (inv_mem hAad) (mul_mem h.2 hx)) fun w hw => ?_
    obtain ⟨w', hw', rfl⟩ := hw
    have h2 := hE ((twistedEntrywiseAut TwistTag.D4 1 Fr)⁻¹ ⟨w', hw'⟩)
    rw [MulAut.apply_inv_self] at h2
    exact graphType_commute_of_conj_eq _ _ _ h2
  have hxh : x = (h : ModGL TwistTag.D4.tag L)⁻¹ * (diagramMap TwistTag.D4 L *
      Units.map (entrywiseHom FrL) (h : ModGL TwistTag.D4.tag L) * (diagramMap TwistTag.D4 L)⁻¹) := by
    calc x = (h : ModGL TwistTag.D4.tag L)⁻¹ * ((diagramMap TwistTag.D4 L *
        Units.map (entrywiseHom FrL) (h : ModGL TwistTag.D4.tag L) * (diagramMap TwistTag.D4 L)⁻¹) *
          ((diagramMap TwistTag.D4 L * Units.map (entrywiseHom FrL)
            (h : ModGL TwistTag.D4.tag L) * (diagramMap TwistTag.D4 L)⁻¹)⁻¹ *
              ((h : ModGL TwistTag.D4.tag L) * x))) := by group
      _ = _ := by rw [hN1, mul_one]
  have hFhad : Units.map (entrywiseHom FrL) (h : ModGL TwistTag.D4.tag L) ∈
      adjointGroup TwistTag.D4.tag L := by
    rw [hFrLdef]
    exact entrywiseFrobGL_mem ℓ f h.2
  have hzfix : diagramMap TwistTag.D4 L * Units.map (entrywiseHom FrL)
      ((h : ModGL TwistTag.D4.tag L) * (Units.map (entrywiseHom FrL)
        (h : ModGL TwistTag.D4.tag L))⁻¹) * (diagramMap TwistTag.D4 L)⁻¹ =
      (h : ModGL TwistTag.D4.tag L) * (Units.map (entrywiseHom FrL)
        (h : ModGL TwistTag.D4.tag L))⁻¹ := by
    have hFx := hxF
    rw [hxh] at hFx
    simp only [map_mul, map_inv, hFP] at hFx
    rw [map_mul, map_inv]
    exact graphType_twisted_fixed _ _ _ _ _ rfl hFx
  have hzad : (h : ModGL TwistTag.D4.tag L) * (Units.map (entrywiseHom FrL)
      (h : ModGL TwistTag.D4.tag L))⁻¹ ∈ adjointGroup TwistTag.D4.tag L :=
    mul_mem h.2 (inv_mem hFhad)
  have hset := (triality_both_field_orientations_simple_full_ambient_fixed_group (ℓ := ℓ) (d := f) hℓ hf K₃ hK₃ L 1
    (Or.inl rfl) Fr.toRingHom (fun c => by simpa using hFr c) FrL hFrL').2.1
  have hzmem : (h : ModGL TwistTag.D4.tag L) * (Units.map (entrywiseHom FrL)
      (h : ModGL TwistTag.D4.tag L))⁻¹ ∈ ((graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom).map
        (baseChangeGL (algebraMap K₃ L)) : Set (ModGL TwistTag.D4.tag L)) := by
    rw [← hset]
    exact ⟨hzad, by rw [pow_one]; exact hzfix⟩
  obtain ⟨z₀, hz₀, hz₀eq⟩ := hzmem
  set z' : ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) := ⟨z₀, hz₀⟩ with hz'
  set δ₀ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) :=
    fieldActor (t := TwistTag.D4) Fr Fr with hδ₀def
  have hδcoe : ∀ g : ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom),
      ((δ₀ g : ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)) : ModGL TwistTag.D4.tag K₃) =
        Units.map (entrywiseHom Fr.toRingHom) (g : ModGL TwistTag.D4.tag K₃) :=
    fun g => coe_fieldActor (t := TwistTag.D4) Fr Fr g
  have hδ3 : δ₀ ^ 3 = 1 := fieldActor_cube (sigma_cube hK₃ Fr hFr)
  have hδ3' : ∀ y, δ₀ (δ₀ (δ₀ y)) = y := fun y => by
    have h3 : (δ₀ ^ 3) y = δ₀ (δ₀ (δ₀ y)) := by
      rw [pow_three, MulAut.mul_apply, MulAut.mul_apply]
    rw [← h3, hδ3]
    rfl
  have hF3h : Units.map (entrywiseHom FrL) (Units.map (entrywiseHom FrL)
      (Units.map (entrywiseHom FrL) (h : ModGL TwistTag.D4.tag L))) = h := by
    rw [units_map_entrywiseHom_comp, units_map_entrywiseHom_comp]
    have hpow : (FrL.comp FrL).comp FrL = FrL ^ TwistTag.D4.order :=
      RingHom.ext fun c => by rw [RingHom.coe_pow]; rfl
    rw [hpow]
    exact hhF
  have hN : z' * δ₀ z' * δ₀ (δ₀ z') = 1 := by
    refine Subtype.ext (baseChangeGL_injective (algebraMap K₃ L) ?_)
    have hz : baseChangeGL (algebraMap K₃ L) (z' : ModGL TwistTag.D4.tag K₃) =
        (h : ModGL TwistTag.D4.tag L) * (Units.map (entrywiseHom FrL)
          (h : ModGL TwistTag.D4.tag L))⁻¹ := hz₀eq
    have e1 : baseChangeGL (algebraMap K₃ L) ((δ₀ z' : ↥(graphFixedRootGroup TwistTag.D4 K₃
        Fr.toRingHom)) : ModGL TwistTag.D4.tag K₃) = Units.map (entrywiseHom FrL)
          ((h : ModGL TwistTag.D4.tag L) * (Units.map (entrywiseHom FrL)
            (h : ModGL TwistTag.D4.tag L))⁻¹) := by
      rw [hδcoe, ← hFι, hz]
    have e2 : baseChangeGL (algebraMap K₃ L) ((δ₀ (δ₀ z') : ↥(graphFixedRootGroup TwistTag.D4 K₃
        Fr.toRingHom)) : ModGL TwistTag.D4.tag K₃) = Units.map (entrywiseHom FrL)
          (Units.map (entrywiseHom FrL) ((h : ModGL TwistTag.D4.tag L) *
            (Units.map (entrywiseHom FrL) (h : ModGL TwistTag.D4.tag L))⁻¹)) := by
      rw [hδcoe, ← hFι, e1]
    rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul, hz, e1, e2, Subgroup.coe_one,
      map_one]
    simp only [map_mul, map_inv, hF3h]
    group
  have hαhat3 : (MulAut.conj z' * δ₀) ^ 3 = 1 := by
    refine MulEquiv.ext fun y => ?_
    have h3 : ((MulAut.conj z' * δ₀) ^ 3) y =
        (z' * δ₀ z' * δ₀ (δ₀ z')) * y * (z' * δ₀ z' * δ₀ (δ₀ z'))⁻¹ := by
      simp only [pow_three, MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hδ3']
      group
    rw [h3, hN, one_mul, inv_one, mul_one]
    rfl
  have hout : (MulAut.conj z' * δ₀) ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) := by
    intro hin
    have hinn : δ₀ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
        ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) := by
      have h1 : (MulAut.conj z')⁻¹ * (MulAut.conj z' * δ₀) = δ₀ := inv_mul_cancel_left _ _
      rw [← h1]
      exact mul_mem (inv_mem ⟨z', rfl⟩) hin
    exact fieldActor_not_inner hℓ hf hK₃ Fr hFr hinn
  refine ⟨MulAut.conj z' * δ₀, hαhat3, hout, ?_⟩
  have hYle : graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom ≤ adjointGroup TwistTag.D4.tag K₃ :=
    (graphFixedRootGroup_le TwistTag.D4 K₃ Fr.toRingHom).trans inf_le_left
  let incl : ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) →*
      ↥(adjointGroup TwistTag.D4.tag K₃) := Subgroup.inclusion hYle
  let ι₃G : ↥(adjointGroup TwistTag.D4.tag K) →* ↥(adjointGroup TwistTag.D4.tag K₃) :=
    ((baseChangeGL (algebraMap K K₃)).comp (adjointGroup TwistTag.D4.tag K).subtype).codRestrict
      (adjointGroup TwistTag.D4.tag K₃) fun u => baseChangeGL_mem_adjointGroup _ u.2
  have hι₃G : ∀ u, (ι₃G u : ModGL TwistTag.D4.tag K₃) =
      baseChangeGL (algebraMap K K₃) (u : ModGL TwistTag.D4.tag K) := fun _ => rfl
  have hι₃Ginj : Function.Injective ι₃G := fun a b hab =>
    Subtype.ext (baseChangeGL_injective (algebraMap K K₃) (by rw [← hι₃G, ← hι₃G, hab]))
  have hFK : ∀ w : ModGL TwistTag.D4.tag K, Units.map (entrywiseHom Fr.toRingHom)
      (baseChangeGL (algebraMap K K₃) w) = baseChangeGL (algebraMap K K₃) w := fun w => by
    rw [units_map_entrywiseHom_eq_baseChangeGL, baseChangeGL_baseChangeGL]
    have : Fr.toRingHom.comp (algebraMap K K₃) = algebraMap K K₃ :=
      RingHom.ext (graphType_frobenius_algebraMap hK Fr hFr)
    rw [this]
  have hcompat : ∀ u, β (ι₃G u) = ι₃G (α u) := fun u => by
    refine Subtype.ext (baseChangeGL_injective (algebraMap K₃ L) ?_)
    calc baseChangeGL (algebraMap K₃ L) ((β (ι₃G u) : ↥(adjointGroup TwistTag.D4.tag K₃)) :
          ModGL TwistTag.D4.tag K₃) =
        (x * diagramMap TwistTag.D4 L) * Units.map (entrywiseHom FrL)
          (baseChangeGL (algebraMap K₃ L) ((ι₃G u : ↥(adjointGroup TwistTag.D4.tag K₃)) :
            ModGL TwistTag.D4.tag K₃)) * (x * diagramMap TwistTag.D4 L)⁻¹ := hstep _
      _ = (x * diagramMap TwistTag.D4 L) * baseChangeGL ((algebraMap K₃ L).comp (algebraMap K K₃))
          (u : ModGL TwistTag.D4.tag K) * (x * diagramMap TwistTag.D4 L)⁻¹ := by
        rw [hι₃G, hFι, hFK, baseChangeGL_baseChangeGL]
      _ = baseChangeGL (algebraMap K₃ L) ((ι₃G (α u) : ↥(adjointGroup TwistTag.D4.tag K₃)) :
          ModGL TwistTag.D4.tag K₃) := by
        rw [hι₃G, baseChangeGL_baseChangeGL, hα]
        group
  have htw : twistedFixedGroup TwistTag.D4 K₃ Fr.toRingHom =
      graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom :=
    (triality_both_field_orientations_simple_full_ambient_fixed_group (ℓ := ℓ) (d := f) hℓ hf K₃
      hK₃ L 1 (Or.inl rfl) Fr.toRingHom (fun c => by simpa using hFr c) FrL hFrL').2.2.1
  have hΘY : ∀ u : ↥(fixSubgroup α),
      ((ψ (ι₃G u.1) : ↥(adjointGroup TwistTag.D4.tag K₃)) : ModGL TwistTag.D4.tag K₃) ∈
        graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom := by
    intro u
    have hu : α u.1 = u.1 := u.2
    have hβu : β (ι₃G u.1) = ι₃G u.1 := by rw [hcompat, hu]
    have h1 := hcomm (ι₃G u.1)
    rw [hβu] at h1
    rw [← htw, mem_twistedFixedGroup_iff_twistHom]
    refine ⟨(ψ (ι₃G u.1)).2, ?_⟩
    have h2 := congrArg Subtype.val h1
    rw [coe_twistedEntrywiseAut, zpow_one] at h2
    rw [twistHom_apply]
    exact h2
  have hrange : ∀ c : ↥(fixSubgroup (MulAut.conj z' * δ₀)), ∃ u : ↥(fixSubgroup α),
      ι₃G u = ψ⁻¹ (incl c.1) := by
    rintro ⟨c, hc⟩
    have hcfix : (MulAut.conj z' * δ₀) c = c := hc
    have hcm : z₀ * Units.map (entrywiseHom Fr.toRingHom) (c : ModGL TwistTag.D4.tag K₃) * z₀⁻¹ =
        (c : ModGL TwistTag.D4.tag K₃) := by
      have := congrArg Subtype.val hcfix
      rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_inv, hδcoe] at this
      exact this
    have hcL : ((h : ModGL TwistTag.D4.tag L) * (Units.map (entrywiseHom FrL)
        (h : ModGL TwistTag.D4.tag L))⁻¹) * Units.map (entrywiseHom FrL)
          (baseChangeGL (algebraMap K₃ L) (c : ModGL TwistTag.D4.tag K₃)) *
        ((h : ModGL TwistTag.D4.tag L) * (Units.map (entrywiseHom FrL)
          (h : ModGL TwistTag.D4.tag L))⁻¹)⁻¹ =
        baseChangeGL (algebraMap K₃ L) (c : ModGL TwistTag.D4.tag K₃) := by
      have := congrArg (baseChangeGL (algebraMap K₃ L)) hcm
      rw [map_mul, map_mul, map_inv, hz₀eq, ← hFι] at this
      exact this
    obtain ⟨u₃, hu₃⟩ : ∃ u₃ : ↥(adjointGroup TwistTag.D4.tag K₃), u₃ = ψ⁻¹ (incl c) := ⟨_, rfl⟩
    have hψu : ψ u₃ = incl c := by rw [hu₃, MulAut.apply_inv_self]
    have hα₀c : twistedEntrywiseAut TwistTag.D4 1 Fr (incl c) = incl c := by
      refine Subtype.ext ?_
      have hmem := (graphFixedRootGroup_le TwistTag.D4 K₃ Fr.toRingHom) c.2
      have htw := ((mem_twistedFixedGroup_iff_twistHom TwistTag.D4 K₃ Fr.toRingHom).1 hmem).2
      rw [coe_twistedEntrywiseAut, zpow_one]
      rw [twistHom_apply] at htw
      exact htw
    have hψc : baseChangeGL (algebraMap K₃ L) (c : ModGL TwistTag.D4.tag K₃) =
        (h : ModGL TwistTag.D4.tag L) * baseChangeGL (algebraMap K₃ L)
          (u₃ : ModGL TwistTag.D4.tag K₃) * (h : ModGL TwistTag.D4.tag L)⁻¹ := by
      have := hψι u₃
      rw [hψu] at this
      exact this
    have hFu : Units.map (entrywiseHom FrL) (baseChangeGL (algebraMap K₃ L)
        (u₃ : ModGL TwistTag.D4.tag K₃)) = baseChangeGL (algebraMap K₃ L)
          (u₃ : ModGL TwistTag.D4.tag K₃) := by
      have hu : baseChangeGL (algebraMap K₃ L) (u₃ : ModGL TwistTag.D4.tag K₃) =
          (h : ModGL TwistTag.D4.tag L)⁻¹ * baseChangeGL (algebraMap K₃ L)
            (c : ModGL TwistTag.D4.tag K₃) * (h : ModGL TwistTag.D4.tag L) := by
        rw [hψc]; group
      have hFc : Units.map (entrywiseHom FrL) (baseChangeGL (algebraMap K₃ L)
          (c : ModGL TwistTag.D4.tag K₃)) =
          (Units.map (entrywiseHom FrL) (h : ModGL TwistTag.D4.tag L) *
            (h : ModGL TwistTag.D4.tag L)⁻¹) * baseChangeGL (algebraMap K₃ L)
              (c : ModGL TwistTag.D4.tag K₃) * ((h : ModGL TwistTag.D4.tag L) *
                (Units.map (entrywiseHom FrL) (h : ModGL TwistTag.D4.tag L))⁻¹) := by
        calc _ = ((h : ModGL TwistTag.D4.tag L) * (Units.map (entrywiseHom FrL)
              (h : ModGL TwistTag.D4.tag L))⁻¹)⁻¹ * (((h : ModGL TwistTag.D4.tag L) *
                (Units.map (entrywiseHom FrL) (h : ModGL TwistTag.D4.tag L))⁻¹) *
                  Units.map (entrywiseHom FrL) (baseChangeGL (algebraMap K₃ L)
                    (c : ModGL TwistTag.D4.tag K₃)) * ((h : ModGL TwistTag.D4.tag L) *
                      (Units.map (entrywiseHom FrL) (h : ModGL TwistTag.D4.tag L))⁻¹)⁻¹) *
                ((h : ModGL TwistTag.D4.tag L) * (Units.map (entrywiseHom FrL)
                  (h : ModGL TwistTag.D4.tag L))⁻¹) := by group
          _ = _ := by rw [hcL]; group
      rw [hu, map_mul, map_mul, map_inv, hFc]
      group
    have hΦu : Units.map (entrywiseHom Fr.toRingHom) (u₃ : ModGL TwistTag.D4.tag K₃) = u₃ := by
      apply baseChangeGL_injective (algebraMap K₃ L)
      rw [← hFι]
      exact hFu
    have hmemfix : (u₃ : ModGL TwistTag.D4.tag K₃) ∈ entrywiseFixedGroup TwistTag.D4.tag Fr :=
      ⟨u₃.2, hΦu⟩
    rw [CFSG.GH74.GLS.Stage2.Bender.Thm1.entrywiseFixedGroup_D4_eq_fixedFieldImage_of_cube Fr
      hFr3] at hmemfix
    obtain ⟨v, hv, hvu⟩ := hmemfix
    let e := graphTypeFixedEquiv hf hK hK₃ Fr hFr
    have hecomp : (algebraMap K K₃).comp e.symm.toRingHom = (fixSubfield Fr).subtype :=
      RingHom.ext fun y => by
        have := graphTypeFixedEquiv_apply hf hK hK₃ Fr hFr (e.symm y)
        rw [RingEquiv.apply_symm_apply] at this
        exact this.symm
    have huKad : baseChangeGL e.symm.toRingHom v ∈ adjointGroup TwistTag.D4.tag K :=
      baseChangeGL_mem_adjointGroup _ hv
    set u : ↥(adjointGroup TwistTag.D4.tag K) := ⟨baseChangeGL e.symm.toRingHom v, huKad⟩ with hudef
    have hu : ι₃G u = u₃ := by
      refine Subtype.ext ?_
      rw [hι₃G]
      change baseChangeGL (algebraMap K K₃) (baseChangeGL e.symm.toRingHom v) = _
      rw [baseChangeGL_baseChangeGL, hecomp]
      exact hvu
    have hβu : β u₃ = u₃ := by
      have h1 := hcomm u₃
      rw [hψu, hα₀c] at h1
      refine ψ.injective ?_
      rw [← h1, hψu]
    have hαu : α u = u := by
      refine hι₃Ginj ?_
      calc ι₃G (α u) = β (ι₃G u) := (hcompat u).symm
        _ = β u₃ := by rw [hu]
        _ = u₃ := hβu
        _ = ι₃G u := hu.symm
    exact ⟨⟨u, hαu⟩, hu.trans hu₃⟩
  have hΘfix : ∀ u : ↥(fixSubgroup α),
      (MulAut.conj z' * δ₀) ⟨((ψ (ι₃G u.1) : ↥(adjointGroup TwistTag.D4.tag K₃)) :
        ModGL TwistTag.D4.tag K₃), hΘY u⟩ =
      ⟨((ψ (ι₃G u.1) : ↥(adjointGroup TwistTag.D4.tag K₃)) : ModGL TwistTag.D4.tag K₃),
        hΘY u⟩ := by
    intro u
    apply Subtype.ext
    apply baseChangeGL_injective (algebraMap K₃ L)
    have hwF : Units.map (entrywiseHom Fr.toRingHom)
        ((ι₃G u.1 : ↥(adjointGroup TwistTag.D4.tag K₃)) : ModGL TwistTag.D4.tag K₃) =
        ((ι₃G u.1 : ↥(adjointGroup TwistTag.D4.tag K₃)) : ModGL TwistTag.D4.tag K₃) := by
      rw [hι₃G, hFK]
    have hBwF : Units.map (entrywiseHom FrL) (baseChangeGL (algebraMap K₃ L)
        ((ι₃G u.1 : ↥(adjointGroup TwistTag.D4.tag K₃)) : ModGL TwistTag.D4.tag K₃)) =
        baseChangeGL (algebraMap K₃ L)
          ((ι₃G u.1 : ↥(adjointGroup TwistTag.D4.tag K₃)) : ModGL TwistTag.D4.tag K₃) := by
      rw [hFι, hwF]
    have hψc := hψι (ι₃G u.1)
    rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, hδcoe]
    change baseChangeGL (algebraMap K₃ L) (z₀ * Units.map (entrywiseHom Fr.toRingHom)
        ((ψ (ι₃G u.1) : ↥(adjointGroup TwistTag.D4.tag K₃)) : ModGL TwistTag.D4.tag K₃) * z₀⁻¹) =
      baseChangeGL (algebraMap K₃ L)
        ((ψ (ι₃G u.1) : ↥(adjointGroup TwistTag.D4.tag K₃)) : ModGL TwistTag.D4.tag K₃)
    rw [map_mul, map_mul, map_inv, hz₀eq, ← hFι, hψc]
    simp only [map_mul, map_inv, hBwF]
    group
  let Θ : ↥(fixSubgroup α) →* ↥(fixSubgroup (MulAut.conj z' * δ₀)) :=
    { toFun := fun u => ⟨⟨((ψ (ι₃G u.1) : ↥(adjointGroup TwistTag.D4.tag K₃)) :
        ModGL TwistTag.D4.tag K₃), hΘY u⟩, hΘfix u⟩
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        apply Subtype.ext
        simp only [Subgroup.coe_mul, map_mul] }
  have hΘinj : Function.Injective Θ := fun a b hab => by
    have h1 := congrArg (fun y : ↥(fixSubgroup (MulAut.conj z' * δ₀)) =>
      ((y.1 : ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)) : ModGL TwistTag.D4.tag K₃)) hab
    have h2 : ψ (ι₃G a.1) = ψ (ι₃G b.1) := Subtype.ext h1
    exact Subtype.ext (hι₃Ginj (ψ.injective h2))
  have hΘsurj : Function.Surjective Θ := fun c => by
    obtain ⟨u, hu⟩ := hrange c
    refine ⟨u, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    have h1 : ψ (ι₃G u.1) = incl c.1 := by rw [hu, MulAut.apply_inv_self]
    have h2 := congrArg Subtype.val h1
    exact h2
  exact ⟨(MulEquiv.ofBijective Θ ⟨hΘinj, hΘsurj⟩)⟩

theorem exists_dual_fixEquiv_one {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f)
    (α : MulAut (adjointGroup Tag.D4 K)) (hα3 : α ^ 3 = 1) (g : adjointGroup Tag.D4 K)
    (a : Fin Tag.D4.rank → Kˣ)
    (hα : α = MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K 1)) :
    ∃ (K₃ : Type) (_ : Field K₃) (_ : Finite K₃) (Fr : K₃ ≃+* K₃),
      Nat.card K₃ = (ℓ ^ f) ^ 3 ∧ (∀ c, Fr c = c ^ (ℓ ^ f)) ∧
      ∃ φ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom), φ ^ 3 = 1 ∧
        φ ∉ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) →*
          MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)).range ∧
        Nonempty (↥(fixSubgroup α) ≃* ↥(fixSubgroup φ)) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨K₃, _, _, _, _, hK₃, Fr, hFr⟩ := graphType_exists_ext hf K hK
  set L := AlgebraicClosure K₃ with hL
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K₃ L).injective ℓ
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K₃
  set ιK : K →+* K₃ := algebraMap K K₃ with hιK
  set ιL : K₃ →+* L := algebraMap K₃ L with hιL
  set ιLK : K →+* L := ιL.comp ιK with hιLK
  set x : ModGL Tag.D4 L := baseChangeGL ιLK ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a)
    with hxdef
  have hx : x ∈ adjointGroup Tag.D4 L := by
    rw [hxdef, map_mul, baseChangeGL_rootDiagUnit]
    exact mul_mem (CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup _ g.2)
      (exceptional_Lang_adjoint_diagonal_lift Tag.D4 L _).1
  have hFrc : (iterateFrobenius L ℓ f).comp ιLK = ιLK := by
    ext c
    simp only [RingHom.comp_apply, iterateFrobenius_def, hιLK, ← map_pow]
    rw [← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hxF : Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x = x := by
    rw [hxdef, units_map_entrywiseHom_eq_baseChangeGL, baseChangeGL_baseChangeGL, hFrc]
  have hM : ∀ u : adjointGroup Tag.D4 K, baseChangeGL ιLK (α u : ModGL Tag.D4 K) =
      (x * d4P L ^ 1) * baseChangeGL ιLK (u : ModGL Tag.D4 K) * (x * d4P L ^ 1)⁻¹ := by
    intro u
    have h := graphType_baseChange_normalForm_one ιLK g a 1 u
    rw [← hα] at h
    exact h
  have hαx : ∀ u : adjointGroup Tag.D4 K, baseChangeGL ιLK (α u : ModGL Tag.D4 K) =
      x * (d4P L * baseChangeGL ιLK (u : ModGL Tag.D4 K) * (d4P L)⁻¹) * x⁻¹ := by
    intro u
    rw [hM u, pow_one]
    group
  have hxP : (x * d4P L) ^ 3 = 1 := by
    have := graphType_cube_eq_one ιLK α hα3 g a 1 hx hM
    rwa [pow_one] at this
  set g₃ : adjointGroup Tag.D4 K₃ := ⟨baseChangeGL ιK (g : ModGL Tag.D4 K),
    CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup _ g.2⟩ with hg₃
  set a₃ : Fin Tag.D4.rank → K₃ˣ := fun i => Units.map ιK.toMonoidHom (a i) with ha₃
  have hx3' : (g₃ : ModGL Tag.D4 K₃) * rootDiagUnit Tag.D4 a₃ =
      baseChangeGL ιK ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a) := by
    rw [map_mul, baseChangeGL_rootDiagUnit]
  have hx3 : baseChangeGL ιL ((g₃ : ModGL Tag.D4 K₃) * rootDiagUnit Tag.D4 a₃) = x := by
    rw [hx3', hxdef, baseChangeGL_baseChangeGL]
  exact ⟨K₃, inferInstance, inferInstance, Fr, hK₃, hFr,
    dual_fixEquiv_ambient hf K hK K₃ hK₃ Fr hFr L x hx hxF hxP
      (MulAut.conj g₃ * (exactNormalAut Tag.D4 K₃ a₃ Fr 0 * d4Graph K₃ 1))
      (fun u => by
        have h := graphType_baseChange_normalForm L ιL g₃ a₃ Fr 1 u
        rw [hx3] at h
        exact h)
      α hαx⟩

theorem exists_dual_fixEquiv {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f)
    (α : MulAut (adjointGroup Tag.D4 K)) (hα3 : α ^ 3 = 1) (g : adjointGroup Tag.D4 K)
    (a : Fin Tag.D4.rank → Kˣ) {ε : ℕ} (hε : ε = 1 ∨ ε = 2)
    (hα : α = MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K ε)) :
    ∃ (K₃ : Type) (_ : Field K₃) (_ : Finite K₃) (Fr : K₃ ≃+* K₃),
      Nat.card K₃ = (ℓ ^ f) ^ 3 ∧ (∀ c, Fr c = c ^ (ℓ ^ f)) ∧
      ∃ φ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom), φ ^ 3 = 1 ∧
        φ ∉ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) →*
          MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)).range ∧
        Nonempty (↥(fixSubgroup α) ≃* ↥(fixSubgroup φ)) := by
  rcases hε with rfl | rfl
  · exact exists_dual_fixEquiv_one hf K hK α hα3 g a hα
  · obtain ⟨g', a', hinv⟩ := graphType_inv_normalForm g a
    rw [← hα] at hinv
    have h3' : α⁻¹ ^ 3 = 1 := by rw [inv_pow, hα3, inv_one]
    obtain ⟨K₃, _, _, Fr, hK₃, hFr, φ, hφ3, hφout, ⟨e⟩⟩ :=
      exists_dual_fixEquiv_one hf K hK α⁻¹ h3' g' a' hinv
    exact ⟨K₃, inferInstance, inferInstance, Fr, hK₃, hFr, φ, hφ3, hφout,
      ⟨(MulEquiv.subgroupCongr (fixSubgroup_inv_eq α).symm).trans e⟩⟩

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual
