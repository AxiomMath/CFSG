module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LinearBlocks
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263SDLinLift
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.Foundations
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.TopScalarLiftSquare
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.SD.Lin

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.CALinearPrimary CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

section Abstract

variable {K : Type} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem exists_primary_ne_id {x : Module.End K V} (hsq : Squarefree (minpoly K x))
    {y : LinearMap.GeneralLinearGroup K V} (hy : y ≠ 1) :
    ∃ h ∈ primaryFactors x, ∃ v ∈ primaryComponent x h, (y : Module.End K V) v ≠ v := by
  by_contra hcon
  push Not at hcon
  apply hy
  have h1 : ((y : LinearMap.GeneralLinearGroup K V) : Module.End K V) = LinearMap.id :=
    ext_primaryComponent hsq (fun a ha v hv => hcon a ha v hv)
  exact Units.ext (by rw [h1]; rfl)

theorem eq_of_smul_of_two_pow (h2 : (2 : K) = 0) {x : Module.End K V} {h : K[X]}
    (hh : h ∈ primaryFactors x) {y : LinearMap.GeneralLinearGroup K V} {a : ℕ}
    (hy : y ^ (2 ^ a) = 1) {c : AdjoinRoot h}
    (hc : ∀ v : primaryComponent x h,
      ((y : Module.End K V) (v : V)) = ((c • v : primaryComponent x h) : V))
    (v : primaryComponent x h) : (y : Module.End K V) (v : V) = (v : V) := by
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  haveI : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  haveI hchar : CharP (AdjoinRoot h) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AdjoinRoot h)).injective 2
  have hpow : ∀ k : ℕ, ∀ w : primaryComponent x h,
      ((((y ^ k : LinearMap.GeneralLinearGroup K V) : Module.End K V)) (w : V)) =
        ((c ^ k • w : primaryComponent x h) : V) := by
    intro k
    induction k with
    | zero =>
      intro w
      simp
    | succ k ih =>
      intro w
      have h1 : ((y ^ (k + 1) : LinearMap.GeneralLinearGroup K V) : Module.End K V) (w : V) =
          ((y ^ k : LinearMap.GeneralLinearGroup K V) : Module.End K V)
            ((y : Module.End K V) (w : V)) := by
        rw [pow_succ, Units.val_mul]
        rfl
      rw [h1, hc w, ih (c • w), smul_smul, ← pow_succ]
  have h3 := hpow (2 ^ a) v
  rw [hy] at h3
  by_cases hv0 : v = 0
  · subst hv0
    simp
  · have h4 : c ^ (2 ^ a) • v = v := Subtype.ext (by simpa using h3.symm)
    have h5 : (c ^ (2 ^ a) - 1) • v = 0 := by rw [sub_smul, h4, one_smul, sub_self]
    have h6 : c ^ (2 ^ a) - 1 = 0 := (smul_eq_zero.1 h5).resolve_right hv0
    have h7 : (c - 1) ^ (2 ^ a) = 0 := by
      rw [sub_pow_char_pow (p := 2), one_pow, sub_eq_zero]
      exact sub_eq_zero.1 h6
    have h8 : c = 1 := sub_eq_zero.1 (pow_eq_zero_iff (pow_ne_zero a two_ne_zero) |>.1 h7)
    rw [hc v, h8, one_smul]

theorem exists_smul_of_finrank_le_one {E W : Type*} [Field E] [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] (hW : Module.finrank E W ≤ 1) (γ : Module.End E W) :
    ∃ c : E, ∀ w : W, γ w = c • w := by
  obtain ⟨v₀, hv₀⟩ := finrank_le_one_iff.1 hW
  obtain ⟨c, hc⟩ := hv₀ (γ v₀)
  refine ⟨c, fun w => ?_⟩
  obtain ⟨r, rfl⟩ := hv₀ w
  rw [map_smul, ← hc, smul_comm]

end Abstract

section Matrix

variable {K : Type} [Field K] [Finite K] {n : ℕ}

local notation "𝒱" => (Fin n → K)

theorem exists_good_block (h2 : (2 : K) = 0) {A : GL (Fin n) K}
    (hsq : Squarefree (minpoly K (glA A : Module.End K 𝒱)))
    {y : LinearMap.GeneralLinearGroup K 𝒱} (hyc : y ∈ gl_centralizer (glA A)) {a : ℕ}
    (hy : y ^ (2 ^ a) = 1) (hy1 : y ≠ 1)
    (hbad : ∀ h ∈ primaryFactors (glA A : Module.End K 𝒱),
      primaryMultiplicity (glA A : Module.End K 𝒱) h = 2 → Nat.card (AdjoinRoot h) ≤ 3 →
        ∀ v ∈ primaryComponent (glA A : Module.End K 𝒱) h, (y : Module.End K 𝒱) v = v) :
    ∃ h ∈ primaryFactors (glA A : Module.End K 𝒱), IsGoodFactor A h ∧
      ∃ v ∈ primaryComponent (glA A : Module.End K 𝒱) h, (y : Module.End K 𝒱) v ≠ v := by
  obtain ⟨h, hh, v, hv, hne⟩ := exists_primary_ne_id hsq hy1
  refine ⟨h, hh, ?_, v, hv, hne⟩
  by_contra hbadh
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  unfold IsGoodFactor at hbadh
  push Not at hbadh
  obtain ⟨hm3, hm2⟩ := hbadh
  by_cases hm : primaryMultiplicity (glA A : Module.End K 𝒱) h ≤ 1
  · obtain ⟨c, hc⟩ := exists_smul_of_finrank_le_one hm
      (commutantRestrict h ⟨(y : Module.End K 𝒱), mem_commutant_of_mem_gl_centralizer hyc⟩)
    exact hne (eq_of_smul_of_two_pow h2 hh hy (c := c) (fun w => congrArg Subtype.val (hc w))
      ⟨v, hv⟩)
  · have hm2' : primaryMultiplicity (glA A : Module.End K 𝒱) h = 2 := by omega
    have hq : Nat.card (AdjoinRoot h) ≤ 3 := by
      have := hm2 (by omega)
      omega
    exact hne (hbad h hh hm2' hq v hv)

theorem exists_noncommuting_in_block (h2 : (2 : K) = 0) {A : GL (Fin n) K}
    (hsq : Squarefree (minpoly K (glA A : Module.End K 𝒱)))
    {y : LinearMap.GeneralLinearGroup K 𝒱} (hyc : y ∈ gl_centralizer (glA A)) {a : ℕ}
    (hy : y ^ (2 ^ a) = 1) {h : K[X]} (hh : h ∈ primaryFactors (glA A : Module.End K 𝒱))
    {v : 𝒱} (hv : v ∈ primaryComponent (glA A : Module.End K 𝒱) h)
    (hne : (y : Module.End K 𝒱) v ≠ v) :
    ∃ g ∈ linearSpecialBlock (glA A) h, g ^ 2 = 1 ∧ y * g ≠ g * y := by
  haveI : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  by_contra hcon
  push Not at hcon
  obtain ⟨c, hc⟩ := exists_smul_of_commute_pow_char hsq hh (ℓ := 2) hyc
    (fun g hg hg2 => hcon g hg hg2)
  exact hne (eq_of_smul_of_two_pow h2 hh hy (c := c) hc ⟨v, hv⟩)

theorem exists_decomp_gl (h2 : (2 : K) = 0) {A : GL (Fin n) K}
    (hsq : Squarefree (minpoly K (glA A : Module.End K 𝒱)))
    {y : LinearMap.GeneralLinearGroup K 𝒱} (hyc : y ∈ gl_centralizer (glA A)) {a : ℕ}
    (hy : y ^ (2 ^ a) = 1) {h : K[X]} (hh : h ∈ primaryFactors (glA A : Module.End K 𝒱)) :
    ∃ w₁ ∈ linearSpecialBlock (glA A) h, ∃ w₂ ∈ gl_centralizer (glA A), y = w₂ * w₁ ∧
      ∀ g ∈ linearSpecialBlock (glA A) h, w₂ * g = g * w₂ := by
  classical
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  haveI : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  haveI hchar : CharP (AdjoinRoot h) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AdjoinRoot h)).injective 2
  set γ : blockGL (glA A : Module.End K 𝒱) h := glCentralizerEquivPi hsq ⟨y, hyc⟩ ⟨h, hh⟩ with hγ
  have hγp : γ ^ (2 ^ a) = 1 := by
    have h1 : (⟨y, hyc⟩ : gl_centralizer (glA A)) ^ (2 ^ a) = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hy)
    have h2' := congrArg (fun z => glCentralizerEquivPi hsq z ⟨h, hh⟩) h1
    simpa only [map_pow, map_one, Pi.pow_apply, Pi.one_apply] using h2'
  have hdet : LinearMap.det (γ : Module.End (AdjoinRoot h)
      (primaryComponent (glA A : Module.End K 𝒱) h)) = 1 := by
    have h3 : LinearMap.det (((γ ^ (2 ^ a) : blockGL (glA A : Module.End K 𝒱) h) :
        Module.End (AdjoinRoot h) (primaryComponent (glA A : Module.End K 𝒱) h))) = 1 := by
      rw [hγp]
      have h1' : (((1 : blockGL (glA A : Module.End K 𝒱) h) :
          Module.End (AdjoinRoot h) (primaryComponent (glA A : Module.End K 𝒱) h))) = LinearMap.id :=
        rfl
      rw [h1', LinearMap.det_id]
    rw [Units.val_pow_eq_pow_val, map_pow] at h3
    have h4 : (LinearMap.det (γ : Module.End (AdjoinRoot h)
        (primaryComponent (glA A : Module.End K 𝒱) h)) - 1) ^ (2 ^ a) = 0 := by
      rw [sub_pow_char_pow (p := 2), h3, one_pow, sub_self]
    exact sub_eq_zero.1 (pow_eq_zero_iff (pow_ne_zero a two_ne_zero) |>.1 h4)
  let u : _root_.SpecialLinearGroup (AdjoinRoot h) (primaryComponent (glA A : Module.End K 𝒱) h) :=
    ⟨LinearMap.GeneralLinearGroup.generalLinearEquiv _ _ γ,
      Units.ext (by rw [LinearEquiv.coe_det]; exact hdet)⟩
  obtain ⟨g₁, hg₁⟩ := linearSpecialBlockRestrict_surjective hsq hh u
  have hg1t : ∀ t ∈ primaryComponent (glA A : Module.End K 𝒱) h,
      ((g₁ : LinearMap.GeneralLinearGroup K 𝒱) : Module.End K 𝒱) t = (y : Module.End K 𝒱) t := by
    intro t ht
    rw [← coe_linearSpecialBlockRestrict g₁ ⟨t, ht⟩, hg₁]
    rfl
  have hg1c : (g₁ : LinearMap.GeneralLinearGroup K 𝒱) ∈ gl_centralizer (glA A) :=
    linearSpecialBlock_le_centralizer _ _ g₁.2
  refine ⟨g₁, g₁.2, y * (g₁ : LinearMap.GeneralLinearGroup K 𝒱)⁻¹,
    mul_mem hyc (inv_mem hg1c), (inv_mul_cancel_right y _).symm, ?_⟩
  intro g hg
  have hgc : g ∈ gl_centralizer (glA A) := linearSpecialBlock_le_centralizer _ _ hg
  have hw2c : y * (g₁ : LinearMap.GeneralLinearGroup K 𝒱)⁻¹ ∈ gl_centralizer (glA A) :=
    mul_mem hyc (inv_mem hg1c)
  have hw2h : ∀ t ∈ primaryComponent (glA A : Module.End K 𝒱) h,
      ((y * (g₁ : LinearMap.GeneralLinearGroup K 𝒱)⁻¹ : LinearMap.GeneralLinearGroup K 𝒱) :
        Module.End K 𝒱) t = t := by
    intro t ht
    have h1 : ((g₁ : LinearMap.GeneralLinearGroup K 𝒱)⁻¹ : LinearMap.GeneralLinearGroup K 𝒱).1 t ∈
        primaryComponent (glA A : Module.End K 𝒱) h :=
      apply_mem_primaryComponent (mem_gl_centralizer.mp (inv_mem hg1c)) ht
    rw [Units.val_mul]
    change (y : Module.End K 𝒱) (((g₁ : LinearMap.GeneralLinearGroup K 𝒱)⁻¹ :
      LinearMap.GeneralLinearGroup K 𝒱).1 t) = t
    rw [← hg1t _ h1]
    change (((g₁ : LinearMap.GeneralLinearGroup K 𝒱) * (g₁ : LinearMap.GeneralLinearGroup K 𝒱)⁻¹ :
      LinearMap.GeneralLinearGroup K 𝒱) : Module.End K 𝒱) t = t
    rw [mul_inv_cancel]
    rfl
  have hgoff : ∀ j ∈ primaryFactors (glA A : Module.End K 𝒱), j ≠ h →
      ∀ t ∈ primaryComponent (glA A : Module.End K 𝒱) j, (g : Module.End K 𝒱) t = t :=
    fun j hj hjh t ht => hg.2.1 j hj hjh t ht
  refine Units.ext (ext_primaryComponent hsq fun j hj v hv => ?_)
  change ((y * (g₁ : LinearMap.GeneralLinearGroup K 𝒱)⁻¹ : LinearMap.GeneralLinearGroup K 𝒱) :
      Module.End K 𝒱) ((g : Module.End K 𝒱) v) =
    (g : Module.End K 𝒱) ((((y * (g₁ : LinearMap.GeneralLinearGroup K 𝒱)⁻¹ :
      LinearMap.GeneralLinearGroup K 𝒱)) : Module.End K 𝒱) v)
  by_cases hjh : j = h
  · subst hjh
    have hgv : (g : Module.End K 𝒱) v ∈ primaryComponent (glA A : Module.End K 𝒱) j :=
      apply_mem_primaryComponent (mem_gl_centralizer.mp hgc) hv
    rw [hw2h _ hgv, hw2h _ hv]
  · have hwv : ((y * (g₁ : LinearMap.GeneralLinearGroup K 𝒱)⁻¹ : LinearMap.GeneralLinearGroup K 𝒱) :
        Module.End K 𝒱) v ∈ primaryComponent (glA A : Module.End K 𝒱) j :=
      apply_mem_primaryComponent (mem_gl_centralizer.mp hw2c) hv
    rw [hgoff j hj hjh v hv, hgoff j hj hjh _ hwv]

theorem exists_decomp_sl (h2 : (2 : K) = 0) {A : GL (Fin n) K}
    (hsq : Squarefree (minpoly K (glA A : Module.End K 𝒱)))
    {g : Matrix.SpecialLinearGroup (Fin n) K} (hgc : slGL n K g ∈ gl_centralizer (glA A)) {a : ℕ}
    (hg : g ^ (2 ^ a) = 1) {h : K[X]} (hh : h ∈ primaryFactors (glA A : Module.End K 𝒱)) :
    ∃ w₁ ∈ specialFactor A h, ∃ w₂ : Matrix.SpecialLinearGroup (Fin n) K,
      slGL n K w₂ ∈ gl_centralizer (glA A) ∧ (∀ f ∈ specialFactor A h, w₂ * f = f * w₂) ∧
        g = w₂ * w₁ := by
  have hy : (slGL n K g) ^ (2 ^ a) = 1 := by rw [← map_pow, hg, map_one]
  obtain ⟨w₁, hw₁, w₂, hw₂, hyeq, hcomm⟩ := exists_decomp_gl h2 hsq hgc hy hh
  have hw₁det : LinearMap.det (w₁ : Module.End K 𝒱) = 1 :=
    det_eq_one_of_mem_linearSpecialBlock hsq hh hw₁
  obtain ⟨w₁', hw₁'⟩ := mem_range_slGL hw₁det
  have hgdet : LinearMap.det ((slGL n K g : LinearMap.GeneralLinearGroup K 𝒱) : Module.End K 𝒱) = 1 := by
    rw [coe_slGL, LinearMap.det_toLin']
    exact g.2
  have hw₂det : LinearMap.det (w₂ : Module.End K 𝒱) = 1 := by
    have h5 := congrArg (fun z : LinearMap.GeneralLinearGroup K 𝒱 => LinearMap.det (z : Module.End K 𝒱)) hyeq
    simp only [Units.val_mul, map_mul, hgdet, hw₁det, mul_one] at h5
    exact h5.symm
  obtain ⟨w₂', hw₂'⟩ := mem_range_slGL hw₂det
  refine ⟨w₁', ?_, w₂', ?_, ?_, ?_⟩
  · show slGL n K w₁' ∈ linearSpecialBlock (glA A) h
    rw [hw₁']
    exact hw₁
  · rw [hw₂']
    exact hw₂
  · intro f hf
    apply slGL_injective
    rw [map_mul, map_mul, hw₂']
    exact hcomm _ hf
  · apply slGL_injective
    rw [map_mul, hw₂', hw₁', ← hyeq]

end Matrix

end CFSG.LocalAnalysis.GLTheoremA.T263.SD.Lin

end
