module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SymplecticOrder
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SymplecticFixed
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Basic
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Families
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.Monster.Existence.Defs
public import CFSG.Open.MonsterY443Defs
public import CFSG.RankThree.PartOne.KC.SymplecticFullCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Polynomial Module CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCSpFull
  CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.RankThree.Classical (spForm spLin spEnd altPrimaryData_spLin SpPrimaryBlocks)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.Open (IsElemAbelian)

variable {r : ℕ} {K : Type} [Field K]

local notation "PSp" => StatedProj (StatedSp r K)

theorem commute_of_spListedFacts [Finite K] {p : ℕ} (hp : p.Prime)
    (hinj : Function.Injective (MulAut.conj : PSp →* MulAut PSp))
    {H E : Subgroup (MulAut PSp)} (hH : innerAut PSp ≤ H) {g : MulAut PSp}
    (hg : g ∈ localDeltaIn p H E) {a : PSp} (ha : MulAut.conj a ∈ E) (ha1 : a ≠ 1)
    {J : Subgroup PSp} (hF : SpListedFacts p H a J) (hJ : p ∣ Nat.card J) :
    ∀ t ∈ J, g * MulAut.conj t = MulAut.conj t * g := by
  have : Finite PSp := CFSG.ClassicalGroups.Symplectic.finite_statedProj_statedSp r K
  obtain ⟨hJN, -, -, hcomp, -⟩ := hF
  have hTC : J.map (MulAut.conj : PSp →* MulAut PSp) ≤
      H ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut PSp)) := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨hH ⟨y, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subgroup.mem_centralizer_singleton_iff.mp (hJN hy)
  have hle := le_fixSub_of_component hp hinj hg ha
    (fun h => ha1 (hinj (by rw [h, map_one]))) hTC hcomp
    (fun hc => (Nat.Prime.coprime_iff_not_dvd hp).1 hc hJ)
  intro t ht
  have hgt : g t = t := (hle ht : t ∈ fixSub g)
  calc g * MulAut.conj t = g * MulAut.conj t * g⁻¹ * g := by group
    _ = MulAut.conj (g t) * g := by rw [mul_conj_mul_inv]
    _ = MulAut.conj t * g := by rw [hgt]

theorem localDeltaIn_eq_bot_psp {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp3 : 3 < p) (hpℓ : p ≠ ℓ) (hr : 2 ≤ r)
    (hrq : ¬ (r = 2 ∧ ℓ ^ f = 2)) (E : Subgroup (MulAut PSp)) (hEin : E ≤ innerAut PSp)
    (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 2) {H : Subgroup (MulAut PSp)}
    (hH : innerAut PSp ≤ H) : localDeltaIn p H E = ⊥ := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero f hℓ.ne_zero)
  have hp2 : p ≠ 2 := by omega
  have hr1 : 1 ≤ r := by omega
  have hinj := spConj_injective hℓ hf hK hr hrq
  have hEel : CFSG.IsElementaryAbelian p E :=
    { toIsMulCommutative := hE.1
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x =>
        Subtype.ext (hE.2 x x.2) }
  obtain ⟨Ahat, hlift, -⟩ := exists_unique_spPlaneLift hr1 hp hp2 hinj E hEin hEel hEc
  have S : SpPlaneSetup ℓ f p r K Ahat := ⟨hℓ, hf, hK, hp, hp3, hpℓ, hr, hrq, hlift.1, hlift.2.1⟩
  have D := S.decomp
  obtain ⟨hA₀, hcard₀⟩ := comap_conj_plane hinj hEin hEel hEc
  refine eq_bot_iff.2 fun g hg => ?_
  rw [Subgroup.mem_bot]
  have hE1 : ∀ x ∈ Ahat, x ≠ 1 → MulAut.conj (proj r K x) ∈ E ∧ proj r K x ≠ 1 := by
    intro x hxA hx1
    have ha : spInnerLift r K x ∈ E := hlift.2.2.1 ▸ Subgroup.mem_map_of_mem _ hxA
    have ha1 : spInnerLift r K x ≠ 1 := fun h =>
      hx1 (hlift.2.2.2 hxA (one_mem _) (h.trans (map_one _).symm))
    exact ⟨ha, fun h => ha1 (by rw [spInnerLift_apply, h, map_one])⟩
  have hkey : ∀ x ∈ Ahat, x ≠ 1 → ∀ J : Subgroup PSp, SpListedFacts p H (proj r K x) J →
      p ∣ Nat.card J → ∀ t ∈ J, g * MulAut.conj t = MulAut.conj t * g :=
    fun x hxA hx1 J hJ hpJ =>
      commute_of_spListedFacts hp hinj hH hg (hE1 x hxA hx1).1 (hE1 x hxA hx1).2 hJ hpJ
  have hblk : ∀ x ∈ Ahat, x ≠ 1 → ∀ h ∈ primaryFactors (spEnd x), h ≠ X - 1 →
      2 ≤ primaryMultiplicity (spEnd x) h →
        ∀ t ∈ spBlockImage x h, g * MulAut.conj t = MulAut.conj t * g := by
    intro x hxA hx1 h hmem hh1 hm2
    have hFx := symplectic_inner_plane_below_prime_local_core_centralization hℓ hf hK hp hp3 hpℓ
      hr hrq H hH _ hA₀ hcard₀ (proj r K x) (hE1 x hxA hx1).1 (hE1 x hxA hx1).2 x rfl
      (S.orderOf_eq hxA hx1)
    exact hkey x hxA hx1 _ (hFx.1 ⟨h, hmem⟩ hh1 hm2)
      (dvd_card_spBlockImage hr1 hp hp2 (S.blocks hxA hx1) ⟨h, hmem⟩ hh1 hm2)
  have hact : ∀ M : Subgroup ↥Ahat, Nat.card M = p → spLineSpace M ≠ ⊥ →
      ∀ x (hxA : x ∈ Ahat), (⟨x, hxA⟩ : ↥Ahat) ∈ M → x ≠ 1 →
        ∀ t ∈ spFixedLayerImage x, g * MulAut.conj t = MulAut.conj t * g := by
    intro M hM hVM x hxA hxM hx1
    obtain ⟨hlisted, -, -⟩ := S.spFixedListed D hM hVM hxA hxM hx1
    obtain ⟨u, huM, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hVM
    have hmove : ∃ y ∈ Ahat, spEnd y u ≠ u := by
      by_contra hcon
      push Not at hcon
      have hu₀ : u ∈ spPlaneFix Ahat :=
        CFSG.RankThree.Classical.mem_fixSub.mpr fun a _ => hcon a a.2
      have huo := (Submodule.mem_inf.mp huM).2
      rw [LinearMap.BilinForm.mem_orthogonal_iff] at huo
      have := (D.nondeg none).2 ⟨u, hu₀⟩ fun z => huo z z.2
      exact hu0 (congrArg Subtype.val this)
    obtain ⟨y, hyA, hyu⟩ := hmove
    have hu : u ∈ LinearMap.ker (spEnd x - 1) := by
      rw [D.ker_eq_sup hM hxA hxM hx1]
      exact Submodule.mem_sup_right huM
    have hxy : y * x = x * y := by
      have := S.elem
      exact congrArg Subtype.val (mul_comm' (⟨y, hyA⟩ : ↥Ahat) ⟨x, hxA⟩)
    have hFx := symplectic_inner_plane_below_prime_local_core_centralization hℓ hf hK hp hp3 hpℓ
      hr hrq H hH _ hA₀ hcard₀ (proj r K x) (hE1 x hxA hx1).1 (hE1 x hxA hx1).2 x rfl
      (S.orderOf_eq hxA hx1)
    exact hkey x hxA hx1 _ (hFx.2.1 hlisted) (dvd_card_spFixedLayerImage hr1 hp hp2
      (S.blocks hxA hx1) hlisted hxy (S.pow_eq_one hyA) hu hyu)
  have hlist : ∀ x ∈ Ahat, x ≠ 1 → CentralizesListed g x := by
    intro x hxA hx1
    refine ⟨fun hlisted t ht => ?_, hblk x hxA hx1⟩
    set M : Subgroup ↥Ahat := Subgroup.zpowers ⟨x, hxA⟩ with hMdef
    have hM : Nat.card M = p := by
      rw [hMdef, Nat.card_zpowers, Subgroup.orderOf_mk, S.orderOf_eq hxA hx1]
    have hxM : (⟨x, hxA⟩ : ↥Ahat) ∈ M := Subgroup.mem_zpowers _
    by_cases hVM : spLineSpace M = ⊥
    ·
      obtain ⟨M₁, -, hM₁, -, -, hV₁, -⟩ := D.two_active
      obtain ⟨t₁, ht₁, ht₁1⟩ := S.exists_ne_one_mem hM₁
      have ht₁1' : (t₁ : StatedSp r K) ≠ 1 := fun h => ht₁1 (Subtype.ext h)
      have hkerx : LinearMap.ker (spEnd x - 1) = spPlaneFix Ahat := by
        rw [D.ker_eq_sup hM hxA hxM hx1, hVM, sup_bot_eq]
      have hker₁ : LinearMap.ker (spEnd (t₁ : StatedSp r K) - 1) =
          spPlaneFix Ahat ⊔ spLineSpace M₁ := D.ker_eq_sup hM₁ t₁.2 ht₁ ht₁1'
      have hle : spFixedFactor x ≤ spFixedFactor (t₁ : StatedSp r K) :=
        spFixedFactor_le_of_ker_le (altPrimaryData_spLin S.p_cast_ne_zero (S.pow_eq_one hxA))
          (altPrimaryData_spLin S.p_cast_ne_zero (S.pow_eq_one t₁.2))
          (D.nondegenerate_ker hM hxA hxM hx1) (by rw [hkerx, hker₁]; exact le_sup_left)
      obtain ⟨hlisted₁, -, -⟩ := S.spFixedListed D hM₁ hV₁ t₁.2 ht₁ ht₁1'
      have h42 : ¬ (spFixedDim (t₁ : StatedSp r K) = 4 ∧ Nat.card K = 2) := by
        rintro ⟨hd4, hK2⟩
        have hdisj : spPlaneFix Ahat ⊓ spLineSpace M₁ = ⊥ := by
          refine eq_bot_iff.2 fun u hu => ?_
          obtain ⟨hu₀, hu₁⟩ := Submodule.mem_inf.mp hu
          have huo := (Submodule.mem_inf.mp hu₁).2
          rw [LinearMap.BilinForm.mem_orthogonal_iff] at huo
          have := (D.nondeg none).2 ⟨u, hu₀⟩ fun z => huo z z.2
          exact (Submodule.mem_bot K).mpr (congrArg Subtype.val this)
        have hsum := Submodule.finrank_sup_add_finrank_inf_eq (spPlaneFix Ahat) (spLineSpace M₁)
        rw [hdisj, finrank_bot, add_zero, ← hker₁, ← spFixedDim_eq_finrank_ker, hd4] at hsum
        have h0 : 2 ≤ Module.finrank K (spPlaneFix Ahat) := by
          rw [← hkerx, ← spFixedDim_eq_finrank_ker]
          exact hlisted.1
        obtain ⟨hpos, hdvd⟩ := D.dim_dvd M₁ hM₁ hV₁
        have h1 := (four_le_lcm_of_small (Or.inl hK2) hp hp3).trans (Nat.le_of_dvd hpos hdvd)
        omega
      have himg₁ : spFixedLayerImage (t₁ : StatedSp r K) =
          (spFixedFactor (t₁ : StatedSp r K)).map (proj r K) := by
        simp [spFixedLayerImage, hlisted₁, h42]
      have hlayer : spFixedLayerImage x ≤ (spFixedFactor x).map (proj r K) := by
        rw [spFixedLayerImage_eq]
        refine Subgroup.map_mono ?_
        unfold spFixedLayerS
        split_ifs <;> first | exact commutator_le_self _ | exact le_rfl
      have htmem : t ∈ spFixedLayerImage (t₁ : StatedSp r K) := by
        rw [himg₁]
        exact Subgroup.map_mono hle (hlayer ht)
      exact hact M₁ hM₁ hV₁ _ t₁.2 ht₁ ht₁1' t htmem
    · exact hact M hM hVM x hxA hxM hx1 t ht
  exact S.eq_one_of_centralizes hlist

end CFSG.HardMathSupport.Timmesfeld.CrossChar
