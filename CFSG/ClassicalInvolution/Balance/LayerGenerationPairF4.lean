module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairExc
public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairF4Data
public import CFSG.ClassicalInvolution.Balance.LayerGenerationRoots
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalF4
public import CFSG.LieType.Chevalley.OddToralInvolutionComponents
public import CFSG.LieType.Chevalley.PinnedBridge
public import CFSG.LieType.Chevalley.RootCharacterConjugation
public import CFSG.LieType.Chevalley.SignCharacterMasks
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.ClassicalInvolution.Balance.BootstrapDischarge
public import CFSG.ClassicalInvolution.Balance.LayerGenerationInner
public import CFSG.ClassicalInvolution.Balance.LayerGenerationTriple
public import CFSG.ClassicalInvolution.Balance.PassTwoFinal
public import CFSG.ClassicalInvolution.Generic.InductionMain
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalE6
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalE7
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCLayer
public import CFSG.ClassicalInvolution.Models.Transfer
public import CFSG.ClassicalInvolution.Models.UnitaryPairs
public import CFSG.ClassicalInvolution.RouteD.TypeAChain
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.BadTwoComponentSubgroup
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieClassical
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieE6E7Triality
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.SignalizerFunctor
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {F : Type} [Field F]

section Elements

@[expose] noncomputable def xk (γ : Fin Tag.F4.rank → ℤ) (c : F) : ↥(adjointGroup .F4 F) :=
  ⟨pinnedX .F4 F γ c, pinnedX_mem_adjointGroup γ c⟩

theorem xk_neg (γ : Fin Tag.F4.rank → ℤ) (c : F) : (xk γ c)⁻¹ = xk γ (-c) :=
  Subtype.ext (pinnedX_neg .F4 F γ c)

theorem mem_rootGroup_iff_xk {γ : Fin Tag.F4.rank → ℤ} (hγ : IsRoot .F4 γ)
    {x : ↥(adjointGroup .F4 F)} :
    x ∈ rootGroup (rootOperatorFamily .F4) F γ ↔ ∃ c : F, x = xk γ c := by
  rw [rootGroup_of_isRoot hγ, ← (rootOperatorFamily .F4).subgroupOf_rootSubgroup_eq F ⟨γ, hγ⟩,
    Subgroup.mem_subgroupOf, mem_rootSubgroup]
  exact ⟨fun ⟨c, hc⟩ => ⟨c, Subtype.ext hc.symm⟩, fun ⟨c, hc⟩ => ⟨c, by rw [hc]; rfl⟩⟩

theorem rootGroup_le_centralizer_of_rootChar_eq_one {γ : Fin Tag.F4.rank → ℤ} (hγ : IsRoot .F4 γ)
    {b : Fin Tag.F4.rank → Fˣ} (hb : rootChar b γ = 1) {u : ↥(adjointGroup .F4 F)}
    (hu : (u : ModGL .F4 F) = rootDiagUnit .F4 b) :
    rootGroup (rootOperatorFamily .F4) F γ ≤
      Subgroup.centralizer ({u} : Set ↥(adjointGroup .F4 F)) := by
  intro x hx
  obtain ⟨c, rfl⟩ := (mem_rootGroup_iff_xk hγ).1 hx
  refine Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext ?_)
  have h := rootDiagUnit_conj_pinnedX b hγ c
  rw [hb, Units.val_one, one_mul] at h
  show pinnedX .F4 F γ c * (u : ModGL .F4 F) = (u : ModGL .F4 F) * pinnedX .F4 F γ c
  rw [hu]
  exact (mul_inv_eq_iff_eq_mul.1 h).symm

end Elements

section Signs

theorem rootChar_mul_tuple' (a b : Fin Tag.F4.rank → Fˣ) (v : Fin Tag.F4.rank → ℤ) :
    rootChar (a * b) v = rootChar a v * rootChar b v := by
  simp only [rootChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

theorem rootChar_eq_one_or_eq_neg_one (hF2 : ringChar F ≠ 2) {b : Fin Tag.F4.rank → Fˣ}
    (hb : ∀ i, b i = 1 ∨ b i = -1) (v : Fin Tag.F4.rank → ℤ) :
    rootChar b v = 1 ∨ rootChar b v = -1 := by
  rw [rootChar_eq_intUnitsMap hF2 hb v]
  generalize maskChar (signTupleBits b) (Multiplicative.ofAdd v) = u
  rcases Int.units_eq_one_or u with rfl | rfl
  · exact Or.inl (map_one _)
  · exact Or.inr (Units.ext (by simp))

theorem rootChar_eq_one_iff_mod_two (hF2 : ringChar F ≠ 2) {b : Fin Tag.F4.rank → Fˣ}
    (hb : ∀ i, b i = 1 ∨ b i = -1) (v : Fin Tag.F4.rank → ℤ) :
    rootChar b v = 1 ↔ maskPairing (signTupleBits b) v % 2 = 0 := by
  rw [rootChar_eq_intUnitsMap hF2 hb v, map_eq_one_iff _ (intUnitsMap_injective hF2),
    maskChar_apply, neg_one_zpow_eq_one_iff, Int.even_iff]

theorem iform_neg_self (γ : Fin Tag.F4.rank → ℤ) : iform (-γ) (-γ) = iform γ γ := by
  rw [← neg_one_smul ℤ γ, iform_smul_left, iform_smul_right]
  ring

end Signs

section Commutator

theorem mem_of_commutator_formula (hF2 : ringChar F ≠ 2) {s β : Fin Tag.F4.rank → ℤ}
    (hs : IsRoot .F4 s) (hβ : IsRoot .F4 β) (hne : s ≠ β) (hne' : s ≠ -β)
    (hcp : commPairs .F4 s β = [(1, 1), (2, 1)]) {N : Subgroup ↥(adjointGroup .F4 F)}
    (hβN : ∀ d : F, xk β d ∈ N) (h2N : ∀ w : F, xk (2 • s + β) w ∈ N)
    (hconj : ∀ c : F, xk s c * xk β 1 * (xk s c)⁻¹ ∈ N) (w : F) : xk (s + β) w ∈ N := by
  obtain ⟨C, hC, hform⟩ := exists_pinnedX_commFormula_F4 hs hβ hne hne'
  have h11 : ((1 : ℕ), (1 : ℕ)) ∈ commPairs .F4 s β := by
    rw [hcp]
    simp
  obtain ⟨hC1, hC2⟩ := hC (1, 1) h11
  have hunit : ((C (1, 1) : ℤ) : F) ≠ 0 := by
    have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF2
    have hcases : C (1, 1) = 1 ∨ C (1, 1) = -1 ∨ C (1, 1) = 2 ∨ C (1, 1) = -2 := by
      rcases abs_cases (C (1, 1)) with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    rcases hcases with h | h | h | h <;> simp [h, h2]
  set c : F := w / (C (1, 1) : F) with hc
  have hCc : (C (1, 1) : F) * c = w := by
    rw [hc]
    field_simp
  have h := hform F c 1
  rw [hcp] at h
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_smul,
    pow_one, one_pow, hCc] at h
  have hK : xk s c * xk β 1 * xk s (-c) * xk β (-1) =
      xk (s + β) w * xk (2 • s + β) ((C (2, 1) : F) * c ^ 2) := Subtype.ext h
  rw [← xk_neg, ← xk_neg] at hK
  have hA := hconj c
  have hB := N.inv_mem (hβN 1)
  have hX := h2N ((C (2, 1) : F) * c ^ 2)
  have : xk (s + β) w = (xk s c * xk β 1 * (xk s c)⁻¹ * (xk β 1)⁻¹) *
      (xk (2 • s + β) ((C (2, 1) : F) * c ^ 2))⁻¹ := by
    rw [hK, mul_inv_cancel_right]
  rw [this]
  exact N.mul_mem (N.mul_mem hA hB) (N.inv_mem hX)

end Commutator

section Core

theorem rankOneRoot_le_of_signs (hF2 : ringChar F ≠ 2) {g : ↥(adjointGroup .F4 F)}
    {cs : Fin 3 → ↥(adjointGroup .F4 F)} {bs : Fin 3 → Fin Tag.F4.rank → Fˣ}
    (hbs : ∀ i j, bs i j = 1 ∨ bs i j = -1)
    (hcs : ∀ i, ((g⁻¹ * cs i * g : ↥(adjointGroup .F4 F)) : ModGL .F4 F) =
      rootDiagUnit .F4 (bs i))
    (htri : ∀ γ : Fin Tag.F4.rank → ℤ, ∃ i, rootChar (bs i) γ = 1)
    {H : Subgroup ↥(adjointGroup .F4 F)}
    (hgood : ∀ R ∈ Generic.fundamentalSubgroups .F4 (f4Datum F),
      (∃ i, R ≤ Subgroup.centralizer ({cs i} : Set ↥(adjointGroup .F4 F))) → R ≤ H)
    {γ : Fin Tag.F4.rank → ℤ} (hγ : IsRoot .F4 γ) : rankOneRoot (f4Datum F) g γ ≤ H := by
  have hcent : ∀ (i : Fin 3) (x : ↥(adjointGroup .F4 F)) (δ : Fin Tag.F4.rank → ℤ), IsRoot .F4 δ →
      rootChar (bs i) δ = 1 → x * (g⁻¹ * cs i * g) = (g⁻¹ * cs i * g) * x →
      rankOneRoot (f4Datum F) (g * x) δ ≤ Subgroup.centralizer ({cs i} : Set _) := by
    intro i x δ hδ hχ hx
    refine map_conj_le_centralizer fun r hr => ?_
    have hu : (g * x)⁻¹ * cs i * (g * x) = g⁻¹ * cs i * g := by
      calc (g * x)⁻¹ * cs i * (g * x) = x⁻¹ * ((g⁻¹ * cs i * g) * x) := by group
        _ = x⁻¹ * (x * (g⁻¹ * cs i * g)) := by rw [hx]
        _ = g⁻¹ * cs i * g := by group
    rw [hu]
    have hle : (f4Datum F).rootGroup δ ⊔ (f4Datum F).rootGroup (-δ) ≤
        Subgroup.centralizer ({g⁻¹ * cs i * g} : Set _) :=
      sup_le (rootGroup_le_centralizer_of_rootChar_eq_one hδ hχ (hcs i))
        (rootGroup_le_centralizer_of_rootChar_eq_one (IsRoot.neg hδ)
          (by rw [rootChar_neg_eq_inv, hχ, inv_one]) (hcs i))
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hr)).symm
  have hmemF : ∀ (x : ↥(adjointGroup .F4 F)) (δ : Fin Tag.F4.rank → ℤ), IsRoot .F4 δ →
      iform δ δ = 4 → rankOneRoot (f4Datum F) x δ ∈ Generic.fundamentalSubgroups .F4 (f4Datum F) :=
    fun x δ hδ h => ⟨x, δ, Or.inl (ModelFacts.isLongestRoot_f4Datum_of_iform_eq_four hδ h), rfl⟩
  have hlong : ∀ δ, IsRoot .F4 δ → iform δ δ = 4 → rankOneRoot (f4Datum F) g δ ≤ H := by
    intro δ hδ hl
    obtain ⟨i, hi⟩ := htri δ
    have h1 := hcent i 1 δ hδ hi (by rw [one_mul, mul_one])
    rw [mul_one] at h1
    exact hgood _ (hmemF g δ hδ hl) ⟨i, h1⟩
  set N : Subgroup ↥(adjointGroup .F4 F) := H.comap (MulAut.conj g).toMonoidHom with hN
  have hlongN : ∀ δ, IsRoot .F4 δ → iform δ δ = 4 → (f4Datum F).rootGroup δ ≤ N := by
    intro δ hδ hl x hx
    exact hlong δ hδ hl (Subgroup.mem_map_of_mem _ (Subgroup.mem_sup_left hx))
  have hshortN : ∀ s', IsRoot .F4 s' → iform s' s' ≠ 4 → (f4Datum F).rootGroup s' ≤ N := by
    intro s' hs' hl x hx
    obtain ⟨i, hi⟩ := htri s'
    have hi' : maskPairing (signTupleBits (bs i)) s' % 2 = 0 :=
      (rootChar_eq_one_iff_mod_two hF2 (hbs i) s').1 hi
    obtain ⟨s, β, hs, hβ, hβl, hmβ, hsum, hne, hne', hcp, h2root, h2l⟩ :=
      f4_short_witness _ hs' hl hi'
    have hχβ : rootChar (bs i) β = 1 := (rootChar_eq_one_iff_mod_two hF2 (hbs i) β).2 hmβ
    have hχs : rootChar (bs i) s = 1 := by
      have h := rootChar_add (bs i) s β
      rw [hsum, hi, hχβ, mul_one] at h
      exact h.symm
    have hβN : ∀ d : F, xk β d ∈ N := fun d =>
      hlongN β hβ hβl ((mem_rootGroup_iff_xk hβ).2 ⟨d, rfl⟩)
    have h2N : ∀ w : F, xk (2 • s + β) w ∈ N := fun w =>
      hlongN _ h2root h2l ((mem_rootGroup_iff_xk h2root).2 ⟨w, rfl⟩)
    have hconj : ∀ c : F, xk s c * xk β 1 * (xk s c)⁻¹ ∈ N := by
      intro c
      have hxs : xk s c ∈ (f4Datum F).rootGroup s := (mem_rootGroup_iff_xk hs).2 ⟨c, rfl⟩
      have hcomm : xk s c * (g⁻¹ * cs i * g) = (g⁻¹ * cs i * g) * xk s c :=
        Subgroup.mem_centralizer_singleton_iff.1
          (rootGroup_le_centralizer_of_rootChar_eq_one hs hχs (hcs i) hxs)
      have h1 := hcent i (xk s c) β hβ hχβ hcomm
      have h2 := hgood _ (hmemF (g * xk s c) β hβ hβl) ⟨i, h1⟩
      have hy : xk β 1 ∈ (f4Datum F).rootGroup β := (mem_rootGroup_iff_xk hβ).2 ⟨1, rfl⟩
      have h3 : (MulAut.conj (g * xk s c)).toMonoidHom (xk β 1) ∈ H :=
        h2 (Subgroup.mem_map_of_mem _ (Subgroup.mem_sup_left hy))
      show g * (xk s c * xk β 1 * (xk s c)⁻¹) * g⁻¹ ∈ H
      have e : g * (xk s c * xk β 1 * (xk s c)⁻¹) * g⁻¹ =
          (MulAut.conj (g * xk s c)).toMonoidHom (xk β 1) := by
        change g * (xk s c * xk β 1 * (xk s c)⁻¹) * g⁻¹ = g * xk s c * xk β 1 * (g * xk s c)⁻¹
        group
      rw [e]
      exact h3
    obtain ⟨c, rfl⟩ := (mem_rootGroup_iff_xk hs').1 hx
    have := mem_of_commutator_formula hF2 hs hβ hne hne' hcp hβN h2N hconj c
    rwa [hsum] at this
  by_cases hl : iform γ γ = 4
  · exact hlong γ hγ hl
  · show ((f4Datum F).rootGroup γ ⊔ (f4Datum F).rootGroup (-γ)).map (MulAut.conj g).toMonoidHom ≤ H
    rw [Subgroup.map_le_iff_le_comap]
    exact sup_le (hshortN γ hγ hl) (hshortN (-γ) (IsRoot.neg hγ) (by rwa [iform_neg_self]))

end Core

section Main

open CFSG.Assembly.LowTwoRank

theorem commutingGeneration_f4 (hF2 : ringChar F ≠ 2) (𝒯 : Subgroup ↥(adjointGroup .F4 F))
    (hframe : PairFrame 𝒯 (Generic.fundamentalSubgroups .F4 (f4Datum F)))
    (hsign : ∀ u ∈ 𝒯, ∃ b : Fin Tag.F4.rank → Fˣ,
      (∀ i, b i = 1 ∨ b i = -1) ∧ (u : ModGL .F4 F) = rootDiagUnit .F4 b)
    (hgen : ∀ g : ↥(adjointGroup .F4 F),
      ⨆ γ ∈ (f4Datum F).roots, rankOneRoot (f4Datum F) g γ = ⊤) :
    ModelFacts.CommutingGeneration (Generic.fundamentalSubgroups .F4 (f4Datum F)) := by
  intro R₁ hR₁ R₂ hR₂ c₁ hc₁ c₂ hc₂ hz₁ hz₂ hx₁₂ hx₂₁
  obtain ⟨g, hg₁, hg₂⟩ := hframe R₁ hR₁ R₂ hR₂ c₁ hc₁ c₂ hc₂ hz₁ hz₂ hx₁₂ hx₂₁
  obtain ⟨b₁, hb₁, he₁⟩ := hsign _ hg₁
  obtain ⟨b₂, hb₂, he₂⟩ := hsign _ hg₂
  let cs : Fin 3 → ↥(adjointGroup .F4 F) := ![c₁, c₂, c₁ * c₂]
  let bs : Fin 3 → Fin Tag.F4.rank → Fˣ := ![b₁, b₂, b₁ * b₂]
  have hbs : ∀ i j, bs i j = 1 ∨ bs i j = -1 := by
    intro i j
    fin_cases i
    · exact hb₁ j
    · exact hb₂ j
    · show (b₁ * b₂) j = 1 ∨ (b₁ * b₂) j = -1
      rcases hb₁ j with h | h <;> rcases hb₂ j with h' | h' <;> simp [h, h']
  have hcs : ∀ i, ((g⁻¹ * cs i * g : ↥(adjointGroup .F4 F)) : ModGL .F4 F) =
      rootDiagUnit .F4 (bs i) := by
    intro i
    fin_cases i
    · exact he₁
    · exact he₂
    · show ((g⁻¹ * (c₁ * c₂) * g : ↥(adjointGroup .F4 F)) : ModGL .F4 F) =
        rootDiagUnit .F4 (b₁ * b₂)
      have : g⁻¹ * (c₁ * c₂) * g = (g⁻¹ * c₁ * g) * (g⁻¹ * c₂ * g) := by group
      rw [this, rootDiagUnit_mul]
      exact congrArg₂ (· * ·) he₁ he₂
  have htri : ∀ γ : Fin Tag.F4.rank → ℤ, ∃ i : Fin 3, rootChar (bs i) γ = 1 := by
    intro γ
    by_cases h1 : rootChar b₁ γ = 1
    · exact ⟨0, h1⟩
    by_cases h2 : rootChar b₂ γ = 1
    · exact ⟨1, h2⟩
    refine ⟨2, ?_⟩
    show rootChar (b₁ * b₂) γ = 1
    rw [rootChar_mul_tuple', (rootChar_eq_one_or_eq_neg_one hF2 hb₁ γ).resolve_left h1,
      (rootChar_eq_one_or_eq_neg_one hF2 hb₂ γ).resolve_left h2]
    simp
  have hgood : ∀ R ∈ Generic.fundamentalSubgroups .F4 (f4Datum F),
      (∃ i, R ≤ Subgroup.centralizer ({cs i} : Set ↥(adjointGroup .F4 F))) →
        R ≤ ⨆ R ∈ Generic.fundamentalSubgroups .F4 (f4Datum F),
          ⨆ (_ : R ≤ Subgroup.centralizer ({c₁} : Set ↥(adjointGroup .F4 F)) ∨
            R ≤ Subgroup.centralizer ({c₂} : Set ↥(adjointGroup .F4 F)) ∨
            R ≤ Subgroup.centralizer ({c₁ * c₂} : Set ↥(adjointGroup .F4 F))), R := by
    rintro R hR ⟨i, hi⟩
    fin_cases i
    · exact le_iSup₂_of_le R hR (le_iSup_of_le (Or.inl hi) le_rfl)
    · exact le_iSup₂_of_le R hR (le_iSup_of_le (Or.inr (Or.inl hi)) le_rfl)
    · exact le_iSup₂_of_le R hR (le_iSup_of_le (Or.inr (Or.inr hi)) le_rfl)
  rw [← hgen g]
  refine iSup₂_le fun γ hγ => ?_
  exact rankOneRoot_le_of_signs hF2 hbs hcs htri hgood (mem_adjDatum_roots.1 hγ)

variable {p e : ℕ} [Fact p.Prime] [NeZero e]

theorem commutingFundamentalGeneration_f4 (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .F4 0 p e)
    (hframe : PairFrame (ModelFacts.excSignGroup .F4 p e)
      (Generic.fundamentalSubgroups .F4 (Generic.modelUniv .F4 0 p e Fact.out).D)) :
    ModelFacts.CommutingFundamentalGeneration p .F4 0 e :=
  commutingGeneration_f4 (by rw [ringChar.eq (GaloisField p e) p]; exact hp2)
    (ModelFacts.excSignGroup .F4 p e) hframe (fun u hu => ModelFacts.mem_excSignGroup.1 hu)
    (iSup_rankOneRoot_eq_top .F4 0 p e Fact.out trivial hadm)

end Main

end CFSG.ClassicalInvolution.Balance.Bootstrap
