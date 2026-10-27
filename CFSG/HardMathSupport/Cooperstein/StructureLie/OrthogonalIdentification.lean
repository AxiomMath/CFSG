module

public import CFSG.HardMathSupport.Cooperstein.StructureLie.ShapeData
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.Std
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.ArfNondeg
import CFSG.Adapters.ClassicalCatalogReverse
import CFSG.Blueprint.SourceClassicalTransportOrthogonal
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
import CFSG.CharacterTheory.Burnside
import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.Arf
import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.Bridge
import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaFour
import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaSix
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingIsometryBasis
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOMinusFacts
import CFSG.Quasithin.Background.B5FinSp
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Index
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
public import CFSG.ClassicalGroups.Orthogonal.Eichler
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open TauCeti CFSG.Assembly.LowTwoRank CFSG.Adapters.RankTwoModelTransports CFSG.ClassicalModels
  CFSG.LocalAnalysis.ComponentInitial CFSG.AGLEmbedding
  CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration

theorem center_eq_bot_of_mulEquiv {Y Z : Type*} [Group Y] [Group Z] (e : Y ≃* Z)
    (h : Subgroup.center Z = ⊥) : Subgroup.center Y = ⊥ := by
  have hm : (Subgroup.center Y).map e.toMonoidHom = Subgroup.center Z := Subgroup.map_center_eq e
  rw [h] at hm
  exact (Subgroup.map_eq_bot_iff_of_injective (Subgroup.center Y) e.injective).1 hm

noncomputable def commutatorEquivOfEq {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    {H : Subgroup G} {H' : Subgroup G'} (h : H.map (e : G →* G') = H') :
    ↥⁅H, H⁆ ≃* ↥⁅H', H'⁆ :=
  (e.subgroupMap _).trans (MulEquiv.subgroupCongr (by rw [Subgroup.map_commutator, h]))

theorem false_of_isSolvable {Y : Type} [Group Y] (hs : Group.IsSolvable Y)
    (hsimp : IsSimpleGroup (Y ⧸ Subgroup.center Y))
    (hnonab : ∃ a b : Y ⧸ Subgroup.center Y, a * b ≠ b * a) : False := by
  have := hsimp
  have : Group.IsSolvable (Y ⧸ Subgroup.center Y) := inferInstance
  obtain ⟨a, b, hab⟩ := hnonab
  exact hab ((IsSimpleGroup.comm_iff_isSolvable).2 this a b)

noncomputable def statedProjEquivOfEqBot {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] (H : Subgroup (GL ι K)) (h : (StatedScalars ι K).subgroupOf H = (⊥ : Subgroup H)) :
    StatedProj H ≃* H :=
  (QuotientGroup.quotientMulEquivOfEq h : H ⧸ (StatedScalars ι K).subgroupOf H ≃*
    H ⧸ (⊥ : Subgroup H)).trans (QuotientGroup.quotientBot (G := H))

theorem statedScalars_zmod_two (ι : Type) [Fintype ι] [DecidableEq ι] :
    StatedScalars ι (ZMod 2) = ⊥ :=
  CFSG.Open.StatedAPI.statedScalars_zmod_two_eq_bot ι

noncomputable def statedProjEquiv {ι : Type} [Fintype ι] [DecidableEq ι]
    (H : Subgroup (GL ι (ZMod 2))) : StatedProj H ≃* H :=
  statedProjEquivOfEqBot H (by rw [statedScalars_zmod_two]; simp)

noncomputable def orthGLCommutatorEquiv {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (Q : QuadraticForm (ZMod 2) W) :
    ↥⁅orthGL Q, orthGL Q⁆ ≃* ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ :=
  commutatorEquivOfEq (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W)
    (Subgroup.map_comap_eq_self_of_surjective
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W).surjective _)

noncomputable def statedOmegaEquiv {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    {Q₀ : (ι → ZMod 2) → ZMod 2} (φ : V ≃ₗ[ZMod 2] (ι → ZMod 2)) (hφ : ∀ v, Q₀ (φ v) = Q v) :
    ↥(StatedOmega Q₀) ≃* ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ :=
  ((CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι (ZMod 2)).subgroupMap _).trans
    ((MulEquiv.subgroupCongr (statedOmega_map_toLinEquiv_eq φ hφ)).trans
      ((conjAut φ).subgroupMap _).symm)

theorem center_commutator_orthogonal_eq_bot {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V}
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      CFSG.ClassicalGroups.Orthogonal.elementaryGroup Q)
    (h1 : ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q,
      (∀ x ∈ CFSG.ClassicalGroups.Orthogonal.elementaryGroup Q, g * x = x * g) → g = 1) :
    Subgroup.center ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ = ⊥ := by
  have hle : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ≤
      TauCeti.QuadraticMap.orthogonalGroup Q := by
    refine Subgroup.commutator_le.2 fun x hx y hy => ?_
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy)
      (Subgroup.inv_mem _ hx)) (Subgroup.inv_mem _ hy)
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  refine h1 z.1 (hle z.2) fun x hx => ?_
  have := Subgroup.mem_center_iff.1 hz ⟨x, hE ▸ hx⟩
  exact (congrArg Subtype.val this).symm

theorem finite_orthogonalGroup {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (Q : QuadraticForm (ZMod 2) V) :
    Finite ↥(TauCeti.QuadraticMap.orthogonalGroup Q) := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  exact Finite.of_injective (fun g : ↥(TauCeti.QuadraticMap.orthogonalGroup Q) =>
    ((g : V ≃ₗ[ZMod 2] V) : V → V)) fun a b h => Subtype.ext (DFunLike.coe_injective h)

theorem isSolvable_commutator_orthogonal_of_card {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    {a b : ℕ} (h : Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup Q) = 2 ^ a * 3 ^ b) :
    Group.IsSolvable ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  have := finite_orthogonalGroup Q
  have := Fintype.ofFinite ↥(TauCeti.QuadraticMap.orthogonalGroup Q)
  have hs : Group.IsSolvable ↥(TauCeti.QuadraticMap.orthogonalGroup Q) :=
    CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
      Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card]; exact h)
  have hle : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ≤
      TauCeti.QuadraticMap.orthogonalGroup Q := by
    refine Subgroup.commutator_le.2 fun x hx y hy => ?_
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy)
      (Subgroup.inv_mem _ hx)) (Subgroup.inv_mem _ hy)
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)

theorem solvable_of_isPlusSpace_small {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V} {m : ℕ} (hm : m ≤ 2)
    (h : IsPlusSpace Q m) :
    Group.IsSolvable ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  obtain ⟨φ, hφ⟩ := h
  rcases (show m = 0 ∨ m = 1 ∨ m = 2 by omega) with rfl | rfl | rfl
  · have : Subsingleton V := φ.toEquiv.subsingleton
    have : Subsingleton (V ≃ₗ[ZMod 2] V) := ⟨fun f g => by ext x; exact Subsingleton.elim _ _⟩
    infer_instance
  · have e : Q.IsometryEquiv (CFSG.LieType.Universal.Spin.quadPlus 1 (ZMod 2)) :=
      { φ with map_app' := hφ }
    have hc := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_congr e
    have h2 := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_quadPlus (K := ZMod 2) 0
    rw [Nat.card_zmod] at h2
    generalize Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup
      (CFSG.LieType.Universal.Spin.quadPlus (0 + 1) (ZMod 2))) = N at h2 hc
    refine isSolvable_commutator_orthogonal_of_card (a := 1) (b := 0) ?_
    norm_num at h2
    omega
  · have e : Q.IsometryEquiv (CFSG.LieType.Universal.Spin.quadPlus 2 (ZMod 2)) :=
      { φ with map_app' := hφ }
    have hc := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_congr e
    have h2 := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_quadPlus (K := ZMod 2) 1
    rw [Nat.card_zmod] at h2
    generalize Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup
      (CFSG.LieType.Universal.Spin.quadPlus (1 + 1) (ZMod 2))) = N at h2 hc
    refine isSolvable_commutator_orthogonal_of_card (a := 3) (b := 2) ?_
    norm_num [Finset.Icc_self] at h2
    omega

theorem solvable_of_isMinusSpace_one {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V} (h : IsMinusSpace Q 1) :
    Group.IsSolvable ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  obtain ⟨φ, hφ⟩ := h
  have e : Q.IsometryEquiv (CFSG.LieType.Universal.Spin.quadMinus 1 (ZMod 2) 1 1) :=
    { φ with map_app' := hφ }
  have hc := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_congr e
  have h2 := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_quadMinus (K := ZMod 2)
    (b := 1) (c := 1) (by decide) 0
  rw [Nat.card_zmod] at h2
  generalize Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup
    (CFSG.LieType.Universal.Spin.quadMinus (0 + 1) (ZMod 2) 1 1)) = N at h2 hc
  refine isSolvable_commutator_orthogonal_of_card (a := 1) (b := 1) ?_
  norm_num at h2
  omega

theorem exists_typeD_of_stated {Y : Type} [Group Y] {m : ℕ} (hm : 4 ≤ m)
    (θ : Y ≃* StatedProj (StatedOmega (StatedQuadPlus m (ZMod 2)))) :
    ∃ d : TauCeti.ValidLieTypeIndex, (∃ q : TauCeti.PrimePower, q.card = 2 ∧ d.1 = .D m q) ∧
      Nonempty (Y ≃* (TauCeti.CFSGIndex.lie d).Group) := by
  let q : PrimePower := ⟨2, 1, Nat.prime_two, Nat.one_pos⟩
  have hv : (LieTypeIndex.D m q).Valid := by
    rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨hm, not_false⟩
  let d : ValidLieTypeIndex := ⟨.D m q, hv⟩
  obtain ⟨φ⟩ := nonempty_ringEquiv_validIndex_fixedField d (ZMod 2) (by
    simp [ValidLieTypeIndex.fieldOrder, d, q])
  have _ : Finite ↥d.fixedField := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField d
  let e1 : StatedProj (StatedOmega (StatedQuadPlus m (ZMod 2))) ≃*
      StatedProj (StatedOmega (StatedQuadPlus m ↥d.fixedField)) :=
    statedProjCongr (glCongr φ)
    (CFSG.ClassicalInvolution.Upgrade.map_statedOmega φ
      (CFSG.ClassicalInvolution.Upgrade.statedQuadPlus_comp φ))
    (glCongr_statedScalars φ)
  exact ⟨d, ⟨q, by simp [PrimePower.card_def, q], rfl⟩,
    ⟨(θ.trans e1).trans
      (CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid m q hv).symm⟩⟩

theorem exists_typeTwistedD_of_stated {Y : Type} [Group Y] {m : ℕ} (hm : 4 ≤ m)
    (θ : Y ≃* StatedProj (StatedOmega (StatedQuadMinus m (ZMod 2) 1 1))) :
    ∃ d : TauCeti.ValidLieTypeIndex,
      (∃ q : TauCeti.PrimePower, q.card = 2 ∧ d.1 = .twistedD m q) ∧
      Nonempty (Y ≃* (TauCeti.CFSGIndex.lie d).Group) := by
  let q : PrimePower := ⟨2, 1, Nat.prime_two, Nat.one_pos⟩
  have hv : (LieTypeIndex.twistedD m q).Valid := by
    rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨hm, not_false⟩
  let d : ValidLieTypeIndex := ⟨.twistedD m q, hv⟩
  have hirr : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0 := by decide
  obtain ⟨b₀, c₀, hirr₀, ⟨eT⟩⟩ :=
    CFSG.RankThree.PartTwo.Census.Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj_of_valid
      m q hv
  obtain ⟨φ⟩ := nonempty_ringEquiv_validIndex_fixedField d (ZMod 2) (by
    simp [ValidLieTypeIndex.fieldOrder, d, q])
  have _ : Finite ↥d.fixedField := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField d
  obtain ⟨e2⟩ := CFSG.Blueprint.EvenSource.nonempty_statedOmegaMinus_equiv (n := m) (by omega)
    (CFSG.ClassicalInvolution.Upgrade.irreducible_map φ hirr) hirr₀
  let e1 : StatedProj (StatedOmega (StatedQuadMinus m (ZMod 2) 1 1)) ≃*
      StatedProj (StatedOmega (StatedQuadMinus m ↥d.fixedField (φ 1) (φ 1))) :=
    statedProjCongr (glCongr φ)
    (CFSG.ClassicalInvolution.Upgrade.map_statedOmega φ
      (CFSG.ClassicalInvolution.Upgrade.statedQuadMinus_comp (n := m) (b := 1) (c := 1) φ rfl
        rfl))
    (glCongr_statedScalars φ)
  exact ⟨d, ⟨q, by simp [PrimePower.card_def, q], rfl⟩, ⟨((θ.trans e1).trans e2).trans eT.symm⟩⟩

theorem exists_twistedA_of_stated {Y : Type} [Group Y] {E : Type} [Field E] [Finite E]
    (hE : Nat.card E = (2 ^ 1) ^ 2) (θ : Y ≃* StatedProj (StatedSU 4 (2 ^ 1) E)) :
    ∃ d : TauCeti.ValidLieTypeIndex,
      (∃ q : TauCeti.PrimePower, q.card = 2 ∧ d.1 = .twistedA 3 q) ∧
      Nonempty (Y ≃* (TauCeti.CFSGIndex.lie d).Group) := by
  let q : PrimePower := ⟨2, 1, Nat.prime_two, Nat.one_pos⟩
  have hv' : (LieTypeIndex.twistedA 3 q).Valid := by
    rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    simp only [PrimePower.card_def, q]
    refine ⟨⟨by omega, fun h => by omega⟩, ?_⟩
    exact not_false
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let L := GaloisField 2 (2 * 1)
  let _ : Fintype E := Fintype.ofFinite E
  let _ : Fintype L := Fintype.ofFinite L
  have hcard : Fintype.card E = Fintype.card L := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hE,
      GaloisField.card 2 (2 * 1) (by omega)]
    norm_num
  let φ : E ≃+* L := FiniteField.ringEquivOfCardEq hcard
  let e1 := statedProjCongr (glCongr (ι := Fin 4) φ) (glCongr_statedSU φ 4 (2 ^ 1))
    (glCongr_statedScalars φ)
  let eT := CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 3 q hv'
  exact ⟨⟨_, hv'⟩, ⟨q, by simp [PrimePower.card_def, q], rfl⟩, ⟨(θ.trans e1).trans eT.symm⟩⟩

section Sp

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

noncomputable def bilinIsometryGroupEquivIsometryGroup (B : LinearMap.BilinForm (ZMod 2) W) :
    bilinIsometryGroup B ≃*
      CFSG.ComponentClassification.CatalogueBAlternatingIsometry.isometryGroup B :=
  ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W).subgroupMap
      (bilinIsometryGroup B)).trans
    (MulEquiv.subgroupCongr (by
      ext g
      constructor
      · rintro ⟨h, hh, rfl⟩
        exact (CFSG.ComponentClassification.CatalogueBAlternatingIsometry.mem_isometryGroup_iff
          B _).mpr hh
      · intro hg
        refine ⟨(LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W).symm g, ?_,
          (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W).apply_symm_apply g⟩
        exact (CFSG.ComponentClassification.CatalogueBAlternatingIsometry.mem_isometryGroup_iff
          B g).mp hg))

noncomputable def glSymplecticTwoPerm :
    TauCeti.GLSymplectic (Fin 2) (ZMod 2) ≃* Equiv.Perm (Fin 6) :=
  CFSG.Quasithin.B5FinSp.rhoEquiv.symm.trans CFSG.Quasithin.B5FinSp.omegaEquiv

theorem nonempty_commutator_bilinIsometryGroup_alt_six
    [FiniteDimensional (ZMod 2) W] {f : LinearMap.BilinForm (ZMod 2) W}
    (hnd : f.Nondegenerate) (halt : f.IsAlt) (h4 : Module.finrank (ZMod 2) W = 4) :
    Nonempty (↥⁅bilinIsometryGroup f, bilinIsometryGroup f⁆ ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨m, hm, ⟨e⟩⟩ :=
    CFSG.ComponentClassification.CatalogueBAlternatingIsometry.exists_isometryEquiv_symplectic
      f halt hnd
  obtain rfl : m = 2 := by omega
  let ψ : ↥(bilinIsometryGroup f) ≃* Equiv.Perm (Fin 6) :=
    ((bilinIsometryGroupEquivIsometryGroup f).trans e).trans glSymplecticTwoPerm
  have h1 : Subgroup.map (bilinIsometryGroup f).subtype
      ⁅(⊤ : Subgroup ↥(bilinIsometryGroup f)), (⊤ : Subgroup ↥(bilinIsometryGroup f))⁆ =
      ⁅bilinIsometryGroup f, bilinIsometryGroup f⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  let e1 : ↥(⁅(⊤ : Subgroup ↥(bilinIsometryGroup f)), (⊤ : Subgroup ↥(bilinIsometryGroup f))⁆) ≃*
      ↥⁅bilinIsometryGroup f, bilinIsometryGroup f⁆ :=
    (Subgroup.equivMapOfInjective _ (bilinIsometryGroup f).subtype
      (bilinIsometryGroup f).subtype_injective).trans (MulEquiv.subgroupCongr h1)
  have h2 : (⊤ : Subgroup ↥(bilinIsometryGroup f)).map
      (ψ : ↥(bilinIsometryGroup f) →* Equiv.Perm (Fin 6)) = ⊤ := by
    rw [Subgroup.map_top]
    exact MonoidHom.range_eq_top.2 ψ.surjective
  let e2 := commutatorEquivOfEq ψ h2
  have h3 : ⁅(⊤ : Subgroup (Equiv.Perm (Fin 6))), ⊤⁆ = alternatingGroup (Fin 6) := by
    rw [← commutator_def]
    exact alternatingGroup.commutator_perm_eq (by simp)
  exact ⟨e1.symm.trans (e2.trans (MulEquiv.subgroupCongr h3))⟩

end Sp

theorem isOrthogonalTwo_of_orth {Y : Type} [Group Y] {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] (Q : QuadraticForm (ZMod 2) W)
    (hQ : PolarNondeg Q) (e : Y ≃* ↥⁅orthGL Q, orthGL Q⁆)
    (hsimp : IsSimpleGroup (Y ⧸ Subgroup.center Y))
    (hnonab : ∃ a b : Y ⧸ Subgroup.center Y, a * b ≠ b * a) :
    Subgroup.center Y = ⊥ ∧ CFSG.AGLEmbedding.IsOrthogonalTwo Y := by
  obtain ⟨ε, m, hstd, hm⟩ := exists_isStdSpace Q hQ
  let eΩ := e.trans (orthGLCommutatorEquiv Q)
  have hsolv : Group.IsSolvable ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ → False := fun hs => by
    have := hs
    have hY : Group.IsSolvable Y := Group.isSolvable_of_isSolvable_injective
      (f := eΩ.toMonoidHom) eΩ.injective
    exact false_of_isSolvable hY hsimp hnonab
  cases ε
  · have hm1 := hm rfl
    obtain ⟨φ, hφ⟩ := (hstd : IsMinusSpace Q m)
    have hφ' : ∀ v, StatedQuadMinus m (ZMod 2) 1 1 (φ v) = Q v := fun v => by
      rw [← CFSG.LieType.Universal.Spin.coe_quadMinus]; exact hφ v
    let θ0 := eΩ.trans (statedOmegaEquiv φ hφ').symm
    have hcenter : 3 ≤ m →  Subgroup.center Y = ⊥ := fun h3 =>
      center_eq_bot_of_mulEquiv eΩ (center_commutator_orthogonal_eq_bot
        (commutator_orthogonalGroup_eq_of_isMinusSpace (by omega) ⟨φ, hφ⟩)
        fun g hg hc => eq_one_of_commute_elementaryGroup_of_isMinusSpace h3 ⟨φ, hφ⟩ hg hc)
    rcases (show m = 1 ∨ m = 2 ∨ m = 3 ∨ 4 ≤ m by omega) with rfl | rfl | rfl | h4
    · exact (hsolv (solvable_of_isMinusSpace_one ⟨φ, hφ⟩)).elim
    · have e5 := θ0.trans statedOmega_quadMinus_two_mulEquiv_alt5
      exact ⟨center_eq_bot_of_mulEquiv e5 (alternatingGroup.center_eq_bot (by simp)),
        Or.inr ⟨5, Or.inl rfl, ⟨e5⟩⟩⟩
    · have hirr : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0 := by decide
      obtain ⟨E, _, hD, ⟨eSU⟩⟩ :=
        CFSG.ComponentClassification.RankTwoClassical.nonempty_statedOmega_quadMinus_three_equiv
          (K := ZMod 2) (m := 1) (by simp) hirr
      let η := θ0.trans eSU
      have hE := hD.card_eq_sq
      have := hD.finite
      have hnq : ((4 : ℕ), 2 ^ 1) ≠ (3, 2) := by simp
      obtain ⟨-, hcen⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hE
        (by norm_num) hnq
      have hcY := hcenter (by omega)
      have hcSU : Subgroup.center ↥(StatedSU 4 (2 ^ 1) E) = ⊥ :=
        center_eq_bot_of_mulEquiv η.symm hcY
      have hsc : (StatedScalars (Fin 4) E).subgroupOf (StatedSU 4 (2 ^ 1) E) =
          (⊥ : Subgroup ↥(StatedSU 4 (2 ^ 1) E)) := by rw [← hcen]; exact hcSU
      obtain ⟨d, ⟨q, hq2, hd⟩, hne⟩ :=
        exists_twistedA_of_stated hE (η.trans (statedProjEquivOfEqBot _ hsc).symm)
      exact ⟨hcY, Or.inl ⟨d, ⟨3, q, hq2, Or.inr (Or.inr ⟨rfl, hd⟩)⟩, hne⟩⟩
    · obtain ⟨d, ⟨q, hq2, hd⟩, hne⟩ :=
        exists_typeTwistedD_of_stated h4 (θ0.trans (statedProjEquiv _).symm)
      exact ⟨hcenter (by omega), Or.inl ⟨d, ⟨m, q, hq2, Or.inr (Or.inl hd)⟩, hne⟩⟩
  · obtain ⟨φ, hφ⟩ := (hstd : IsPlusSpace Q m)
    have hφ' : ∀ v, StatedQuadPlus m (ZMod 2) (φ v) = Q v := fun v => by
      rw [← CFSG.LieType.Universal.Spin.coe_quadPlus]; exact hφ v
    let θ0 := eΩ.trans (statedOmegaEquiv φ hφ').symm
    have hcenter : 3 ≤ m →  Subgroup.center Y = ⊥ := fun h3 =>
      center_eq_bot_of_mulEquiv eΩ (center_commutator_orthogonal_eq_bot
        (commutator_orthogonalGroup_eq_of_isPlusSpace h3 ⟨φ, hφ⟩)
        fun g hg hc => eq_one_of_commute_elementaryGroup_of_isPlusSpace h3 ⟨φ, hφ⟩ hg hc)
    rcases (show m ≤ 2 ∨ m = 3 ∨ 4 ≤ m by omega) with h2 | rfl | h4
    · exact (hsolv (solvable_of_isPlusSpace_small h2 ⟨φ, hφ⟩)).elim
    · have e8 := θ0.trans statedOmega_quadPlus_three_mulEquiv_alt8
      exact ⟨hcenter le_rfl, Or.inr ⟨8, Or.inr (Or.inr rfl), ⟨e8⟩⟩⟩
    · obtain ⟨d, ⟨q, hq2, hd⟩, hne⟩ :=
        exists_typeD_of_stated h4 (θ0.trans (statedProjEquiv _).symm)
      exact ⟨hcenter (by omega), Or.inl ⟨d, ⟨m, q, hq2, Or.inl hd⟩, hne⟩⟩

theorem isOrthogonalTwo_of_shapeOut {Y : Type} [Group Y] [Finite Y] (h : ShapeOut Y)
    (hsimp : IsSimpleGroup (Y ⧸ Subgroup.center Y))
    (hnonab : ∃ a b : Y ⧸ Subgroup.center Y, a * b ≠ b * a)
    (hAlt : ∀ m : ℕ, (m = 7 ∨ 9 ≤ m) → IsEmpty ((Y ⧸ Subgroup.center Y) ≃* alternatingGroup (Fin m))) :
    Subgroup.center Y = ⊥ ∧ CFSG.AGLEmbedding.IsOrthogonalTwo Y := by
  rcases h with ⟨W, i1, i2, i3, Q, hQ, ⟨e⟩⟩ | ⟨W, i1, i2, i3, f, h4, hnd, halt, ⟨e⟩⟩ |
    ⟨m, hm, ⟨e⟩⟩
  · exact isOrthogonalTwo_of_orth Q hQ e hsimp hnonab
  · obtain ⟨e6⟩ := nonempty_commutator_bilinIsometryGroup_alt_six hnd halt h4
    have e' := e.trans e6
    exact ⟨center_eq_bot_of_mulEquiv e' (alternatingGroup.center_eq_bot (by simp)),
      Or.inr ⟨6, Or.inr (Or.inl rfl), ⟨e'⟩⟩⟩
  · have hc : Subgroup.center Y = ⊥ :=
      center_eq_bot_of_mulEquiv e (alternatingGroup.center_eq_bot (by simpa using (by omega : 4 ≤ m)))
    refine ⟨hc, Or.inr ?_⟩
    by_cases hm' : m = 5 ∨ m = 6 ∨ m = 8
    · exact ⟨m, hm', ⟨e⟩⟩
    · exfalso
      have e2 : Y ⧸ Subgroup.center Y ≃* Y :=
        (QuotientGroup.quotientMulEquivOfEq hc).trans (QuotientGroup.quotientBot (G := Y))
      exact (hAlt m (by omega)).false (e2.trans e)

end CFSG.HardMathSupport.Cooperstein.StructureLie
