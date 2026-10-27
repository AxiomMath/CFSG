module
public import CFSG.LieType.Chevalley.E7Three.CentralizerSolvable
public import CFSG.LieType.Chevalley.E7Three.CentralizerInner
public import CFSG.LieType.Chevalley.E7Three.CentralizerFour
public import CFSG.LieType.Chevalley.E7Three.CentralizerOvergroup
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcBridgeU
public import CFSG.LocalAnalysis.ABGTheoremB.CoverEmbedding
public import CFSG.LieType.Chevalley.E7Three.ScalarReach
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxToral
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerTorus
public import CFSG.LieType.AlgebraicGroups.FiniteNormalizerComponentAction
public import CFSG.LieType.Chevalley.E7Three.FourAutomizer
public import CFSG.RankThree.Chevalley.SteinbergBNF4NativeB2
public import CFSG.RankThree.Chevalley.SteinbergBUF4B2QuarticDescent
public import CFSG.RankThree.Chevalley.SteinbergBUF4CyclotomicFourDescent
public import CFSG.RankThree.Chevalley.SteinbergBUF4CyclotomicFourTools
public import CFSG.RankThree.PartOne.K133H.G2Plane
public import CFSG.Sporadic.Co1Block.TwoBTri

public noncomputable section
set_option autoImplicit false
namespace CFSG.LieType.Chevalley.E7Three.Centralizer
open Matrix CFSG.Blueprint.Chevalley CFSG.RankThree.PartOne.KA5L
  CFSG.LieType.AlgebraicGroups CFSG.StandardType
open scoped MatrixGroups
theorem centralizer_map_eq_cubeCent_fixed_at_original_field
    {F k : Type} [Field F] [Finite F] [CharP F 2] [Field k] [CharP k 2] [Algebra F k]
    (Fr : k →+* k) (hFr : ∀ c, Fr c = c ^ Nat.card F) (hbij : Function.Bijective Fr)
    (A : Subgroup (adjointGroup .E7 F))
    {ζ : kˣ} (hζ : IsPrimitiveRoot ζ 3) (g : adjointGroup .E7 k)
    (hA : A.map ((MulAut.conj (g : ModGL .E7 k)).toMonoidHom.comp
      ((baseChangeGL (algebraMap F k)).comp (adjointGroup .E7 F).subtype)) =
        cubeE ζ hζ.pow_eq_one) :
    let ι := (baseChangeGL (algebraMap F k)).comp (adjointGroup .E7 F).subtype
    let φ := MulAut.conj (g : ModGL .E7 k)
    let Ψ := φ.toMonoidHom.comp ((baseChangeGL Fr).comp φ.symm.toMonoidHom)
    (Subgroup.centralizer (A : Set (adjointGroup .E7 F))).map (φ.toMonoidHom.comp ι) =
      cubeCent ζ hζ.pow_eq_one ⊓ Ψ.eqLocus (MonoidHom.id _) ∧
      ∀ e ∈ cubeE ζ hζ.pow_eq_one, Ψ e = e := by
  intro ι φ Ψ
  let σ := baseChangeGL (τ := .E7) Fr
  let ψ := φ.toMonoidHom.comp ι
  have hι : Function.Injective ι :=
    (baseChangeGL_injective (algebraMap F k)).comp Subtype.val_injective
  have hψ : Function.Injective ψ := φ.injective.comp hι
  have hrat : adjointGroup .E7 k ⊓ σ.eqLocus (MonoidHom.id _) = ι.range := by
    have h := CFSG.HardMathSupport.C14ExcBridgeU.fixed_eq_map
      (K := F) (L := k) (τ := .E7) (Or.inr (Or.inr (Or.inl rfl))) Fr hFr hbij
    change adjointGroup .E7 k ⊓ σ.eqLocus (MonoidHom.id _) =
      (adjointGroup .E7 F).map (baseChangeGL (algebraMap F k)) at h
    rw [h]
    simp only [ι, MonoidHom.range_comp, Subgroup.range_subtype]
  have hιfix : ∀ z : adjointGroup .E7 F, σ (ι z) = ι z := by
    intro z
    have hz : ι z ∈ ι.range := ⟨z, rfl⟩
    rw [← hrat] at hz
    exact hz.2
  have hΨψ : ∀ z : adjointGroup .E7 F, Ψ (ψ z) = ψ z := by
    intro z
    change φ (σ (φ.symm (φ (ι z)))) = φ (ι z)
    rw [φ.symm_apply_apply, hιfix]
  have hrange : ψ.range = adjointGroup .E7 k ⊓ Ψ.eqLocus (MonoidHom.id _) := by
    apply le_antisymm
    · rintro y ⟨z, rfl⟩
      refine ⟨?_, hΨψ z⟩
      change (g : ModGL .E7 k) * ι z * (g : ModGL .E7 k)⁻¹ ∈ adjointGroup .E7 k
      exact (adjointGroup .E7 k).mul_mem
        ((adjointGroup .E7 k).mul_mem g.2
          (CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup _ z.2))
        ((adjointGroup .E7 k).inv_mem g.2)
    · intro y hy
      have hxG : φ.symm y ∈ adjointGroup .E7 k := by
        change (g : ModGL .E7 k)⁻¹ * y * (g : ModGL .E7 k) ∈ adjointGroup .E7 k
        exact (adjointGroup .E7 k).mul_mem
          ((adjointGroup .E7 k).mul_mem ((adjointGroup .E7 k).inv_mem g.2) hy.1) g.2
      have hxfix : σ (φ.symm y) = φ.symm y := by
        apply φ.injective
        change Ψ y = φ (φ.symm y)
        rw [φ.apply_symm_apply]
        exact hy.2
      have hm : φ.symm y ∈ ι.range := by rw [← hrat]; exact ⟨hxG, hxfix⟩
      obtain ⟨z, hz⟩ := hm
      refine ⟨z, ?_⟩
      change φ (ι z) = y
      rw [hz, φ.apply_symm_apply]
  constructor
  · rw [CFSG.ABGTheoremB.Setting.map_centralizer_eq_range_inf hψ, hA, hrange]
    ext y
    simp only [cubeCent, Subgroup.mem_inf]
    tauto
  · intro e he
    rw [← hA] at he
    obtain ⟨z, hz, rfl⟩ := he
    exact hΨψ z


theorem isSolvable_centralizer_of_conjugate_cube_and_inner_frobenius
    {F k : Type} [Field F] [Finite F] [CharP F 2] [Field k] [CharP k 2]
    [IsAlgClosed k] [Algebra F k]
    (f : ℕ) (hf : 1 ≤ f) (hF : Nat.card F = 2 ^ f)
    (A : Subgroup (adjointGroup .E7 F))
    {ζ : kˣ} (hζ : IsPrimitiveRoot ζ 3) (g : adjointGroup .E7 k)
    (hA : A.map ((MulAut.conj (g : ModGL .E7 k)).toMonoidHom.comp
      ((baseChangeGL (algebraMap F k)).comp (adjointGroup .E7 F).subtype)) =
        cubeE ζ hζ.pow_eq_one)
    (a : SL(2, k))
    (hΔ : ∀ x : SL(2, k),
      ((MulAut.conj (g : ModGL .E7 k)).toMonoidHom.comp
        ((baseChangeGL (iterateFrobenius k 2 f)).comp
          (MulAut.conj (g : ModGL .E7 k)).symm.toMonoidHom)) (cubeSL2 k x) =
      cubeSL2 k (a * SpecialLinearGroup.map (iterateFrobenius k 2 f) x * a⁻¹))
    (hNPC : CFSG.HasNormalPComplement 3
      ↥(_root_.commutator ↥(Subgroup.centralizer (A : Set (adjointGroup .E7 F))))) :
    Group.IsSolvable ↥(Subgroup.centralizer (A : Set (adjointGroup .E7 F))) := by
  let ι := (baseChangeGL (τ := .E7) (algebraMap F k)).comp (adjointGroup .E7 F).subtype
  let φ := MulAut.conj (g : ModGL .E7 k)
  let ψ := φ.toMonoidHom.comp ι
  let Ψ := φ.toMonoidHom.comp
    ((baseChangeGL (iterateFrobenius k 2 f)).comp φ.symm.toMonoidHom)
  have hFr : ∀ c : k, iterateFrobenius k 2 f c = c ^ Nat.card F := by
    intro c
    rw [iterateFrobenius_def, hF]
  have hbij : Function.Bijective (iterateFrobenius k 2 f) :=
    (iterateFrobeniusEquiv k 2 f).bijective
  obtain ⟨heq, hE⟩ := centralizer_map_eq_cubeCent_fixed_at_original_field
    (iterateFrobenius k 2 f) hFr hbij A hζ g hA
  let C := Subgroup.centralizer (A : Set (adjointGroup .E7 F))
  let D := cubeCent ζ hζ.pow_eq_one ⊓ Ψ.eqLocus (MonoidHom.id _)
  have hψ : Function.Injective ψ := φ.injective.comp
    ((baseChangeGL_injective (algebraMap F k)).comp Subtype.val_injective)
  let e : C ≃* D :=
    (C.equivMapOfInjective ψ hψ).trans (MulEquiv.subgroupCongr heq)
  have hNPCD : CFSG.HasNormalPComplement 3 ↥(_root_.commutator ↥D) :=
    CFSG.hasNormalPComplement_of_equiv 3 e.commutatorCongr hNPC
  have hΔ' : ∀ x : SL(2, k), Ψ (cubeSL2 k x) = cubeSL2 k
      (a * SpecialLinearGroup.map (iterateFrobenius k 2 (f * 1)) x * a⁻¹) := by
    simpa only [Nat.mul_one] using hΔ
  have hsD : Group.IsSolvable ↥D :=
    cubeCent_frobenius_isSolvable_of_three_complement f 1 hf (by decide) hF hζ a Ψ hΔ' hE hNPCD
  let : Group.IsSolvable ↥D := hsD
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

theorem isSolvable_centralizer_of_conjugate_cube
    {F k : Type} [Field F] [Finite F] [CharP F 2] [Field k] [CharP k 2]
    [IsAlgClosed k] [Algebra F k]
    (A : Subgroup (adjointGroup .E7 F))
    {ζ : kˣ} (hζ : IsPrimitiveRoot ζ 3) (g : adjointGroup .E7 k)
    (hA : A.map ((MulAut.conj (g : ModGL .E7 k)).toMonoidHom.comp
      ((baseChangeGL (algebraMap F k)).comp (adjointGroup .E7 F).subtype)) =
        cubeE ζ hζ.pow_eq_one)
    (hNPC : CFSG.HasNormalPComplement 3
      ↥(_root_.commutator ↥(Subgroup.centralizer (A : Set (adjointGroup .E7 F))))) :
    Group.IsSolvable ↥(Subgroup.centralizer (A : Set (adjointGroup .E7 F))) := by
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨f, -, hfcard⟩ := FiniteField.card F 2
  have hf : 1 ≤ (f : ℕ) := f.pos
  have hF : Nat.card F = 2 ^ (f : ℕ) := by simpa [Nat.card_eq_fintype_card] using hfcard
  let Fr := iterateFrobenius k 2 (f : ℕ)
  let σ := baseChangeGL (τ := .E7) Fr
  let φ := MulAut.conj (g : ModGL .E7 k)
  let Ψ := φ.toMonoidHom.comp (σ.comp φ.symm.toMonoidHom)
  have hFr : ∀ c : k, Fr c = c ^ Nat.card F := by
    intro c
    change iterateFrobenius k 2 (f : ℕ) c = _
    rw [iterateFrobenius_def, hF]
  have hbij : Function.Bijective Fr := (iterateFrobeniusEquiv k 2 (f : ℕ)).bijective
  obtain ⟨heq, hE⟩ := centralizer_map_eq_cubeCent_fixed_at_original_field Fr hFr hbij A hζ g hA
  have hginv : (g : ModGL .E7 k)⁻¹ ∈ adjointGroup .E7 k :=
    (adjointGroup .E7 k).inv_mem g.2
  have hfix : ∀ e ∈ cubeE ζ hζ.pow_eq_one,
      baseChangeGL Fr ((g : ModGL .E7 k)⁻¹ * e * (g : ModGL .E7 k)) =
        (g : ModGL .E7 k)⁻¹ * e * (g : ModGL .E7 k) := by
    intro e he
    apply φ.injective
    change Ψ e = φ (φ.symm e)
    rw [φ.apply_symm_apply]
    exact hE e he
  obtain ⟨a, ha⟩ := exists_inner_baseChangeGL_conj_cubeSL2 hζ Fr hginv hfix
  simp only [inv_inv] at ha
  have hΔ : ∀ x : SL(2, k), Ψ (cubeSL2 k x) =
      cubeSL2 k (a * SpecialLinearGroup.map Fr x * a⁻¹) := by
    intro x
    change (g : ModGL .E7 k) *
      baseChangeGL Fr ((g : ModGL .E7 k)⁻¹ * cubeSL2 k x * (g : ModGL .E7 k)) *
      (g : ModGL .E7 k)⁻¹ = _
    rw [ha x]
    group
  exact isSolvable_centralizer_of_conjugate_cube_and_inner_frobenius
    (f : ℕ) hf hF A hζ g hA a hΔ hNPC

theorem isSolvable_centralizer_of_conjugate_fourCube
    {F k : Type} [Field F] [CharP F 2] [Field k] [CharP k 2]
    [IsAlgClosed k] [Algebra F k]
    (A : Subgroup (adjointGroup .E7 F))
    {ζ : kˣ} (hζ : IsPrimitiveRoot ζ 3) (g : adjointGroup .E7 k)
    (hA : A.map ((MulAut.conj (g : ModGL .E7 k)).toMonoidHom.comp
      ((baseChangeGL (algebraMap F k)).comp (adjointGroup .E7 F).subtype)) =
        fourE ζ hζ.pow_eq_one) :
    Group.IsSolvable ↥(Subgroup.centralizer (A : Set (adjointGroup .E7 F))) := by
  let ι := (baseChangeGL (τ := .E7) (algebraMap F k)).comp (adjointGroup .E7 F).subtype
  let φ := MulAut.conj (g : ModGL .E7 k)
  let ψ := φ.toMonoidHom.comp ι
  let C := Subgroup.centralizer (A : Set (adjointGroup .E7 F))
  let D := fourCent ζ hζ.pow_eq_one
  have hψ : Function.Injective ψ := φ.injective.comp
    ((baseChangeGL_injective (algebraMap F k)).comp Subtype.val_injective)
  have hm : ∀ z : C, ψ z ∈ D := by
    intro z
    constructor
    · change (g : ModGL .E7 k) * ι z * (g : ModGL .E7 k)⁻¹ ∈ adjointGroup .E7 k
      exact (adjointGroup .E7 k).mul_mem
        ((adjointGroup .E7 k).mul_mem g.2
          (CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup _ (z : adjointGroup .E7 F).2))
        ((adjointGroup .E7 k).inv_mem g.2)
    · change ψ z ∈ Subgroup.centralizer (fourE ζ hζ.pow_eq_one : Set (ModGL .E7 k))
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [← hA] at hy
      obtain ⟨a, ha, rfl⟩ := hy
      change ψ a * ψ z = ψ z * ψ a
      rw [← map_mul, ← map_mul]
      exact congrArg ψ (Subgroup.mem_centralizer_iff.1 z.2 a ha)
  let t : C →* D := (ψ.comp C.subtype).codRestrict D hm
  have ht : Function.Injective t := by
    intro x y hxy
    apply Subtype.ext
    apply hψ
    exact congrArg (fun z : D => (z : ModGL .E7 k)) hxy
  have hs : Group.IsSolvable D := Group.isSolvable_of_comm fun x y => Subtype.ext
    (Subgroup.mem_centralizer_iff.1 (fourCent_le_centralizer hζ x.2) y y.2).symm
  let : Group.IsSolvable D := hs
  exact Group.isSolvable_of_isSolvable_injective (f := t) ht

theorem isSolvable_centralizer_of_conjugate_cube_or_fourCube
    {F k : Type} [Field F] [Finite F] [CharP F 2] [Field k] [CharP k 2]
    [IsAlgClosed k] [Algebra F k]
    (A : Subgroup (adjointGroup .E7 F))
    {ζ : kˣ} (hζ : IsPrimitiveRoot ζ 3)
    (hA : ∃ g : adjointGroup .E7 k,
      A.map ((MulAut.conj (g : ModGL .E7 k)).toMonoidHom.comp
        ((baseChangeGL (algebraMap F k)).comp (adjointGroup .E7 F).subtype)) =
          cubeE ζ hζ.pow_eq_one ∨
      A.map ((MulAut.conj (g : ModGL .E7 k)).toMonoidHom.comp
        ((baseChangeGL (algebraMap F k)).comp (adjointGroup .E7 F).subtype)) =
          fourE ζ hζ.pow_eq_one)
    (hNPC : CFSG.HasNormalPComplement 3
      ↥(_root_.commutator ↥(Subgroup.centralizer (A : Set (adjointGroup .E7 F))))) :
    Group.IsSolvable ↥(Subgroup.centralizer (A : Set (adjointGroup .E7 F))) := by
  obtain ⟨g, hA | hA⟩ := hA
  · exact isSolvable_centralizer_of_conjugate_cube A hζ g hA hNPC
  · exact isSolvable_centralizer_of_conjugate_fourCube A hζ g hA

theorem isSolvable_centralizer_of_cube_le_conjugate
    {F k : Type} [Field F] [Finite F] [CharP F 2] [Field k] [CharP k 2]
    [IsAlgClosed k] [Algebra F k]
    (A : Subgroup (adjointGroup .E7 F))
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hexp : ∀ x ∈ A, x ^ 3 = 1)
    {ζ : kˣ} (hζ : IsPrimitiveRoot ζ 3)
    (hA : ∃ g : adjointGroup .E7 k, cubeE ζ hζ.pow_eq_one ≤
      A.map ((MulAut.conj (g : ModGL .E7 k)).toMonoidHom.comp
        ((baseChangeGL (algebraMap F k)).comp (adjointGroup .E7 F).subtype)))
    (hNPC : CFSG.HasNormalPComplement 3
      ↥(_root_.commutator ↥(Subgroup.centralizer (A : Set (adjointGroup .E7 F))))) :
    Group.IsSolvable ↥(Subgroup.centralizer (A : Set (adjointGroup .E7 F))) := by
  obtain ⟨g, hg⟩ := hA
  let ι := (baseChangeGL (τ := .E7) (algebraMap F k)).comp (adjointGroup .E7 F).subtype
  let φ := MulAut.conj (g : ModGL .E7 k)
  let ψ := φ.toMonoidHom.comp ι
  let E := A.map ψ
  have hEG : E ≤ adjointGroup .E7 k := by
    rintro _ ⟨x, hx, rfl⟩
    exact (adjointGroup .E7 k).mul_mem
      ((adjointGroup .E7 k).mul_mem g.2
        (CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup _ x.2))
      ((adjointGroup .E7 k).inv_mem g.2)
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm x hx y hy]
  have hEexp : ∀ x ∈ E, x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hexp x hx, map_one]
  obtain ⟨_, ⟨Q, rfl⟩, hc⟩ := exists_conj_eq_cubeE_or_fourE hζ hEG hEcomm hEexp hg
  have hQG : cubeSL2 k Q ∈ adjointGroup .E7 k := a5Frame_mem_adjointGroup _
  let g' : adjointGroup .E7 k :=
    ⟨cubeSL2 k Q * g, (adjointGroup .E7 k).mul_mem hQG g.2⟩
  have hmap : A.map ((MulAut.conj (g' : ModGL .E7 k)).toMonoidHom.comp ι) =
      E.map (MulAut.conj (cubeSL2 k Q)).toMonoidHom := by
    change A.map _ = (A.map ψ).map _
    rw [Subgroup.map_map]
    congr 1
  apply isSolvable_centralizer_of_conjugate_cube_or_fourCube A hζ _ hNPC
  refine ⟨g', ?_⟩
  change A.map ((MulAut.conj (g' : ModGL .E7 k)).toMonoidHom.comp ι) = _ ∨ _
  rw [hmap]
  exact hc

theorem isSolvable_centralizer_of_not_toral
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (A : Subgroup (adjointGroup .E7 F))
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hexp : ∀ x ∈ A, x ^ 3 = 1)
    (hT : ¬ ExcFramesHalf.IsToralSubgroup .E7 (AlgebraicClosure F)
      (A.map ((baseChangeGL (algebraMap F (AlgebraicClosure F))).comp
        (adjointGroup .E7 F).subtype)))
    (hNPC : CFSG.HasNormalPComplement 3
      ↥(_root_.commutator ↥(Subgroup.centralizer (A : Set (adjointGroup .E7 F))))) :
    Group.IsSolvable ↥(Subgroup.centralizer (A : Set (adjointGroup .E7 F))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP (AlgebraicClosure F) 2 :=
    charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective 2
  let : NeZero (3 : AlgebraicClosure F) := ⟨fun h0 =>
    (by decide : ¬ (2 ∣ 3)) ((CharP.cast_eq_zero_iff (AlgebraicClosure F) 2 3).1 h0)⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.prim (M := AlgebraicClosure F) (n := 3)
  obtain ⟨ζ, rfl⟩ := hz.isUnit (by decide)
  have hζ : IsPrimitiveRoot ζ 3 := IsPrimitiveRoot.coe_units_iff.1 hz
  let ι := (baseChangeGL (τ := .E7) (algebraMap F (AlgebraicClosure F))).comp
    (adjointGroup .E7 F).subtype
  have : Finite (adjointGroup .E7 F) := by
    have : Finite (ModGL .E7 F) := finite_modGL
    exact Subtype.finite
  have : Finite ↥(A.map ι) := Finite.of_surjective (fun x : A => (⟨ι x, x, x.2, rfl⟩ : A.map ι))
    (by rintro ⟨_, x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩)
  have hEG : A.map ι ≤ adjointGroup .E7 (AlgebraicClosure F) := by
    rintro _ ⟨x, -, rfl⟩
    exact CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup _ x.2
  have hEcomm : ∀ x ∈ A.map ι, ∀ y ∈ A.map ι, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm x hx y hy]
  have hEexp : ∀ x ∈ A.map ι, x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hexp x hx, map_one]
  have hnt : ¬ ∃ g ∈ adjointGroup .E7 (AlgebraicClosure F), ∀ x ∈ A.map ι,
      g * x * g⁻¹ ∈ torusGroup .E7 (AlgebraicClosure F) := by
    rintro ⟨g, hg, h⟩
    exact hT ⟨g⁻¹, inv_mem hg, fun x hx => by rw [inv_inv]; exact h x hx⟩
  obtain ⟨g, hg, hcube⟩ := ScalarReach.exists_conj_cubeE_le_of_not_toral
    (CFSG.HardMathSupport.Timmesfeld.CrossChar.isAlgebraic_zmod_algebraicClosure_of_finite F 2)
    hζ hEG hEcomm hEexp hnt
  refine isSolvable_centralizer_of_cube_le_conjugate A hcomm hexp hζ ⟨⟨g, hg⟩, ?_⟩ hNPC
  rw [← Subgroup.map_map]
  exact hcube

end CFSG.LieType.Chevalley.E7Three.Centralizer
