module

public import CFSG.LieType.Chevalley.E6Three.Position
public import CFSG.LieType.Chevalley.E6Three.StabilizerZeroOne
public import CFSG.RankThree.PartOne.KE.ThreeA1Solvable
public import CFSG.LieType.Chevalley.E6Three.RotatedA2
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilySolvable
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.StandardType.GGTwE6FixedA2SL3

public section

set_option autoImplicit false

namespace CFSG.LieType.Chevalley.E6Three.PositionCentralizer

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.StandardType.TableBExc CFSG.StandardType.TableBExc.Three CFSG.StandardType.TableBExc.E6Three
  CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.StandardType.TwE6HyperplaneTypes CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley.MaxTorusPart CFSG.LieType.Chevalley.E6Three.ModelKernel
  CFSG.LieType.Chevalley.E6Three.Position CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Roots

theorem kernelRoots_position_zero : ∀ α ∈ rootFinset .E6,
    (triPairing (positionBasis 0 0) α = 0 ∧ triPairing (positionBasis 0 1) α = 0) ↔
      α ∈ fixedA2E6 := by decide +kernel

theorem kernelRoots_position_one : ∀ α ∈ rootFinset .E6,
    (triPairing (positionBasis 1 0) α = 0 ∧ triPairing (positionBasis 1 1) α = 0) ↔
      α ∈ CFSG.RankThree.PartOne.KE.threeRootSet (τ := .E6)
        (Pi.single (0 : Fin 6) 1) (Pi.single (5 : Fin 6) 1) (CFSG.SeitzReduction.highRoot .E6) := by
  simp only [CFSG.RankThree.PartOne.KE.threeRootSet, Set.mem_insert_iff, Set.mem_singleton_iff]
  decide +kernel

theorem position_one_strongly_orthogonal :
    let r : Fin 3 → Fin Tag.E6.rank → ℤ :=
      ![Pi.single (0 : Fin 6) 1, Pi.single (5 : Fin 6) 1, CFSG.SeitzReduction.highRoot .E6]
    ∀ i j : Fin 3, i ≠ j →
      iform (τ := .E6) (r i) (r j) = 0 ∧ ¬ IsRoot .E6 (r i + r j) ∧ ¬ IsRoot .E6 (r i - r j) := by
  let r : Fin 3 → Fin Tag.E6.rank → ℤ :=
    ![Pi.single (0 : Fin 6) 1, Pi.single (5 : Fin 6) 1, CFSG.SeitzReduction.highRoot .E6]
  have h : ∀ i j : Fin 3, i ≠ j → iform (τ := .E6) (r i) (r j) = 0 ∧
      r i + r j ∉ rootFinset .E6 ∧ r i - r j ∉ rootFinset .E6 := by
    decide +kernel
  change ∀ i j : Fin 3, i ≠ j → iform (τ := .E6) (r i) (r j) = 0 ∧
    ¬ IsRoot .E6 (r i + r j) ∧ ¬ IsRoot .E6 (r i - r j)
  intro i j hij
  exact ⟨(h i j hij).1, fun hr => (h i j hij).2.1 (mem_rootFinset.2 hr),
    fun hr => (h i j hij).2.2 (mem_rootFinset.2 hr)⟩

@[expose] def rotA2E6 : List (Fin Tag.E6.rank → ℤ) :=
  [![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, -1, 0], ![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, -1],
    ![0, 0, 0, 0, 1, 1], ![0, 0, 0, 0, -1, -1]]

theorem kernelRoots_position_three : ∀ α ∈ rootFinset .E6,
    (triPairing (positionBasis 3 0) α = 0 ∧ triPairing (positionBasis 3 1) α = 0) ↔
      α ∈ rotA2E6 := by
  decide +kernel

theorem kernelRoots_position_four : ∀ α ∈ rootFinset .E6,
    ¬ (triPairing (positionBasis 4 0) α = 0 ∧ triPairing (positionBasis 4 1) α = 0) := by
  decide +kernel

theorem rotA2E6_subset_rootFinset : ∀ α ∈ rotA2E6, α ∈ rootFinset .E6 := by
  decide +kernel

theorem wordProd_positionWord_of_three_le {k : Fin 5} (hk : 3 ≤ k.val) :
    (coxeterSystem .E6).wordProd (positionWord k) =
      modelHomE6 (SemidirectProduct.inl (Multiplicative.ofAdd ![1, 1, 1])) := by
  rw [positionWord, if_neg (by omega), modelHomE6_inl]
  rfl

end Roots

section Bounds

variable {L : Type} [Field L]

theorem familyGroup_position_one {ζ : Lˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) :
    familyGroup (K := L) (fun i : Fin 2 => zetaVec ζ hζ (positionBasis 1 i)) =
      torusGroup .E6 L ⊔ rootSpan .E6 L
        (CFSG.RankThree.PartOne.KE.threeRootSet (τ := .E6)
          (Pi.single (0 : Fin 6) 1) (Pi.single (5 : Fin 6) 1) (CFSG.SeitzReduction.highRoot .E6)) := by
  have hker : familyKernel (fun i : Fin 2 => zetaVec ζ hζ (positionBasis 1 i)) =
      CFSG.RankThree.PartOne.KE.threeRootSet (τ := .E6)
        (Pi.single (0 : Fin 6) 1) (Pi.single (5 : Fin 6) 1) (CFSG.SeitzReduction.highRoot .E6) := by
    ext α
    simp only [familyKernel, Set.mem_setOf_eq, Fin.forall_fin_two,
      rootChar_zetaVec_eq_one_iff hζo]
    constructor
    · rintro ⟨hα, h⟩
      exact (kernelRoots_position_one α (mem_rootFinset.2 hα)).1 h
    · intro hα
      have hroot : IsRoot .E6 α := by
        rcases hα with rfl | rfl | rfl | rfl | rfl | rfl
        exacts [IsRoot.basis _, CFSG.LieType.Chevalley.IsRoot.neg (IsRoot.basis _),
          IsRoot.basis _, CFSG.LieType.Chevalley.IsRoot.neg (IsRoot.basis _),
          CFSG.SeitzReduction.isRoot_highRoot _,
          CFSG.LieType.Chevalley.IsRoot.neg (CFSG.SeitzReduction.isRoot_highRoot _)]
      exact ⟨hroot, (kernelRoots_position_one α (mem_rootFinset.2 hroot)).2 hα⟩
  rw [familyGroup, hker]

theorem isSolvable_of_le_familyCentralizer_position_one
    [IsAlgClosed L] [CharP L 2]
    {K : Type} [Field K] [Finite K] [Algebra K L] [Algebra.IsAlgebraic K L]
    {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ 3) (C : Subgroup (ModGL .E6 L)) [Finite C]
    (hC : C ≤ familyCentralizer .E6 L
      (fun i : Fin 2 => zetaVec ζ hζ.pow_eq_one (positionBasis 1 i)))
    (hNPC : CFSG.HasNormalPComplement 3 ↥(_root_.commutator C)) : Group.IsSolvable C := by
  let a : Fin 2 → Fin Tag.E6.rank → Lˣ := fun i => zetaVec ζ hζ.pow_eq_one (positionBasis 1 i)
  let M := familyGroup (K := L) a
  let H := C ⊓ M
  let P := H.subgroupOf C
  have hder : (_root_.commutator P).map P.subtype ≤ _root_.commutator C := by
    rw [map_commutator_eq]
    exact Subgroup.commutator_mono le_top le_top
  have hNPCP : CFSG.HasNormalPComplement 3 ↥(_root_.commutator P) :=
    CFSG.hasNormalPComplement_of_map_subtype 3 P (_root_.commutator P)
      (CFSG.hasNormalPComplement_of_le 3 hder hNPC)
  let φ : P →* ModGL .E6 L := C.subtype.comp P.subtype
  have hφi : Function.Injective φ := C.subtype_injective.comp P.subtype_injective
  have hφM : φ.range ≤ torusGroup .E6 L ⊔ rootSpan .E6 L
      (CFSG.RankThree.PartOne.KE.threeRootSet (τ := .E6)
        (Pi.single (0 : Fin 6) 1) (Pi.single (5 : Fin 6) 1) (CFSG.SeitzReduction.highRoot .E6)) := by
    rintro _ ⟨x, rfl⟩
    have hx : φ x ∈ M := x.2.2
    change φ x ∈ familyGroup (K := L)
      (fun i : Fin 2 => zetaVec ζ hζ.pow_eq_one (positionBasis 1 i)) at hx
    rwa [familyGroup_position_one hζ.eq_orderOf.symm hζ.pow_eq_one] at hx
  have hc12 := CFSG.RankThree.Chevalley.rootSL2_commute_of_orth (τ := .E6) (K := L)
    (IsRoot.basis (0 : Fin Tag.E6.rank)) (IsRoot.basis (5 : Fin Tag.E6.rank))
    (position_one_strongly_orthogonal 0 1 (by decide)).1
    (position_one_strongly_orthogonal 0 1 (by decide)).2.1
    (position_one_strongly_orthogonal 0 1 (by decide)).2.2
  have hc13 := CFSG.RankThree.Chevalley.rootSL2_commute_of_orth (τ := .E6) (K := L)
    (IsRoot.basis (0 : Fin Tag.E6.rank)) (CFSG.SeitzReduction.isRoot_highRoot .E6)
    (position_one_strongly_orthogonal 0 2 (by decide)).1
    (position_one_strongly_orthogonal 0 2 (by decide)).2.1
    (position_one_strongly_orthogonal 0 2 (by decide)).2.2
  have hc23 := CFSG.RankThree.Chevalley.rootSL2_commute_of_orth (τ := .E6) (K := L)
    (IsRoot.basis (5 : Fin Tag.E6.rank)) (CFSG.SeitzReduction.isRoot_highRoot .E6)
    (position_one_strongly_orthogonal 1 2 (by decide)).1
    (position_one_strongly_orthogonal 1 2 (by decide)).2.1
    (position_one_strongly_orthogonal 1 2 (by decide)).2.2
  have : Group.IsSolvable P := CFSG.RankThree.PartOne.KE.isSolvable_of_threeA1_and_complement_derived
    hc12 hc13 hc23 (IsRoot.basis _) (IsRoot.basis _) (CFSG.SeitzReduction.isRoot_highRoot .E6)
    (K := K) φ hφM (by rw [(MonoidHom.ker_eq_bot_iff φ).mpr hφi]; exact bot_le) hNPCP
  have hHC : H ≤ C := inf_le_left
  have : Group.IsSolvable H :=
    (Subgroup.subgroupOfEquivOfLe hHC).isSolvable_congr.mp inferInstance
  have : Group.IsSolvable (familyStabilizerSubgroup a) := by
    have := StabilizerZeroOne.isSolvable_stabOne
    exact solvable_of_solvable_injective (Subgroup.inclusion_injective
      (K := StabilizerFour.stabPair (positionBasis 1 0) (positionBasis 1 1)) fun w hw =>
        StabilizerFour.mem_stabPair_of_mem_familyStabilizer hζ.eq_orderOf.symm hζ.pow_eq_one
          (positionBasis 1) (mem_familyStabilizerSubgroup.1 hw))
  exact isSolvable_of_le_familyCentralizer a hC

theorem familyGroup_position_zero {ζ : Lˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) :
    familyGroup (K := L) (fun i : Fin 2 => zetaVec ζ hζ (positionBasis 0 i)) =
      torusGroup .E6 L ⊔ rootSpan .E6 L {α | α ∈ fixedA2E6} := by
  have hker : familyKernel (fun i : Fin 2 => zetaVec ζ hζ (positionBasis 0 i)) =
      {α | α ∈ fixedA2E6} := by
    ext α
    simp only [familyKernel, Set.mem_setOf_eq, Fin.forall_fin_two,
      rootChar_zetaVec_eq_one_iff hζo]
    constructor
    · rintro ⟨hα, h⟩
      exact (kernelRoots_position_zero α (mem_rootFinset.2 hα)).1 h
    · intro hα
      have hr := CFSG.StandardType.TwE6FixedA2Type.isRoot_of_mem_fixedA2E6 hα
      exact ⟨hr, (kernelRoots_position_zero α (mem_rootFinset.2 hr)).2 hα⟩
  rw [familyGroup, hker]

section PositionZero

theorem isSolvable_of_le_familyCentralizer_position_zero
    [IsAlgClosed L] [CharP L 2]
    {K : Type} [Field K] [Finite K] [Algebra K L] [Algebra.IsAlgebraic K L]
    {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ 3) (C : Subgroup (ModGL .E6 L)) [Finite C]
    (hC : C ≤ familyCentralizer .E6 L
      (fun i : Fin 2 => zetaVec ζ hζ.pow_eq_one (positionBasis 0 i)))
    (hNPC : CFSG.HasNormalPComplement 3 ↥(_root_.commutator C)) : Group.IsSolvable C := by
  let a : Fin 2 → Fin Tag.E6.rank → Lˣ := fun i => zetaVec ζ hζ.pow_eq_one (positionBasis 0 i)
  let M := familyGroup (K := L) a
  let H := C ⊓ M
  let P := H.subgroupOf C
  have hder : (_root_.commutator P).map P.subtype ≤ _root_.commutator C := by
    rw [map_commutator_eq]
    exact Subgroup.commutator_mono le_top le_top
  have hNPCP : CFSG.HasNormalPComplement 3 ↥(_root_.commutator P) :=
    CFSG.hasNormalPComplement_of_map_subtype 3 P (_root_.commutator P)
      (CFSG.hasNormalPComplement_of_le 3 hder hNPC)
  have hHC : H ≤ C := inf_le_left
  let e : P ≃* H := Subgroup.subgroupOfEquivOfLe hHC
  have : Finite H := Finite.of_injective (Subgroup.inclusion hHC)
    (Subgroup.inclusion_injective hHC)
  have hNPCH : CFSG.HasNormalPComplement 3 ↥(_root_.commutator H) :=
    CFSG.hasNormalPComplement_of_equiv 3 e.commutatorCongr hNPCP
  have hHW : H ≤ torusGroup .E6 L ⊔ rootSpan .E6 L {α | α ∈ fixedA2E6} := by
    rw [← familyGroup_position_zero hζ.eq_orderOf.symm hζ.pow_eq_one]
    exact inf_le_right
  have : Group.IsSolvable H :=
    CFSG.StandardType.TwE6FixedA2SL3.isSolvable_fixedA2Torus_of_complement_derived
      (K := K) H hHW hNPCH
  have : Group.IsSolvable (familyStabilizerSubgroup a) := by
    have := StabilizerZeroOne.isSolvable_stabZero
    exact solvable_of_solvable_injective (Subgroup.inclusion_injective
      (K := StabilizerFour.stabPair (positionBasis 0 0) (positionBasis 0 1)) fun w hw =>
        StabilizerFour.mem_stabPair_of_mem_familyStabilizer hζ.eq_orderOf.symm hζ.pow_eq_one
          (positionBasis 0) (mem_familyStabilizerSubgroup.1 hw))
  exact isSolvable_of_le_familyCentralizer a hC

end PositionZero

theorem pow_three_eq_one_of_position {k : Fin 5} (hk : 3 ≤ k.val) {n : ModGL .E6 L}
    (hnN : n ∈ monomialSubgroup .E6 L)
    (hw : weylQuotientHom .E6 L ⟨n, hnN⟩ = (coxeterSystem .E6).wordProd (positionWord k))
    {t : ModGL .E6 L} (ht : t ∈ torusGroup .E6 L) (htn : t * n = n * t) : t ^ 3 = 1 :=
  CFSG.StandardType.E6NonToralThree.pow_three_eq_one_of_commute hnN (by decide)
    (hw.trans (wordProd_positionWord_of_three_le hk)) ht htn

theorem mem_stabFour_of_mem_familyStabilizer {ζ : Lˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    {w : WeylGroup .E6}
    (hw : w ∈ familyStabilizer fun i : Fin 2 => zetaVec ζ hζ (positionBasis 4 i)) :
    w ∈ StabilizerFour.stabFour :=
  StabilizerFour.mem_stabPair_of_mem_familyStabilizer hζo hζ (positionBasis 4) hw

theorem exists_torus_mul_canonicalRep_of_position_four [IsAlgClosed L] {ζ : Lˣ}
    (hζ : IsPrimitiveRoot ζ 3) {E : Subgroup (ModGL .E6 L)}
    (hT : ∀ u, u ∈ E ⊓ torusGroup .E6 L ↔
      ∃ z, PositionMem 4 z ∧ u = rootDiagUnit .E6 (zetaVec ζ hζ.pow_eq_one z)) :
    ∀ c ∈ adjointGroup .E6 L ⊓ Subgroup.centralizer (E : Set (ModGL .E6 L)),
      ∃ w ∈ StabilizerFour.stabFour, ∃ h ∈ torusGroup .E6 L,
        c = h * canonicalRep (coxeterSystem .E6) L w := by
  have hζo : orderOf ζ = 3 := hζ.eq_orderOf.symm
  let a : Fin 2 → Fin Tag.E6.rank → Lˣ := fun i => zetaVec ζ hζ.pow_eq_one (positionBasis 4 i)
  have ha : ∀ i, rootDiagUnit .E6 (a i) ∈ E := by
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · exact (Subgroup.mem_inf.1 ((hT _).2 ⟨_, ⟨1, 0, by simp⟩, rfl⟩)).1
    · exact (Subgroup.mem_inf.1 ((hT _).2 ⟨_, ⟨0, 1, by simp⟩, rfl⟩)).1
  have hker : familyKernel a = ∅ := by
    ext α
    simp only [familyKernel, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and,
      Fin.forall_fin_two, a, rootChar_zetaVec_eq_one_iff hζo]
    exact fun hα h0 h1 => kernelRoots_position_four α (mem_rootFinset.2 hα) ⟨h0, h1⟩
  intro c hc
  have hcF : c ∈ familyCentralizer .E6 L a := by
    rw [mem_familyCentralizer]
    refine ⟨hc.1, fun i => ?_⟩
    rw [Subgroup.mem_centralizer_iff.1 hc.2 _ (ha i), mul_inv_cancel_right]
  obtain ⟨w, hwS, h, hh, u, hu, v, hv, rfl⟩ := familyCentralizer_factors .E6 L a c hcF
  rw [hker, Set.empty_inter] at hu hv
  have hu1 : u = 1 := by simpa [rootSpan] using hu
  have hv1 : v = 1 := by simpa [rootSpan] using hv
  subst hu1 hv1
  exact ⟨w, mem_stabFour_of_mem_familyStabilizer hζo _ hwS, h, hh, by group⟩

theorem centralizer_le_monomial_of_position_four [IsAlgClosed L] {ζ : Lˣ}
    (hζ : IsPrimitiveRoot ζ 3) {E : Subgroup (ModGL .E6 L)}
    (hT : ∀ u, u ∈ E ⊓ torusGroup .E6 L ↔
      ∃ z, PositionMem 4 z ∧ u = rootDiagUnit .E6 (zetaVec ζ hζ.pow_eq_one z)) :
    adjointGroup .E6 L ⊓ Subgroup.centralizer (E : Set (ModGL .E6 L)) ≤
      monomialSubgroup .E6 L := by
  intro c hc
  obtain ⟨w, -, h, hh, rfl⟩ := exists_torus_mul_canonicalRep_of_position_four hζ hT c hc
  exact mul_mem (torusGroup_le_monomialSubgroup hh) (canonicalRep_mem_monomialSubgroup L w)

theorem weylQuotientHom_mem_stabFour_of_position_four [IsAlgClosed L] {ζ : Lˣ}
    (hζ : IsPrimitiveRoot ζ 3) {E : Subgroup (ModGL .E6 L)}
    (hT : ∀ u, u ∈ E ⊓ torusGroup .E6 L ↔
      ∃ z, PositionMem 4 z ∧ u = rootDiagUnit .E6 (zetaVec ζ hζ.pow_eq_one z))
    {c : ModGL .E6 L} (hc : c ∈ adjointGroup .E6 L ⊓ Subgroup.centralizer (E : Set (ModGL .E6 L)))
    (hcN : c ∈ monomialSubgroup .E6 L) :
    weylQuotientHom .E6 L ⟨c, hcN⟩ ∈ StabilizerFour.stabFour := by
  obtain ⟨w, hwS, h, hh, rfl⟩ := exists_torus_mul_canonicalRep_of_position_four hζ hT c hc
  rw [CFSG.HardMathSupport.Timmesfeld.CrossChar.weylQuotientHom_torus_mul hh w hcN]
  exact hwS

theorem isSolvable_centralizer_of_position_two [IsAlgClosed L] {ζ : Lˣ}
    (hζ : IsPrimitiveRoot ζ 3) {E : Subgroup (ModGL .E6 L)}
    (hT : ∀ u, u ∈ E ⊓ torusGroup .E6 L ↔
      ∃ z, PositionMem 2 z ∧ u = rootDiagUnit .E6 (zetaVec ζ hζ.pow_eq_one z)) :
    Group.IsSolvable ↥(adjointGroup .E6 L ⊓ Subgroup.centralizer (E : Set (ModGL .E6 L))) := by
  classical
  have h24 : ∀ z, PositionMem 2 z ↔ PositionMem 4 z := fun _ => Iff.rfl
  have hT4 : ∀ u, u ∈ E ⊓ torusGroup .E6 L ↔
      ∃ z, PositionMem 4 z ∧ u = rootDiagUnit .E6 (zetaVec ζ hζ.pow_eq_one z) :=
    fun u => by simpa only [h24] using hT u
  set C := adjointGroup .E6 L ⊓ Subgroup.centralizer (E : Set (ModGL .E6 L)) with hC
  have hCN : C ≤ monomialSubgroup .E6 L := centralizer_le_monomial_of_position_four hζ hT4
  let ψ : C →* WeylGroup .E6 := (weylQuotientHom .E6 L).comp (Subgroup.inclusion hCN)
  have hψS : ∀ c : C, ψ c ∈ StabilizerFour.stabFour := fun c =>
    weylQuotientHom_mem_stabFour_of_position_four hζ hT4 c.2 (hCN c.2)
  have hkerT : ∀ c : C, ψ c = 1 → (c : ModGL .E6 L) ∈ torusGroup .E6 L :=
    fun c h1 => CFSG.HardMathSupport.Timmesfeld.CrossChar.mem_torusGroup_of_weylQuotientHom_eq_one
      (hCN c.2) h1
  have hRP : IsPGroup 3 ψ.range :=
    StabilizerFour.isPGroup_stabFour.to_le fun x ⟨c, hc⟩ => hc ▸ hψS c
  have hcomm : ∀ x y : ψ.ker, x * y = y * x := by
    intro x y
    have hxT := hkerT x.1 x.2
    have hyT := hkerT y.1 y.2
    obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hxT
    apply Subtype.ext
    apply Subtype.ext
    change (x : ModGL .E6 L) * (y : ModGL .E6 L) = (y : ModGL .E6 L) * (x : ModGL .E6 L)
    rw [hb]
    exact rootDiagUnit_mul_comm_of_mem_torusGroup b hyT
  have : Group.IsSolvable ψ.ker := isSolvable_of_comm hcomm
  have : Group.IsNilpotent ψ.range := hRP.isNilpotent
  exact solvable_of_ker_le_range ψ.ker.subtype ψ.rangeRestrict fun x hx =>
    ⟨⟨x, (MonoidHom.mem_ker.2 (by
      have := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
      exact this))⟩, rfl⟩

theorem isPGroup_isSolvable_centralizer_of_position_four [IsAlgClosed L] {ζ : Lˣ}
    (hζ : IsPrimitiveRoot ζ 3) {E : Subgroup (ModGL .E6 L)}
    (hT : ∀ u, u ∈ E ⊓ torusGroup .E6 L ↔
      ∃ z, PositionMem 4 z ∧ u = rootDiagUnit .E6 (zetaVec ζ hζ.pow_eq_one z))
    {n : ModGL .E6 L} (hn : n ∈ E) (hnN : n ∈ monomialSubgroup .E6 L)
    (hw : weylQuotientHom .E6 L ⟨n, hnN⟩ = (coxeterSystem .E6).wordProd (positionWord 4)) :
    IsPGroup 3 ↥(adjointGroup .E6 L ⊓ Subgroup.centralizer (E : Set (ModGL .E6 L))) ∧
      Group.IsSolvable ↥(adjointGroup .E6 L ⊓ Subgroup.centralizer (E : Set (ModGL .E6 L))) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := adjointGroup .E6 L ⊓ Subgroup.centralizer (E : Set (ModGL .E6 L)) with hC
  have hCN : C ≤ monomialSubgroup .E6 L := centralizer_le_monomial_of_position_four hζ hT
  let ψ : C →* WeylGroup .E6 := (weylQuotientHom .E6 L).comp (Subgroup.inclusion hCN)
  have hψS : ∀ c : C, ψ c ∈ StabilizerFour.stabFour := fun c =>
    weylQuotientHom_mem_stabFour_of_position_four hζ hT c.2 (hCN c.2)
  have hT3 : ∀ c : C, (c : ModGL .E6 L) ∈ torusGroup .E6 L → (c : ModGL .E6 L) ^ 3 = 1 :=
    fun c hcT => pow_three_eq_one_of_position (by decide) hnN hw hcT
      (Subgroup.mem_centralizer_iff.1 c.2.2 n hn).symm
  have hkerT : ∀ c : C, ψ c = 1 → (c : ModGL .E6 L) ∈ torusGroup .E6 L :=
    fun c h1 => CFSG.HardMathSupport.Timmesfeld.CrossChar.mem_torusGroup_of_weylQuotientHom_eq_one
      (hCN c.2) h1
  have hRP : IsPGroup 3 ψ.range :=
    StabilizerFour.isPGroup_stabFour.to_le fun x ⟨c, hc⟩ => hc ▸ hψS c
  refine ⟨fun c => ?_, ?_⟩
  · obtain ⟨k, hk⟩ := hRP ⟨ψ c, c, rfl⟩
    have hk' : ψ (c ^ 3 ^ k) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hk
    refine ⟨k + 1, Subtype.ext ?_⟩
    have h3 := hT3 (c ^ 3 ^ k) (hkerT _ hk')
    rw [pow_succ, pow_mul]
    simpa using h3
  · apply isSolvable_centralizer_of_position_two hζ
    have h42 : ∀ z, PositionMem 4 z ↔ PositionMem 2 z := fun _ => Iff.rfl
    exact fun u => by simpa only [h42] using hT u

theorem mem_rotA2E6_iff (α : Fin Tag.E6.rank → ℤ) : α ∈ rotA2E6 ↔
    ∃ i j : Fin 3, i ≠ j ∧ α = CFSG.RankThree.E6.chainRoot CFSG.RankThree.E6.chain56 i j := by
  constructor
  · intro h
    exact (by decide +kernel : ∀ β ∈ rotA2E6, ∃ i j : Fin 3, i ≠ j ∧
      β = CFSG.RankThree.E6.chainRoot CFSG.RankThree.E6.chain56 i j) α h
  · rintro ⟨i, j, hij, rfl⟩
    exact (by decide +kernel : ∀ i j : Fin 3, i ≠ j →
      CFSG.RankThree.E6.chainRoot CFSG.RankThree.E6.chain56 i j ∈ rotA2E6) i j hij

theorem familyGroup_position_three {ζ : Lˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) :
    familyGroup (K := L) (fun i : Fin 2 => zetaVec ζ hζ (positionBasis 3 i)) =
      torusGroup .E6 L ⊔ (CFSG.RankThree.PartOne.TCX.E.e6rhoA2₂ L).range := by
  have hker : familyKernel (fun i : Fin 2 => zetaVec ζ hζ (positionBasis 3 i)) =
      parabolicRoots .E6 CFSG.RankThree.E6.support56 := by
    ext α
    rw [CFSG.RankThree.PartOne.TCX.E.a2Std₂.roots α, ← mem_rotA2E6_iff]
    simp only [familyKernel, Set.mem_setOf_eq, Fin.forall_fin_two,
      rootChar_zetaVec_eq_one_iff hζo]
    constructor
    · rintro ⟨hα, h⟩
      exact (kernelRoots_position_three α (mem_rootFinset.2 hα)).1 h
    · intro hα
      have hα' := rotA2E6_subset_rootFinset α hα
      exact ⟨mem_rootFinset.1 hα', (kernelRoots_position_three α hα').2 hα⟩
  rw [familyGroup, hker, CFSG.RankThree.PartOne.TCX.E.e6rhoA2₂_range, subsystemGroup_eq_rootSpan]

theorem isSolvable_centralizer_of_position_three {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ 3)
    {E : Subgroup (ModGL .E6 L)}
    (hT : ∀ u, u ∈ E ⊓ torusGroup .E6 L ↔
      ∃ z, PositionMem 3 z ∧ u = rootDiagUnit .E6 (zetaVec ζ hζ.pow_eq_one z))
    {n : ModGL .E6 L} (hn : n ∈ E) (hnN : n ∈ monomialSubgroup .E6 L)
    (hw : weylQuotientHom .E6 L ⟨n, hnN⟩ = (coxeterSystem .E6).wordProd (positionWord 3)) :
    Group.IsSolvable ↥(adjointGroup .E6 L ⊓ Subgroup.centralizer (E : Set (ModGL .E6 L))) := by
  have hζo : orderOf ζ = 3 := hζ.eq_orderOf.symm
  set C := adjointGroup .E6 L ⊓ Subgroup.centralizer (E : Set (ModGL .E6 L)) with hC
  let a : Fin 2 → Fin Tag.E6.rank → Lˣ := fun i => zetaVec ζ hζ.pow_eq_one (positionBasis 3 i)
  have ha : ∀ i, rootDiagUnit .E6 (a i) ∈ E := by
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · exact (Subgroup.mem_inf.1 ((hT _).2 ⟨_, ⟨1, 0, by simp⟩, rfl⟩)).1
    · exact (Subgroup.mem_inf.1 ((hT _).2 ⟨_, ⟨0, 1, by simp⟩, rfl⟩)).1
  have hCF : C ≤ familyCentralizer .E6 L a := fun c hc => by
    rw [mem_familyCentralizer]
    refine ⟨hc.1, fun i => ?_⟩
    rw [Subgroup.mem_centralizer_iff.1 hc.2 _ (ha i), mul_inv_cancel_right]
  have hM := familyGroup_position_three (L := L) hζo hζ.pow_eq_one
  have : Group.IsSolvable ↥(C ⊓ familyGroup (K := L) a) :=
    RotatedA2.isSolvable_of_le_of_commute hnN hw (hM ▸ inf_le_right)
      fun h hh => (Subgroup.mem_centralizer_iff.1 hh.1.2 n hn).symm
  have : Group.IsSolvable (familyStabilizerSubgroup a) := by
    have := StabilizerThree.isSolvable_stabThree
    exact solvable_of_solvable_injective (Subgroup.inclusion_injective (K := StabilizerThree.stabThree)
      fun w hw => StabilizerThree.mem_stabThree_of_mem_familyStabilizer hζo hζ.pow_eq_one (mem_familyStabilizerSubgroup.1 hw))
  exact isSolvable_of_le_familyCentralizer a hCF

end Bounds

section OriginalField

theorem exists_injective_inndiag_centralizer {K : Type} [Field K] (A : Subgroup (ModGL .E6 K))
    {g : ModGL .E6 (AlgebraicClosure K)} (hg : g ∈ adjointGroup .E6 (AlgebraicClosure K)) :
    ∃ φ : ↥(CFSG.StandardType.RecipeExcLang.inndiagGroup .E6 K ⊓
        Subgroup.centralizer (A : Set (ModGL .E6 K))) →*
        ↥(adjointGroup .E6 (AlgebraicClosure K) ⊓ Subgroup.centralizer
          (((A.map (baseChangeGL (algebraMap K (AlgebraicClosure K)))).map
            (MulAut.conj g).toMonoidHom : Subgroup (ModGL .E6 (AlgebraicClosure K))) :
              Set (ModGL .E6 (AlgebraicClosure K)))),
      Function.Injective φ := by
  set ι := baseChangeGL (τ := .E6) (algebraMap K (AlgebraicClosure K)) with hι
  set E' := (A.map ι).map (MulAut.conj g).toMonoidHom with hE'
  set C₀ := CFSG.StandardType.RecipeExcLang.inndiagGroup .E6 K ⊓
    Subgroup.centralizer (A : Set (ModGL .E6 K)) with hC₀
  let f : C₀ →* ModGL .E6 (AlgebraicClosure K) :=
    (MulAut.conj g).toMonoidHom.comp (ι.comp C₀.subtype)
  have hf : ∀ x : C₀, f x ∈ adjointGroup .E6 (AlgebraicClosure K) ⊓
      Subgroup.centralizer (E' : Set (ModGL .E6 (AlgebraicClosure K))) := by
    intro x
    have h1 : f x ∈ adjointGroup .E6 (AlgebraicClosure K) :=
      (adjointGroup .E6 (AlgebraicClosure K)).mul_mem
        ((adjointGroup .E6 (AlgebraicClosure K)).mul_mem hg
          (CFSG.StandardType.RecipeExcLang.baseChangeGL_mem_adjointGroup_of_mem_inndiag _ x.2.1))
        ((adjointGroup .E6 (AlgebraicClosure K)).inv_mem hg)
    refine Subgroup.mem_inf.2 ⟨h1, Subgroup.mem_centralizer_iff.2 ?_⟩
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    have hax : a * (x : ModGL .E6 K) = (x : ModGL .E6 K) * a :=
      Subgroup.mem_centralizer_iff.1 x.2.2 a ha
    change (MulAut.conj g).toMonoidHom (ι a) * (MulAut.conj g).toMonoidHom (ι (x : ModGL .E6 K)) =
      (MulAut.conj g).toMonoidHom (ι (x : ModGL .E6 K)) * (MulAut.conj g).toMonoidHom (ι a)
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hax]
  refine ⟨f.codRestrict _ hf, fun x y hxy => ?_⟩
  have h1 : f x = f y := congrArg Subtype.val hxy
  have h2 : ι (x : ModGL .E6 K) = ι (y : ModGL .E6 K) := (MulAut.conj g).injective h1
  exact Subtype.ext (baseChangeGL_injective _ h2)

section AllPositions

theorem isSolvable_of_le_inndiag_centralizer_of_not_toral_three
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (A : Subgroup (ModGL .E6 K)) (hAI : A ≤ CFSG.StandardType.RecipeExcLang.inndiagGroup .E6 K)
    (hA : CFSG.Open.IsElemAbelian 3 A) (hcard : Nat.card A = 3 ^ 3)
    (hnt : ¬ CFSG.StandardType.ExcFramesHalf.IsToralSubgroup .E6 (AlgebraicClosure K)
      (A.map (baseChangeGL (algebraMap K (AlgebraicClosure K)))))
    (H : Subgroup (ModGL .E6 K))
    (hH : H ≤ CFSG.StandardType.RecipeExcLang.inndiagGroup .E6 K ⊓
      Subgroup.centralizer (A : Set (ModGL .E6 K)))
    (hNPC : CFSG.HasNormalPComplement 3 ↥(_root_.commutator H)) : Group.IsSolvable H := by
  classical
  have : Finite (ModGL .E6 K) := finite_modGL
  have : NeZero ((3 : ℕ) : K) := ⟨fun h => by
    have h' := (CharP.cast_eq_zero_iff K 2 3).1 h
    norm_num at h'⟩
  obtain ⟨ζ0, hζ0⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) 3
  obtain ⟨ζ, hζ⟩ : ∃ ζ : (AlgebraicClosure K)ˣ, IsPrimitiveRoot ζ 3 :=
    ⟨_, IsPrimitiveRoot.isUnit_unit (by norm_num) hζ0⟩
  obtain ⟨g, hg, k, hN, hT, n, hn, hnN, hw⟩ :=
    exists_conj_position_inndiag_image_of_not_toral A hAI hA hcard hnt ζ hζ
  let E := (A.map (baseChangeGL (algebraMap K (AlgebraicClosure K)))).map
    (MulAut.conj g).toMonoidHom
  let Q := adjointGroup .E6 (AlgebraicClosure K) ⊓
    Subgroup.centralizer (E : Set (ModGL .E6 (AlgebraicClosure K)))
  obtain ⟨φ, hφ⟩ := exists_injective_inndiag_centralizer A hg
  let ψ := Q.subtype.comp (φ.comp (Subgroup.inclusion hH))
  have hψ : Function.Injective ψ :=
    Q.subtype_injective.comp (hφ.comp (Subgroup.inclusion_injective hH))
  let e := MonoidHom.ofInjective hψ
  have : Finite ψ.range := Finite.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  have hNPC' : CFSG.HasNormalPComplement 3 ↥(_root_.commutator ψ.range) :=
    CFSG.hasNormalPComplement_of_equiv 3 e.commutatorCongr hNPC
  have hψQ : ψ.range ≤ Q := by
    rintro _ ⟨h, rfl⟩
    exact (φ (Subgroup.inclusion hH h)).2
  let a : Fin 2 → Fin Tag.E6.rank → (AlgebraicClosure K)ˣ :=
    fun i => zetaVec ζ hζ.pow_eq_one (positionBasis k i)
  have ha : ∀ i, rootDiagUnit .E6 (a i) ∈ E := by
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · exact (Subgroup.mem_inf.1 ((hT _).2 ⟨_, ⟨1, 0, by simp⟩, rfl⟩)).1
    · exact (Subgroup.mem_inf.1 ((hT _).2 ⟨_, ⟨0, 1, by simp⟩, rfl⟩)).1
  have hCF : ψ.range ≤ familyCentralizer .E6 (AlgebraicClosure K) a := by
    intro x hx
    have hxQ := hψQ hx
    refine mem_familyCentralizer.2 ⟨hxQ.1, fun i => ?_⟩
    rw [Subgroup.mem_centralizer_iff.1 hxQ.2 _ (ha i), mul_inv_cancel_right]
  have hs : Group.IsSolvable ψ.range := by
    fin_cases k
    · exact isSolvable_of_le_familyCentralizer_position_zero (K := K) hζ ψ.range hCF hNPC'
    · exact isSolvable_of_le_familyCentralizer_position_one (K := K) hζ ψ.range hCF hNPC'
    · have : Group.IsSolvable Q := isSolvable_centralizer_of_position_two hζ hT
      exact solvable_of_solvable_injective (Subgroup.inclusion_injective hψQ)
    · have : Group.IsSolvable Q := isSolvable_centralizer_of_position_three hζ hT hn hnN hw
      exact solvable_of_solvable_injective (Subgroup.inclusion_injective hψQ)
    · have : Group.IsSolvable Q := (isPGroup_isSolvable_centralizer_of_position_four hζ hT hn hnN hw).2
      exact solvable_of_solvable_injective (Subgroup.inclusion_injective hψQ)
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

end AllPositions

end OriginalField

end CFSG.LieType.Chevalley.E6Three.PositionCentralizer
