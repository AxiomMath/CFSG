module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8Four6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8Spin6
public import CFSG.LieType.Chevalley.ToralCentralizerBruhat
public import CFSG.LieType.Chevalley.RootCharacterKernelProduct
public import CFSG.LieType.AlgebraicGroups.KernelRootGroup
public import CFSG.LieType.AlgebraicGroups.KernelRootDescent
public import CFSG.ClassicalInvolution.RouteD.GapsOrthChain
public import CFSG.HardMathSupport.Lang.TwE6Step3.TwoA2Split
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.Chevalley.SteinbergBNNoninnerComponentNodes
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedCosetDescent
public import CFSG.RankThree.Chevalley.SteinbergCFOddE7E8NoninnerComponent
public import CFSG.RankThree.Classical2.TwistedE6Phi3A2A2Case
public import CFSG.RankThree.Lattice.SteinbergBIE6EvenBruhat
public import CFSG.RankThree.Lattice.SteinbergBIE6Qplus
public import CFSG.RankThree.Lattice.SteinbergBIGenPerfect
public import CFSG.RankThree.Lattice.SteinbergBIGenQuasisimple
public import CFSG.RankThree.PartOne.KE.Basic
public import CFSG.RankThree.PartOne.KE.E6FourData
public import CFSG.RankThree.PartOne.KE.E8FiveData
public import CFSG.RankThree.PartOne.KE.E8NineData
public import CFSG.RankThree.PartOne.KE.NativeCyclicMain
public import CFSG.RankThree.PartOne.KE.PlaneToral
public import CFSG.RankThree.PartOne.KE6.Phi6Decomp
public import CFSG.RankThree.PartOne.KE6.Phi6Excl
public import CFSG.RankThree.PartOne.KE6.Phi6Frame
public import CFSG.RankThree.PartOne.KF4.KernelTools
public import Certificates.Certificate1953
public import Certificates.Certificate1954

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Four

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration.ExcHigh
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.AnisoE8
  CFSG.StandardType CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Spin
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Steinberg.Adjoint
  CFSG.ClassicalInvolution.RouteD.Exotic CFSG.HardMathSupport.Timmesfeld.CrossChar
open scoped Pointwise

section Characters

@[expose] def iformCharAdd (u : Fin 4 → Fin Tag.E8.rank → ℤ) :
    (Fin Tag.E8.rank → ℤ) →+ (Fin 4 → ℤ) where
  toFun v j := iform (u j) v
  map_zero' := by
    funext j
    simp [iform]
  map_add' x y := by
    funext j
    rw [Pi.add_apply, iform_add_right]

@[expose] def iformChar (u : Fin 4 → Fin Tag.E8.rank → ℤ) :
    Multiplicative (Fin Tag.E8.rank → ℤ) →* Multiplicative (Fin 4 → ℤ) :=
  AddMonoidHom.toMultiplicative (iformCharAdd u)

@[expose] def e8D4LeviRoots : Set (Fin (Tag.rank .E8) → ℤ) :=
  {α | IsRoot .E8 α ∧ ∀ j : Fin 4, iform (e8D4PerpSimple j) α = 0}

theorem kernelRoots_iformChar_levi :
    kernelRoots (iformChar e8D4PerpSimple) = e8D4LeviRoots := by
  ext α
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun j => ?_⟩
    have h4 : (iformChar e8D4PerpSimple) (Multiplicative.ofAdd α) =
        Multiplicative.ofAdd (iformCharAdd e8D4PerpSimple α) := rfl
    rw [h4] at h2
    exact congrFun (Multiplicative.ofAdd.injective h2) j
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    change Multiplicative.ofAdd (iformCharAdd e8D4PerpSimple α) = Multiplicative.ofAdd 0
    rw [Multiplicative.ofAdd.injective.eq_iff]
    funext j
    exact h2 j

@[expose] def e8D4LeviReach (l : List (Fin 4)) (δ : Fin (Tag.rank .E8) → ℤ) :
    Fin (Tag.rank .E8) → ℤ :=
  l.foldr (fun j u => u - iform (e8D4LeviSimple j) u • e8D4LeviSimple j) δ

theorem e8D4LeviTable_spec :
    ∀ β ∈ rootFinset .E8, (∀ j : Fin 4, iform (e8D4PerpSimple j) β = 0) →
      ∃ e ∈ e8D4PerpTable, e8D4LeviReach e.2 (e8D4LeviSimple e.1) = β := by
  decide +kernel

end Characters

section Roots

variable {K : Type} [Field K]

private theorem rootSubgroup_leviSimple_pair_le (j : Fin 4) :
    rootSubgroup Tag.E8 K (e8D4LeviSimple j) ⊔
        rootSubgroup Tag.E8 K (-(e8D4LeviSimple j)) ≤
      (e8D4Levi K).map (adjointGroup Tag.E8 K).subtype := by
  have hpair : rootPairE8 K (e8D4LeviSimple j) ≤ e8D4Levi K := by
    rw [e8D4Levi_eq]
    exact le_iSup (fun i : Fin 4 => rootPairE8 K (e8D4Root (Fin.castAdd 4 i))) j
  refine sup_le (ExcE8Four.rootSubgroup_le_map_of_rootPair_le (e8D4Root_isRoot _) hpair) ?_
  exact ExcE8Four.rootSubgroup_le_map_of_rootPair_le (IsRoot.neg (e8D4Root_isRoot _))
    (by rw [ExcE8Four.rootPairE8_neg]; exact hpair)

private theorem rootSubgroup_leviReach_le (l : List (Fin 4))
    {δ : Fin (Tag.rank .E8) → ℤ} (hδ : IsRoot .E8 δ)
    (h : rootSubgroup Tag.E8 K δ ≤ (e8D4Levi K).map (adjointGroup Tag.E8 K).subtype) :
    IsRoot .E8 (e8D4LeviReach l δ) ∧
      rootSubgroup Tag.E8 K (e8D4LeviReach l δ) ≤
        (e8D4Levi K).map (adjointGroup Tag.E8 K).subtype := by
  induction l with
  | nil => exact ⟨hδ, h⟩
  | cons j l ih =>
    obtain ⟨hr, hle⟩ := ih
    have hstep : e8D4LeviReach (j :: l) δ =
        e8D4LeviReach l δ -
          iform (e8D4LeviSimple j) (e8D4LeviReach l δ) • e8D4LeviSimple j := rfl
    rw [hstep]
    refine ⟨?_, ExcE8Four.rootSubgroup_reflect_le_of_rootPair_le (e8D4Root_isRoot _)
      (rootSubgroup_leviSimple_pair_le j) hr hle⟩
    change IsRoot .E8 (e8D4LeviReach l δ -
      iform (e8D4Root (Fin.castAdd 4 j)) (e8D4LeviReach l δ) • e8D4Root (Fin.castAdd 4 j))
    rw [← rootReflection_smul_SL (τ := Tag.E8) (fun ε hε => iform_self_of_isRoot_E8Fr hε)
      (e8D4Root_isRoot (Fin.castAdd 4 j))]
    exact IsRoot.smul hr _

theorem rootSpan_e8D4LeviRoots_le :
    rootSpan Tag.E8 K e8D4LeviRoots ≤
      (e8D4Levi K).map (adjointGroup Tag.E8 K).subtype := by
  refine iSup₂_le fun β hβ => ?_
  obtain ⟨e, -, he⟩ := e8D4LeviTable_spec β (mem_rootFinset.2 hβ.1) hβ.2
  have hstart : IsRoot .E8 (e8D4LeviSimple e.1) := e8D4Root_isRoot _
  rw [← he]
  exact (rootSubgroup_leviReach_le e.2 hstart
    (le_sup_left.trans (rootSubgroup_leviSimple_pair_le e.1))).2

theorem e8D4Levi_le_rootSpan_e8D4LeviRoots :
    (e8D4Levi K).map (adjointGroup Tag.E8 K).subtype ≤
      rootSpan Tag.E8 K e8D4LeviRoots := by
  rw [e8D4Levi_eq, Subgroup.map_iSup]
  refine iSup_le fun j => ?_
  simp only [rootPairE8, Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rintro x ⟨z, hz, rfl⟩
    have hmem : (z : ModGL Tag.E8 K) ∈ rootSubgroup Tag.E8 K (e8D4LeviSimple j) := by
      have h2 : z ∈ (rootSubgroup Tag.E8 K (e8D4LeviSimple j)).subgroupOf
          (adjointGroup Tag.E8 K) := by
        rw [subgroupOf_rootSubgroup_eq_rootGroup (rootOperatorFamily .E8)
          (show IsRoot .E8 (e8D4LeviSimple j) from e8D4Root_isRoot _)]
        exact hz
      exact Subgroup.mem_subgroupOf.1 h2
    refine rootSubgroup_le_rootSpan ?_ hmem
    refine ⟨e8D4Root_isRoot _, fun i => ?_⟩
    rw [iform_comm]
    simpa only [e8D4LeviSimple, e8D4PerpSimple] using (e8D4Root_facts j i).2.2.1
  · rintro x ⟨z, hz, rfl⟩
    have hmem : (z : ModGL Tag.E8 K) ∈ rootSubgroup Tag.E8 K (-(e8D4LeviSimple j)) := by
      have h2 : z ∈ (rootSubgroup Tag.E8 K (-(e8D4LeviSimple j))).subgroupOf
          (adjointGroup Tag.E8 K) := by
        rw [subgroupOf_rootSubgroup_eq_rootGroup (rootOperatorFamily .E8)
          (show IsRoot .E8 (-(e8D4LeviSimple j)) from IsRoot.neg (e8D4Root_isRoot _))]
        exact hz
      exact Subgroup.mem_subgroupOf.1 h2
    refine rootSubgroup_le_rootSpan ?_ hmem
    refine ⟨IsRoot.neg (e8D4Root_isRoot _), fun i => ?_⟩
    have hzero : iform (e8D4PerpSimple i) (e8D4LeviSimple j) = 0 := by
      rw [iform_comm]
      simpa only [e8D4LeviSimple, e8D4PerpSimple] using (e8D4Root_facts j i).2.2.1
    rw [iform_neg_right, hzero, neg_zero]

theorem rootSpan_e8D4LeviRoots_eq :
    rootSpan Tag.E8 K e8D4LeviRoots =
      (e8D4Levi K).map (adjointGroup Tag.E8 K).subtype :=
  le_antisymm rootSpan_e8D4LeviRoots_le e8D4Levi_le_rootSpan_e8D4LeviRoots

end Roots

section Structural

private theorem rootSpan_union_le {K : Type} [Field K] (S T : Set (Fin Tag.E8.rank → ℤ)) :
    rootSpan Tag.E8 K (S ∪ T) ≤ rootSpan Tag.E8 K S ⊔ rootSpan Tag.E8 K T := by
  refine iSup₂_le fun α hα => ?_
  rcases hα with h | h
  · exact le_sup_of_le_left
      (le_iSup₂ (f := fun α (_ : α ∈ S) => rootSubgroup Tag.E8 K α) α h)
  · exact le_sup_of_le_right
      (le_iSup₂ (f := fun α (_ : α ∈ T) => rootSubgroup Tag.E8 K α) α h)

theorem kernelRoots_d4d4Char_subset :
    kernelRoots d4d4Char ⊆ e8D4LeviRoots ∪ e8D4PerpRoots := by
  have hcheck : ∀ α ∈ rootFinset .E8, d4d4Char (Multiplicative.ofAdd α) = 1 →
      (∀ j : Fin 4, iform (e8D4PerpSimple j) α = 0) ∨
        (∀ j : Fin 4, iform (e8D4LeviSimple j) α = 0) := by
    decide +kernel
  rintro α ⟨hroot, hχ⟩
  rcases hcheck α (mem_rootFinset.2 hroot) hχ with h | h
  · exact Or.inl ⟨hroot, h⟩
  · exact Or.inr ⟨hroot, h⟩

theorem torus_sup_rootSpan_levi_le_normalizer_perp {L : Type} [Field L] :
    torusGroup .E8 L ⊔ rootSpan .E8 L e8D4LeviRoots ≤
      Subgroup.normalizer (rootSpan .E8 L e8D4PerpRoots : Set (ModGL .E8 L)) := by
  have hcen : (e8D4Levi L).map (adjointGroup .E8 L).subtype ≤
      Subgroup.centralizer
        ((e8D4Perp L).map (adjointGroup .E8 L).subtype : Set (ModGL .E8 L)) := by
    rintro x ⟨x', hx', rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro y ⟨y', hy', rfl⟩
    exact (congrArg Subtype.val (e8D4Levi_commute_perp x' hx' y' hy')).symm
  refine sup_le (CFSG.LieType.Chevalley.torusGroup_le_normalizer_rootSpan
    (S := e8D4PerpRoots) (fun α hα => hα.1)) ?_
  rw [rootSpan_e8D4LeviRoots_eq, rootSpan_e8D4PerpRoots_eq]
  exact hcen.trans (Subgroup.centralizer_le_normalizer _)

theorem torus_sup_rootSpan_d4d4_le_normalizer_perp {L : Type} [Field L] :
    torusGroup .E8 L ⊔ rootSpan .E8 L (kernelRoots d4d4Char) ≤
      Subgroup.normalizer (rootSpan .E8 L e8D4PerpRoots : Set (ModGL .E8 L)) := by
  refine sup_le (CFSG.LieType.Chevalley.torusGroup_le_normalizer_rootSpan
    (S := e8D4PerpRoots) (fun α hα => hα.1)) ?_
  refine (rootSpan_mono kernelRoots_d4d4Char_subset).trans ?_
  refine (rootSpan_union_le _ _).trans ?_
  refine sup_le ?_ ?_
  · exact le_sup_right.trans (torus_sup_rootSpan_levi_le_normalizer_perp (L := L))
  · rw [rootSpan_e8D4PerpRoots_eq]
    exact Subgroup.le_normalizer

end Structural

section Descent

private theorem sup_kernelRoots_le_sup_levi_perp {L : Type} [Field L] :
    torusGroup .E8 L ⊔ rootSpan .E8 L (kernelRoots d4d4Char) ≤
      (torusGroup .E8 L ⊔ rootSpan .E8 L e8D4LeviRoots) ⊔ rootSpan .E8 L e8D4PerpRoots := by
  refine sup_le (le_sup_of_le_left le_sup_left) ?_
  refine (rootSpan_mono kernelRoots_d4d4Char_subset).trans ?_
  exact (rootSpan_union_le _ _).trans
    (sup_le (le_sup_of_le_left le_sup_right) le_sup_right)

theorem mem_e8D4Levi_of_adjEmb_eq {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L]
    {n : ℕ} (hn : Nat.Coprime n (Nat.card K - 1))
    {g : ModGL .E8 L} (hgM : g ∈ torusGroup .E8 L ⊔ rootSpan .E8 L (kernelRoots d4d4Char))
    {a : Fin Tag.E8.rank → Lˣ} (ha : e8D4PerpRoots ⊆ rootCharKernel a)
    {x : adjointGroup .E8 K} (hx : adjEmb .E8 K L x = g * rootDiagUnit .E8 a * g⁻¹)
    (hxn : x ^ n = 1) : x ∈ e8D4Levi K := by
  have hgM' : g ∈ (torusGroup .E8 L ⊔ rootSpan .E8 L e8D4LeviRoots) ⊔
      rootSpan .E8 L e8D4PerpRoots :=
    sup_kernelRoots_le_sup_levi_perp hgM
  have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right
    (torusGroup .E8 L ⊔ rootSpan .E8 L e8D4LeviRoots)
    (rootSpan .E8 L e8D4PerpRoots) (torus_sup_rootSpan_levi_le_normalizer_perp (L := L))
  have hgM'' : g ∈ ((torusGroup .E8 L ⊔ rootSpan .E8 L e8D4LeviRoots :
      Subgroup (ModGL .E8 L)) : Set (ModGL .E8 L)) *
        (rootSpan .E8 L e8D4PerpRoots : Set (ModGL .E8 L)) := by
    rw [← hcoe]
    exact hgM' 
  obtain ⟨m, hm, r, hr, hg_eq⟩ := hgM''
  rw [← hg_eq] at hx
  have hcent : r ∈ Subgroup.centralizer {rootDiagUnit .E8 a} :=
    rootSpan_le_centralizer a ha hr
  have hrcomm : r * rootDiagUnit .E8 a * r⁻¹ = rootDiagUnit .E8 a := by
    have h := (Subgroup.mem_centralizer_singleton_iff.1 hcent).symm
    rw [← h]
    group
  have hgd : (m * r) * rootDiagUnit .E8 a * (m * r)⁻¹ =
      m * rootDiagUnit .E8 a * m⁻¹ := by
    rw [mul_inv_rev]
    calc m * r * rootDiagUnit .E8 a * (r⁻¹ * m⁻¹)
        = m * (r * rootDiagUnit .E8 a * r⁻¹) * m⁻¹ := by group
      _ = m * rootDiagUnit .E8 a * m⁻¹ := by rw [hrcomm]
  have hdH : rootDiagUnit .E8 a ∈ torusGroup .E8 L :=
    CFSG.SeitzReduction.E8Pilot.rootDiagUnit_mem_torusGroup_E8 a
  have hmemL : m * rootDiagUnit .E8 a * m⁻¹ ∈
      torusGroup .E8 L ⊔ rootSpan .E8 L e8D4LeviRoots :=
    mul_mem (mul_mem hm (Subgroup.mem_sup_left hdH)) (inv_mem hm)
  have hbase : baseChangeGL (algebraMap K L) (x : ModGL .E8 K) ∈
      torusGroup .E8 L ⊔ rootSpan .E8 L e8D4LeviRoots := by
    rw [← adjEmb_apply]
    rw [hx, hgd]
    exact hmemL
  have hdesc : (x : ModGL .E8 K) ∈ torusGroup .E8 K ⊔
      rootSpan .E8 K (kernelRoots (iformChar e8D4PerpSimple)) :=
    mem_torus_sup_rootSpan_of_baseChangeGL_mem (algebraMap K L)
      (iformChar e8D4PerpSimple) (x := (x : ModGL .E8 K)) x.2 (by
        rw [kernelRoots_iformChar_levi]
        exact hbase)
  rw [kernelRoots_iformChar_levi] at hdesc
  have hxn' : (x : ModGL .E8 K) ^ n = 1 := by
    have h := congrArg Subtype.val hxn
    simpa using h
  have hstrip : (x : ModGL .E8 K) ∈ rootSpan .E8 K e8D4LeviRoots :=
    mem_rootSpan_of_mem_torus_sup_of_pow_eq_one (S := e8D4LeviRoots)
      (fun α hα => hα.1) hn hdesc hxn'
  rw [rootSpan_e8D4LeviRoots_eq] at hstrip
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hstrip
  have hyx' : y = x := Subtype.ext hyx
  rwa [hyx'] at hy

end Descent

section Kernels

private theorem perp_exponent_zero :
    ∀ α ∈ rootFinset .E8, (∀ j : Fin 4, iform (e8D4LeviSimple j) α = 0) →
      (α 1 + α 2 - α 0 - α 4 = 0 ∧ 2 * α 3 - α 1 - α 2 - α 4 = 0) ∧
        (2 * α 4 - α 3 - α 5 = 0 ∧ 2 * α 1 - α 3 = 0) := by
  decide +kernel

theorem perpRoots_subset_rootCharKernel_d6 {K : Type} [Field K] {p : ℕ} [Fact p.Prime]
    {ζ : Kˣ} (lam : ZMod p) :
    e8D4PerpRoots ⊆ rootCharKernel (d6TorsionChar p ζ lam) := by
  rintro α ⟨hroot, hperp⟩
  have hz := perp_exponent_zero α (mem_rootFinset.2 hroot) hperp
  refine ⟨hroot, ?_⟩
  rw [rootChar_d6TorsionChar, hz.1.1, hz.1.2]
  simp

theorem perpRoots_subset_rootCharKernel_d6z {K : Type} [Field K] {p : ℕ} [Fact p.Prime]
    {ζ : Kˣ} (lam : ZMod p) :
    e8D4PerpRoots ⊆ rootCharKernel (d6zTorsionChar p ζ lam) := by
  rintro α ⟨hroot, hperp⟩
  have hz := perp_exponent_zero α (mem_rootFinset.2 hroot) hperp
  refine ⟨hroot, ?_⟩
  rw [rootChar_d6zTorsionChar, hz.2.1, hz.2.2]
  simp

end Kernels

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Four
