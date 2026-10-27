module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166E6FourCent2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Layer
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcLang.Family

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Chevalley.C2E6Overlap CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.ExceptionalCover
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Certs

private theorem prod_zpow_eq_zpow_sum {G : Type*} [CommGroup G] {ι : Type} (s : Finset ι)
    (g : G) (n : ι → ℤ) : ∏ i ∈ s, g ^ n i = g ^ ∑ i ∈ s, n i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, zpow_add, ih]

private theorem e6FourToralParam_pow_three (i : Fin Tag.E6.rank) : e6FourToralParam i ^ 3 = 1 := by
  have hval : e6FourToralParam i =
      omegaUnit ^ (∑ j : Fin Tag.E6.rank, e6FourToralExponent j * Tag.E6.cartan j i) := by
    rw [e6FourToralParam, cartanChar]
    simp only [CFSG.LieType.Steinberg.CentralExt.AdjointClosed.tvec]
    rw [Finset.prod_congr rfl (fun j _ => by rw [← zpow_mul])]
    exact prod_zpow_eq_zpow_sum Finset.univ omegaUnit
      (fun j => e6FourToralExponent j * Tag.E6.cartan j i)
  rw [hval, ← zpow_natCast, ← zpow_mul, mul_comm, omegaUnit_zpow_eq_one_iff]
  exact dvd_mul_right 3 _

private theorem e6FourToralParam_isSolvable_quotient :
    Group.IsSolvable (↥(rootCharStabilizerSubgroup e6FourToralParam) ⧸
      (kernelReflectionGroup e6FourToralParam).subgroupOf
        (rootCharStabilizerSubgroup e6FourToralParam)) :=
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.isSolvable_quotient
    Nat.prime_three e6FourToralParam_pow_three

private instance e6FourJ_normal_in_toralCentralizer :
    ((subsystemGroup Tag.E6 K setD).subgroupOf
      (toralCentralizer Tag.E6 K e6FourToralParam)).Normal := by
  rw [← rootSpan_rootCharKernel_e6FourToralParam]
  infer_instance

private theorem e6FourToralRootGroup_eq_sup :
    toralRootGroup Tag.E6 K e6FourToralParam =
      torusGroup Tag.E6 K ⊔ subsystemGroup Tag.E6 K setD := by
  show torusGroup Tag.E6 K ⊔ rootSpan Tag.E6 K (rootCharKernel e6FourToralParam) = _
  rw [rootSpan_rootCharKernel_e6FourToralParam]

private instance e6FourToralRootGroup_normal_in_toralCentralizer :
    ((toralRootGroup Tag.E6 K e6FourToralParam).subgroupOf
      (toralCentralizer Tag.E6 K e6FourToralParam)).Normal := by
  obtain ⟨-, h, -, -, -, -, -⟩ :=
    Chevalley_toral_centralizer_root_generated_quotient Tag.E6 K e6FourToralParam
  exact h

private theorem isSolvable_toralCentralizer_quotient :
    Group.IsSolvable (↥(toralCentralizer Tag.E6 K e6FourToralParam) ⧸
      (toralRootGroup Tag.E6 K e6FourToralParam).subgroupOf
        (toralCentralizer Tag.E6 K e6FourToralParam)) := by
  obtain ⟨-, -, -, -, φ, hφ, -⟩ :=
    Chevalley_toral_centralizer_root_generated_quotient Tag.E6 K e6FourToralParam
  haveI := e6FourToralParam_isSolvable_quotient
  exact Group.isSolvable_of_surjective hφ

private theorem isSolvable_toralCentralizer_J :
    Group.IsSolvable (↥(toralCentralizer Tag.E6 K e6FourToralParam) ⧸
      (subsystemGroup Tag.E6 K setD).subgroupOf
        (toralCentralizer Tag.E6 K e6FourToralParam)) := by
  let C := toralCentralizer Tag.E6 K e6FourToralParam
  let J : Subgroup (ModGL Tag.E6 K) := subsystemGroup Tag.E6 K setD
  let M : Subgroup (ModGL Tag.E6 K) := torusGroup Tag.E6 K ⊔ J
  have hJC : J ≤ C := subsystemGroup_le_toralCentralizer_e6FourToralParam
  have hJM : J ≤ M := le_sup_right
  have hMC : M ≤ C := sup_le (torusGroup_le_toralCentralizer e6FourToralParam) hJC
  have hT : torusGroup Tag.E6 K ≤ Subgroup.normalizer (J : Set (ModGL Tag.E6 K)) := by
    rw [show J = rootSpan Tag.E6 K (rootCharKernel e6FourToralParam) from
      rootSpan_rootCharKernel_e6FourToralParam.symm]
    exact torusGroup_le_normalizer_rootSpan
      (S := rootCharKernel e6FourToralParam) (fun α hα => hα.1)
  haveI hMnorm : (J.subgroupOf M).Normal :=
    Subgroup.normal_subgroupOf_sup_of_le_normalizer hT
  have hMJs : Group.IsSolvable (↥M ⧸ (J.subgroupOf M)) :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.isSolvable_sup_quotient_of_comm
      (fun x hx y hy => CFSG.LieType.Chevalley.RootTorus.torusGroup_mul_comm hx hy) hT
  have hMnormal : (M.subgroupOf C).Normal := by
    rw [show M = toralRootGroup Tag.E6 K e6FourToralParam from
      e6FourToralRootGroup_eq_sup.symm]
    infer_instance
  haveI := hMnormal
  have hCMs : Group.IsSolvable (↥C ⧸ (M.subgroupOf C)) := by
    have heq : (toralRootGroup Tag.E6 K e6FourToralParam).subgroupOf C = M.subgroupOf C := by
      rw [show M = toralRootGroup Tag.E6 K e6FourToralParam from e6FourToralRootGroup_eq_sup.symm]
    haveI : ((toralRootGroup Tag.E6 K e6FourToralParam).subgroupOf C).Normal :=
      e6FourToralRootGroup_normal_in_toralCentralizer
    haveI := isSolvable_toralCentralizer_quotient
    exact Group.isSolvable_of_isSolvable_injective
      (f := (QuotientGroup.quotientMulEquivOfEq heq).symm.toMonoidHom)
      (QuotientGroup.quotientMulEquivOfEq heq).symm.injective
  haveI := hMJs
  haveI := hCMs
  let f : (↥M ⧸ (J.subgroupOf M)) →* (↥C ⧸ (J.subgroupOf C)) :=
    QuotientGroup.map (N := J.subgroupOf M) (M := J.subgroupOf C)
      (Subgroup.inclusion hMC) (by
        intro x hx
        exact hx)
  let g : (↥C ⧸ (J.subgroupOf C)) →* (↥C ⧸ (M.subgroupOf C)) :=
    QuotientGroup.map (N := J.subgroupOf C) (M := M.subgroupOf C)
      (MonoidHom.id ↥C) (by
        intro x hx
        exact hJM hx)
  have hfg : g.ker ≤ f.range := by
    rintro x hx
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective x
    rw [MonoidHom.mem_ker] at hx
    simp only [g, QuotientGroup.map_mk'] at hx
    have hcM : (c : ↥C) ∈ M.subgroupOf C := (QuotientGroup.eq_one_iff _).1 hx
    refine ⟨QuotientGroup.mk ⟨c, hcM⟩, ?_⟩
    simp only [f, QuotientGroup.map_mk']
    rfl
  exact Group.isSolvable_of_ker_le_range f g hfg

private theorem centralizer_e6FourX_eq_toralCentralizer_subgroupOf :
    Subgroup.centralizer ({e6FourX} : Set (adjointGroup Tag.E6 K)) =
      (toralCentralizer Tag.E6 K e6FourToralParam).subgroupOf
        (adjointGroup Tag.E6 K) := by
  ext g
  constructor
  · intro hg
    refine Subgroup.mem_inf.2 ⟨g.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hg e6FourX (Set.mem_singleton _))
  · intro hg
    have hc := (Subgroup.mem_inf.1 hg).2
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    apply Subtype.ext
    exact hc (rootDiagUnit Tag.E6 e6FourToralParam) (Set.mem_singleton _)

theorem e6FourJ_comp :
    IsComponentOf e6FourJ
        (Subgroup.centralizer ({e6FourX} : Set (adjointGroup Tag.E6 K))) ∧
      GLALayer (Subgroup.centralizer ({e6FourX} : Set (adjointGroup Tag.E6 K))) = e6FourJ := by
  let G := adjointGroup Tag.E6 K
  let C := toralCentralizer Tag.E6 K e6FourToralParam
  let J : Subgroup (ModGL Tag.E6 K) := subsystemGroup Tag.E6 K setD
  let CG : Subgroup G := C.subgroupOf G
  let JG : Subgroup G := J.subgroupOf G
  have hC : C ≤ G := inf_le_left
  have hJC : J ≤ C := subsystemGroup_le_toralCentralizer_e6FourToralParam
  have hCGeq : Subgroup.centralizer ({e6FourX} : Set G) = CG :=
    centralizer_e6FourX_eq_toralCentralizer_subgroupOf
  have hJCG : JG ≤ CG := fun x hx => hJC hx
  have hCN : C ≤ Subgroup.normalizer (J : Set (ModGL Tag.E6 K)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJC).1 e6FourJ_normal_in_toralCentralizer
  have hCGN : CG ≤ Subgroup.normalizer (JG : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hg' : (g : ModGL Tag.E6 K) ∈ C := Subgroup.mem_subgroupOf.1 hg
    constructor
    · intro hx
      exact Subgroup.mem_subgroupOf.2
        ((Subgroup.mem_normalizer_iff.1 (hCN hg') (x : ModGL Tag.E6 K)).1
          (Subgroup.mem_subgroupOf.1 hx))
    · intro hx
      have hx' : (g : ModGL Tag.E6 K) * (x : ModGL Tag.E6 K) * (g : ModGL Tag.E6 K)⁻¹ ∈ J :=
        Subgroup.mem_subgroupOf.1 hx
      exact Subgroup.mem_subgroupOf.2
        ((Subgroup.mem_normalizer_iff.1 (hCN hg') (x : ModGL Tag.E6 K)).2 hx')
  have hN : (JG.subgroupOf CG).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJCG).2 hCGN
  haveI := hN
  let e : CG ≃* C := Subgroup.subgroupOfEquivOfLe hC
  have hmapJ : (JG.subgroupOf CG).map e.toMonoidHom = J.subgroupOf C := by
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 hg)
    · intro hx
      have hxJ : (x : ModGL Tag.E6 K) ∈ J := Subgroup.mem_subgroupOf.1 hx
      refine ⟨⟨⟨(x : ModGL Tag.E6 K), subsystemGroup_le_adjointGroup_E6 hxJ⟩, hJC hxJ⟩, ?_, ?_⟩
      · exact Subgroup.mem_subgroupOf.2 hxJ
      · rfl
  let g : (↥C ⧸ J.subgroupOf C) →* (↥CG ⧸ JG.subgroupOf CG) :=
    QuotientGroup.map (N := J.subgroupOf C) (M := JG.subgroupOf CG) e.symm.toMonoidHom (by
      intro x hx
      have hxJ : (x : ModGL Tag.E6 K) ∈ J := Subgroup.mem_subgroupOf.1 hx
      have hxG : (x : ModGL Tag.E6 K) ∈ G := subsystemGroup_le_adjointGroup_E6 hxJ
      have h1 : (⟨(x : ModGL Tag.E6 K), hxG⟩ : G) ∈ JG := Subgroup.mem_subgroupOf.2 hxJ
      change (((e.symm x : CG) : G)) ∈ JG
      exact h1)
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    refine ⟨QuotientGroup.mk ⟨(x : ModGL Tag.E6 K), Subgroup.mem_subgroupOf.1 x.2⟩, ?_⟩
    simp only [g, QuotientGroup.map_mk']
    rfl
  have hsolv : Group.IsSolvable (↥CG ⧸ JG.subgroupOf CG) := by
    exact @Group.isSolvable_of_surjective (↥C ⧸ J.subgroupOf C)
      (↥CG ⧸ JG.subgroupOf CG) _ _ g hg isSolvable_toralCentralizer_J
  have hJq : CFSG.IsQuasisimple ↥JG := isQuasisimple_e6FourJ
  have hcomp := isComponentOf_and_glaLayer_eq_of_normal_solvable_of_isQuasisimple
    hJCG hN hJq hsolv
  rw [← hCGeq] at hcomp
  exact hcomp

end Certs

end CFSG.LocalAnalysis.GLTheoremA.Y10F
