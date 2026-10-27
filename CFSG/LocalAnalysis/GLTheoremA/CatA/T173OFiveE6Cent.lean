module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveLayer
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.LocalAnalysis.ComponentInitial.SylowLocalTransfer
public import CFSG.LieType.Chevalley.OddToralInvolutionComponents
public import CFSG.LieType.Chevalley.ToralCentralizerQuotient
public import CFSG.LieType.Chevalley.RankOneCentralImage
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotPositionPerfect
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeHat
public import CFSG.Blueprint.SourceExceptionalRootData
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotPositionB

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section PowerFix

variable {F : Type} [Field F]

private theorem zpow_apply_fixed {g : ModGL Tag.E6 F} {v : RootModule Tag.E6 F}
    (h : (g : Module.End F (RootModule Tag.E6 F)) v = v) (m : ℤ) :
    (((g ^ m : ModGL Tag.E6 F)) : Module.End F (RootModule Tag.E6 F)) v = v := by
  have hinv : (((g⁻¹ : ModGL Tag.E6 F)) : Module.End F (RootModule Tag.E6 F)) v = v := by
    have h1 : (((g⁻¹ : ModGL Tag.E6 F)) : Module.End F (RootModule Tag.E6 F))
        (((g : ModGL Tag.E6 F) : Module.End F (RootModule Tag.E6 F)) v) =
        (((g⁻¹ * g : ModGL Tag.E6 F)) : Module.End F (RootModule Tag.E6 F)) v := by
      rw [Units.val_mul, Module.End.mul_apply]
    rwa [h, inv_mul_cancel, Units.val_one, Module.End.one_apply] at h1
  refine zpow_induction_right (g := g)
    (P := fun a : ModGL Tag.E6 F =>
      ((a : Module.End F (RootModule Tag.E6 F)) v = v)) ?_ ?_ ?_ m
  · rw [Units.val_one, Module.End.one_apply]
  · intro a ha
    rw [Units.val_mul, Module.End.mul_apply, h, ha]
  · intro a ha
    rw [Units.val_mul, Module.End.mul_apply, hinv, ha]

end PowerFix

section TorusThree

variable {F : Type} [Field F]

private theorem e6TorusThree_le_torusGroup {ζ : Fˣ} :
    e6TorusThree F ζ ≤ torusGroup Tag.E6 F := by
  rw [e6TorusThree]
  exact (Subgroup.closure_le _).2 (by rintro _ ⟨i, rfl⟩; exact torusElt_mem_torusGroup i ζ)

private theorem sq_ne_one_of_orderOf_eq_three {ζ : Fˣ} (hζ : orderOf ζ = 3) :
    (ζ ^ 2 : F) ≠ 1 := by
  intro h
  have h2 : ζ ^ 2 = 1 := Units.ext h
  have hdvd : orderOf ζ ∣ 2 := orderOf_dvd_iff_pow_eq_one.2 h2
  rw [hζ] at hdvd
  norm_num at hdvd

private theorem torusElt_apply_rootVec_self (i : Fin Tag.E6.rank) (t : Fˣ) :
    (((torusElt Tag.E6 F i t : ModGL Tag.E6 F)) : Module.End F (RootModule Tag.E6 F))
        (rootVec Tag.E6 F (Pi.single i 1)) =
      ((t ^ 2 : Fˣ) : F) • rootVec Tag.E6 F (Pi.single i 1) := by
  rw [torusElt_rootVec i t (isRoot_single Tag.E6 i), sum_cartan_mul_pi_single,
    CFSG.Blueprint.EvenSource.cartan_apply_self]
  rfl

private theorem torusElt_apply_rootVec_of_cartan_eq_zero {i j : Fin Tag.E6.rank}
    (hij : Tag.E6.cartan i j = 0) (t : Fˣ) :
    (((torusElt Tag.E6 F i t : ModGL Tag.E6 F)) : Module.End F (RootModule Tag.E6 F))
        (rootVec Tag.E6 F (Pi.single j 1)) = rootVec Tag.E6 F (Pi.single j 1) := by
  rw [torusElt_rootVec i t (isRoot_single Tag.E6 j), sum_cartan_mul_pi_single, hij, zpow_zero,
    Units.val_one, one_smul]

private theorem not_torusElt_zero_mem_zpowers {ζ : Fˣ} (hζ : orderOf ζ = 3) :
    torusElt Tag.E6 F 0 ζ ∉ Subgroup.zpowers (torusElt Tag.E6 F 1 ζ) := by
  intro hmem
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hmem
  set w : RootModule Tag.E6 F := rootVec Tag.E6 F (Pi.single (0 : Fin Tag.E6.rank) 1) with hwdef
  have hw : w ≠ 0 := by
    rw [hwdef, rootVec_eq_single_of_isRoot (isRoot_single Tag.E6 0)]
    exact Finsupp.single_ne_zero.2 one_ne_zero
  have hyw : (((torusElt Tag.E6 F 1 ζ : ModGL Tag.E6 F)) :
      Module.End F (RootModule Tag.E6 F)) w = w := by
    rw [hwdef]
    exact torusElt_apply_rootVec_of_cartan_eq_zero (i := 1) (j := 0) (by decide) ζ
  have hxw : (((torusElt Tag.E6 F 0 ζ : ModGL Tag.E6 F)) :
      Module.End F (RootModule Tag.E6 F)) w = (ζ ^ 2 : F) • w := by
    rw [hwdef]
    exact torusElt_apply_rootVec_self 0 ζ
  have hfix : ((((torusElt Tag.E6 F 1 ζ) ^ m : ModGL Tag.E6 F)) :
      Module.End F (RootModule Tag.E6 F)) w = w := zpow_apply_fixed hyw m
  rw [hm] at hfix
  rw [hxw] at hfix
  have h3 : (ζ ^ 2 : F) • w = (1 : F) • w := by simpa using hfix
  exact sq_ne_one_of_orderOf_eq_three hζ (smul_left_injective F hw h3)

private theorem not_e6TorusThree_le_zpowers {ζ : Fˣ} (hζ : orderOf ζ = 3)
    (g : ModGL Tag.E6 F) : ¬ e6TorusThree F ζ ≤ Subgroup.zpowers g := by
  intro hle
  have hζ3 : ζ ^ 3 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have hζ2 := sq_ne_one_of_orderOf_eq_three (F := F) hζ
  have hx1 : torusElt Tag.E6 F 0 ζ ≠ 1 := by
    intro h
    have h2 := sq_eq_one_of_torusElt_eq_one (τ := Tag.E6) (K := F) 0 h
    exact hζ2 (by simpa using h2)
  have hy1 : torusElt Tag.E6 F 1 ζ ≠ 1 := by
    intro h
    have h2 := sq_eq_one_of_torusElt_eq_one (τ := Tag.E6) (K := F) 1 h
    exact hζ2 (by simpa using h2)
  have hx3 : torusElt Tag.E6 F 0 ζ ^ 3 = 1 := by
    change (torusEltHom (τ := Tag.E6) (K := F) 0 ζ) ^ 3 = 1
    rw [← map_pow, hζ3, map_one]
  have hy3 : torusElt Tag.E6 F 1 ζ ^ 3 = 1 := by
    change (torusEltHom (τ := Tag.E6) (K := F) 1 ζ) ^ 3 = 1
    rw [← map_pow, hζ3, map_one]
  set C : Subgroup (ModGL Tag.E6 F) := Subgroup.zpowers g with hC
  haveI : IsCyclic ↥C := Subgroup.isCyclic_zpowers g
  have hxT : torusElt Tag.E6 F 0 ζ ∈ e6TorusThree F ζ :=
    Subgroup.subset_closure (Set.mem_range_self (0 : Fin Tag.E6.rank))
  have hyT : torusElt Tag.E6 F 1 ζ ∈ e6TorusThree F ζ :=
    Subgroup.subset_closure (Set.mem_range_self (1 : Fin Tag.E6.rank))
  have hxG : torusElt Tag.E6 F 0 ζ ∈ C := hle hxT
  have hyG : torusElt Tag.E6 F 1 ζ ∈ C := hle hyT
  set xC : ↥C := ⟨torusElt Tag.E6 F 0 ζ, hxG⟩ with hxC
  set yC : ↥C := ⟨torusElt Tag.E6 F 1 ζ, hyG⟩ with hyC
  have hx3C : xC ^ 3 = 1 := Subtype.ext hx3
  have hy3C : yC ^ 3 = 1 := Subtype.ext hy3
  have hx1C : xC ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  have hy1C : yC ≠ 1 := fun h => hy1 (congrArg Subtype.val h)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hxo : orderOf xC = 3 := orderOf_eq_prime hx3C hx1C
  have hyo : orderOf yC = 3 := orderOf_eq_prime hy3C hy1C
  haveI : Finite ↥(Subgroup.zpowers xC) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hxo]; norm_num)
  have hle' : Subgroup.zpowers xC ≤ Subgroup.zpowers yC := by
    rw [IsCyclic.subgroup_le_iff_card_dvd, Nat.card_zpowers, Nat.card_zpowers, hxo, hyo]
  have hxmem : xC ∈ Subgroup.zpowers yC := hle' (Subgroup.mem_zpowers xC)
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hxmem
  refine not_torusElt_zero_mem_zpowers (F := F) hζ ⟨m, ?_⟩
  have h := congrArg (fun t : ↥C => (t : ModGL Tag.E6 F)) hm
  simpa [xC, yC] using h

end TorusThree

section RootLayer


theorem rootSubgroup_le_stdLayerD {F : Type} [Field F] [Finite F] [CharP F 2]
    (hq : 4 ≤ Nat.card F) {c : Fin Tag.E6.rank → Fˣ} (hc3 : ∀ i, c i ^ 3 = 1)
    (hd1 : rootDiagUnit Tag.E6 c ≠ 1) {α : Fin Tag.E6.rank → ℤ}
    (hα : α ∈ rootCharKernel c) :
    rootSubgroup Tag.E6 F α ≤ stdLayerD (adjointGroup Tag.E6 F) (rootDiagUnit Tag.E6 c) := by
  classical
  have hαroot : IsRoot Tag.E6 α := hα.1
  have hneg : -α ∈ rootCharKernel c := by
    refine ⟨IsRoot.neg hαroot, ?_⟩
    rw [show -α = (-1 : ℤ) • α from (neg_one_smul ℤ α).symm, rootChar_zsmul, zpow_neg_one,
      hα.2, inv_one]
  have hQle : rootSubgroup Tag.E6 F α ⊔ rootSubgroup Tag.E6 F (-α) ≤
      toralCentralizer Tag.E6 F c :=
    sup_le ((le_iSup₂_of_le α hα le_rfl).trans (rootSpan_rootCharKernel_le_toralCentralizer c))
      ((le_iSup₂_of_le (-α) hneg le_rfl).trans (rootSpan_rootCharKernel_le_toralCentralizer c))
  have hQadj : rootSubgroup Tag.E6 F α ⊔ rootSubgroup Tag.E6 F (-α) ≤
      adjointGroup Tag.E6 F := hQle.trans inf_le_left
  have hQcent : rootSubgroup Tag.E6 F α ⊔ rootSubgroup Tag.E6 F (-α) ≤
      Subgroup.centralizer ({rootDiagUnit Tag.E6 c} : Set (ModGL Tag.E6 F)) :=
    hQle.trans inf_le_right
  have hQperf : ⁅rootSubgroup Tag.E6 F α ⊔ rootSubgroup Tag.E6 F (-α),
      rootSubgroup Tag.E6 F α ⊔ rootSubgroup Tag.E6 F (-α)⁆ =
      rootSubgroup Tag.E6 F α ⊔ rootSubgroup Tag.E6 F (-α) :=
    CFSG.SeitzReduction.E8Pilot.commutator_rootSubgroup_sup_neg (τ := Tag.E6) (K := F) hq hαroot
  have hd3 : rootDiagUnit Tag.E6 c ^ 3 = 1 := by
    rw [rootDiagUnit_pow]
    rw [show c ^ 3 = 1 from funext hc3, rootDiagUnit_one]
  have hQlayer : rootSubgroup Tag.E6 F α ⊔ rootSubgroup Tag.E6 F (-α) ≤
      stdLayerD (adjointGroup Tag.E6 F) (rootDiagUnit Tag.E6 c) :=
    le_stdLayerD_E6_of_perfect
      (CFSG.StandardType.TableBExc.E6Three.rootDiagUnit_mem_hatGroup c) hd1 hd3 hQadj hQcent
      hQperf
  exact le_sup_left.trans hQlayer

end RootLayer

section ComponentCases

variable {F : Type} [Field F]

private theorem isSolvable_torusGroup :
    Group.IsSolvable ↥(torusGroup Tag.E6 F) := by
  refine Group.isSolvable_of_comm fun x y => Subtype.ext ?_
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup x.2
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup y.2
  show (x : ModGL Tag.E6 F) * (y : ModGL Tag.E6 F) =
    (y : ModGL Tag.E6 F) * (x : ModGL Tag.E6 F)
  rw [ha, hb, ← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]

private theorem false_of_component_le_torus {L M H X : Subgroup (ModGL Tag.E6 F)}
    (hLmem : L ≤ X) (hMX : M ≤ X) (hM : M = H) (hH : H = torusGroup Tag.E6 F)
    (hls : CFSG.Assembly.IsQuasisimple L)
    (hLM : L.subgroupOf X ≤ M.subgroupOf X) : False := by
  have hLM' : L ≤ M := by
    have h := Subgroup.map_mono hLM (f := X.subtype)
    rwa [Subgroup.map_subgroupOf_eq_of_le hLmem,
      Subgroup.map_subgroupOf_eq_of_le hMX] at h
  have hLH : L ≤ H := hM ▸ hLM'
  haveI : Group.IsSolvable ↥H := hH ▸ isSolvable_torusGroup
  exact CFSG.LocalAnalysis.ComponentInitial.not_le_of_isQuasisimple_of_isSolvable
    hls ‹Group.IsSolvable ↥H› hLH

private theorem false_of_commutator_component_toralRootGroup {ζ : Fˣ}
    {A L M X : Subgroup (ModGL Tag.E6 F)} {d : ModGL Tag.E6 F}
    (hζ : orderOf ζ = 3) (hLmem : L ≤ X) (hMX : M ≤ X)
    (hM : M = torusGroup Tag.E6 F) (hA : e6TorusThree F ζ ≤ A)
    (hcent : A ⊓ Subgroup.centralizer (L : Set (ModGL Tag.E6 F)) = Subgroup.zpowers d)
    (hcomm : ⁅L.subgroupOf X, M.subgroupOf X⁆ = ⊥) : False := by
  have hcomm' : ⁅M, L⁆ = ⊥ := by
    have h := congrArg (Subgroup.map X.subtype) hcomm
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hLmem,
      Subgroup.map_subgroupOf_eq_of_le hMX, Subgroup.map_bot] at h
    rw [Subgroup.commutator_comm]
    exact h
  have hMcent : M ≤ Subgroup.centralizer (L : Set (ModGL Tag.E6 F)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm'
  have hTle : e6TorusThree F ζ ≤ A ⊓ Subgroup.centralizer (L : Set (ModGL Tag.E6 F)) := by
    refine le_inf hA fun t ht => hMcent ?_
    rw [hM]
    exact e6TorusThree_le_torusGroup ht
  rw [hcent] at hTle
  exact not_e6TorusThree_le_zpowers hζ d hTle

end ComponentCases

section KernelNonempty


theorem rootCharKernel_nonempty_of_torusThree_le {F : Type} [Field F] [Finite F] [CharP F 2]
    {ζ : Fˣ} (hζ : orderOf ζ = 3) {A : Subgroup (ModGL Tag.E6 F)}
    (hA : e6TorusThree F ζ ≤ A) {c : Fin Tag.E6.rank → Fˣ}
    (hcomp : IsComponentOf (stdLayerD (adjointGroup Tag.E6 F) (rootDiagUnit Tag.E6 c))
      (adjointGroup Tag.E6 F ⊓
        Subgroup.centralizer ({rootDiagUnit Tag.E6 c} : Set (ModGL Tag.E6 F))))
    (hcent : A ⊓ Subgroup.centralizer
        (stdLayerD (adjointGroup Tag.E6 F) (rootDiagUnit Tag.E6 c) : Set (ModGL Tag.E6 F)) =
      Subgroup.zpowers (rootDiagUnit Tag.E6 c)) :
    (rootCharKernel c).Nonempty := by
  classical
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  set d := rootDiagUnit Tag.E6 c with hddef
  set X : Subgroup (ModGL Tag.E6 F) :=
    adjointGroup Tag.E6 F ⊓ Subgroup.centralizer ({d} : Set (ModGL Tag.E6 F)) with hXdef
  set L : Subgroup (ModGL Tag.E6 F) := stdLayerD (adjointGroup Tag.E6 F) d with hLdef
  set H : Subgroup (ModGL Tag.E6 F) := torusGroup Tag.E6 F with hHdef
  set M : Subgroup (ModGL Tag.E6 F) := toralRootGroup Tag.E6 F c with hMdef
  have hM : M = H := by
    rw [hMdef, hHdef]
    show torusGroup Tag.E6 F ⊔ rootSpan Tag.E6 F (rootCharKernel c) = torusGroup Tag.E6 F
    rw [hne, show rootSpan Tag.E6 F (∅ : Set (Fin Tag.E6.rank → ℤ)) = ⊥ from by simp [rootSpan],
      sup_bot_eq]
  have hHX : H ≤ X := by
    rw [hHdef, hXdef]
    simpa [toralCentralizer, hddef] using
      (torusGroup_le_toralCentralizer (τ := Tag.E6) (K := F) c)
  have hMX : M ≤ X := hM ▸ hHX
  have hLmem : L ≤ X := hcomp.1
  have hXeq : X = toralCentralizer Tag.E6 F c := by
    rw [hXdef, toralCentralizer, hddef]
  have hMN : (M.subgroupOf X).Normal := by
    have h := toralRootGroup_normal (τ := Tag.E6) (K := F) c
    rwa [← hMdef, ← hXeq] at h
  have hcompA : CFSG.Assembly.IsComponentOf L X := (CFSG.Assembly.isComponentOf_iff_open).2 hcomp
  have hcompC : CFSG.IsComponent (L.subgroupOf X) :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hLmem).1 hcompA
  haveI : Finite (ModGL Tag.E6 F) := finite_modGL
  haveI : Finite ↥X := Subtype.finite
  rcases CFSG.LocalCores.component_normal_subgroup hcompC hMN with hLM | hcomm
  · exact false_of_component_le_torus hLmem hMX hM hHdef hcompA.2.2 hLM
  · exact false_of_commutator_component_toralRootGroup hζ hLmem hMX hM hA hcent hcomm

end KernelNonempty

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
