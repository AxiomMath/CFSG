
module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7LatticeBase
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL3
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7LatticeBase
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Enc
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7LatticeInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7IsoInputs
public import CFSG.Foundations
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherSylow
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.Quasithin.Background.A1cModuleCoprime
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3Structure312
public import CFSG.Quasithin.Background.OrderingMax
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Sporadic.J4Base
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
public import CFSG.Walter.Defs
public import Certificates.Certificate8026Base

@[expose] public section

namespace CFSG.QuasithinUnique.Vol2Native.A312L.Seven

open Matrix Equiv CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.QuasithinUnique.Setup.X7a

section Alt

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

def permMulEquiv (e : α ≃ β) : Perm α ≃* Perm β where
  toEquiv := e.permCongr
  map_mul' f g := by ext x; simp [Equiv.permCongr_apply]

theorem sign_permMulEquiv (e : α ≃ β) (p : Perm α) :
    Perm.sign (permMulEquiv e p) = Perm.sign p :=
  Perm.sign_permCongr e p

def altCongr (e : α ≃ β) : alternatingGroup α ≃* alternatingGroup β :=
  (MulEquiv.subgroupMap (permMulEquiv e) (alternatingGroup α)).trans
    (MulEquiv.subgroupCongr (by
      ext q
      simp only [Subgroup.mem_map, Equiv.Perm.mem_alternatingGroup]
      constructor
      · rintro ⟨p, hp, rfl⟩
        exact (sign_permMulEquiv e p).trans hp
      · intro hq
        refine ⟨(permMulEquiv e).symm q, ?_, by simp⟩
        have := sign_permMulEquiv e ((permMulEquiv e).symm q)
        rw [MulEquiv.apply_symm_apply] at this
        exact this.symm.trans hq))

end Alt

abbrev A7s : Subgroup P7 := alternatingGroup (Fin 7)

noncomputable def altRangeEquiv (s : Finset (Fin 7)) :
    ↥(alternatingGroup.ofSubtype s).range ≃* alternatingGroup (Fin s.card) :=
  (MonoidHom.ofInjective alternatingGroup.ofSubtype_injective).symm.trans
    (altCongr (s.equivFinOfCardEq rfl))

def actPerm (g : SpecialLinearGroup (Fin 3) (ZMod 2)) : Perm {v : V3 // v ≠ 0} :=
  Equiv.subtypeEquiv (SpecialLinearGroup.toLin' g).toEquiv (fun _ =>
    not_congr (SpecialLinearGroup.toLin' g).map_eq_zero_iff.symm)

theorem actPerm_apply (g : SpecialLinearGroup (Fin 3) (ZMod 2)) (v : {v : V3 // v ≠ 0}) :
    (actPerm g v).1 = (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v.1 := rfl

def actHom : SpecialLinearGroup (Fin 3) (ZMod 2) →* Perm {v : V3 // v ≠ 0} where
  toFun := actPerm
  map_one' := by
    ext v : 2
    simp [actPerm_apply]
  map_mul' g h := by
    ext v : 2
    simp [actPerm_apply, Matrix.mulVec_mulVec]

theorem actHom_injective : Function.Injective actHom := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  rw [Subgroup.mem_bot]
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  have hv : (Pi.single j 1 : V3) ≠ 0 := by
    intro h
    have := congrFun h j
    simp at this
  have := congrArg (fun p : Perm {v : V3 // v ≠ 0} => (p ⟨Pi.single j 1, hv⟩).1 i) hg
  simpa [actHom, actPerm_apply, Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply]
    using this

def rho (lab : Fin 7 ≃ {v : V3 // v ≠ 0}) : SpecialLinearGroup (Fin 3) (ZMod 2) →* P7 :=
  (permMulEquiv lab.symm).toMonoidHom.comp actHom

theorem rho_injective (lab : Fin 7 ≃ {v : V3 // v ≠ 0}) : Function.Injective (rho lab) :=
  (permMulEquiv lab.symm).injective.comp actHom_injective

theorem rho_apply (lab : Fin 7 ≃ {v : V3 // v ≠ 0}) (g : SpecialLinearGroup (Fin 3) (ZMod 2))
    (x : Fin 7) : (lab (rho lab g x)).1 = (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ (lab x).1 := by
  show (lab (lab.symm (actPerm g (lab x)))).1 = _
  rw [Equiv.apply_symm_apply]
  rfl

def lab8 : Fin 7 ≃ {v : V3 // v ≠ 0} where
  toFun x := ⟨vec8 x, by revert x; decide⟩
  invFun v := idxOf vec8 v.1
  left_inv := by decide
  right_inv := by decide

def lab9 : Fin 7 ≃ {v : V3 // v ≠ 0} where
  toFun x := ⟨vec9 x, by revert x; decide⟩
  invFun v := idxOf vec9 v.1
  left_inv := by decide
  right_inv := by decide

theorem rho8_apply (g : SpecialLinearGroup (Fin 3) (ZMod 2)) (x : Fin 7) :
    rho lab8 g x = idxOf vec8 ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ vec8 x) := by
  have h := rho_apply lab8 g x
  have hx : (lab8 x).1 = vec8 x := rfl
  rw [hx] at h
  have : rho lab8 g x = lab8.symm ⟨(g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ vec8 x, by
      rw [← h]; exact (lab8 (rho lab8 g x)).2⟩ := by
    apply lab8.injective
    rw [Equiv.apply_symm_apply]
    exact Subtype.ext h
  rw [this]
  rfl

theorem rho9_apply (g : SpecialLinearGroup (Fin 3) (ZMod 2)) (x : Fin 7) :
    rho lab9 g x = idxOf vec9 ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ vec9 x) := by
  have h := rho_apply lab9 g x
  have hx : (lab9 x).1 = vec9 x := rfl
  rw [hx] at h
  have : rho lab9 g x = lab9.symm ⟨(g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ vec9 x, by
      rw [← h]; exact (lab9 (rho lab9 g x)).2⟩ := by
    apply lab9.injective
    rw [Equiv.apply_symm_apply]
    exact Subtype.ext h
  rw [this]
  rfl

theorem enc_rho8 (g : SpecialLinearGroup (Fin 3) (ZMod 2)) :
    R7.enc (rho lab8 g) = rhoRaw vec8 g := by
  rw [R7.enc_def]
  simp only [rhoRaw, rho8_apply]

theorem enc_rho9 (g : SpecialLinearGroup (Fin 3) (ZMod 2)) :
    R7.enc (rho lab9 g) = rhoRaw vec9 g := by
  rw [R7.enc_def]
  simp only [rhoRaw, rho9_apply]

theorem card_slThree : Nat.card (SpecialLinearGroup (Fin 3) (ZMod 2)) = 168 := by
  rw [Matrix.card_SL_field]
  simp [Fin.prod_univ_three]

theorem scalars_three_eq_bot : scalars 3 (ZMod 2) = ⊥ := by
  rw [eq_bot_iff]
  rintro A ⟨c, -, hA⟩
  have hc : c = 1 := Subsingleton.elim _ _
  rw [Subgroup.mem_bot]
  refine Subtype.ext ?_
  rw [hA, hc]
  simp

noncomputable def slThreeEquivProj : SpecialLinearGroup (Fin 3) (ZMod 2) ≃* projectiveSL 3 (ZMod 2) :=
  MulEquiv.ofBijective (proj 3 (ZMod 2)) ⟨by
    rw [← MonoidHom.ker_eq_bot_iff, ker_proj, scalars_three_eq_bot], proj_surjective 3 (ZMod 2)⟩

noncomputable def slThree_equiv_statedProj :
    SpecialLinearGroup (Fin 3) (ZMod 2) ≃* StatedProj (StatedSL 3 (ZMod 2)) :=
  slThreeEquivProj.trans (statedSLEquivProjectiveSL 3 (ZMod 2)).symm

theorem slThree_isSimple : IsSimpleGroup (SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  obtain ⟨-, hsimple, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := ZMod 2) (n := 3)
    (by norm_num) (Or.inl le_rfl)
  exact (slThreeEquivProj.trans
    (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 (ZMod 2)).symm).isSimpleGroup

theorem slThree_nonabelian : ∃ a b : SpecialLinearGroup (Fin 3) (ZMod 2), a * b ≠ b * a := by
  have := slThree_isSimple
  by_contra h
  push Not at h
  have hsolv : Group.IsSolvable (SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    IsSimpleGroup.comm_iff_isSolvable.mp h
  have hperf := CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect
    (K := ZMod 2) (n := 3) le_rfl
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial
    (G := SpecialLinearGroup (Fin 3) (ZMod 2))).ne (Group.isPerfect_def.mp hperf)

end CFSG.QuasithinUnique.Vol2Native.A312L.Seven
