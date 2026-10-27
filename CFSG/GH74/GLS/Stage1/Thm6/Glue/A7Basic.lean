module

public import CFSG.GH74.GLS.Stage1.Thm6.Glue.Data
public import CFSG.GH74.GLS.Stage1.Thm6.Glue.A7Core
public import CFSG.GH74.GLS.IVK.Statements.Sec1A7
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.GH74.GLS.Stage1.Thm6.Glue.Conf
public import CFSG.GH74.GLS.Stage1.Thm6.Glue.KFacts
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.After
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Lemma12_7
public import CFSG.GH74.GLS.Stage1.Thm6.Setup
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Glue

structure IVKA7Facts : Prop where
  hT : IVK.IVK_1_1T
  ha : IVK.IVK_1_1a
  hd : IVK.IVK_1_1d
  hf : IVK.IVK_1_1f
  hg : IVK.IVK_1_1g

@[expose] def Rd7 {G : Type} [Group G] (x : G) (Kb : Subgroup (CentralizerBar x)) [Kb.Normal]
    (T : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ T ∧ g ∈ Cx x ∧ phig x Kb g ∈ IVK.innAut ↥Kb}
  one_mem' := ⟨one_mem _, one_mem _, by rw [phig_one]; exact one_mem _⟩
  mul_mem' := by
    rintro a b ⟨ha, haC, haD⟩ ⟨hb, hbC, hbD⟩
    exact ⟨mul_mem ha hb, mul_mem haC hbC, by rw [phig_mul x Kb haC hbC]; exact mul_mem haD hbD⟩
  inv_mem' := by
    rintro a ⟨ha, haC, haD⟩
    exact ⟨inv_mem ha, inv_mem haC, by rw [phig_inv x Kb haC]; exact inv_mem haD⟩

theorem mem_Rd7 {G : Type} [Group G] {x : G} {Kb : Subgroup (CentralizerBar x)} [Kb.Normal]
    {T : Subgroup G} {g : G} :
    g ∈ Rd7 x Kb T ↔ g ∈ T ∧ g ∈ Cx x ∧ phig x Kb g ∈ IVK.innAut ↥Kb := Iff.rfl

namespace A7

open Subgroup CFSG CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12

local notation "S₇" => Equiv.Perm (Fin 7)
local notation "A₇" => alternatingGroup (Fin 7)

@[expose] noncomputable def autA7 : S₇ ≃* MulAut A₇ :=
  MulEquiv.ofBijective (MulAut.conjNormal (H := A₇))
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by norm_num) (by norm_num))

theorem autA7_apply (σ : S₇) (y : A₇) : ((autA7 σ y : A₇) : S₇) = σ * y * σ⁻¹ :=
  MulAut.conjNormal_apply σ y

section Psi

variable {K : Type*} [Group K] (eK : K ≃* A₇)

@[expose] noncomputable def PsiA7 : MulAut K ≃* S₇ := (MulAut.congr eK).trans autA7.symm

theorem autA7_PsiA7 (a : MulAut K) : autA7 (PsiA7 eK a) = MulAut.congr eK a := by
  simp [PsiA7]

theorem PsiA7_spec (a : MulAut K) (k : K) :
    ((eK (a k) : A₇) : S₇) = PsiA7 eK a * (eK k : S₇) * (PsiA7 eK a)⁻¹ := by
  have h := congrArg (fun φ : MulAut A₇ => (φ (eK k) : S₇)) (autA7_PsiA7 eK a)
  simp only [autA7_apply] at h
  rw [h]
  simp [MulAut.congr_apply]

theorem PsiA7_conj (k : K) : PsiA7 eK (MulAut.conj k) = (eK k : S₇) := by
  show autA7.symm (MulAut.congr eK (MulAut.conj k)) = _
  rw [MulEquiv.symm_apply_eq]
  ext y
  rw [autA7_apply]
  simp [MulAut.congr_apply, MulAut.conj_apply]

include eK in
theorem conj_injective : Function.Injective (MulAut.conj : K →* MulAut K) := by
  intro a b hab
  have h := congrArg (PsiA7 eK) hab
  rw [PsiA7_conj, PsiA7_conj] at h
  exact eK.injective (Subtype.ext h)

end Psi

section Rho

variable {G : Type} [Group G] (x : G) (Kb : Subgroup (CentralizerBar x)) [Kb.Normal]
  (eK : ↥Kb ≃* A₇)

@[expose] noncomputable def rho (g : G) : S₇ := PsiA7 eK (phig x Kb g)

@[expose] noncomputable def rhoC : ↥(Cx x) →* S₇ := (PsiA7 eK).toMonoidHom.comp (phiC x Kb)

theorem rho_of_mem {g : G} (hg : g ∈ Cx x) : rho x Kb eK g = rhoC x Kb eK ⟨g, hg⟩ := by
  show PsiA7 eK (phig x Kb g) = PsiA7 eK (phiC x Kb ⟨g, hg⟩)
  rw [phig_of_mem x Kb hg]

theorem rho_mul {g h : G} (hg : g ∈ Cx x) (hh : h ∈ Cx x) :
    rho x Kb eK (g * h) = rho x Kb eK g * rho x Kb eK h := by
  simp only [rho, phig_mul x Kb hg hh, map_mul]

theorem rho_one : rho x Kb eK (1 : G) = 1 := by
  simp [rho, phig_one]

theorem rho_inv {g : G} (hg : g ∈ Cx x) : rho x Kb eK g⁻¹ = (rho x Kb eK g)⁻¹ := by
  simp only [rho, phig_inv x Kb hg, map_inv]

theorem rho_eq_one_iff (g : G) : rho x Kb eK g = 1 ↔ phig x Kb g = 1 :=
  (PsiA7 eK).map_eq_one_iff

theorem rho_inj {g h : G} (e : rho x Kb eK g = rho x Kb eK h) : phig x Kb g = phig x Kb h :=
  (PsiA7 eK).injective e

theorem rho_Kg {g : G} (hg : g ∈ Kg x Kb) :
    rho x Kb eK g = ((eK ⟨pr x g, ((mem_Kg x Kb).1 hg).2⟩ : A₇) : S₇) := by
  rw [rho, phig_eq_conj x Kb hg, PsiA7_conj]

theorem rho_mem_A_of_Kg {g : G} (hg : g ∈ Kg x Kb) : rho x Kb eK g ∈ A₇ := by
  rw [rho_Kg x Kb eK hg]
  exact (eK _).2

theorem rho_mem_A_iff (g : G) : rho x Kb eK g ∈ A₇ ↔ phig x Kb g ∈ IVK.innAut ↥Kb := by
  constructor
  · intro h
    let y : A₇ := ⟨rho x Kb eK g, h⟩
    refine ⟨eK.symm y, ?_⟩
    apply (PsiA7 eK).injective
    have h2 : ((eK (eK.symm y) : A₇) : S₇) = rho x Kb eK g := by
      rw [MulEquiv.apply_symm_apply]
    rw [PsiA7_conj, h2]
    rfl
  · rintro ⟨k, hk⟩
    show PsiA7 eK (phig x Kb g) ∈ A₇
    rw [← hk, PsiA7_conj]
    exact (eK k).2

end Rho

theorem sylowSplit_of_IVK (h : IVKA7Facts) (Tp : Sylow 2 S₇) :
    ∃ f : S₇, SylowSplit (Tp : Subgroup S₇) f := by
  obtain ⟨f, hord, -, hmem, hbot, hcomm, hsup⟩ := h.hT Tp
  refine ⟨f, ?_, ?_, hmem, hbot, hcomm, hsup, ?_⟩
  · rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.1 (by rw [hord])
  · intro h1
    rw [h1, orderOf_one] at hord
    omega
  · obtain ⟨k, hk, -, ⟨e⟩⟩ := h.ha Tp
    have hk4 : k = 4 := by omega
    subst hk4
    exact ⟨e⟩

end A7

end CFSG.GH74.GLS.Stage1.Thm6.Glue
