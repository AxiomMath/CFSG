module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.Chevalley.SteinbergCDTrialityThreeSixTorus
public import CFSG.RankThree.PartOne.KGD.D4T36Frame

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
open scoped Matrix

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

section Arithmetic

theorem d4ThreeSixW_diagramMap_inv_rootVec_perm {L : Type} [Field L]
    {γ : Fin TwistTag.D4.tag.rank → ℤ} (hγ : IsRoot TwistTag.D4.tag γ) :
    ((diagramMap TwistTag.D4 L)⁻¹ : ModGL TwistTag.D4.tag L).val
        (rootVec TwistTag.D4.tag L (permLattice TwistTag.D4.perm γ)) =
      rootVec TwistTag.D4.tag L γ := by
  rw [← diagramMap_rootVec TwistTag.D4 L γ hγ]
  have h2 : (((diagramMap TwistTag.D4 L)⁻¹ * diagramMap TwistTag.D4 L : ModGL TwistTag.D4.tag L) :
      Module.End L (RootModule TwistTag.D4.tag L)) (rootVec TwistTag.D4.tag L γ) =
      rootVec TwistTag.D4.tag L γ := by
    rw [inv_mul_cancel]
    rfl
  exact h2

theorem d4ThreeSixW_perm_symm_pow_threeSixExp {ε : ℤ} (hε : ε = 1 ∨ ε = -1) :
    TwistTag.D4.perm.symm ^ threeSixExp ε = TwistTag.D4.perm.symm := by
  have h3 : TwistTag.D4.perm.symm ^ 3 = 1 := by decide
  rcases hε with rfl | rfl
  · rw [show threeSixExp 1 = 3 + 1 from rfl, pow_add, h3, one_mul, pow_one]
  · rw [show threeSixExp (-1) = 3 * 3 + 1 from rfl, pow_add, pow_mul, h3, one_pow, one_mul,
      pow_one]

theorem d4ThreeSixW_twelveW_pow_threeSixExp {ε : ℤ} (hε : ε = 1 ∨ ε = -1) :
    twelveW ^ threeSixExp ε = d4T36M ε := by
  rw [d4T36M_eq]
  rcases hε with rfl | rfl
  · rw [show threeSixExp 1 = 4 from rfl, one_smul]
    rfl
  · rw [show threeSixExp (-1) = 6 + 4 from rfl, pow_add, twelveW_pow_six, neg_one_mul,
      neg_one_smul]
    rfl

theorem d4ThreeSixW_simple_mul_smul (z : Fin TwistTag.D4.tag.rank → ℤ) :
    (simple TwistTag.D4.tag 2 * simple TwistTag.D4.tag 0) • z =
      twelveW *ᵥ permLattice TwistTag.D4.perm.symm z := by
  have hperm : ∀ y : Fin Tag.D4.rank → ℤ,
      permLattice trialityRho (permLattice trialityRho.symm y) = y := fun y =>
    CFSG.RankThree.PartOne.KGD.permLattice_permLattice_symm y
  have h : ∀ y : Fin Tag.D4.rank → ℤ, (simple Tag.D4 2 * simple Tag.D4 0) • y =
      trialityC *ᵥ permLattice trialityRho.symm y := fun y => by
    rw [trialityC_eq_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, trialityP_mulVec, hperm,
      reflMat_mulVec, reflMat_mulVec, mul_smul, simple_smul, simple_smul]
  exact h z

end Arithmetic

section Recursion

variable {L : Type} [Field L]

theorem d4ThreeSixW_trialityM_pow_succ (k : ℕ) :
    trialityM L ^ (k + 1) * (diagramMap TwistTag.D4 L ^ (k + 1))⁻¹ =
      trialityTwistN L * (diagramMap TwistTag.D4 L *
        (trialityM L ^ k * (diagramMap TwistTag.D4 L ^ k)⁻¹) * (diagramMap TwistTag.D4 L)⁻¹) := by
  rw [trialityM, pow_succ', pow_succ']
  group

end Recursion

section Conjugation

variable {L : Type} [Field L]

theorem d4ThreeSixW_diagramMap_pow_threeSixExp {ε : ℤ} (hε : ε = 1 ∨ ε = -1) :
    diagramMap TwistTag.D4 L ^ threeSixExp ε = diagramMap TwistTag.D4 L := by
  have hP3 : diagramMap TwistTag.D4 L ^ 3 = 1 := diagramMap_pow_order TwistTag.D4 L
  rcases hε with rfl | rfl
  · rw [show threeSixExp 1 = 3 + 1 from rfl, pow_add, hP3, one_mul, pow_one]
  · rw [show threeSixExp (-1) = 3 * 3 + 1 from rfl, pow_add, pow_mul, hP3, one_pow, one_mul,
      pow_one]

theorem d4ThreeSixW_mapsRootLines_conj_diagramMap {g : ModGL TwistTag.D4.tag L}
    {w : WeylGroup TwistTag.D4.tag} (hg : MapsRootLines g w) :
    MapsRootLines (diagramMap TwistTag.D4 L * g * (diagramMap TwistTag.D4 L)⁻¹)
      (weylTwist TwistTag.D4 w) := by
  intro α hα
  have hβ : IsRoot TwistTag.D4.tag (permLattice TwistTag.D4.perm.symm α) :=
    hα.permLattice (cartan_perm_symm TwistTag.D4.cartan_perm)
  obtain ⟨c, hc⟩ := hg _ hβ
  refine ⟨c, ?_⟩
  have h1 : ((diagramMap TwistTag.D4 L)⁻¹ : ModGL TwistTag.D4.tag L).val
      (rootVec TwistTag.D4.tag L α) =
      rootVec TwistTag.D4.tag L (permLattice TwistTag.D4.perm.symm α) := by
    have := d4ThreeSixW_diagramMap_inv_rootVec_perm (L := L) hβ
    rwa [CFSG.RankThree.PartOne.KGD.permLattice_permLattice_symm] at this
  have h2 : permLattice TwistTag.D4.perm (w • permLattice TwistTag.D4.perm.symm α) =
      weylTwist TwistTag.D4 w • α := by
    have := weylTwist_smul_permLattice TwistTag.D4 w (permLattice TwistTag.D4.perm.symm α)
    rw [CFSG.RankThree.PartOne.KGD.permLattice_permLattice_symm] at this
    exact this.symm
  rw [Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply, h1, hc, map_smul,
    diagramMap_rootVec _ _ _ (IsRoot.smul hβ w), h2]

theorem d4ThreeSixW_conj_diagramMap_mem_closure {h : ModGL TwistTag.D4.tag L}
    (hh : h ∈ Subgroup.closure (Set.range fun i : Fin TwistTag.D4.tag.rank =>
      weylElt TwistTag.D4.tag L i 1)) :
    diagramMap TwistTag.D4 L * h * (diagramMap TwistTag.D4 L)⁻¹ ∈
      Subgroup.closure (Set.range fun i : Fin TwistTag.D4.tag.rank =>
        weylElt TwistTag.D4.tag L i 1) := by
  induction hh using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [diagramMap_mul_weylElt_one (K := L) i, mul_inv_cancel_right]
    exact Subgroup.subset_closure ⟨_, rfl⟩
  | one => simp [one_mem]
  | mul x y _ _ hx hy =>
    rw [show diagramMap TwistTag.D4 L * (x * y) * (diagramMap TwistTag.D4 L)⁻¹ =
      (diagramMap TwistTag.D4 L * x * (diagramMap TwistTag.D4 L)⁻¹) *
        (diagramMap TwistTag.D4 L * y * (diagramMap TwistTag.D4 L)⁻¹) by group]
    exact mul_mem hx hy
  | inv x _ hx =>
    rw [show diagramMap TwistTag.D4 L * x⁻¹ * (diagramMap TwistTag.D4 L)⁻¹ =
      (diagramMap TwistTag.D4 L * x * (diagramMap TwistTag.D4 L)⁻¹)⁻¹ by group]
    exact inv_mem hx

end Conjugation

section Induction

variable {L : Type} [Field L]

theorem d4ThreeSixW_trialityM_pow_mem_closure (k : ℕ) :
    trialityM L ^ k * (diagramMap TwistTag.D4 L ^ k)⁻¹ ∈
      Subgroup.closure (Set.range fun i : Fin TwistTag.D4.tag.rank =>
        weylElt TwistTag.D4.tag L i 1) := by
  induction k with
  | zero => simp [one_mem]
  | succ k ih =>
    have hn : trialityTwistN L ∈ Subgroup.closure (Set.range fun i : Fin TwistTag.D4.tag.rank =>
        weylElt TwistTag.D4.tag L i 1) :=
      mul_mem (Subgroup.subset_closure ⟨2, rfl⟩) (Subgroup.subset_closure ⟨0, rfl⟩)
    rw [d4ThreeSixW_trialityM_pow_succ]
    exact mul_mem hn (d4ThreeSixW_conj_diagramMap_mem_closure ih)

theorem d4ThreeSixW_trialityM_pow_mapsRootLines (k : ℕ) :
    ∃ w : WeylGroup TwistTag.D4.tag,
      MapsRootLines (trialityM L ^ k * (diagramMap TwistTag.D4 L ^ k)⁻¹) w ∧
        ∀ x, w • x = twelveW ^ k *ᵥ permLattice (TwistTag.D4.perm.symm ^ k) x := by
  induction k with
  | zero =>
    refine ⟨1, ?_, fun x => ?_⟩
    · rw [pow_zero, pow_zero, inv_one, mul_one]
      exact mapsRootLines_one
    · rw [one_smul, pow_zero, pow_zero, Matrix.one_mulVec]
      rfl
  | succ k ih =>
    obtain ⟨w, hw, hx⟩ := ih
    refine ⟨simple TwistTag.D4.tag 2 * simple TwistTag.D4.tag 0 * weylTwist TwistTag.D4 w, ?_,
      fun x => ?_⟩
    · rw [d4ThreeSixW_trialityM_pow_succ]
      exact ((mapsRootLines_weylElt 2).mul (mapsRootLines_weylElt 0)).mul
        (d4ThreeSixW_mapsRootLines_conj_diagramMap hw)
    · have h1 : weylTwist TwistTag.D4 w • x = permLattice TwistTag.D4.perm
          (w • permLattice TwistTag.D4.perm.symm x) := by
        have := weylTwist_smul_permLattice TwistTag.D4 w (permLattice TwistTag.D4.perm.symm x)
        rwa [CFSG.RankThree.PartOne.KGD.permLattice_permLattice_symm] at this
      rw [mul_smul, h1, d4ThreeSixW_simple_mul_smul,
        CFSG.RankThree.PartOne.KGD.permLattice_symm_permLattice, hx, Matrix.mulVec_mulVec,
        pow_succ', pow_succ]
      rfl

end Induction

section Main

theorem threeSixN_mem_monomialSubgroup {L : Type} [Field L] {ε : ℤ} (hε : ε = 1 ∨ ε = -1) :
    threeSixN L ε ∈ monomialSubgroup TwistTag.D4.tag L := by
  have h := d4ThreeSixW_trialityM_pow_mem_closure (L := L) (threeSixExp ε)
  rw [d4ThreeSixW_diagramMap_pow_threeSixExp hε] at h
  exact Subgroup.mem_sup_right h

theorem threeSixN_weylImage {L : Type} [Field L] {ε : ℤ} (hε : ε = 1 ∨ ε = -1) :
    ∀ x, weylQuotientHom TwistTag.D4.tag L ⟨threeSixN L ε, threeSixN_mem_monomialSubgroup hε⟩ • x =
      d4T36M ε *ᵥ permLattice TwistTag.D4.perm.symm x := by
  obtain ⟨w, hw, hx⟩ := d4ThreeSixW_trialityM_pow_mapsRootLines (L := L) (threeSixExp ε)
  rw [d4ThreeSixW_diagramMap_pow_threeSixExp hε] at hw
  intro x
  rw [weylQuotientHom_eq (g := ⟨threeSixN L ε, threeSixN_mem_monomialSubgroup hε⟩) hw, hx,
    d4ThreeSixW_twelveW_pow_threeSixExp hε, d4ThreeSixW_perm_symm_pow_threeSixExp hε]

end Main

end CFSG.GH74.GLS.Stage2.Bender.Thm1
