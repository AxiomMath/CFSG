module

public import CFSG.GH74.GLS.SP.DatumBN
public import CFSG.GH74.GLS.SP.SpDefs
import CFSG.GH74.BNPair.Bridge
import CFSG.ClassicalGroups.Symplectic.Model
import CFSG.LieType.Universal.SymplecticExtras.Torus

public noncomputable section

namespace CFSG.GH74.GLS.SP

open CFSG.GH74.BNPair CFSG.GroupActions CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic
  CFSG.LieType.Steinberg CFSG.LieType.RootSystem CFSG.LieType.CurtisTits CFSG.Assembly.LowTwoRank
open scoped Pointwise

theorem card_coxeterMatrix_cartanC_two :
    Nat.card (coxeterMatrix (isFiniteType_cartanC 2)).Group = 8 := by
  have h01 : cartanC 2 0 1 = -2 := by decide
  have h10 : cartanC 2 1 0 = -1 := by decide
  have hM : (coxeterMatrix (isFiniteType_cartanC 2)).M 0 1 = 4 := by
    simp only [coxeterMatrix, TauCeti.coxeterMatrixOfCartanMatrix_apply, h01, h10]
    norm_num
  have h := card_coxeterGroup_fin_two (coxeterMatrix (isFiniteType_cartanC 2))
  omega

section Concrete

variable (F : Type) [Field F]

theorem spB_inf_spN : spB F ⊓ spN F = spT F :=
  borel_inf_weylN (isCTGroupDatum 2 F) (steinbergExtras 2 F)

instance spCartan_normal : (cartan (spB F) (spN F)).Normal :=
  cartan_normal_of_datum (D := rootDatum 2 F) (n := weylRep 2 F) (H := torus 2 F)
    (isCTGroupDatum 2 F) (steinbergExtras 2 F)

abbrev spNRep (i : Fin 2) : spN F :=
  ⟨weylRep 2 F i, n_mem_weylN (D := rootDatum 2 F) (n := weylRep 2 F) (H := torus 2 F) i⟩

noncomputable def spWeylEquiv :
    WeylGroup (spB F) (spN F) ≃* (coxeterMatrix (isFiniteType_cartanC 2)).Group :=
  weylEquiv (D := rootDatum 2 F) (n := weylRep 2 F) (H := torus 2 F) (isCTGroupDatum 2 F)
    (steinbergExtras 2 F) (hN := spCartan_normal F)

theorem spWeylEquiv_spNRep (i : Fin 2) :
    spWeylEquiv F ((spNRep F i : spN F) : WeylGroup (spB F) (spN F)) =
      (coxeterMatrix (isFiniteType_cartanC 2)).toCoxeterSystem.simple i :=
  weylEquiv_n (D := rootDatum 2 F) (n := weylRep 2 F) (H := torus 2 F) (isCTGroupDatum 2 F)
    (steinbergExtras 2 F) (_hN := spCartan_normal F) i

theorem spConjBy_rootGroup {m : spN F} {i : Fin 2}
    (h : (m : WeylGroup (spB F) (spN F)) = ((spNRep F i : spN F) : WeylGroup (spB F) (spN F)))
    {γ : Fin 2 → ℤ} (hγ : γ ∈ (rootDatum 2 F).roots) :
    conjBy (m : StatedSp 2 F) ((rootDatum 2 F).rootGroup γ) =
      (rootDatum 2 F).rootGroup (weylAction (isFiniteType_cartanC 2)
        ((coxeterMatrix (isFiniteType_cartanC 2)).toCoxeterSystem.simple i) γ) :=
  conjBy_rootGroup_of_mk_eq (D := rootDatum 2 F) (n := weylRep 2 F) (H := torus 2 F)
    (isCTGroupDatum 2 F) (steinbergExtras 2 F) (_hN := spCartan_normal F) h hγ

theorem spNRep_ne : ((spNRep F 0 : spN F) : WeylGroup (spB F) (spN F)) ≠
    ((spNRep F 1 : spN F) : WeylGroup (spB F) (spN F)) := by
  intro h
  have h' := congrArg (spWeylEquiv F) h
  rw [spWeylEquiv_spNRep, spWeylEquiv_spNRep] at h'
  exact absurd ((coxeterMatrix (isFiniteType_cartanC 2)).toCoxeterSystem.simple_injective h')
    (by decide)

theorem card_weyl_sp : Nat.card (WeylGroup (spB F) (spN F)) = 8 := by
  rw [Nat.card_congr (spWeylEquiv F).toEquiv]
  exact card_coxeterMatrix_cartanC_two

theorem spSplitBN (hnil : Group.IsNilpotent (spU F)) :
    SplitBN (spB F) (spN F) (spU F) (spNRep F) :=
  splitBN_of_datum (D := rootDatum 2 F) (n := weylRep 2 F) (H := torus 2 F) (isCTGroupDatum 2 F)
    (steinbergExtras 2 F) hnil

open Classical in
theorem spIsTitsSystem (hnil : Group.IsNilpotent (spU F)) :
    IsTitsSystem (spB F) (spN F)
      {((spNRep F 0 : spN F) : WeylGroup (spB F) (spN F)),
        ((spNRep F 1 : spN F) : WeylGroup (spB F) (spN F))} := by
  obtain ⟨S, hS, hSrange⟩ := SplitBN.isTitsSystem (spSplitBN F hnil)
  have hSeq : S = {((spNRep F 0 : spN F) : WeylGroup (spB F) (spN F)),
      ((spNRep F 1 : spN F) : WeylGroup (spB F) (spN F))} := by
    apply Finset.coe_injective
    rw [hSrange]
    ext x
    simp only [Set.mem_range, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · left; rfl
      · right; rfl
    · rintro (rfl | rfl)
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩]
  rwa [hSeq] at hS

theorem spIsSaturated (hBE : BruhatExtras (rootDatum 2 F) (torus 2 F)) :
    IsSaturated (spB F) (spN F) :=
  isSaturated_of_datum (D := rootDatum 2 F) (n := weylRep 2 F) (H := torus 2 F)
    (isCTGroupDatum 2 F) (steinbergExtras 2 F) hBE

theorem spB_eq_mul :
    ((spB F : Subgroup (StatedSp 2 F)) : Set (StatedSp 2 F)) =
      ((spB F ⊓ spN F : Subgroup _) : Set _) * ((spU F : Subgroup _) : Set _) :=
  borel_eq_mul_of_datum (D := rootDatum 2 F) (n := weylRep 2 F) (H := torus 2 F)
    (isCTGroupDatum 2 F) (steinbergExtras 2 F)

theorem spIsSplit (hnil : Group.IsNilpotent (spU F)) : IsSplit (spB F) (spN F) (spU F) :=
  ⟨hnil, spB_eq_mul F⟩

theorem center_le_spT : Subgroup.center (StatedSp 2 F) ≤ spT F := by
  intro g hg
  rw [center_eq 2 F] at hg
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 hg
  have hmat : (((g : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = Matrix.scalar (Fin 2 ⊕ Fin 2) (c : F) := by
    rw [← hc, Matrix.GeneralLinearGroup.coe_scalar]
  have hsp : ((g : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) ∈ TauCeti.GLSymplectic (Fin 2) F := by
    rw [← CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic]
    exact (g : StatedSp 2 F).2
  have h12 : 1 ≤ 2 := by norm_num
  rw [TauCeti.GLSymplectic.mem_iff_mem_symplecticGroup, hmat,
    CFSG.ClassicalGroups.Symplectic.scalar_mem_symplecticGroup_iff h12] at hsp
  have hc2 : c * c = 1 := Units.ext (by simpa [sq] using hsp)
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
  have hv : ∀ a : Fin 2, corootVec 2 F 0 c a = c := by
    intro a
    fin_cases a <;> simp [corootVec, hcinv]
  have hdiag : Matrix.scalar (Fin 2 ⊕ Fin 2) (c : F) = Matrix.diagonal
      (Sum.elim (fun i => ((corootVec 2 F 0 c i : Fˣ) : F))
        (fun i => (((corootVec 2 F 0 c i)⁻¹ : Fˣ) : F))) := by
    rw [Matrix.scalar_apply]
    congr 1
    funext a
    rcases a with i | i
    · show (c : F) = ((corootVec 2 F 0 c i : Fˣ) : F)
      rw [hv i]
    · show (c : F) = (((corootVec 2 F 0 c i)⁻¹ : Fˣ) : F)
      rw [hv i, hcinv]
  have hgd : g = equivStatedSp 2 F
      (TauCeti.GLSymplecticFin.diagonal (corootVec 2 F 0 c)) := by
    apply SpExtras.mat_injective
    rw [SpExtras.mat_equiv_diagonal, SpExtras.mat_apply, hmat]
    exact hdiag
  exact le_iSup (fun i => torus 2 F i) 0 (SpExtras.mem_torus_iff.2 ⟨c, hgd⟩)

end Concrete

end CFSG.GH74.GLS.SP
