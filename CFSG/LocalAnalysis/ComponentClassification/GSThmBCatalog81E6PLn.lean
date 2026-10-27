module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PLd
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4StabOrd

public section

namespace CFSG.ComponentClassification.GSThmB.P211

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {F : Type} [Field F]

theorem card_dvd_of_nonsquare [Finite F] (A : GL (Fin 4) F) (ν : Fˣ)
    (hsq : A ^ 2 = GeneralLinearGroup.scalar (Fin 4) ν) (hns : ¬ IsSquare (ν : F))
    {M : Subgroup (projectiveSL 4 F)} (hM : ⁅M, M⁆ = M) (hfix : ∀ x ∈ M, conjAut 4 F A x = x) :
    Nat.card M ∣ Nat.card F ^ 2 * (Nat.card F ^ 4 - 1) := by
  classical
  let _ := Fintype.ofFinite F
  obtain ⟨E, _, _, ρ, hE, hρ⟩ :=
    CatFactsL4U4.StabL.exists_centralizer_embedding_card A ν hsq hns
  set C := CatFactsSp4.fixOf (CatalogueBHigherLinearAction.slConjugation 4 F A) with hC
  have hι : ∀ g : C, SpecialLinearGroup.toGL (g : SpecialLinearGroup (Fin 4) F) ∈
      centralizer ({A} : Set (GL (Fin 4) F)) := fun g => by
    rw [mem_centralizer_singleton_iff]
    apply Units.ext
    simp only [Units.val_mul]
    exact comm_of_mem_fixOf g.2
  set ι : C →* centralizer ({A} : Set (GL (Fin 4) F)) :=
    (SpecialLinearGroup.toGL.comp C.subtype).codRestrict _ hι with hιdef
  have hιinj : Function.Injective ι := fun x y hxy =>
    Subtype.ext (SpecialLinearGroup.toGL_injective (congrArg Subtype.val hxy))
  set φ := ρ.comp ι with hφ
  have hφinj : Function.Injective φ := hρ.comp hιinj
  have hker : (commutator C).map φ ≤ (GeneralLinearGroup.det : GL (Fin 2) E →* Eˣ).ker := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 := Abelianization.commutator_subset_ker ((GeneralLinearGroup.det).comp φ) hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at h1
    rw [MonoidHom.mem_ker]
    exact h1
  have hSL : Nat.card (SpecialLinearGroup (Fin 2) E) = Nat.card F ^ 2 * (Nat.card F ^ 4 - 1) := by
    rw [card_SL_two, hE, ← pow_mul]
  have hcard : Nat.card (commutator C) ∣ Nat.card F ^ 2 * (Nat.card F ^ 4 - 1) := by
    rw [← Subgroup.card_map_of_injective hφinj, ← hSL,
      Nat.card_congr (SpecialLinearGroup.toGLKerEquiv).toEquiv]
    exact Subgroup.card_dvd_of_le hker
  have hcomm : ⁅C, C⁆ = (commutator C).map C.subtype := by
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have h1 : M ≤ (⁅C, C⁆).map (proj 4 F) :=
    perfect_le_map_commutator hM (perfect_le_map_fixOf_proj _ (conjAut_proj A) hM hfix)
  refine (Subgroup.card_dvd_of_le h1).trans ((Subgroup.card_map_dvd _ _).trans ?_)
  rw [hcomm, Subgroup.card_map_of_injective C.subtype_injective]
  exact hcard

end CFSG.ComponentClassification.GSThmB.P211
