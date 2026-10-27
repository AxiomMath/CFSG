module

public import CFSG.GH74.Generic.BProg.B2.GenLocDiag
public import CFSG.RankThree.PartOne.AUTSL.Interface
public import CFSG.GH74.Generic.BProg.B2.GenLoc4Defs
public import CFSG.GH74.SectionalRank

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification Subgroup

namespace GenLocL4Lift

variable {F : Type} [Field F] [Finite F]

theorem descendAut_surjective : Function.Surjective (LinearFlag.descendAut 4 F) := by
  intro β
  obtain ⟨A, σ, ε, -, h⟩ := (LinearFlag.automorphism_generation (n := 4) (K := F) (by norm_num)).2 β
  refine ⟨CatalogueBHigherLinearAction.slConjugation 4 F A *
    CatalogueBHigherLinearField.slFieldAut (Fin 4) F σ * CatalogueBGraphForm.slGraphAut 4 F ^ ε, ?_⟩
  rw [h]
  simp only [LinearFlag.conjAut, LinearFlag.fieldAut, LinearFlag.dualAut, map_mul, map_pow, MonoidHom.comp_apply]

theorem descendAut_bijective : Function.Bijective (LinearFlag.descendAut 4 F) :=
  ⟨CFSG.RankThree.PartOne.AUTSL.descendAut_injective (by norm_num), descendAut_surjective⟩

omit [Finite F] in
theorem descendAut_conj (g : Matrix.SpecialLinearGroup (Fin 4) F) :
    LinearFlag.descendAut 4 F (MulAut.conj g) = MulAut.conj (LinearFlag.proj 4 F g) := by
  ext x
  obtain ⟨h, rfl⟩ := LinearFlag.proj_surjective 4 F x
  rw [LinearFlag.descendAut_proj, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]

omit [Finite F] in
theorem map_inn :
    (MulAut.conj : Matrix.SpecialLinearGroup (Fin 4) F →* MulAut (Matrix.SpecialLinearGroup (Fin 4) F)).range.map
        (LinearFlag.descendAut 4 F) =
      (MulAut.conj : LinearFlag.projectiveSL 4 F →* MulAut (LinearFlag.projectiveSL 4 F)).range := by
  ext φ
  constructor
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨LinearFlag.proj 4 F g, (descendAut_conj g).symm⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨g, rfl⟩ := LinearFlag.proj_surjective 4 F x
    exact ⟨MulAut.conj g, ⟨g, rfl⟩, descendAut_conj g⟩

omit [Finite F] in
theorem innJoin_descend {A : Type} [Group A]
    (α : A →* MulAut (Matrix.SpecialLinearGroup (Fin 4) F))
    (α' : A →* MulAut (LinearFlag.projectiveSL 4 F)) (h : ∀ a, LinearFlag.descendAut 4 F (α a) = α' a) :
    innJoin α' = (innJoin α).map (LinearFlag.descendAut 4 F) := by
  unfold innJoin
  rw [Subgroup.map_sup, map_inn]
  congr 1
  ext φ
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨α a, ⟨a, rfl⟩, h a⟩
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, (h a).symm⟩

theorem sectional_of_descend {A : Type} [Group A]
    (α : A →* MulAut (Matrix.SpecialLinearGroup (Fin 4) F))
    (α' : A →* MulAut (LinearFlag.projectiveSL 4 F)) (h : ∀ a, LinearFlag.descendAut 4 F (α a) = α' a)
    {r : ℕ} (hsect : SectionalTwoRankLE ↥(innJoin α') r) : SectionalTwoRankLE ↥(innJoin α) r := by
  have heq := innJoin_descend α α' h
  have iso := (innJoin α).equivMapOfInjective (LinearFlag.descendAut 4 F) descendAut_bijective.1
  exact SectionalTwoRankLE.of_mulEquiv ((MulEquiv.subgroupCongr heq).trans iso.symm) hsect

@[expose] def Sl4GenStmt (F : Type) [Field F] [Finite F] : Prop :=
  ∀ {A : Type} [Group A] [Finite A] (α : A →* MulAut (Matrix.SpecialLinearGroup (Fin 4) F)),
    IsRank23 A → SectionalTwoRankLE ↥(innJoin α) 4 → gammaAct α = ⊤

theorem gammaAct_projectiveSL4_of_sl4 (h : Sl4GenStmt F) {A : Type} [Group A] [Finite A]
    (α' : A →* MulAut (LinearFlag.projectiveSL 4 F)) (hA : IsRank23 A)
    (hsect : SectionalTwoRankLE ↥(innJoin α') 4) : gammaAct α' = ⊤ := by
  let Φ : MulAut (Matrix.SpecialLinearGroup (Fin 4) F) ≃* MulAut (LinearFlag.projectiveSL 4 F) :=
    MulEquiv.ofBijective (LinearFlag.descendAut 4 F) descendAut_bijective
  let α : A →* MulAut (Matrix.SpecialLinearGroup (Fin 4) F) := Φ.symm.toMonoidHom.comp α'
  have hαa : ∀ a, LinearFlag.descendAut 4 F (α a) = α' a := fun a => Φ.apply_symm_apply (α' a)
  exact GenLocDiag.gammaAct_eq_top_of_surj α α' (LinearFlag.proj 4 F) (LinearFlag.proj_surjective 4 F)
    (fun a x => by rw [← hαa a, LinearFlag.descendAut_proj]) (h α hA (sectional_of_descend α α' hαa hsect))

theorem genLoc4_projectiveSL4 (h : Sl4GenStmt F) : GenLoc4 (LinearFlag.projectiveSL 4 F) :=
  fun _ _ _ α' hA hsect => Or.inl (gammaAct_projectiveSL4_of_sl4 h α' hA hsect)

theorem genLoc4_sl4 (h : Sl4GenStmt F) : GenLoc4 (Matrix.SpecialLinearGroup (Fin 4) F) :=
  fun _ _ _ α hA hsect => Or.inl (h α hA hsect)

end GenLocL4Lift

end CFSG.GH74.Generic.BProg.B2
