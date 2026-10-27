module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Blueprint.Catalog

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter CatalogueSchreierLinearTwo Subgroup

universe u v

theorem lieModel_psl2_data {Y : Type} [Group Y] {p f : ℕ}
    (h : Blueprint.LieModel Y .PSL 2 p f) :
    p.Prime ∧ 1 ≤ f ∧ p ^ f ≠ 2 ∧ p ^ f ≠ 3 ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (Y ≃* PSL2 F) := by
  rcases h with ⟨-, ⟨hp, hf, -, h2, h3⟩, F, _, _, hF, ⟨e⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · exact ⟨hp, hf, fun h => h2 (by rw [h]), fun h => h3 (by rw [h]), F, inferInstance,
      inferInstance, hF,
      ⟨e.trans (Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm⟩⟩
  all_goals exact absurd h0 (by norm_num)

theorem isOddPrimePower_of {F : Type u} [Finite F] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hF : Nat.card F = p ^ f) : IsOddPrimePower (Nat.card F) :=
  ⟨p, f, hp, hp.odd_of_ne_two hp2, hf, hF⟩

variable (F : Type u) [Field F]

@[expose] def incl : PSL2 F →* PGammaL2 F :=
  (SemidirectProduct.inl : PGL2 F →* PGammaL2 F).comp
    (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F))

theorem incl_apply (x : PSL2 F) :
    incl F x = SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL x) := rfl

theorem incl_injective : Function.Injective (incl F) :=
  SemidirectProduct.inl_injective.comp Matrix.ProjectiveSpecialLinearGroup.toPGL_injective

theorem range_incl : (incl F).range = pGammaL2PSLRange F := rfl

theorem semilinearAction_incl (x : PSL2 F) : semilinearAction F (incl F x) = MulAut.conj x := by
  rw [incl_apply, semilinearAction_inl, pglAction_toPGL]

variable {F} {Y : Type v} [Group Y] [Finite F]

@[expose] def autEquiv (e : Y ≃* PSL2 F) : MulAut Y ≃* PGammaL2 F :=
  (MulAut.congr e).trans (semilinearEquivAut F).symm

theorem semilinearAction_autEquiv (e : Y ≃* PSL2 F) (α : MulAut Y) :
    semilinearAction F (autEquiv e α) = MulAut.congr e α := by
  change semilinearEquivAut F ((semilinearEquivAut F).symm (MulAut.congr e α)) = _
  exact (semilinearEquivAut F).apply_symm_apply _

theorem semilinearAction_autEquiv_apply (e : Y ≃* PSL2 F) (α : MulAut Y) (y : Y) :
    semilinearAction F (autEquiv e α) (e y) = e (α y) := by
  rw [semilinearAction_autEquiv, MulAut.congr_apply]
  simp

theorem autEquiv_eq_iff (e : Y ≃* PSL2 F) (α : MulAut Y) (g : PGammaL2 F) :
    autEquiv e α = g ↔ MulAut.congr e α = semilinearAction F g := by
  constructor
  · rintro rfl
    exact (semilinearAction_autEquiv e α).symm
  · intro h
    apply (semilinearEquivAut F).injective
    change semilinearAction F (autEquiv e α) = semilinearAction F g
    rw [semilinearAction_autEquiv, h]

theorem autEquiv_conj (e : Y ≃* PSL2 F) (y : Y) :
    autEquiv e (MulAut.conj y) = incl F (e y) := by
  rw [autEquiv_eq_iff, semilinearAction_incl]
  ext x
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem autEquiv_comp_conj (e : Y ≃* PSL2 F) :
    (autEquiv e).toMonoidHom.comp (MulAut.conj : Y →* MulAut Y) =
      (incl F).comp e.toMonoidHom :=
  MonoidHom.ext fun y => autEquiv_conj e y

theorem map_autEquiv_innOf (e : Y ≃* PSL2 F) (T : Subgroup Y) :
    (T.map (MulAut.conj : Y →* MulAut Y)).map (autEquiv e).toMonoidHom =
      (T.map e.toMonoidHom).map (incl F) := by
  rw [Subgroup.map_map, Subgroup.map_map, autEquiv_comp_conj]

theorem map_autEquiv_innAut (e : Y ≃* PSL2 F) :
    (MulAut.conj : Y →* MulAut Y).range.map (autEquiv e).toMonoidHom = pGammaL2PSLRange F := by
  rw [MonoidHom.range_eq_map, map_autEquiv_innOf, ← range_incl,
    Subgroup.map_top_of_surjective _ e.surjective, ← MonoidHom.range_eq_map]

theorem conj_incl (g : PGammaL2 F) (x : PSL2 F) :
    g * incl F x * g⁻¹ = incl F (semilinearAction F g x) := by
  apply (semilinearEquivAut F).injective
  change semilinearAction F (g * incl F x * g⁻¹) = semilinearAction F (incl F _)
  rw [map_mul, map_mul, map_inv, semilinearAction_incl, semilinearAction_incl]
  ext z
  simp [MulAut.conj_apply]

theorem commute_incl_iff (g : PGammaL2 F) (x : PSL2 F) :
    g * incl F x = incl F x * g ↔ semilinearAction F g x = x := by
  rw [← (incl_injective F).eq_iff, ← conj_incl, mul_inv_eq_iff_eq_mul]

theorem apply_eq_iff_commute (e : Y ≃* PSL2 F) (α : MulAut Y) (y : Y) :
    α y = y ↔ autEquiv e α * incl F (e y) = incl F (e y) * autEquiv e α := by
  rw [commute_incl_iff, semilinearAction_autEquiv_apply, e.injective.eq_iff]

end CFSG.ComponentClassification.AutL2Facts
