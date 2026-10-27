module

public import CFSG.Open.FischerThreeTranspositionMilestoneDefs
public import CFSG.Quasithin.Background.P4InspOrthA5

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4Insp

open Matrix CFSG.Open CFSG.GroupTheory.WeirSylow CFSG.Quasithin.G11 CFSG.Quasithin.G11.P4InspOrth

theorem nonempty_mulEquiv_orthogonalGroup {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] (Q : QuadraticForm K (ι → K)) :
    Nonempty (↥(fischerMatrixGroup fun A : Matrix ι ι K => ∀ x, Q (A *ᵥ x) = Q x) ≃*
      ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) := by
  have hcl : (fischerMatrixGroup fun A : Matrix ι ι K => ∀ x, Q (A *ᵥ x) = Q x) =
      (TauCeti.QuadraticMap.orthogonalGroup Q).comap
        (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).toMonoidHom :=
    CFSG.ClassicalGroups.Orthogonal.closure_isometries_eq_comap rfl
  refine ⟨((CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).subgroupMap _).trans
    (MulEquiv.subgroupCongr ?_)⟩
  rw [hcl]
  exact Subgroup.map_comap_eq_self_of_surjective
    (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).surjective _

theorem orthogonalGroup_eq_orthSub {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (Q : QuadraticForm (ZMod 2) V) : TauCeti.QuadraticMap.orthogonalGroup Q = orthSub (⇑Q) := by
  ext g
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  exact Iff.rfl

theorem nonempty_mulEquiv_orthSub {U V : Type} [AddCommGroup U] [Module (ZMod 2) U]
    [AddCommGroup V] [Module (ZMod 2) V] {q : U → ZMod 2} {q' : V → ZMod 2}
    (ι : U ≃ₗ[ZMod 2] V) (hι : ∀ x, q' (ι x) = q x) :
    Nonempty (↥(orthSub q) ≃* ↥(orthSub q')) :=
  ⟨((p4insporth_cg ι).subgroupMap (orthSub q)).trans
    (MulEquiv.subgroupCongr (p4insporth_map_cg_orthSub ι hι))⟩

theorem nonempty_mulEquiv_perm_five_orthSub :
    Nonempty (↥(orthSub (p4insporth_qN 5)) ≃* Equiv.Perm (Fin 5)) :=
  ⟨(MulEquiv.subgroupCongr p4insporth_range_perm5.symm).trans
    (MonoidHom.ofInjective (p4insporth_permHom_injective (n := 5) (by norm_num))).symm⟩

theorem nonempty_mulEquiv_perm_five_of_orth {X : Type} [Group X] {D : Set X}
    {Q : QuadraticForm (ZMod 2) (Fin (2 * 2) → ZMod 2)}
    (hnd : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0)
    (hmin : ¬ ∃ W : Submodule (ZMod 2) (Fin (2 * 2) → ZMod 2),
      Module.finrank (ZMod 2) W = 2 ∧ ∀ w ∈ W, Q w = 0)
    (hmod : fischerLinearModel D (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x)
      (fischerTransvections (QuadraticMap.polar Q) fun v => Q v = 1)) :
    Nonempty (X ≃* Equiv.Perm (Fin 5)) := by
  obtain ⟨φ, -⟩ := hmod
  have hQ : (QuadraticMap.polarBilin Q).Nondegenerate :=
    ⟨fun x hx => hnd x fun y => by simpa using hx y,
      fun y hy => hnd y fun x => by rw [QuadraticMap.polar_comm]; simpa using hy x⟩
  have hdim : Module.finrank (ZMod 2) (Fin (2 * 2) → ZMod 2) = 2 * 2 := by
    rw [Module.finrank_fin_fun]
  have hminus : ¬ IsPlusType Q := by
    rintro ⟨W, hW, hWs⟩
    exact hmin ⟨W, by omega, hWs⟩
  obtain ⟨e⟩ := nonempty_isometry_of_isPlusType_iff (n := 2) hQ
    (p4insporth_nondegenerate_quad p4insporth_symplectic5 (p4insporth_qN_add 5)) hdim
    (by rw [finrank_permCore_five]) (iff_of_false hminus p4insporth_not_plus5)
  have hι : ∀ x, p4insporth_qN 5 (e.toLinearEquiv x) = ⇑Q x := fun x => e.map_app x
  obtain ⟨e1⟩ := nonempty_mulEquiv_orthogonalGroup Q
  obtain ⟨e2⟩ := nonempty_mulEquiv_orthSub e.toLinearEquiv hι
  obtain ⟨e3⟩ := nonempty_mulEquiv_perm_five_orthSub
  exact ⟨φ.trans (e1.trans ((MulEquiv.subgroupCongr (orthogonalGroup_eq_orthSub Q)).trans
    (e2.trans e3)))⟩

end CFSG.GF2Type.Smith1979.W4Insp
