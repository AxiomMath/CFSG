module

public import CFSG.ClassicalGroups.Orthogonal.CharTwoTransvection
public import CFSG.ClassicalGroups.Orthogonal.Matrix
public import CFSG.Open.FischerThreeTranspositionMilestoneDefs

public section

namespace CFSG.Fischer.Classification

open CFSG.Open CFSG.ClassicalGroups.Orthogonal Matrix QuadraticMap Module

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem fischerMatrixGroup_isometry_eq_comap {K : Type} [Field K] (Q : QuadraticForm K (ι → K)) :
    (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x) =
      (TauCeti.QuadraticMap.orthogonalGroup Q).comap (toLinEquiv ι K).toMonoidHom :=
  closure_isometries_eq_comap rfl

theorem mem_fischerMatrixGroup_isometry_iff {K : Type} [Field K] (Q : QuadraticForm K (ι → K))
    (A : GL ι K) :
    A ∈ (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x) ↔
      ∀ x, Q ((A : Matrix ι ι K) *ᵥ x) = Q x := by
  rw [fischerMatrixGroup_isometry_eq_comap, Subgroup.mem_comap,
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  rfl

section Reflect

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable (Q : QuadraticForm (ZMod 2) (ι → ZMod 2))

noncomputable def orthTransvectionGL (v : ι → ZMod 2) : GL ι (ZMod 2) :=
  (toLinEquiv ι (ZMod 2)).symm (reflect Q v)

variable {Q}

theorem toLinEquiv_orthTransvectionGL (v : ι → ZMod 2) :
    toLinEquiv ι (ZMod 2) (orthTransvectionGL Q v) = reflect Q v :=
  MulEquiv.apply_symm_apply _ _

private theorem orthTransvectionGL_mulVec_aux {v : ι → ZMod 2} (hv : Q v = 1)
    (x : ι → ZMod 2) :
    (orthTransvectionGL Q v : Matrix ι ι (ZMod 2)) *ᵥ x = x + polar Q x v • v := by
  rw [← toLinEquiv_apply, toLinEquiv_orthTransvectionGL, reflect_apply_of_map_eq_one hv]

private theorem mem_fischerTransvections_polar_iff (g : GL ι (ZMod 2)) :
    g ∈ fischerTransvections (polar Q) (fun v => Q v = 1) ↔
      ∃ v, Q v = 1 ∧ toLinEquiv ι (ZMod 2) g = reflect Q v := by
  refine exists_congr fun v => and_congr_right fun hv => ?_
  rw [LinearEquiv.ext_iff]
  simp only [toLinEquiv_apply, reflect_apply_of_map_eq_one hv]

private theorem orthTransvectionGL_mem_fischerTransvections_aux {v : ι → ZMod 2}
    (hv : Q v = 1) : orthTransvectionGL Q v ∈ fischerTransvections (polar Q) (fun v => Q v = 1) :=
  (mem_fischerTransvections_polar_iff _).mpr ⟨v, hv, toLinEquiv_orthTransvectionGL v⟩

private theorem eq_orthTransvectionGL_of_mem_aux {g : GL ι (ZMod 2)}
    (hg : g ∈ fischerTransvections (polar Q) (fun v => Q v = 1)) :
    ∃ v, Q v = 1 ∧ g = orthTransvectionGL Q v := by
  obtain ⟨v, hv, hgv⟩ := (mem_fischerTransvections_polar_iff g).mp hg
  exact ⟨v, hv, (toLinEquiv ι (ZMod 2)).injective (by rw [hgv, toLinEquiv_orthTransvectionGL])⟩

private theorem fischerTransvections_polar_subset_aux :
    fischerTransvections (polar Q) (fun v => Q v = 1) ⊆
      (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x) := by
  intro g hg
  obtain ⟨v, -, hgv⟩ := (mem_fischerTransvections_polar_iff g).mp hg
  rw [SetLike.mem_coe, fischerMatrixGroup_isometry_eq_comap, Subgroup.mem_comap,
    MulEquiv.coe_toMonoidHom, hgv]
  exact reflect_mem_orthogonalGroup Q v

private theorem closure_fischerTransvections_polar_eq_comap :
    Subgroup.closure (fischerTransvections (polar Q) fun v => Q v = 1) =
      (Subgroup.closure (Set.range (reflect Q))).comap (toLinEquiv ι (ZMod 2)).toMonoidHom := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro g hg
    obtain ⟨v, -, hgv⟩ := (mem_fischerTransvections_polar_iff g).mp hg
    rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, hgv]
    exact Subgroup.subset_closure ⟨v, rfl⟩
  · have key : ∀ H : Subgroup ((ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2)),
        H.comap (toLinEquiv ι (ZMod 2)).toMonoidHom =
          H.map (toLinEquiv ι (ZMod 2)).symm.toMonoidHom :=
      fun H => Subgroup.comap_equiv_eq_map_symm (toLinEquiv ι (ZMod 2)) H
    rw [key, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
    by_cases hv : Q v = 0
    · rw [SetLike.mem_coe, reflect_of_map_eq_zero hv, map_one]
      exact one_mem _
    · exact Subgroup.subset_closure
        (orthTransvectionGL_mem_fischerTransvections_aux (zmod_two_eq_one_of_ne_zero hv))

private theorem fischerMatrixGroup_orthogonal_eq_closure_aux (m : ℕ) (hm : 2 ≤ m)
    (Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2))
    (hnd : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0)
    (hplus : m = 2 → ¬ ∃ W : Submodule (ZMod 2) (Fin (2 * m) → ZMod 2),
      Module.finrank (ZMod 2) W = 2 ∧ ∀ w ∈ W, Q w = 0) :
    (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x) =
      Subgroup.closure (fischerTransvections (QuadraticMap.polar Q) fun v => Q v = 1) := by
  have hQ : (polarBilin Q).Nondegenerate :=
    ⟨fun x hx => hnd x fun y => by simpa using hx y,
      fun y hy => hnd y fun x => by rw [polar_comm]; simpa using hy x⟩
  have hdim : finrank (ZMod 2) (Fin (2 * m) → ZMod 2) = 2 * m := Module.finrank_fin_fun _
  have hE : 5 ≤ finrank (ZMod 2) (Fin (2 * m) → ZMod 2) ∨
      ¬ ∃ W : Submodule (ZMod 2) (Fin (2 * m) → ZMod 2),
        finrank (ZMod 2) W = 2 ∧ ∀ w ∈ W, Q w = 0 := by
    rcases Nat.lt_or_ge m 3 with h | h
    · exact Or.inr (hplus (by omega))
    · exact Or.inl (by omega)
  rw [fischerMatrixGroup_isometry_eq_comap, closure_fischerTransvections_polar_eq_comap,
    orthogonalGroup_eq_closure_reflect hQ (by omega) hE]

end Reflect

variable {Q : QuadraticForm (ZMod 2) (ι → ZMod 2)}

theorem orthTransvectionGL_mulVec {v : ι → ZMod 2} (hv : Q v = 1) (x : ι → ZMod 2) :
    (orthTransvectionGL Q v : Matrix ι ι (ZMod 2)) *ᵥ x = x + polar Q x v • v :=
  orthTransvectionGL_mulVec_aux hv x

theorem orthTransvectionGL_mem_fischerTransvections {v : ι → ZMod 2} (hv : Q v = 1) :
    orthTransvectionGL Q v ∈ fischerTransvections (polar Q) (fun v => Q v = 1) :=
  orthTransvectionGL_mem_fischerTransvections_aux hv

theorem eq_orthTransvectionGL_of_mem_fischerTransvections {g : GL ι (ZMod 2)}
    (hg : g ∈ fischerTransvections (polar Q) (fun v => Q v = 1)) :
    ∃ v, Q v = 1 ∧ g = orthTransvectionGL Q v :=
  eq_orthTransvectionGL_of_mem_aux hg

theorem fischerTransvections_polar_subset :
    fischerTransvections (polar Q) (fun v => Q v = 1) ⊆
      (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x) :=
  fischerTransvections_polar_subset_aux

theorem fischerMatrixGroup_orthogonal_eq_closure (m : ℕ) (hm : 2 ≤ m)
    (Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2))
    (hnd : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0)
    (hplus : m = 2 → ¬ ∃ W : Submodule (ZMod 2) (Fin (2 * m) → ZMod 2),
      Module.finrank (ZMod 2) W = 2 ∧ ∀ w ∈ W, Q w = 0) :
    (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x) =
      Subgroup.closure (fischerTransvections (QuadraticMap.polar Q) fun v => Q v = 1) :=
  fischerMatrixGroup_orthogonal_eq_closure_aux m hm Q hnd hplus

end CFSG.Fischer.Classification
