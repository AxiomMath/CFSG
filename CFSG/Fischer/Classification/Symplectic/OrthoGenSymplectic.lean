module

public import CFSG.ClassicalGroups.Alternating.Generation
public import CFSG.Open.FischerThreeTranspositionMilestoneDefs

public section

namespace CFSG.Fischer.Classification

open CFSG.Open CFSG.ClassicalGroups.Alternating CFSG.LocalAnalysis.ComponentInitial Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem fischerMatrixGroup_bilin_eq_comap {K : Type} [Field K]
    (b : LinearMap.BilinForm K (ι → K)) :
    (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y) =
      (bilinIsometryGroup b).comap (GeneralLinearGroup.toLin (n := ι) (R := K)).toMonoidHom := by
  apply le_antisymm
  · rw [fischerMatrixGroup, Subgroup.closure_le]
    intro A hA x y
    simpa [GeneralLinearGroup.coe_toLin] using hA x y
  · intro A hA
    refine Subgroup.subset_closure fun x y => ?_
    simpa [GeneralLinearGroup.coe_toLin] using hA x y

theorem mem_fischerMatrixGroup_bilin_iff {K : Type} [Field K] (b : LinearMap.BilinForm K (ι → K))
    (A : GL ι K) :
    A ∈ (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y) ↔
      ∀ x y, b ((A : Matrix ι ι K) *ᵥ x) ((A : Matrix ι ι K) *ᵥ y) = b x y := by
  rw [fischerMatrixGroup_bilin_eq_comap, Subgroup.mem_comap, mem_bilinIsometryGroup]
  simp [GeneralLinearGroup.coe_toLin]

section Transvection

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable (b : LinearMap.BilinForm (ZMod 2) (ι → ZMod 2)) (halt : ∀ x, b x x = 0)

noncomputable def sympTransvectionGL (v : ι → ZMod 2) : GL ι (ZMod 2) :=
  GeneralLinearGroup.toLin.symm (symplecticTransvection b halt v 1)

variable {b halt}

private theorem toLin_sympTransvectionGL_apply (v x : ι → ZMod 2) :
    (GeneralLinearGroup.toLin (sympTransvectionGL b halt v) : (ι → ZMod 2) →ₗ[ZMod 2] _) x =
      x + b x v • v := by
  have hb : b.IsAlt := halt
  have h : GeneralLinearGroup.toLin (sympTransvectionGL b halt v) =
      symplecticTransvection b hb v 1 :=
    MulEquiv.apply_symm_apply _ _
  rw [h, symplecticTransvection_apply, one_mul]

private theorem sympTransvectionGL_mulVec_aux (v x : ι → ZMod 2) :
    (sympTransvectionGL b halt v : Matrix ι ι (ZMod 2)) *ᵥ x = x + b x v • v := by
  simpa [GeneralLinearGroup.coe_toLin] using toLin_sympTransvectionGL_apply (halt := halt) v x

private theorem eq_sympTransvectionGL_iff (g : GL ι (ZMod 2)) (v : ι → ZMod 2) :
    g = sympTransvectionGL b halt v ↔ ∀ x, (g : Matrix ι ι (ZMod 2)) *ᵥ x = x + b x v • v := by
  rw [← GeneralLinearGroup.toLin.injective.eq_iff, Units.ext_iff, LinearMap.ext_iff]
  refine forall_congr' fun x => ?_
  rw [toLin_sympTransvectionGL_apply]
  simp [GeneralLinearGroup.coe_toLin]

private theorem sympTransvectionGL_mem_fischerTransvections_aux {v : ι → ZMod 2} (hv : v ≠ 0) :
    sympTransvectionGL b halt v ∈ fischerTransvections (fun x y => b x y) (fun v => v ≠ 0) :=
  ⟨v, hv, (eq_sympTransvectionGL_iff _ v).mp rfl⟩

private theorem eq_sympTransvectionGL_of_mem_aux {g : GL ι (ZMod 2)}
    (hg : g ∈ fischerTransvections (fun x y => b x y) (fun v => v ≠ 0)) :
    ∃ v, v ≠ 0 ∧ g = sympTransvectionGL b halt v := by
  obtain ⟨v, hv, hgv⟩ := hg
  exact ⟨v, hv, (eq_sympTransvectionGL_iff g v).mpr hgv⟩

private theorem sympTransvectionGL_mem_fischerMatrixGroup_aux (v : ι → ZMod 2) :
    sympTransvectionGL b halt v ∈
      (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y) := by
  have hb : b.IsAlt := halt
  have h : GeneralLinearGroup.toLin (sympTransvectionGL b halt v) =
      symplecticTransvection b hb v 1 :=
    MulEquiv.apply_symm_apply _ _
  rw [fischerMatrixGroup_bilin_eq_comap, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, h]
  exact symplecticTransvection_mem_bilinIsometryGroup hb v 1

omit [DecidableEq ι] in
private theorem symplecticTransvection_eq_one_or (hb : b.IsAlt) (a : ι → ZMod 2) (c : ZMod 2) :
    symplecticTransvection b hb a c = 1 ∨
      a ≠ 0 ∧ symplecticTransvection b hb a c = symplecticTransvection b hb a 1 := by
  by_cases ha : a = 0
  · refine Or.inl (Units.ext (LinearMap.ext fun x => ?_))
    rw [symplecticTransvection_apply, ha, smul_zero, add_zero]
    rfl
  have h01 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases h01 c with rfl | rfl
  · exact Or.inl (symplecticTransvection_zero hb a)
  · exact Or.inr ⟨ha, rfl⟩

private theorem closure_fischerTransvections_bilin_eq_comap (hb : b.IsAlt) :
    Subgroup.closure (fischerTransvections (fun x y => b x y) fun v => v ≠ 0) =
      (Subgroup.closure {g | ∃ (a : ι → ZMod 2) (c : ZMod 2),
        g = symplecticTransvection b hb a c}).comap
          (GeneralLinearGroup.toLin (n := ι) (R := ZMod 2)).toMonoidHom := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro g hg
    obtain ⟨v, -, hgv⟩ := eq_sympTransvectionGL_of_mem_aux (halt := hb) hg
    have h : GeneralLinearGroup.toLin g = symplecticTransvection b hb v 1 := by
      rw [hgv]
      exact MulEquiv.apply_symm_apply _ _
    rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, h]
    exact Subgroup.subset_closure ⟨v, 1, rfl⟩
  · have key : ∀ H : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) (ι → ZMod 2)),
        H.comap (GeneralLinearGroup.toLin (n := ι) (R := ZMod 2)).toMonoidHom =
          H.map (GeneralLinearGroup.toLin (n := ι) (R := ZMod 2)).symm.toMonoidHom :=
      fun H => Subgroup.comap_equiv_eq_map_symm GeneralLinearGroup.toLin H
    rw [key, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨a, c, rfl⟩, rfl⟩
    rcases symplecticTransvection_eq_one_or hb a c with h | ⟨ha, h⟩
    · rw [SetLike.mem_coe, h, map_one]
      exact one_mem _
    · rw [h]
      exact Subgroup.subset_closure
        (sympTransvectionGL_mem_fischerTransvections_aux (halt := hb) ha)

include halt in
private theorem fischerMatrixGroup_bilin_eq_closure_aux (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) :
    (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y) =
      Subgroup.closure (fischerTransvections (fun x y => b x y) fun v => v ≠ 0) := by
  have hb : b.IsAlt := halt
  have hbn : b.Nondegenerate :=
    (LinearMap.IsRefl.nondegenerate_iff_separatingLeft hb.isRefl).mpr hnd
  rw [fischerMatrixGroup_bilin_eq_comap, closure_fischerTransvections_bilin_eq_comap hb,
    alternating_transvection_generation hb hbn]

end Transvection

variable {b : LinearMap.BilinForm (ZMod 2) (ι → ZMod 2)} {halt : ∀ x, b x x = 0}

theorem sympTransvectionGL_mulVec (v x : ι → ZMod 2) :
    (sympTransvectionGL b halt v : Matrix ι ι (ZMod 2)) *ᵥ x = x + b x v • v :=
  sympTransvectionGL_mulVec_aux v x

theorem sympTransvectionGL_mem_fischerTransvections {v : ι → ZMod 2} (hv : v ≠ 0) :
    sympTransvectionGL b halt v ∈ fischerTransvections (fun x y => b x y) (fun v => v ≠ 0) :=
  sympTransvectionGL_mem_fischerTransvections_aux hv

theorem eq_sympTransvectionGL_of_mem_fischerTransvections (halt : ∀ x, b x x = 0)
    {g : GL ι (ZMod 2)} (hg : g ∈ fischerTransvections (fun x y => b x y) (fun v => v ≠ 0)) :
    ∃ v, v ≠ 0 ∧ g = sympTransvectionGL b halt v :=
  eq_sympTransvectionGL_of_mem_aux hg

theorem sympTransvectionGL_mem_fischerMatrixGroup (v : ι → ZMod 2) :
    sympTransvectionGL b halt v ∈
      (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y) :=
  sympTransvectionGL_mem_fischerMatrixGroup_aux v

theorem fischerTransvections_bilin_subset (halt : ∀ x, b x x = 0) :
    fischerTransvections (fun x y => b x y) (fun v => v ≠ 0) ⊆
      (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y) := by
  intro g hg
  obtain ⟨v, -, rfl⟩ := eq_sympTransvectionGL_of_mem_fischerTransvections halt hg
  exact sympTransvectionGL_mem_fischerMatrixGroup v

theorem fischerMatrixGroup_bilin_eq_closure (b : LinearMap.BilinForm (ZMod 2) (ι → ZMod 2))
    (halt : ∀ x, b x x = 0) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) :
    (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y) =
      Subgroup.closure (fischerTransvections (fun x y => b x y) fun v => v ≠ 0) :=
  fischerMatrixGroup_bilin_eq_closure_aux (halt := halt) hnd

theorem fischerMatrixGroup_symplectic_eq_closure (m : ℕ)
    (b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2)) (halt : ∀ x, b x x = 0)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) :
    (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y) =
      Subgroup.closure (fischerTransvections (fun x y => b x y) fun v => v ≠ 0) :=
  fischerMatrixGroup_bilin_eq_closure b halt hnd

end CFSG.Fischer.Classification
