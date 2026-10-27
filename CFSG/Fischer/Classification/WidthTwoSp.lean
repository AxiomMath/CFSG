module

public import CFSG.RankThree.SubgroupLists.SymplecticFischerSp
public import CFSG.OddTranspositions.Width
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Fischer.Classification

open CFSG.Open Matrix CFSG.OddTranspositions

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {m : ℕ} (b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2))
  (halt : ∀ x, b x x = 0)

noncomputable abbrev tv (v : Fin (2 * m) → ZMod 2) : GL (Fin (2 * m)) (ZMod 2) :=
  sympTransvectionGL b halt v

theorem tv_mem_fischerTransvections {v : Fin (2 * m) → ZMod 2} (hv : v ≠ 0) :
    tv b halt v ∈ fischerTransvections (fun x y => b x y) (fun v => v ≠ 0) :=
  sympTransvectionGL_mem_fischerTransvections (b := b) (halt := halt) hv

theorem tv_mem_fischerMatrixGroup (v : Fin (2 * m) → ZMod 2) :
    tv b halt v ∈
      fischerMatrixGroup (fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y) :=
  sympTransvectionGL_mem_fischerMatrixGroup (b := b) (halt := halt) v

theorem tv_commute {v w : Fin (2 * m) → ZMod 2} (hvw : b v w = 0) :
    Commute (tv b halt v) (tv b halt w) :=
  CFSG.RankThree.SubgroupLists.SpFischer.sympTransvectionGL_commute
    (b := b) (halt := halt) hvw

theorem eq_of_tv_eq (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    {v w : Fin (2 * m) → ZMod 2} (hv : v ≠ 0) (h : tv b halt v = tv b halt w) : v = w :=
  CFSG.RankThree.SubgroupLists.SpFischer.eq_of_sympTransvectionGL_eq
    (b := b) halt hnd hv (by simpa [tv] using h)

theorem exists_three_pairwise_orthogonal (halt : ∀ x, b x x = 0) (hm : 2 ≤ m)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) :
    ∃ v0 v1 v2 : Fin (2 * m) → ZMod 2,
      v0 ≠ 0 ∧ v1 ≠ 0 ∧ v2 ≠ 0 ∧
      v0 ≠ v1 ∧ v0 ≠ v2 ∧ v1 ≠ v2 ∧
      b v0 v1 = 0 ∧ b v0 v2 = 0 ∧ b v1 v2 = 0 := by
  classical
  have hb : b.IsAlt := halt
  have hbn : b.Nondegenerate :=
    (LinearMap.IsRefl.nondegenerate_iff_separatingLeft hb.isRefl).mpr hnd
  obtain ⟨m', bs, hbs⟩ := hb.exists_basis_toMatrix_eq_J hbn
  have hcard : Fintype.card (Fin m' ⊕ Fin m') = 2 * m := by
    rw [← Module.finrank_eq_card_basis bs, Module.finrank_fintype_fun_eq_card]
    simp
  have hm' : m' = m := by
    rw [Fintype.card_sum, Fintype.card_fin] at hcard
    omega
  subst m'
  let i0 : Fin m := ⟨0, by omega⟩
  let i1 : Fin m := ⟨1, by omega⟩
  let v0 : Fin (2 * m) → ZMod 2 := bs (Sum.inl i0)
  let v1 : Fin (2 * m) → ZMod 2 := bs (Sum.inl i1)
  let v2 : Fin (2 * m) → ZMod 2 := v0 + v1
  have hJ : ∀ x y, b (bs x) (bs y) = Matrix.J (Fin m) (ZMod 2) x y := by
    intro x y
    rw [← LinearMap.BilinForm.toMatrix_apply bs b x y, hbs]
  have hi01 : i0 ≠ i1 := by
    intro h
    have := congrArg Fin.val h
    simp [i0, i1] at this
  have hv0 : v0 ≠ 0 := bs.ne_zero _
  have hv1 : v1 ≠ 0 := bs.ne_zero _
  have hv01 : v0 ≠ v1 := by
    intro h
    exact hi01 (Sum.inl.inj (bs.injective h))
  have hv2 : v2 ≠ 0 := by
    intro h
    have h' : v0 = v1 := by
      have := congrArg (fun x => x + v1) h
      simpa [v2, add_assoc, ZModModule.add_self] using this
    exact hv01 h'
  have hv02 : v0 ≠ v2 := by
    intro h
    have h' : v1 = 0 := by
      have h1 : v0 + v1 = v0 + 0 := by simpa [v2] using h.symm
      simpa using add_left_cancel h1
    exact hv1 h'
  have hv12 : v1 ≠ v2 := by
    intro h
    have h' : v0 = 0 := by
      have := congrArg (fun x => x + v1) h.symm
      simpa [v2, add_assoc, add_comm, add_left_comm, ZModModule.add_self] using this
    exact hv0 h'
  have h01 : b v0 v1 = 0 := by
    have := hJ (Sum.inl i0) (Sum.inl i1)
    simpa [v0, v1, Matrix.J] using this
  have h10 : b v1 v0 = 0 := by
    have := hJ (Sum.inl i1) (Sum.inl i0)
    simpa [v0, v1, Matrix.J] using this
  have h02 : b v0 v2 = 0 := by
    change b v0 (v0 + v1) = 0
    rw [map_add, halt v0, h01, add_zero]
  have h12 : b v1 v2 = 0 := by
    change b v1 (v0 + v1) = 0
    rw [map_add, h10, halt v1, add_zero]
  exact ⟨v0, v1, v2, hv0, hv1, hv2, hv01, hv02, hv12, h01, h02, h12⟩

theorem exists_three_commuting_transvections (halt : ∀ x, b x x = 0) (hm : 2 ≤ m)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) :
    ∃ g0 g1 g2 : GL (Fin (2 * m)) (ZMod 2),
      g0 ∈ fischerMatrixGroup (fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y) ∧
      g1 ∈ fischerMatrixGroup (fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y) ∧
      g2 ∈ fischerMatrixGroup (fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y) ∧
      g0 ∈ fischerTransvections (fun x y => b x y) (fun v => v ≠ 0) ∧
      g1 ∈ fischerTransvections (fun x y => b x y) (fun v => v ≠ 0) ∧
      g2 ∈ fischerTransvections (fun x y => b x y) (fun v => v ≠ 0) ∧
      g0 ≠ g1 ∧ g0 ≠ g2 ∧ g1 ≠ g2 ∧
      Commute g0 g1 ∧ Commute g0 g2 ∧ Commute g1 g2 := by
  obtain ⟨v0, v1, v2, hv0, hv1, hv2, hv01, hv02, hv12, h01, h02, h12⟩ :=
    exists_three_pairwise_orthogonal b halt hm hnd
  refine ⟨tv b halt v0, tv b halt v1, tv b halt v2,
    tv_mem_fischerMatrixGroup b halt v0, tv_mem_fischerMatrixGroup b halt v1,
    tv_mem_fischerMatrixGroup b halt v2,
    tv_mem_fischerTransvections b halt hv0, tv_mem_fischerTransvections b halt hv1,
    tv_mem_fischerTransvections b halt hv2, ?_, ?_, ?_,
    tv_commute b halt h01, tv_commute b halt h02, tv_commute b halt h12⟩
  · intro h
    exact hv01 (eq_of_tv_eq b halt hnd hv0 h)
  · intro h
    exact hv02 (eq_of_tv_eq b halt hnd hv0 h)
  · intro h
    exact hv12 (eq_of_tv_eq b halt hnd hv1 h)

theorem exists_three_commuting_mem_of_sp_case {G : Type*} [Group G] {D : Set G}
    (hSp : ∃ m : ℕ, 2 ≤ m ∧ ∃ b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2),
      (∀ x, b x x = 0) ∧ (∀ x, (∀ y, b x y = 0) → x = 0) ∧
      fischerLinearModel D
        (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y)
        (fischerTransvections (fun x y => b x y) fun v => v ≠ 0)) :
    ∃ y0 y1 y2 : G,
      y0 ∈ D ∧ y1 ∈ D ∧ y2 ∈ D ∧
      y0 ≠ y1 ∧ y0 ≠ y2 ∧ y1 ≠ y2 ∧
      Commute y0 y1 ∧ Commute y0 y2 ∧ Commute y1 y2 := by
  classical
  obtain ⟨m, hm, b, halt, hnd, φ, hD⟩ := hSp
  obtain ⟨g0, g1, g2, hg0H, hg1H, hg2H, hg0T, hg1T, hg2T,
    hg01, hg02, hg12, hc01, hc02, hc12⟩ :=
    exists_three_commuting_transvections b halt hm hnd
  let y0 : G := φ.symm ⟨g0, hg0H⟩
  let y1 : G := φ.symm ⟨g1, hg1H⟩
  let y2 : G := φ.symm ⟨g2, hg2H⟩
  have hy0D : y0 ∈ D := by
    rw [hD y0]
    simpa [y0] using hg0T
  have hy1D : y1 ∈ D := by
    rw [hD y1]
    simpa [y1] using hg1T
  have hy2D : y2 ∈ D := by
    rw [hD y2]
    simpa [y2] using hg2T
  have hy01 : y0 ≠ y1 := by
    intro h
    exact hg01 (by simpa [y0, y1] using φ.symm.injective h)
  have hy02 : y0 ≠ y2 := by
    intro h
    exact hg02 (by simpa [y0, y2] using φ.symm.injective h)
  have hy12 : y1 ≠ y2 := by
    intro h
    exact hg12 (by simpa [y1, y2] using φ.symm.injective h)
  have hcomm01 : Commute y0 y1 := by
    have hH : Commute (φ y0) (φ y1) := by
      rw [show φ y0 = ⟨g0, hg0H⟩ from φ.apply_symm_apply ⟨g0, hg0H⟩,
        show φ y1 = ⟨g1, hg1H⟩ from φ.apply_symm_apply ⟨g1, hg1H⟩]
      exact Subtype.ext hc01
    simpa [y0, y1] using hH.map φ.symm.toMonoidHom
  have hcomm02 : Commute y0 y2 := by
    have hH : Commute (φ y0) (φ y2) := by
      rw [show φ y0 = ⟨g0, hg0H⟩ from φ.apply_symm_apply ⟨g0, hg0H⟩,
        show φ y2 = ⟨g2, hg2H⟩ from φ.apply_symm_apply ⟨g2, hg2H⟩]
      exact Subtype.ext hc02
    simpa [y0, y2] using hH.map φ.symm.toMonoidHom
  have hcomm12 : Commute y1 y2 := by
    have hH : Commute (φ y1) (φ y2) := by
      rw [show φ y1 = ⟨g1, hg1H⟩ from φ.apply_symm_apply ⟨g1, hg1H⟩,
        show φ y2 = ⟨g2, hg2H⟩ from φ.apply_symm_apply ⟨g2, hg2H⟩]
      exact Subtype.ext hc12
    simpa [y1, y2] using hH.map φ.symm.toMonoidHom
  exact ⟨y0, y1, y2, hy0D, hy1D, hy2D, hy01, hy02, hy12,
    hcomm01, hcomm02, hcomm12⟩

theorem width_two_false_of_sp_case {G : Type*} [Group G] {D : Set G}
    (hSp : ∃ m : ℕ, 2 ≤ m ∧ ∃ b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2),
      (∀ x, b x x = 0) ∧ (∀ x, (∀ y, b x y = 0) → x = 0) ∧
      fischerLinearModel D
        (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y)
        (fischerTransvections (fun x y => b x y) fun v => v ≠ 0)) :
    ¬ WidthLe D 2 := by
  obtain ⟨y0, y1, y2, hy0D, hy1D, hy2D, hy01, hy02, hy12, hcomm01, hcomm02, hcomm12⟩ :=
    exists_three_commuting_mem_of_sp_case hSp
  intro hW
  rw [widthLe_two_iff] at hW
  exact hW y0 hy0D y1 hy1D y2 hy2D hy01 hy02 hy12
    ⟨hcomm01, hcomm02, hcomm12⟩

end CFSG.Fischer.Classification
