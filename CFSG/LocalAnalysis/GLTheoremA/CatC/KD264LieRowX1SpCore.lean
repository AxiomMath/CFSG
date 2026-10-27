module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1SpIsom
public import CFSG.LargeExtraspecial.S45QPhi
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1SpCent
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1SpFix

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Sp

open CFSG.Open Module

section Core

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
variable {E : Subgroup (W ≃ₗ[ZMod 2] W)} {n : ℕ} (D : PlaneData E n)

@[expose] noncomputable def PlaneData.GU (f : LinearMap.BilinForm (ZMod 2) W) :
    Subgroup (↥(D.piecesOf (idxLo n)) ≃ₗ[ZMod 2] ↥(D.piecesOf (idxLo n))) :=
  TauCeti.BilinForm.isometryGroup (D.fU f)

@[expose] noncomputable def PlaneData.Ψ (f : LinearMap.BilinForm (ZMod 2) W) (hn : 2 ≤ n) :
    ↥(D.GU f) →* (W ≃ₗ[ZMod 2] W) :=
  (extEquiv (D.piecesOf (idxLo n)) (D.piecesOf (idxHi n)) (D.isCompl_pieces hn)).comp
    (D.GU f).subtype

@[expose] noncomputable def PlaneData.Hg (f : LinearMap.BilinForm (ZMod 2) W) (hn : 2 ≤ n) :
    Subgroup (W ≃ₗ[ZMod 2] W) :=
  (D.Ψ f hn).range

@[expose] noncomputable def PlaneData.Lg (f : LinearMap.BilinForm (ZMod 2) W) (hn : 2 ≤ n) :
    Subgroup (W ≃ₗ[ZMod 2] W) :=
  (commutator ↥(D.GU f)).map (D.Ψ f hn)

@[expose] noncomputable def PlaneData.Cg (f : LinearMap.BilinForm (ZMod 2) W) :
    Subgroup (W ≃ₗ[ZMod 2] W) :=
  Subgroup.centralizer (D.fixU : Set (W ≃ₗ[ZMod 2] W)) ⊓ TauCeti.BilinForm.isometryGroup f

theorem PlaneData.Ψ_injective (f : LinearMap.BilinForm (ZMod 2) W) (hn : 2 ≤ n) :
    Function.Injective (D.Ψ f hn) :=
  (extEquiv_injective _ _ _).comp Subtype.val_injective

theorem PlaneData.Ψ_mem_isom (f : LinearMap.BilinForm (ZMod 2) W)
    (hf : ∀ g ∈ E, ∀ x y, f (g x) (g y) = f x y) (hfalt : f.IsAlt) (hn : 2 ≤ n)
    (φ : ↥(D.GU f)) : (D.Ψ f hn φ) ∈ TauCeti.BilinForm.isometryGroup f := by
  rw [TauCeti.BilinForm.mem_isometryGroup_iff]
  intro x y
  have hφ : ∀ u v : ↥(D.piecesOf (idxLo n)), f (φ.1 u : W) (φ.1 v : W) = f u v := by
    intro u v
    exact (TauCeti.BilinForm.mem_isometryGroup_iff.1 φ.2) u v
  exact D.extFun_isom f hf hfalt hn φ.1 hφ x y

theorem PlaneData.Hg_le_Cg (f : LinearMap.BilinForm (ZMod 2) W)
    (hf : ∀ g ∈ E, ∀ x y, f (g x) (g y) = f x y) (hfalt : f.IsAlt) (hn : 2 ≤ n) :
    D.Hg f hn ≤ D.Cg f := by
  rintro x ⟨φ, rfl⟩
  refine Subgroup.mem_inf.2 ⟨?_, D.Ψ_mem_isom f hf hfalt hn φ⟩
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  exact D.extFun_comm _ _ (D.isCompl_pieces hn) rfl rfl h hh φ.1

theorem PlaneData.Cg_stable (f : LinearMap.BilinForm (ZMod 2) W)
    (hf : ∀ g ∈ E, ∀ x y, f (g x) (g y) = f x y) (hfalt : f.IsAlt) (hfnd : f.Nondegenerate)
    (hE : IsElemAbelian 3 E) (hn : 2 ≤ n) {c : W ≃ₗ[ZMod 2] W} (hc : c ∈ D.Cg f) :
    (∀ u ∈ D.piecesOf (idxLo n), c u ∈ D.piecesOf (idxLo n)) ∧
    (∀ u ∈ D.piecesOf (idxLo n), c.symm u ∈ D.piecesOf (idxLo n)) ∧
    (∀ w ∈ D.piecesOf (idxHi n), c w ∈ D.piecesOf (idxHi n)) ∧
    (∀ w ∈ D.piecesOf (idxHi n), c.symm w ∈ D.piecesOf (idxHi n)) := by
  obtain ⟨hcent, hiso⟩ := Subgroup.mem_inf.1 hc
  have hcomm : ∀ i : Fin n, 2 ≤ i.val → ∀ v, c (D.e i v) = D.e i (c v) := by
    intro i hi v
    have h := (Subgroup.mem_centralizer_iff.1 hcent) (D.e i) (D.e_mem_fixU i hi)
    have hv := congrArg (fun φ : W ≃ₗ[ZMod 2] W => φ v) h
    simpa [LinearEquiv.mul_apply] using hv.symm
  have hcomm' : ∀ i : Fin n, 2 ≤ i.val → ∀ v, c.symm (D.e i v) = D.e i (c.symm v) := by
    intro i hi v
    apply c.injective
    rw [LinearEquiv.apply_symm_apply, hcomm i hi, LinearEquiv.apply_symm_apply]
  have hW : ∀ w ∈ D.piecesOf (idxHi n), c w ∈ D.piecesOf (idxHi n) :=
    D.hi_stable hE c hcomm
  have hWi : ∀ w ∈ D.piecesOf (idxHi n), c.symm w ∈ D.piecesOf (idxHi n) :=
    D.hi_stable hE c.symm hcomm'
  have hgf : ∀ x y, f (c x) (c y) = f x y := fun x y =>
    (TauCeti.BilinForm.mem_isometryGroup_iff.1 hiso) x y
  have hU : ∀ u ∈ D.piecesOf (idxLo n), c u ∈ D.piecesOf (idxLo n) :=
    D.lo_stable f hf hfalt hfnd hn c hgf hWi
  have hgf' : ∀ x y, f (c.symm x) (c.symm y) = f x y := by
    intro x y
    rw [← hgf (c.symm x) (c.symm y), LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have hUi : ∀ u ∈ D.piecesOf (idxLo n), c.symm u ∈ D.piecesOf (idxLo n) :=
    D.lo_stable f hf hfalt hfnd hn c.symm hgf' (fun w hw => by
      rw [LinearEquiv.symm_symm]
      exact hW w hw)
  exact ⟨hU, hUi, hW, hWi⟩

theorem PlaneData.restrictU_mem_GU (f : LinearMap.BilinForm (ZMod 2) W) (c : W ≃ₗ[ZMod 2] W)
    (hcf : ∀ x y, f (c x) (c y) = f x y) (hU : ∀ u ∈ D.piecesOf (idxLo n), c u ∈ D.piecesOf (idxLo n))
    (hUi : ∀ u ∈ D.piecesOf (idxLo n), c.symm u ∈ D.piecesOf (idxLo n)) :
    restrictU (D.piecesOf (idxLo n)) c (hU) (hUi) ∈ D.GU f := by
  rw [PlaneData.GU, TauCeti.BilinForm.mem_isometryGroup_iff]
  intro u v
  rw [PlaneData.fU_apply, PlaneData.fU_apply, restrictU_apply, restrictU_apply]
  exact hcf _ _

theorem PlaneData.conj_Hg_mem (f : LinearMap.BilinForm (ZMod 2) W)
    (hf : ∀ g ∈ E, ∀ x y, f (g x) (g y) = f x y) (hfalt : f.IsAlt) (hfnd : f.Nondegenerate)
    (hE : IsElemAbelian 3 E) (hn : 2 ≤ n) {c : W ≃ₗ[ZMod 2] W} (hc : c ∈ D.Cg f)
    {x : W ≃ₗ[ZMod 2] W} (hx : x ∈ D.Hg f hn) : c * x * c⁻¹ ∈ D.Hg f hn := by
  obtain ⟨hU, hUi, hW, hWi⟩ := D.Cg_stable f hf hfalt hfnd hE hn hc
  obtain ⟨φ, rfl⟩ := hx
  have hcf : ∀ u v, f (c u) (c v) = f u v := fun u v =>
    (TauCeti.BilinForm.mem_isometryGroup_iff.1 (Subgroup.mem_inf.1 hc).2) u v
  have hgU := D.restrictU_mem_GU f c hcf hU hUi
  refine ⟨⟨restrictU (D.piecesOf (idxLo n)) c hU hUi * φ.1 *
      (restrictU (D.piecesOf (idxLo n)) c hU hUi).symm, ?_⟩, ?_⟩
  · exact mul_mem (mul_mem hgU φ.2) (inv_mem hgU)
  · have key := conj_extFun (D.piecesOf (idxLo n)) (D.piecesOf (idxHi n)) (D.isCompl_pieces hn) c
      hU hUi hW hWi φ.1
    exact key.symm

theorem PlaneData.Lg_conj_mem (f : LinearMap.BilinForm (ZMod 2) W) (hn : 2 ≤ n)
    {x : W ≃ₗ[ZMod 2] W} (hx : x ∈ D.Hg f hn) {y : W ≃ₗ[ZMod 2] W} (hy : y ∈ D.Lg f hn) :
    x * y * x⁻¹ ∈ D.Lg f hn := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  refine ⟨a * b * a⁻¹, Subgroup.Normal.conj_mem inferInstance b hb a, ?_⟩
  simp [map_mul, map_inv]

theorem PlaneData.isSubnormal_Lg_Cg (f : LinearMap.BilinForm (ZMod 2) W)
    (hf : ∀ g ∈ E, ∀ x y, f (g x) (g y) = f x y) (hfalt : f.IsAlt) (hfnd : f.Nondegenerate)
    (hE : IsElemAbelian 3 E) (hn : 2 ≤ n) :
    CFSG.Open.IsSubnormal (D.Lg f hn) (D.Cg f) := by
  have hLH : D.Lg f hn ≤ D.Hg f hn := by
    rintro y ⟨b, _, rfl⟩
    exact ⟨b, rfl⟩
  have hHC : D.Hg f hn ≤ D.Cg f := D.Hg_le_Cg f hf hfalt hn
  refine CFSG.Open.IsSubnormal.step hLH ?_
    (CFSG.Open.IsSubnormal.step hHC ?_ (CFSG.Open.IsSubnormal.refl (D.Cg f)))
  · constructor
    intro n' hn' g
    rw [Subgroup.mem_subgroupOf] at hn' ⊢
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact D.Lg_conj_mem f hn g.2 hn'
  · constructor
    intro n' hn' g
    rw [Subgroup.mem_subgroupOf] at hn' ⊢
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact D.conj_Hg_mem f hf hfalt hfnd hE hn g.2 hn'

theorem PlaneData.Lg_iso_alt (f : LinearMap.BilinForm (ZMod 2) W)
    (hf : ∀ g ∈ E, ∀ x y, f (g x) (g y) = f x y) (hfalt : f.IsAlt) (hfnd : f.Nondegenerate)
    (hn : 2 ≤ n) :
    Nonempty (↥(D.Lg f hn) ≃* alternatingGroup (Fin 6)) := by
  have hnd := D.fU_nondeg f hf hfalt hfnd hn
  have h4 : Module.finrank (ZMod 2) ↥(D.piecesOf (idxLo n)) = 4 := D.finrank_lo hn
  obtain ⟨Φ0⟩ := CFSG.LargeExtraspecial.S45Q.nonempty_isometryGroup_equiv_perm
    (D.fU_isAlt f hfalt) hnd h4
  let Φ : ↥(D.GU f) ≃* Equiv.Perm (Fin 6) := Φ0
  have hmap : (commutator ↥(D.GU f)).map (Φ : ↥(D.GU f) →* Equiv.Perm (Fin 6)) =
      commutator (Equiv.Perm (Fin 6)) := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.2 Φ.surjective, commutator_def]
  have hcomm : Nonempty (commutator ↥(D.GU f) ≃* alternatingGroup (Fin 6)) :=
    ⟨(((Φ.subgroupMap (commutator ↥(D.GU f))).trans
      (MulEquiv.subgroupCongr hmap)).trans
      (MulEquiv.subgroupCongr (alternatingGroup.commutator_perm_eq (by simp))))⟩
  obtain ⟨ψ⟩ := hcomm
  exact ⟨((Subgroup.equivMapOfInjective (commutator ↥(D.GU f)) (D.Ψ f hn)
    (D.Ψ_injective f hn)).symm.trans ψ)⟩

end Core

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Sp

end
