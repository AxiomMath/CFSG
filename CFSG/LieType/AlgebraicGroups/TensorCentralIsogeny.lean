module
public import CFSG.LieType.AlgebraicGroups.FixedComponentProduct
public import TauCeti.Algebra.AlgebraicGroup.Isogeny.Basic
public import TauCeti.RingTheory.RingHom.FaithfullyFlat

public noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace CFSG.LieType.AlgebraicGroups
universe u
variable {k : Type u} [Field k]

theorem pointsMulEquiv_eq_affine
    (T S : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (A : CommAlgCat.{u} k) :
    TauCeti.FiniteTypeCommHopfAlgCat.pointsMulEquiv A T S =
      TauCeti.AffineGroup.Product.pointsMulEquiv (R := k) (H₁ := T) (H₂ := S) (A := A) := by
  let E := TauCeti.FiniteTypeCommHopfAlgCat.pointsMulEquiv A T S
  let F := TauCeti.AffineGroup.Product.pointsMulEquiv (R := k) (H₁ := T) (H₂ := S) (A := A)
  apply MulEquiv.ext
  intro y
  apply E.symm.injective
  rw [E.symm_apply_apply]
  calc
    y = F.symm (F y) := (F.symm_apply_apply y).symm
    _ = E.symm (F y) := by
      dsimp only [E, F]
      rw [TauCeti.FiniteTypeCommHopfAlgCat.pointsMulEquiv_symm_apply,
        TauCeti.AffineGroup.Product.pointsMulEquiv_symm_apply]

theorem lTensor_comp_includeLeft
    (T D S : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (q : D.obj ⟶ S.obj) :
    (q.hom.lTensor T).comp
        (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
          (TauCeti.FiniteTypeCommHopfAlgCat.includeLeft T D)) =
      TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
        (TauCeti.FiniteTypeCommHopfAlgCat.includeLeft T S) := by
  apply BialgHom.ext
  intro t
  have hL : (q.hom.lTensor T)
      ((TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
        (TauCeti.FiniteTypeCommHopfAlgCat.includeLeft T D)) t) =
      t ⊗ₜ[k] q.hom (1 : D) := by
    rw [TauCeti.FiniteTypeCommHopfAlgCat.includeLeft_apply]
    change (Bialgebra.TensorProduct.map (BialgHom.id k T) q.hom) (t ⊗ₜ[k] (1 : D)) =
      t ⊗ₜ[k] q.hom (1 : D)
    rw [Bialgebra.TensorProduct.map_tmul, BialgHom.id_apply]
  have hR : (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
      (TauCeti.FiniteTypeCommHopfAlgCat.includeLeft T S)) t = t ⊗ₜ[k] (1 : S) :=
    TauCeti.FiniteTypeCommHopfAlgCat.includeLeft_apply T S t
  rw [BialgHom.comp_apply, hL, hR, map_one]

theorem lTensor_comp_includeRight
    (T D S : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (q : D.obj ⟶ S.obj) :
    (q.hom.lTensor T).comp
        (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
          (TauCeti.FiniteTypeCommHopfAlgCat.includeRight T D)) =
      (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
        (TauCeti.FiniteTypeCommHopfAlgCat.includeRight T S)).comp q.hom := by
  apply BialgHom.ext
  intro d
  have hL : (q.hom.lTensor T)
      ((TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
        (TauCeti.FiniteTypeCommHopfAlgCat.includeRight T D)) d) =
      (1 : T) ⊗ₜ[k] q.hom d := by
    rw [TauCeti.FiniteTypeCommHopfAlgCat.includeRight_apply]
    change (Bialgebra.TensorProduct.map (BialgHom.id k T) q.hom) ((1 : T) ⊗ₜ[k] d) =
      (1 : T) ⊗ₜ[k] q.hom d
    rw [Bialgebra.TensorProduct.map_tmul, BialgHom.id_apply]
  have hR : ((TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
      (TauCeti.FiniteTypeCommHopfAlgCat.includeRight T S)).comp q.hom) d =
      (1 : T) ⊗ₜ[k] q.hom d := by
    rw [BialgHom.comp_apply, TauCeti.FiniteTypeCommHopfAlgCat.includeRight_apply]
  rw [BialgHom.comp_apply, hL, hR]

theorem pointsMulEquiv_mapDomain_lTensor
    (T D S : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (q : D.obj ⟶ S.obj) (A : CommAlgCat.{u} k)
    (y : TauCeti.HopfAlgebra.points (R := k)
      (H := TauCeti.FiniteTypeCommHopfAlgCat.tensorProduct T S) A) :
    TauCeti.FiniteTypeCommHopfAlgCat.pointsMulEquiv A T D
        (TauCeti.AlgHom.mapDomain (q.hom.lTensor T) y) =
      ((TauCeti.FiniteTypeCommHopfAlgCat.pointsMulEquiv A T S y).1,
        TauCeti.AlgHom.mapDomain q.hom
          (TauCeti.FiniteTypeCommHopfAlgCat.pointsMulEquiv A T S y).2) := by
  apply Prod.ext
  · rw [CFSG.LieType.AlgebraicGroups.FixedProduct.pointsMulEquiv_fst_eq,
      ← MonoidHom.comp_apply, ← TauCeti.AlgHom.mapDomain_comp,
      lTensor_comp_includeLeft,
      CFSG.LieType.AlgebraicGroups.FixedProduct.pointsMulEquiv_fst_eq]
  · rw [CFSG.LieType.AlgebraicGroups.FixedProduct.pointsMulEquiv_snd_eq,
      ← MonoidHom.comp_apply, ← TauCeti.AlgHom.mapDomain_comp,
      lTensor_comp_includeRight, TauCeti.AlgHom.mapDomain_comp, MonoidHom.comp_apply,
      CFSG.LieType.AlgebraicGroups.FixedProduct.pointsMulEquiv_snd_eq]

theorem isCentralPoint_of_fst_one
    (T S : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    {A : CommAlgCat.{u} k}
    (y : TauCeti.HopfAlgebra.points (R := k)
      (H := TauCeti.FiniteTypeCommHopfAlgCat.tensorProduct T S) A)
    (h1 : (TauCeti.FiniteTypeCommHopfAlgCat.pointsMulEquiv A T S y).1 = 1)
    (h2 : TauCeti.HopfAlgebra.IsCentralPoint
      (TauCeti.FiniteTypeCommHopfAlgCat.pointsMulEquiv A T S y).2) :
    TauCeti.HopfAlgebra.IsCentralPoint y := by
  rw [TauCeti.HopfAlgebra.isCentralPoint_def]
  intro B _ _ φ x
  rw [commute_iff_eq]
  let Bc : CommAlgCat.{u} k := CommAlgCat.of k B
  let PB := TauCeti.FiniteTypeCommHopfAlgCat.pointsMulEquiv (R := k) (A := Bc) T S
  apply PB.injective
  simp only [PB, map_mul,
    TauCeti.FiniteTypeCommHopfAlgCat.pointsMulEquiv_mapValue (R := k)
      (A := A) (B := Bc) T S φ y,
    h1, map_one]
  apply Prod.ext
  · simp
  · exact (((TauCeti.HopfAlgebra.isCentralPoint_def _).1 h2) φ (PB x).2).eq

theorem isCentralIsogeny_lTensor
    (T D S : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (q : D.obj ⟶ S.obj) (hq : TauCeti.CommHopfAlgCat.IsCentralIsogeny q) :
    TauCeti.CommHopfAlgCat.IsCentralIsogeny
      (_root_.CommHopfAlgCat.ofHom (q.hom.lTensor T)) := by
  have hfin : (q.hom.lTensor T).toAlgHom.Finite := by
    change (Algebra.TensorProduct.map (AlgHom.id k T) q.hom.toAlgHom).Finite
    exact RingHom.Finite.tensorProductMap (f := AlgHom.id k T)
      (RingEquiv.refl T).finite hq.finite
  have hflat : (q.hom.lTensor T).toAlgHom.toRingHom.FaithfullyFlat := by
    change (Algebra.TensorProduct.lTensor T q.hom.toAlgHom).toRingHom.FaithfullyFlat
    exact RingHom.FaithfullyFlat.lTensor T hq.faithfullyFlat
  let Tft := TauCeti.FiniteTypeCommHopfAlgCat.tensorProduct T D
  let Sft := TauCeti.FiniteTypeCommHopfAlgCat.tensorProduct T S
  let F : Tft.obj ⟶ Sft.obj := _root_.CommHopfAlgCat.ofHom (q.hom.lTensor T)
  have hcentral : (TauCeti.CommHopfAlgCat.kernelHopfIdeal F).IsCentral := by
    apply (TauCeti.CommHopfAlgCat.isCentral_iff_forall_isCentralPoint _ _).2
    intro A y hy
    let P_D := TauCeti.FiniteTypeCommHopfAlgCat.pointsMulEquiv (R := k) (A := A) T D
    let P_S := TauCeti.FiniteTypeCommHopfAlgCat.pointsMulEquiv (R := k) (A := A) T S
    have hy1 : TauCeti.AlgHom.mapDomain (q.hom.lTensor T) y = 1 :=
      (TauCeti.CommHopfAlgCat.mapPointsFunctor_app_eq_one_iff F A y).2 hy
    have hpair := pointsMulEquiv_mapDomain_lTensor T D S q A y
    have hfirst : (P_S y).1 = 1 := by
      have h := congrArg (fun w => (P_D w).1) hy1
      rw [hpair, map_one] at h
      simpa [P_S] using h
    have hsecond : TauCeti.AlgHom.mapDomain q.hom (P_S y).2 = 1 := by
      have h := congrArg (fun w => (P_D w).2) hy1
      rw [hpair, map_one] at h
      simpa [P_S] using h
    have hc : TauCeti.HopfAlgebra.IsCentralPoint (P_S y).2 :=
      TauCeti.CommHopfAlgCat.isCentralPoint_of_mem_quotientPointsSubgroup S.obj
        (TauCeti.CommHopfAlgCat.kernelHopfIdeal q) hq.isCentral_kernelHopfIdeal A
        ((TauCeti.CommHopfAlgCat.mapPointsFunctor_app_eq_one_iff q A (P_S y).2).1 hsecond)
    simpa [Sft, P_S] using isCentralPoint_of_fst_one T S y hfirst hc
  exact (TauCeti.CommHopfAlgCat.isCentralIsogeny_iff F).2 ⟨hfin, hflat, hcentral⟩

theorem lTensor_comp_map_of_equivariant
    (T D S : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (q : D.obj ⟶ S.obj) (τ : T →ₐc[k] T)
    (α : D →ₐc[k] D) (β : S →ₐc[k] S)
    (h : q.hom.comp α = β.comp q.hom) :
    (q.hom.lTensor T).comp (Bialgebra.TensorProduct.map τ α) =
      (Bialgebra.TensorProduct.map τ β).comp (q.hom.lTensor T) := by
  apply BialgHom.ext
  intro z
  change (q.hom.lTensor T) (Bialgebra.TensorProduct.map τ α z) =
    Bialgebra.TensorProduct.map τ β ((q.hom.lTensor T) z)
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    change (Bialgebra.TensorProduct.map (BialgHom.id k T) q.hom)
        (Bialgebra.TensorProduct.map τ α (a ⊗ₜ[k] b)) =
      Bialgebra.TensorProduct.map τ β
        (Bialgebra.TensorProduct.map (BialgHom.id k T) q.hom (a ⊗ₜ[k] b))
    rw [Bialgebra.TensorProduct.map_tmul, Bialgebra.TensorProduct.map_tmul,
      Bialgebra.TensorProduct.map_tmul, Bialgebra.TensorProduct.map_tmul,
      BialgHom.id_apply, BialgHom.id_apply]
    exact congrArg (fun d => τ a ⊗ₜ[k] d) (congrArg (fun f : D →ₐc[k] S => f b) h)
  | add a b ha hb => simp only [map_add, ha, hb]

end CFSG.LieType.AlgebraicGroups
