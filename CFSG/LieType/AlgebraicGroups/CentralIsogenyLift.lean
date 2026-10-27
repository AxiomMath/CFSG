module
public import TauCeti.RingTheory.FiniteType.FiniteRange
public import TauCeti.LinearAlgebra.TensorProduct.Separation
public import TauCeti.Algebra.AlgebraicGroup.Isogeny.Basic
public import CFSG.LieType.AlgebraicGroups.FixedComponentNorm
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.BaseChange

public noncomputable section
open CategoryTheory WithConv
open scoped TensorProduct
namespace CFSG.LieType.AlgebraicGroups
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

theorem bialgHom_eq_of_comp_eq_of_isogeny
    (D S X : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (q : D.obj ⟶ S.obj) (hq : TauCeti.CommHopfAlgCat.IsIsogeny q)
    [IsReduced X] [ConnectedSpace (PrimeSpectrum X)]
    (f g : S →ₐc[k] X) (hfg : f.comp q.hom = g.comp q.hom) : f = g := by
  let δ : S →ₐ[k] X := ((toConv f.toAlgHom)⁻¹ * toConv g.toAlgHom).ofConv
  have hδq : δ.comp q.hom.toAlgHom = (Algebra.ofId k X).comp (Bialgebra.counitAlgHom k D) := by
    have hmaps : TauCeti.AlgHom.mapDomain q.hom (toConv f.toAlgHom) =
        TauCeti.AlgHom.mapDomain q.hom (toConv g.toAlgHom) := by
      apply WithConv.ofConv_injective
      exact congrArg BialgHom.toAlgHom hfg
    have h := map_mul (TauCeti.AlgHom.mapDomain q.hom)
      (toConv f.toAlgHom)⁻¹ (toConv g.toAlgHom)
    rw [map_inv, hmaps, inv_mul_cancel] at h
    exact congrArg ofConv h
  have hkill : (TauCeti.CommHopfAlgCat.kernelHopfIdeal q).toIdeal ≤
      RingHom.ker δ.toRingHom :=
    (TauCeti.CommHopfAlgCat.kernelHopfIdeal_toIdeal_le_ker_iff q δ).2 hδq
  let K := TauCeti.CommHopfAlgCat.quotient S.obj (TauCeti.CommHopfAlgCat.kernelHopfIdeal q)
  let δK : K →ₐ[k] X := Ideal.Quotient.liftₐ _ δ (fun _ h => hkill h)
  let : Module.Finite k K := TauCeti.CommHopfAlgCat.moduleFinite_quotient_kernelHopfIdeal hq.finite
  have hδ : ∀ a, δ a = algebraMap k X (Bialgebra.counitAlgHom k X (δ a)) := by
    intro a
    classical
    apply TauCeti.eq_algebraMap_of_finite_range_eval (δ a) ?_ (Bialgebra.counitAlgHom k X)
    apply (Set.finite_range fun x : K →ₐ[k] k => x (Ideal.Quotient.mk _ a)).subset
    rintro _ ⟨x, rfl⟩
    exact ⟨x.comp δK, rfl⟩
  have hc : ∀ a, Bialgebra.counitAlgHom k X (δ a) = Bialgebra.counitAlgHom k S a := by
    have hf : TauCeti.AlgHom.mapValue (Bialgebra.counitAlgHom k X) (toConv f.toAlgHom) =
        (1 : WithConv (S →ₐ[k] k)) := by
      rw [TauCeti.AlgHom.mapValue_apply]
      apply WithConv.ofConv_injective
      exact BialgHom.counitAlgHom_comp f
    have hg : TauCeti.AlgHom.mapValue (Bialgebra.counitAlgHom k X) (toConv g.toAlgHom) =
        (1 : WithConv (S →ₐ[k] k)) := by
      rw [TauCeti.AlgHom.mapValue_apply]
      apply WithConv.ofConv_injective
      exact BialgHom.counitAlgHom_comp g
    have h := map_mul (TauCeti.AlgHom.mapValue (Bialgebra.counitAlgHom k X))
      (toConv f.toAlgHom)⁻¹ (toConv g.toAlgHom)
    rw [map_inv, hf, hg, inv_one, one_mul] at h
    rw [TauCeti.AlgHom.mapValue_apply] at h
    exact fun a => AlgHom.congr_fun (congrArg ofConv h) a
  have hδone : toConv δ = 1 := by
    apply WithConv.ofConv_injective
    ext a
    change δ a = algebraMap k X (Bialgebra.counitAlgHom k S a)
    exact (hδ a).trans (congrArg (algebraMap k X) (hc a))
  apply BialgHom.ext
  intro a
  have h := inv_mul_eq_one.mp hδone
  exact AlgHom.congr_fun (congrArg ofConv h) a

omit [IsAlgClosed k] in
theorem isCentralPoint_of_commute_of_separating
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) {ι : Type*}
    (p : ι → TauCeti.HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k))
    (hsep : ∀ a : H, (∀ i, (p i).ofConv a = 0) → a = 0)
    {A : CommAlgCat.{u} k}
    (z : TauCeti.HopfAlgebra.points (R := k) (H := H) A)
    (hz : ∀ i, Commute z (TauCeti.AlgHom.mapValue (Algebra.ofId k A) (p i))) :
    TauCeti.HopfAlgebra.IsCentralPoint z := by
  let l : H →ₐ[k] H ⊗[k] A := Algebra.TensorProduct.includeLeft
  let r : A →ₐ[k] H ⊗[k] A := Algebra.TensorProduct.includeRight
  let x : WithConv (H →ₐ[k] H ⊗[k] A) := toConv l
  let s : WithConv (H →ₐ[k] H ⊗[k] A) := TauCeti.AlgHom.mapValue r z
  have hsx : Commute s x := by
    rw [commute_iff_eq]
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro a
    rw [← sub_eq_zero]
    apply TauCeti.tensor_eq_zero_of_forall_lid_rTensor_eq_zero
      (fun i => (p i).ofConv.toLinearMap) hsep
    intro i
    let e : H ⊗[k] A →ₐ[k] A :=
      Algebra.TensorProduct.productMap ((Algebra.ofId k A).comp (p i).ofConv) (AlgHom.id k A)
    have he : ∀ v : H ⊗[k] A,
        TensorProduct.lid k A ((p i).ofConv.toLinearMap.rTensor A v) = e v := by
      intro v
      induction v using TensorProduct.inductionOn with
      | tmul h a => simp [e, Algebra.smul_def]
      | add v w hv hw => simp only [map_add, hv, hw]
    rw [he, map_sub, sub_eq_zero]
    have he_s : TauCeti.AlgHom.mapValue e s = z := by
      rw [TauCeti.AlgHom.mapValue_apply]
      apply WithConv.ofConv_injective
      apply AlgHom.ext
      intro b
      simp [s, r, e, TauCeti.AlgHom.mapValue_apply]
    have he_x : TauCeti.AlgHom.mapValue e x =
        TauCeti.AlgHom.mapValue (Algebra.ofId k A) (p i) := by
      rw [TauCeti.AlgHom.mapValue_apply, TauCeti.AlgHom.mapValue_apply]
      apply WithConv.ofConv_injective
      apply AlgHom.ext
      intro b
      simp [x, l, e, Algebra.TensorProduct.productMap_left]
    have h := (hz i).eq
    have h1 := map_mul (TauCeti.AlgHom.mapValue e) s x
    have h2 := map_mul (TauCeti.AlgHom.mapValue e) x s
    rw [he_s, he_x] at h1 h2
    have hm : TauCeti.AlgHom.mapValue e (s * x) =
        TauCeti.AlgHom.mapValue e (x * s) := h1.trans (h.trans h2.symm)
    have hma := AlgHom.congr_fun (congrArg ofConv hm) a
    simpa only [TauCeti.AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply] using hma
  rw [TauCeti.HopfAlgebra.isCentralPoint_def]
  intro B _ _ φ y
  let e : H ⊗[k] A →ₐ[k] B := Algebra.TensorProduct.productMap y.ofConv φ
  have hs : TauCeti.AlgHom.mapValue e s = TauCeti.AlgHom.mapValue φ z := by
    rw [TauCeti.AlgHom.mapValue_apply, TauCeti.AlgHom.mapValue_apply]
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro b
    simp [s, r, e, TauCeti.AlgHom.mapValue_apply]
  have hx : TauCeti.AlgHom.mapValue e x = y := by
    rw [TauCeti.AlgHom.mapValue_apply]
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro b
    simp [x, l, e, Algebra.TensorProduct.productMap_left]
  simpa only [hs, hx] using hsx.map (TauCeti.AlgHom.mapValue e)


theorem isCentralPoint_of_commute_base_points
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) [IsReduced H]
    {A : CommAlgCat.{u} k}
    (z : TauCeti.HopfAlgebra.points (R := k) (H := H) A)
    (hz : ∀ p : TauCeti.HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k),
      Commute z (TauCeti.AlgHom.mapValue (Algebra.ofId k A) p)) :
    TauCeti.HopfAlgebra.IsCentralPoint z := by
  apply isCentralPoint_of_commute_of_separating H (fun p => p) _ z hz
  intro a ha
  apply TauCeti.eq_of_forall_algHom_apply_eq (k := k) (K := k)
  intro p
  exact (ha (toConv p)).trans (map_zero _).symm

omit [IsAlgClosed k] in
theorem isCentralPoint_of_mapDomain_of_isCentralIsogeny_of_separating_commutator
    (D S : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (q : D.obj ⟶ S.obj) (hq : TauCeti.CommHopfAlgCat.IsCentralIsogeny q)
    (hsep : ∀ a : S, (∀ p : commutator
      (TauCeti.HopfAlgebra.points (R := k) (H := S) (CommAlgCat.of k k)), p.val.ofConv a = 0) → a = 0)
    {A : CommAlgCat.{u} k}
    (z : TauCeti.HopfAlgebra.points (R := k) (H := S) A)
    (hz : TauCeti.HopfAlgebra.IsCentralPoint (TauCeti.AlgHom.mapDomain q.hom z)) :
    TauCeti.HopfAlgebra.IsCentralPoint z := by
  let P := TauCeti.AlgHom.mapValue (H := S) (Algebra.ofId k A)
  let Q := TauCeti.AlgHom.mapDomain (A := A) q.hom
  have hQker : Q.ker ≤ Subgroup.center
      (TauCeti.HopfAlgebra.points (R := k) (H := S) A) := by
    have hker := TauCeti.CommHopfAlgCat.quotientPointsSubgroup_kernelHopfIdeal_eq_ker_mapPointsFunctor
      q A
    change TauCeti.CommHopfAlgCat.quotientPointsSubgroup S.obj
        (TauCeti.CommHopfAlgCat.kernelHopfIdeal q) A = Q.ker at hker
    rw [← hker]
    exact (TauCeti.CommHopfAlgCat.quotientPointsSubgroup_le_center S.obj _
      hq.isCentral_kernelHopfIdeal A).trans TauCeti.HopfAlgebra.center_le_center
  have hcentral : ∀ p : TauCeti.HopfAlgebra.points (R := k) (H := S) (CommAlgCat.of k k),
      z * P p * z⁻¹ * (P p)⁻¹ ∈ Subgroup.center
        (TauCeti.HopfAlgebra.points (R := k) (H := S) A) := by
    intro p
    apply hQker
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    have hc : Commute (Q z) (Q (P p)) := hz.commute (Q (P p))
    rw [hc.eq]
    group
  let δ : TauCeti.HopfAlgebra.points (R := k) (H := S) (CommAlgCat.of k k) →*
      Subgroup.center (TauCeti.HopfAlgebra.points (R := k) (H := S) A) :=
    { toFun := fun p => ⟨z * P p * z⁻¹ * (P p)⁻¹, hcentral p⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := by
        intro p t
        apply Subtype.ext
        change z * P (p * t) * z⁻¹ * (P (p * t))⁻¹ =
          (z * P p * z⁻¹ * (P p)⁻¹) * (z * P t * z⁻¹ * (P t)⁻¹)
        have hc := (Subgroup.mem_center_iff.mp (hcentral t)) (P p)⁻¹
        rw [map_mul, mul_inv_rev]
        calc
          z * (P p * P t) * z⁻¹ * ((P t)⁻¹ * (P p)⁻¹) =
              z * P p * z⁻¹ * (z * P t * z⁻¹ * (P t)⁻¹) * (P p)⁻¹ := by group
          _ = z * P p * z⁻¹ * ((P p)⁻¹ * (z * P t * z⁻¹ * (P t)⁻¹)) := by
            rw [mul_assoc, hc]
          _ = (z * P p * z⁻¹ * (P p)⁻¹) * (z * P t * z⁻¹ * (P t)⁻¹) := by group }
  apply isCentralPoint_of_commute_of_separating S (fun p : commutator
    (TauCeti.HopfAlgebra.points (R := k) (H := S) (CommAlgCat.of k k)) => p.val) hsep z
  intro p
  have hδ : δ p.val = 1 := (Abelianization.commutator_subset_ker δ) p.property
  have hd : z * P p.val * z⁻¹ * (P p.val)⁻¹ = 1 := congrArg Subtype.val hδ
  rw [commute_iff_eq]
  have h := congrArg (fun x => x * P p.val * z) hd
  simpa only [mul_assoc, inv_mul_cancel, mul_one, one_mul] using h

theorem comp_comm_of_lifts_of_isogeny
    (D S : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (q : D.obj ⟶ S.obj) (hq : TauCeti.CommHopfAlgCat.IsIsogeny q)
    [IsReduced S] [ConnectedSpace (PrimeSpectrum S)]
    (F σ : D →ₐc[k] D) (FS σS : S →ₐc[k] S)
    (hF : FS.comp q.hom = q.hom.comp F)
    (hσ : σS.comp q.hom = q.hom.comp σ)
    (hcomm : F.comp σ = σ.comp F) : FS.comp σS = σS.comp FS := by
  apply bialgHom_eq_of_comp_eq_of_isogeny D S S q hq
  calc
    (FS.comp σS).comp q.hom = FS.comp (σS.comp q.hom) := BialgHom.comp_assoc _ _ _
    _ = FS.comp (q.hom.comp σ) := by rw [hσ]
    _ = (FS.comp q.hom).comp σ := (BialgHom.comp_assoc _ _ _).symm
    _ = (q.hom.comp F).comp σ := by rw [hF]
    _ = q.hom.comp (F.comp σ) := BialgHom.comp_assoc _ _ _
    _ = q.hom.comp (σ.comp F) := by rw [hcomm]
    _ = (q.hom.comp σ).comp F := (BialgHom.comp_assoc _ _ _).symm
    _ = (σS.comp q.hom).comp F := by rw [hσ]
    _ = σS.comp (q.hom.comp F) := BialgHom.comp_assoc _ _ _
    _ = σS.comp (FS.comp q.hom) := by rw [hF]
    _ = (σS.comp FS).comp q.hom := (BialgHom.comp_assoc _ _ _).symm


theorem cube_eq_id_of_lift_of_isogeny
    (D S : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (q : D.obj ⟶ S.obj) (hq : TauCeti.CommHopfAlgCat.IsIsogeny q)
    [IsReduced S] [ConnectedSpace (PrimeSpectrum S)]
    (σD : D →ₐc[k] D) (σS : S →ₐc[k] S)
    (hD : (σD.comp σD).comp σD = BialgHom.id k D)
    (hσ : q.hom.comp σD = σS.comp q.hom) :
    (σS.comp σS).comp σS = BialgHom.id k S := by
  apply bialgHom_eq_of_comp_eq_of_isogeny D S S q hq
  calc
    ((σS.comp σS).comp σS).comp q.hom =
        σS.comp (σS.comp (σS.comp q.hom)) := by rw [BialgHom.comp_assoc, BialgHom.comp_assoc]
    _ = σS.comp (σS.comp (q.hom.comp σD)) := by rw [hσ]
    _ = σS.comp ((σS.comp q.hom).comp σD) := by rw [BialgHom.comp_assoc]
    _ = σS.comp ((q.hom.comp σD).comp σD) := by rw [hσ]
    _ = (σS.comp q.hom).comp (σD.comp σD) := by rw [BialgHom.comp_assoc, BialgHom.comp_assoc]
    _ = (q.hom.comp σD).comp (σD.comp σD) := by rw [hσ]
    _ = q.hom.comp ((σD.comp σD).comp σD) := by simp only [BialgHom.comp_assoc]
    _ = q.hom := by rw [hD, BialgHom.comp_id]
    _ = (BialgHom.id k S).comp q.hom := (BialgHom.id_comp _).symm

end CFSG.LieType.AlgebraicGroups
