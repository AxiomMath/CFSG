module

public import CFSG.LieType.AlgebraicGroups.CanonicalReductiveFactors
public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Parabolic
public import TauCeti.Algebra.AlgebraicGroup.Derived.PointClosure

public noncomputable section

open WithConv
open TauCeti
open TauCeti.Cocharacter
open scoped commutatorElement

namespace CFSG.LieType.AlgebraicGroups.CanonicalReductive

universe u

variable {k : Type u} [Field k]

noncomputable def evalPoint (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (t : k) :
    WithConv (M →ₐ[k] Polynomial k) →* WithConv (M →ₐ[k] k) :=
  AlgHom.mapValue ((Polynomial.aeval t).restrictScalars k)

section Helpers

theorem aeval_eq_eval (t : k) (p : Polynomial k) :
    Polynomial.aeval t p = p.eval t := by
  rw [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id]

theorem aeval_restrictScalars_apply (t : k) (p : Polynomial k) :
    (Polynomial.aeval t).restrictScalars k p = p.eval t := by
  rw [AlgHom.coe_restrictScalars']
  exact aeval_eq_eval t p

theorem evalPoint_ofConv_apply
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (t : k)
    (F : WithConv (M →ₐ[k] Polynomial k)) (x : M) :
    (evalPoint M t F).ofConv x = (F.ofConv x).eval t := by
  rw [evalPoint, AlgHom.mapValue_apply, WithConv.ofConv_toConv, AlgHom.comp_apply]
  exact aeval_restrictScalars_apply t (F.ofConv x)

theorem evalPoint_zero
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (F : WithConv (M →ₐ[k] Polynomial k)) :
    evalPoint M 0 F = evalZeroPoint k F := by
  rw [evalPoint, evalZeroPoint_apply, AlgHom.mapValue_apply]

theorem evalPoint_constPolyPoint
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (t : k)
    (g : WithConv (M →ₐ[k] k)) :
    evalPoint M t (constPolyPoint k g) = g := by
  rw [evalPoint, constPolyPoint_apply, AlgHom.mapValue_apply, WithConv.ofConv_toConv,
    ← AlgHom.comp_assoc, ← AlgHom.mapValue_apply]
  have h : ((Polynomial.aeval t).restrictScalars k).comp
      (IsScalarTower.toAlgHom k k (Polynomial k)) = AlgHom.id k k := by
    apply AlgHom.ext
    intro a
    simp [AlgHom.coe_restrictScalars']
  rw [h, AlgHom.mapValue_id, MonoidHom.id_apply]

theorem point_comp_toLaurent (t : kˣ) :
    (MultiplicativeGroup.point (R := k) t).comp
        (Polynomial.toLaurentAlg.restrictScalars k) =
      (Polynomial.aeval (t : k)).restrictScalars k := by
  apply Polynomial.algHom_ext
  simp [MultiplicativeGroup.point, AlgHom.coe_restrictScalars']

theorem map_genericUnit_point (t : kˣ) :
    Units.map (MultiplicativeGroup.point (R := k) t).toMonoidHom
        (MultiplicativeGroup.genericUnit k) = t := by
  apply Units.ext
  rw [Units.coe_map, MultiplicativeGroup.genericUnit_val]
  change (MultiplicativeGroup.point (R := k) t) (LaurentPolynomial.T 1) = (t : k)
  rw [MultiplicativeGroup.point_T]
  simp

theorem mapValue_point_ofPolyPoint
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (t : kˣ)
    (F : WithConv (M →ₐ[k] Polynomial k)) :
    AlgHom.mapValue (MultiplicativeGroup.point (R := k) t) (ofPolyPoint k F) =
      evalPoint M (t : k) F := by
  rw [ofPolyPoint_apply, AlgHom.mapValue_apply, WithConv.ofConv_toConv, ← AlgHom.comp_assoc,
    ← AlgHom.mapValue_apply, point_comp_toLaurent, evalPoint]

theorem mapValue_point_conjugate
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (l : M →ₐc[k] LaurentPolynomial k) (t : kˣ) (g : WithConv (M →ₐ[k] k)) :
    AlgHom.mapValue (MultiplicativeGroup.point (R := k) t) (conjugate k l g) =
      pointsHom k l t * g * (pointsHom k l t)⁻¹ := by
  have h : (MultiplicativeGroup.point (R := k) t).comp
      (IsScalarTower.toAlgHom k k (LaurentPolynomial k)) = AlgHom.id k k := by
    apply AlgHom.ext
    intro a
    simp
  rw [mapValue_conjugate (A := k) (C := k), map_genericUnit_point, h, AlgHom.mapValue_id,
    MonoidHom.id_apply]

variable [IsAlgClosed k]

theorem polynomial_eq_zero_of_eval_eq_zero_of_ne (p : Polynomial k)
    (h : ∀ t : k, t ≠ 0 → p.eval t = 0) : p = 0 := by
  have hX : p * Polynomial.X = 0 := by
    apply Polynomial.zero_of_eval_zero
    intro t
    rcases eq_or_ne t 0 with rfl | ht
    · simp
    · rw [Polynomial.eval_mul_X, h t ht, zero_mul]
  simpa using Polynomial.mul_X_pow_eq_zero (p := p) (n := 1) (by simpa using hX)

theorem inv_ofConv_eq_zero_of_mem_unipotent
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) [IsReduced M]
    (l : M →ₐc[k] LaurentPolynomial k) {u : WithConv (M →ₐ[k] k)}
    (hu : u ∈ TauCeti.Cocharacter.unipotent k l)
    {x : M} (hx : x ∈ TauCeti.CommHopfAlgCat.derivedDefiningIdeal (R := k) M) :
    u⁻¹.ofConv x = 0 := by
  obtain ⟨huP, hlim⟩ := mem_unipotent_iff.mp hu
  let F : WithConv (M →ₐ[k] Polynomial k) := extend k l ⟨u, huP⟩
  have hF : ofPolyPoint k F = conjugate k l u := ofPolyPoint_extend (g := ⟨u, huP⟩)
  let G : WithConv (M →ₐ[k] Polynomial k) := F * constPolyPoint k u⁻¹
  have hcomm : ∀ t : kˣ, evalPoint M (t : k) G = ⁅pointsHom k l t, u⁆ := by
    intro t
    have h1 : evalPoint M (t : k) F = pointsHom k l t * u * (pointsHom k l t)⁻¹ := by
      rw [← mapValue_point_ofPolyPoint M t F, hF]
      exact mapValue_point_conjugate M l t u
    have h2 : evalPoint M (t : k) (constPolyPoint k u⁻¹) = u⁻¹ :=
      evalPoint_constPolyPoint M (t : k) u⁻¹
    dsimp only [G]
    rw [map_mul, h1, h2, commutatorElement_def]
  have hvan : ∀ t : k, t ≠ 0 → (G.ofConv x).eval t = 0 := by
    intro t ht
    have hmem : ⁅pointsHom k l (Units.mk0 t ht), u⁆ ∈ commutator (WithConv (M →ₐ[k] k)) :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    have hz :=
      (TauCeti.CommHopfAlgCat.mem_derivedDefiningIdeal_iff_forall_commutator_apply_eq_zero
        (k := k) (H := M) x).mp hx ⟨_, hmem⟩
    rw [← evalPoint_ofConv_apply, ← Units.val_mk0 ht, hcomm (Units.mk0 t ht)]
    exact hz
  have hp : G.ofConv x = 0 := polynomial_eq_zero_of_eval_eq_zero_of_ne (G.ofConv x) hvan
  have hzero : evalPoint M 0 G = u⁻¹ := by
    dsimp only [G]
    rw [map_mul]
    have hF0 : evalPoint M 0 F = 1 := by
      rw [evalPoint_zero]
      rw [show evalZeroPoint k F = limit k l ⟨u, huP⟩ from
        (limit_apply (A := k) (l := l) (g := ⟨u, huP⟩)).symm]
      exact hlim
    rw [hF0, evalPoint_constPolyPoint, one_mul]
  calc u⁻¹.ofConv x = (evalPoint M 0 G).ofConv x := by rw [hzero]
    _ = (G.ofConv x).eval 0 := evalPoint_ofConv_apply M 0 G x
    _ = 0 := by rw [hp]; simp

end Helpers

variable [IsAlgClosed k]

theorem forall_derivedDefiningIdeal_apply_eq_zero_of_mem_unipotent
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) [IsReduced M]
    (l : M →ₐc[k] LaurentPolynomial k) {g : WithConv (M →ₐ[k] k)}
    (hg : g ∈ TauCeti.Cocharacter.unipotent k l) :
    ∀ x ∈ TauCeti.CommHopfAlgCat.derivedDefiningIdeal (R := k) M.obj, g.ofConv x = 0 := by
  intro x hx
  have hg' : g⁻¹ ∈ TauCeti.Cocharacter.unipotent k l := inv_mem hg
  have h := inv_ofConv_eq_zero_of_mem_unipotent M l hg' hx
  rwa [inv_inv] at h

omit [IsAlgClosed k] in
theorem exists_derivedCoordinateMap_point_of_forall
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) {g : WithConv (M →ₐ[k] k)}
    (hg : ∀ x ∈ TauCeti.CommHopfAlgCat.derivedDefiningIdeal (R := k) M.obj, g.ofConv x = 0) :
    ∃ d : TauCeti.HopfAlgebra.points (R := k) (H := derivedCoordinate M) (CommAlgCat.of k k),
      TauCeti.AlgHom.mapDomain (derivedCoordinateMap M) d = g := by
  let I := TauCeti.CommHopfAlgCat.derivedDefiningIdeal (R := k) M
  have hI : ∀ a : M, a ∈ I.toIdeal → g.ofConv a = 0 :=
    fun a ha => hg a (TauCeti.HopfIdeal.mem_toIdeal.mp ha)
  let f : M ⧸ I.toIdeal →ₐ[k] k := Ideal.Quotient.liftₐ I.toIdeal g.ofConv hI
  refine ⟨toConv f, ?_⟩
  apply WithConv.ofConv_injective
  ext x
  rw [TauCeti.AlgHom.mapDomain_apply_apply]
  have hcomp := Ideal.Quotient.liftₐ_comp I.toIdeal g.ofConv hI
  rw [TauCeti.CommHopfAlgCat.mkQuotient_apply]
  exact AlgHom.congr_fun hcomp x

theorem exists_derivedCoordinateMap_point_of_mem_unipotent
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) [IsReduced M]
    (l : M →ₐc[k] LaurentPolynomial k) {g : WithConv (M →ₐ[k] k)}
    (hg : g ∈ TauCeti.Cocharacter.unipotent k l) :
    ∃ d : TauCeti.HopfAlgebra.points (R := k) (H := derivedCoordinate M) (CommAlgCat.of k k),
      TauCeti.AlgHom.mapDomain (derivedCoordinateMap M) d = g :=
  exists_derivedCoordinateMap_point_of_forall M
    (forall_derivedDefiningIdeal_apply_eq_zero_of_mem_unipotent M l hg)

end CFSG.LieType.AlgebraicGroups.CanonicalReductive
