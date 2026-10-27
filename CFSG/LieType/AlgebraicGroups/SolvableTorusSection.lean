module

public import CFSG.LieType.AlgebraicGroups.SolvableUnipotentKernel
public import CFSG.LieType.AlgebraicGroups.DiagonalCharacterDetector
public import CFSG.LieType.AlgebraicGroups.ClosedPointCentralizer
public import CFSG.LinearAlgebra.FiniteTriangularCentralizer
public import CFSG.LieType.AlgebraicGroups.TorusImageIdentityComponent
public import CFSG.LieType.AlgebraicGroups.NilpotentSemisimple
public import CFSG.LieType.AlgebraicGroups.SolvableAffineEmbedding
public import CFSG.LieType.AlgebraicGroups.SolvableDiagonalQuotient
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.DominantPoints

public noncomputable section

open CategoryTheory WithConv TauCeti
open scoped TensorProduct

namespace CFSG.LieType.AlgebraicGroups

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
theorem exists_faithful_triangular_point_representation
    (H : FiniteTypeCommHopfAlgCat.{u,u} k)
    {V : Type u} [AddCommGroup V] [Module k V] [Comodule k H V]
    {n : ℕ} (b : Module.Basis (Fin n) k V)
    (hupper : (Comodule.coefficientMatrix (C := H) b).IsUpperTriangular)
    (hfaith : Function.Surjective (Comodule.coordinateBialgHom (H := H) b)) :
    ∃ ρ : WithConv (H →ₐ[k] k) →* upperTriangularGroup (Fin n) k,
      Function.Injective ρ ∧ ∀ g i,
        (UpperTriangularGroup.diag (ρ g) i : k) =
          g.ofConv (Comodule.coefficientMatrix (C := H) b i i) := by
  let f := Comodule.coordinateBialgHom (H := H) b
  let ρGL := (GeneralLinear.pointsMulEquiv n).toMonoidHom.comp (AlgHom.mapDomain (A := k) f)
  have hmat (g : WithConv (H →ₐ[k] k)) :
      (ρGL g : Matrix (Fin n) (Fin n) k) =
        (Comodule.coefficientMatrix (C := H) b).map g.ofConv := by
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, AlgHom.mapDomain_apply]
    exact AlgHom.pointsMulEquiv_comp_coordinateBialgHom _ _
  have hmem (g : WithConv (H →ₐ[k] k)) : ρGL g ∈ upperTriangularGroup (Fin n) k := by
    rw [UpperTriangularGroup.mem_iff]
    rw [hmat]
    intro i j hji
    simp only [Matrix.map_apply, hupper hji, map_zero]
  let ρ := ρGL.codRestrict (upperTriangularGroup (Fin n) k) hmem
  have hi : Function.Injective (AlgHom.mapDomain (A := k) f) := by
    intro g h heq
    apply WithConv.ext
    apply AlgHom.ext
    intro x
    obtain ⟨a, rfl⟩ := hfaith x
    have h := congrArg (fun p => p.ofConv a) heq
    simpa only [AlgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_apply,
      BialgHom.coe_toAlgHom] using h
  have hρ : Function.Injective ρ := by
    intro g h heq
    apply hi
    apply (GeneralLinear.pointsMulEquiv n).injective
    exact congrArg Subtype.val heq
  refine ⟨ρ, hρ, fun g i => ?_⟩
  rw [UpperTriangularGroup.diag_apply_val]
  exact congrArg (fun M : Matrix (Fin n) (Fin n) k => M i i) (hmat g)

theorem exists_finite_lift_nilpotent_centralizer
    (H T : FiniteTypeCommHopfAlgCat.{u,u} k)
    (hT : torusCommHopfAlgProperty k T) (p : T →ₐc[k] H)
    (hps : Function.Surjective (AlgHom.mapDomain (A := k) p))
    (hker : ∀ g : WithConv (H →ₐ[k] k),
      AlgHom.mapDomain p g = 1 → HopfAlgebra.IsUnipotentPoint g)
    {V : Type u} [AddCommGroup V] [Module k V] [Comodule k H V]
    {n : ℕ} (b : Module.Basis (Fin n) k V)
    (hupper : (Comodule.coefficientMatrix (C := H) b).IsUpperTriangular)
    (hfaith : Function.Surjective (Comodule.coordinateBialgHom (H := H) b))
    (c : Fin n → _root_.GroupLike k T)
    (hc : ∀ i, p (c i) = Comodule.coefficientMatrix (C := H) b i i) :
    ∃ L : Subgroup (WithConv (H →ₐ[k] k)), Finite L ∧
      Group.IsNilpotent (Subgroup.centralizer (L : Set (WithConv (H →ₐ[k] k)))) ∧
      Subgroup.map (AlgHom.mapDomain (A := k) p)
        (Subgroup.centralizer (L : Set (WithConv (H →ₐ[k] k)))) = ⊤ := by
  obtain ⟨l, hl, hlk⟩ : ∃ l : ℕ, l.Prime ∧ (l : k) ≠ 0 := by
    by_cases h2 : (2 : k) ≠ 0
    · exact ⟨2, Nat.prime_two, h2⟩
    · refine ⟨3, Nat.prime_three, ?_⟩
      have h3 : ((3 : ℕ) : k) = 1 := by
        have hh2 : (2 : k) = 0 := not_ne_iff.mp h2
        calc
          ((3 : ℕ) : k) = (2 : k) + 1 := by norm_num
          _ = 1 := by rw [hh2, zero_add]
      rw [h3]
      exact one_ne_zero
  obtain ⟨e, F, he, hF, hcard, hmem, hdet⟩ :=
    exists_finite_diagonal_character_detector T hT c hl hlk
  let : Finite F := hF
  obtain ⟨s, L, hs, hsinj, hL, hfinite, hmap⟩ :=
    exists_finite_torus_lift_centralizer_surjective H T hT p hps hker F hcard
  let : Coalgebra.IsCocomm k T := hT.isCocomm k T
  let : CommGroup (WithConv (T →ₐ[k] k)) := inferInstance
  obtain ⟨ρ, hρ, hρdiag⟩ := exists_faithful_triangular_point_representation H b hupper hfaith
  let δ : WithConv (T →ₐ[k] k) →* (Fin n → kˣ) := diagonalCharacterHom T c
  have hcompat (g : WithConv (H →ₐ[k] k)) :
      UpperTriangularGroup.diag (ρ g) = δ (AlgHom.mapDomain (A := k) p g) := by
    funext i
    apply Units.ext
    rw [hρdiag]
    have hd := diagonalCharacterHom_apply_val T c (AlgHom.mapDomain (A := k) p g) i
    change (δ (AlgHom.mapDomain (A := k) p g) i : k) = _ at hd
    rw [hd]
    change g.ofConv (Comodule.coefficientMatrix (C := H) b i i) = g.ofConv (p (c i))
    rw [hc]
  have hnil : Group.IsNilpotent (Subgroup.centralizer (s.range : Set (WithConv (H →ₐ[k] k)))) := by
    apply CFSG.LinearAlgebra.centralizer_nilpotent_of_finite_triangular_detector
      (k := k) (E := WithConv (H →ₐ[k] k)) (A := WithConv (T →ₐ[k] k))
      ρ hρ (AlgHom.mapDomain (A := k) p) δ hcompat F hcard s hs
    intro M h t
    have hM : ∀ t ∈ F, Matrix.diagonal (fun i => t.ofConv (c i)) * M =
        M * Matrix.diagonal (fun i => t.ofConv (c i)) := by
      intro t ht
      simpa only [δ, diagonalCharacterHom_apply_val] using h ⟨t, ht⟩
    simpa only [δ, diagonalCharacterHom_apply_val] using (hdet M).mp hM t
  exact ⟨L, hfinite, hL.symm ▸ hnil, hmap⟩

theorem exists_connected_nilpotent_cover_of_diagonal_quotient
    (H T : FiniteTypeCommHopfAlgCat.{u,u} k)
    (hT : torusCommHopfAlgProperty k T) (p : T →ₐc[k] H)
    (hps : Function.Surjective (AlgHom.mapDomain (A := k) p))
    (hker : ∀ g : WithConv (H →ₐ[k] k),
      AlgHom.mapDomain p g = 1 → HopfAlgebra.IsUnipotentPoint g)
    {V : Type u} [AddCommGroup V] [Module k V] [Comodule k H V]
    {n : ℕ} (b : Module.Basis (Fin n) k V)
    (hupper : (Comodule.coefficientMatrix (C := H) b).IsUpperTriangular)
    (hfaith : Function.Surjective (Comodule.coordinateBialgHom (H := H) b))
    (c : Fin n → _root_.GroupLike k T)
    (hc : ∀ i, p (c i) = Comodule.coefficientMatrix (C := H) b i i) :
    ∃ (P : FiniteTypeCommHopfAlgCat.{u,u} k) (a : H →ₐc[k] P),
      Function.Surjective a ∧ IsReduced P ∧ ConnectedSpace (PrimeSpectrum P) ∧
      Group.IsNilpotent (WithConv (P →ₐ[k] k)) ∧
      Function.Surjective (AlgHom.mapDomain (A := k) (a.comp p)) := by
  obtain ⟨L, hfinite, hnil, hmap⟩ :=
    exists_finite_lift_nilpotent_centralizer H T hT p hps hker b hupper hfaith c hc
  let C := Subgroup.centralizer (L : Set (WithConv (H →ₐ[k] k)))
  let I := HopfIdeal.vanishingIdeal C
  let Q := FiniteTypeCommHopfAlgCat.quotient H I
  let q : H →ₐc[k] Q := (CommHopfAlgCat.mkQuotient H.obj I).hom
  have hq : Function.Surjective q := CommHopfAlgCat.mkQuotient_surjective H.obj I
  have hCQ : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k) = C :=
    quotientPointsSubgroup_vanishingIdeal_centralizer H L
  let e₀ := CommHopfAlgCat.quotientPointsSubgroupIso H.obj I (CommAlgCat.of k k)
  let e : WithConv (Q →ₐ[k] k) ≃* C :=
    (MulEquiv.ofBijective e₀.hom.hom
      (ConcreteCategory.bijective_of_isIso e₀.hom)).trans (MulEquiv.subgroupCongr hCQ)
  let : Group.IsNilpotent C := hnil
  let : Group.IsNilpotent (WithConv (Q →ₐ[k] k)) := (Group.isNilpotent_congr e).mpr inferInstance
  have hQsur : Function.Surjective (AlgHom.mapDomain (A := k) (q.comp p)) := by
    intro t
    have ht : t ∈ C.map (AlgHom.mapDomain (A := k) p) := by
      rw [hmap]
      exact Subgroup.mem_top t
    obtain ⟨g, hgC, hgt⟩ := Subgroup.mem_map.mp ht
    have hgI : g ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k) :=
      hCQ.symm ▸ hgC
    let u := CommHopfAlgCat.liftQuotientPoint H.obj I (CommAlgCat.of k k) g
      ((CommHopfAlgCat.mem_quotientPointsSubgroup_iff H.obj I (CommAlgCat.of k k) g).mp hgI)
    have hqu : AlgHom.mapDomain q u = g := by
      rw [AlgHom.mapDomain_apply]
      change CommHopfAlgCat.quotientPointsHom H.obj I (CommAlgCat.of k k) u = g
      exact CommHopfAlgCat.quotientPointsHom_liftQuotientPoint _ _ _ _ _
    refine ⟨u, ?_⟩
    change AlgHom.mapDomain p (AlgHom.mapDomain q u) = t
    rw [hqu]
    exact hgt
  let : IsReduced Q := inferInstanceAs (IsReduced (CommHopfAlgCat.quotient H.obj I))
  let : Algebra.Smooth k Q := (smoothCommHopfAlgProperty_iff Q.obj).mp
    (smoothCommHopfAlgProperty_of_isAlgClosed_of_isReduced k Q.obj)
  let P := FiniteTypeCommHopfAlgCat.identityComponent Q
  let q₀ : Q →ₐc[k] P := (FiniteTypeCommHopfAlgCat.mkQuotient Q
    (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := Q))).hom.hom
  have hq₀ : Function.Surjective q₀ := CommHopfAlgCat.mkQuotient_surjective _ _
  let : Algebra.Smooth k P := FiniteTypeCommHopfAlgCat.smooth_identityComponent Q
  let : IsReduced P := TauCeti.isReduced_of_smooth k P
  let : ConnectedSpace (PrimeSpectrum P) :=
    FiniteTypeCommHopfAlgCat.connectedSpace_identityComponent Q
  have hq₀i : Function.Injective (AlgHom.mapDomain (A := k) q₀) := by
    intro g h heq
    apply WithConv.ext
    apply AlgHom.ext
    intro x
    obtain ⟨a, rfl⟩ := hq₀ x
    have h := congrArg (fun t => t.ofConv a) heq
    simpa only [AlgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_apply,
      BialgHom.coe_toAlgHom] using h
  have hnilP : Group.IsNilpotent (WithConv (P →ₐ[k] k)) := by
    apply Subgroup.isNilpotent_of_ker_le_center (AlgHom.mapDomain (A := k) q₀)
    intro g hg
    have hg1 : g = 1 := hq₀i ((MonoidHom.mem_ker.mp hg).trans (map_one _).symm)
    rw [hg1]
    exact Subgroup.one_mem _
  have hpsP : Function.Surjective (AlgHom.mapDomain (A := k) ((q₀.comp q).comp p)) := by
    simpa only [BialgHom.comp_assoc] using
      surjective_identityComponent_of_surjective_torus Q T hT (q.comp p) hQsur
  exact ⟨P, q₀.comp q, hq₀.comp hq, inferInstance, inferInstance, hnilP, hpsP⟩

theorem exists_torus_section_of_nilpotent_cover
    (H P T : FiniteTypeCommHopfAlgCat.{u,u} k) [IsReduced P]
    [ConnectedSpace (PrimeSpectrum P)]
    [Group.IsNilpotent (WithConv (P →ₐ[k] k))]
    (hT : torusCommHopfAlgProperty k T) (p : T →ₐc[k] H)
    (a : H →ₐc[k] P)
    (hsur : Function.Surjective (AlgHom.mapDomain (A := k) (a.comp p)))
    (hrestrict : ∀ (Q : FiniteTypeCommHopfAlgCat.{u,u} k), torusCommHopfAlgProperty k Q →
      ∀ q : P →ₐc[k] Q, Function.Surjective q → Function.Surjective (q.comp (a.comp p))) :
    ∃ j : H →ₐc[k] T, j.comp p = BialgHom.id k T := by
  have hc : geometricallyConnectedCommHopfAlgProperty k P.obj :=
    (geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace k P.obj).mpr inferInstance
  have hcentral : ∀ g x : WithConv (P →ₐ[k] k),
      Commute (HopfAlgebra.Point.semisimplePart k P k g) x := by
    intro g x
    exact NilpotentSemisimple.commute_semisimplePoint_of_nilpotent P hc _
      ((HopfAlgebra.isSemisimplePoint_def _).mpr
        (HopfAlgebra.Point.isSemisimple_pointsAction_semisimplePart k P k g)) x
  let hr := CFSG.ThirdParty.TauCeti.CentralJordan.exists_mem_groupLikeSetSpan_forall_apply_eq hcentral
  let hm := CFSG.ThirdParty.TauCeti.CentralJordan.semisimplePart_mul_of_central_parts hcentral
  let σ : P →ₐc[k] P := CFSG.ThirdParty.TauCeti.RegularJordan.semisimplePartBialgHom hr hm
  let F := _root_.CommHopfAlgCat.ofHom σ
  let Q := FiniteTypeCommHopfAlgCat.of k (CommHopfAlgCat.image F)
  let q : P →ₐc[k] Q := (CommHopfAlgCat.mkImage F).hom
  let i : Q →ₐc[k] P := (CommHopfAlgCat.imageι F).hom
  have hQ : torusCommHopfAlgProperty k Q :=
    CFSG.ThirdParty.TauCeti.RegularJordan.torus_semisimpleImage hr hm hc
  have hq : Function.Surjective q := CommHopfAlgCat.mkImage_surjective F
  have hσ (g : WithConv (P →ₐ[k] k)) :
      AlgHom.mapDomain σ g = HopfAlgebra.Point.semisimplePart k P k g :=
    CFSG.ThirdParty.TauCeti.RegularJordan.mapDomain_semisimplePartBialgHom hr hm g
  let r : T →ₐc[k] Q := q.comp (a.comp p)
  have hri : Function.Surjective (AlgHom.mapDomain (A := k) r) := by
    intro t
    obtain ⟨g, hg⟩ := hsur t
    refine ⟨AlgHom.mapDomain i g, ?_⟩
    have hqi : AlgHom.mapDomain q (AlgHom.mapDomain i g) = AlgHom.mapDomain σ g := by
      apply WithConv.ext
      apply AlgHom.ext
      intro x
      change g.ofConv (i (q x)) = g.ofConv (σ x)
      exact congrArg g.ofConv (CommHopfAlgCat.imageι_mkImage_apply F x)
    have hcalc : AlgHom.mapDomain r (AlgHom.mapDomain i g) =
        AlgHom.mapDomain (a.comp p) (AlgHom.mapDomain σ g) := by
      change AlgHom.mapDomain (a.comp p) (AlgHom.mapDomain q (AlgHom.mapDomain i g)) = _
      rw [hqi]
    rw [hcalc, hσ]
    have hn := HopfAlgebra.Point.semisimplePart_mapDomain (a.comp p) g
    rw [hg] at hn
    have hs : HopfAlgebra.Point.semisimplePart k T k t = t :=
      HopfAlgebra.Point.semisimplePart_eq_self k T k
        ((HopfAlgebra.isSemisimplePoint_def _).mp (isSemisimplePoint_of_torus T hT t))
    exact hn.symm.trans hs
  let : Algebra.Smooth k T := (smoothCommHopfAlgProperty_iff T.obj).mp (hT.smooth k T)
  let : IsReduced T := TauCeti.isReduced_of_smooth k T
  have hinj : Function.Injective r := by
    intro x y hxy
    apply TauCeti.eq_of_forall_algHom_apply_eq (k := k) (K := k)
    intro t
    obtain ⟨u, hu⟩ := hri (toConv t)
    have hx := congrArg (fun v : WithConv (T →ₐ[k] k) => v.ofConv x) hu
    have hy := congrArg (fun v : WithConv (T →ₐ[k] k) => v.ofConv y) hu
    change u.ofConv (r x) = t x at hx
    change u.ofConv (r y) = t y at hy
    rw [← hx, ← hy, hxy]
  have hsurj : Function.Surjective r := hrestrict Q hQ q hq
  let e := BialgEquiv.ofBijective r ⟨hinj, hsurj⟩
  let j : H →ₐc[k] T := e.symm.toBialgHom.comp (q.comp a)
  refine ⟨j, ?_⟩
  apply BialgHom.ext
  intro x
  change e.symm (r x) = x
  change e.symm (e x) = x
  exact e.symm_apply_apply x

theorem exists_section_of_triangular_diagonal_image
    (H : FiniteTypeCommHopfAlgCat.{u,u} k) [IsReduced H]
    [ConnectedSpace (PrimeSpectrum H)]
    {V : Type u} [AddCommGroup V] [Module k V] [Comodule k H V]
    {n : ℕ} (b : Module.Basis (Fin n) k V)
    (hupper : (Comodule.coefficientMatrix (C := H) b).IsUpperTriangular)
    (hdiag : ∀ i, IsGroupLikeElem k (Comodule.coefficientMatrix (C := H) b i i))
    (hfaith : Function.Surjective (Comodule.coordinateBialgHom (H := H) b)) :
    let F := _root_.CommHopfAlgCat.ofHom (triangularDiagonalCharacterMap H b hdiag)
    let T := FiniteTypeCommHopfAlgCat.of k (CommHopfAlgCat.image F)
    ∃ j : H →ₐc[k] T, j.comp (CommHopfAlgCat.imageι F).hom = BialgHom.id k T := by
  let F := _root_.CommHopfAlgCat.ofHom (triangularDiagonalCharacterMap H b hdiag)
  let T := FiniteTypeCommHopfAlgCat.of k (CommHopfAlgCat.image F)
  let p : T →ₐc[k] H := (CommHopfAlgCat.imageι F).hom
  have hT : torusCommHopfAlgProperty k T :=
    torus_image_of_groupAlgebra H (triangularDiagonalCharacterMap H b hdiag)
  have hp : Function.Injective p := CommHopfAlgCat.imageι_injective F
  have hps : Function.Surjective (AlgHom.mapDomain (A := k) p) := by
    intro t
    obtain ⟨g, hg⟩ := CommHopfAlgCat.mapPointsFunctor_app_surjective_of_injective k
      (CommHopfAlgCat.imageι F) hp t
    refine ⟨g, ?_⟩
    change (CommHopfAlgCat.mapPointsFunctor (CommHopfAlgCat.imageι F)).app (CommAlgCat.of k k) g = t
    exact hg
  have hker (g : WithConv (H →ₐ[k] k)) :
      AlgHom.mapDomain p g = 1 → HopfAlgebra.IsUnipotentPoint g := by
    intro hg
    exact (isUnipotentPoint_iff_diagonal_coefficients_eq_one H b hfaith hupper hdiag g).mpr
      ((triangularDiagonalImageMap_points_eq_one_iff H b hdiag g).mp hg)
  obtain ⟨c, hc⟩ := exists_groupLike_diagonal_lift H b hdiag
  obtain ⟨P, a, has, hred, hconn, hnil, hsur⟩ :=
    exists_connected_nilpotent_cover_of_diagonal_quotient H T hT p hps hker b hupper hfaith c hc
  let : IsReduced P := hred
  let : ConnectedSpace (PrimeSpectrum P) := hconn
  let : Group.IsNilpotent (WithConv (P →ₐ[k] k)) := hnil
  apply exists_torus_section_of_nilpotent_cover H P T hT p a hsur
  intro Q hQ q hq
  have h := surjective_diagonal_image_restriction_of_torus H Q hQ b hupper hdiag hfaith
    (q.comp a) (hq.comp has)
  simpa only [BialgHom.comp_assoc] using h

theorem exists_torus_quotient_section_of_solvable
    (H : FiniteTypeCommHopfAlgCat.{u,u} k) [IsReduced H]
    [ConnectedSpace (PrimeSpectrum H)]
    [Group.IsSolvable (WithConv (H →ₐ[k] k))] :
    ∃ (T : FiniteTypeCommHopfAlgCat.{u,u} k) (p : T →ₐc[k] H) (j : H →ₐc[k] T),
      torusCommHopfAlgProperty k T ∧ Function.Injective p ∧
      CommHopfAlgCat.kernelHopfIdeal (_root_.CommHopfAlgCat.ofHom p) =
        FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal H ∧
      j.comp p = BialgHom.id k T ∧
      ∀ (Q : FiniteTypeCommHopfAlgCat.{u,u} k), torusCommHopfAlgProperty k Q →
        ∀ q : H →ₐc[k] Q, Function.Surjective q → Function.Surjective (q.comp p) := by
  obtain ⟨D, n, b, f, hD, hgen, hupper, hdiag, hfaith, hsquare, hf⟩ :=
    exists_upperTriangular_coordinateEmbedding_data H
  let : Module.Finite k D.toSubmodule := hD
  let : AddCommGroup D.toRegularSubcomodule := Module.addCommMonoidToAddCommGroup k
  let F := _root_.CommHopfAlgCat.ofHom (triangularDiagonalCharacterMap H b hdiag)
  let T := FiniteTypeCommHopfAlgCat.of k (CommHopfAlgCat.image F)
  let p : T →ₐc[k] H := (CommHopfAlgCat.imageι F).hom
  obtain ⟨j, hj⟩ := exists_section_of_triangular_diagonal_image H b hupper hdiag hfaith
  have hT : torusCommHopfAlgProperty k T :=
    torus_image_of_groupAlgebra H (triangularDiagonalCharacterMap H b hdiag)
  have hp : Function.Injective p := CommHopfAlgCat.imageι_injective F
  have hker (g : WithConv (H →ₐ[k] k)) :
      AlgHom.mapDomain p g = 1 → HopfAlgebra.IsUnipotentPoint g := by
    intro hg
    exact (isUnipotentPoint_iff_diagonal_coefficients_eq_one H b hfaith hupper hdiag g).mpr
      ((triangularDiagonalImageMap_points_eq_one_iff H b hdiag g).mp hg)
  refine ⟨T, p, j, hT, hp,
    kernelHopfIdeal_eq_unipotentRadical_of_torus_section H T hT p hp hker j hj, hj, ?_⟩
  intro Q hQ q hq
  exact surjective_diagonal_image_restriction_of_torus H Q hQ b hupper hdiag hfaith q hq

end CFSG.LieType.AlgebraicGroups
