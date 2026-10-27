module
public import CFSG.LieType.AlgebraicGroups.MatrixFixedComponentsThree
public import CFSG.LieType.AlgebraicGroups.TorusPointSubgroups
public import CFSG.LieType.AlgebraicGroups.SubgroupCoordinateInclusion
public import TauCeti.Algebra.AlgebraicGroup.Torus.SmoothConnected

public noncomputable section
namespace CFSG.LieType.AlgebraicGroups
open WithConv Subgroup CategoryTheory CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped CFSG.ConvolutionPoints

variable {τ : Tag} {k : Type} [Field k] [IsAlgClosed k]

theorem not_torus_of_matrix_inverted_odd
    (K : Subgroup (CFSG.Blueprint.Chevalley.ModGL τ k))
    (hK : IsPointClosed k (transportPoints (modGLPoint τ k) (K : Set (CFSG.Blueprint.Chevalley.ModGL τ k))))
    {g e : CFSG.Blueprint.Chevalley.ModGL τ k} (hg : g ∈ K) (he : e ∈ K)
    {n : ℕ} (hn : Odd n) (hen : e ^ n = 1) (he1 : e ≠ 1) (hinv : g * e * g⁻¹ = e⁻¹) :
    ¬ TauCeti.torusCommHopfAlgProperty k (MatrixComponents.coordinateHopf K) := by
  have hpn : modGLPoint τ k e ^ n = 1 := by rw [← map_pow, hen, map_one]
  have hp1 : modGLPoint τ k e ≠ 1 := by
    intro h
    exact he1 ((modGLPoint τ k).injective (h.trans (map_one _).symm))
  have hpinv : modGLPoint τ k g * modGLPoint τ k e * (modGLPoint τ k g)⁻¹ =
      (modGLPoint τ k e)⁻¹ := by rw [← map_inv, ← map_mul, ← map_mul, hinv, map_inv]
  exact not_torus_of_inverted_odd _
    (MatrixComponents.pointsZero_subgroupIdeal_map_modGLPoint K hK)
    (Subgroup.mem_map_of_mem (modGLPoint τ k).toMonoidHom hg)
    (Subgroup.mem_map_of_mem (modGLPoint τ k).toMonoidHom he) hn hpn hp1 hpinv


theorem torus_hopf_points_le_connected_centralizer
    (K : Subgroup (ModGL τ k))
    (hK : IsPointClosed k (transportPoints (modGLPoint τ k) (K : Set (ModGL τ k))))
    (e : ModGL τ k) (heK : e ∈ K)
    (J : TauCeti.HopfIdeal k (MatrixComponents.coordinateHopf K))
    (hJ : TauCeti.torusCommHopfAlgProperty k
      (TauCeti.FiniteTypeCommHopfAlgCat.quotient (MatrixComponents.coordinateHopf K) J))
    (heJ : (MatrixComponents.coordinatePointsMulEquiv K hK).symm ⟨e,heK⟩ ∈
      TauCeti.CommHopfAlgCat.quotientPointsSubgroup (MatrixComponents.coordinateHopf K).obj J
        (CommAlgCat.of k k))
    (x : TauCeti.HopfAlgebra.points (H := TauCeti.FiniteTypeCommHopfAlgCat.quotient
      (MatrixComponents.coordinateHopf K) J) (CommAlgCat.of k k)) :
    (MatrixComponents.coordinatePointsMulEquiv K hK
      (TauCeti.CommHopfAlgCat.quotientPointsHom (MatrixComponents.coordinateHopf K).obj J
        (CommAlgCat.of k k) x) : ModGL τ k) ∈
          closedIdentityComponent (K ⊓ centralizer {e}) := by
  let M := MatrixComponents.coordinateHopf K
  let Q := TauCeti.FiniteTypeCommHopfAlgCat.quotient M J
  let ψ := MatrixComponents.coordinatePointsMulEquiv K hK
  let π := (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient M J).hom.hom
  let ep := ψ.symm ⟨e,heK⟩
  have heq : ep ∈ (TauCeti.AlgHom.mapDomain (A := k) π).range := heJ
  obtain ⟨eQ, heQ⟩ := heq
  let N := K ⊓ centralizer {e}
  have hN := isPointClosed_inf hK (isPointClosed_centralizer {e})
  have hQcomm := TauCeti.torusCommHopfAlgProperty.isCocomm k Q hJ
  have hqc : ∀ z : Q →ₐ[k] k, (ψ (TauCeti.AlgHom.mapDomain π (toConv z)) : ModGL τ k) ∈ N := by
    intro z
    refine ⟨(ψ _).2, ?_⟩
    change (ψ (TauCeti.AlgHom.mapDomain π (toConv z)) : ModGL τ k) ∈ centralizer {e}
    rw [mem_centralizer_singleton_iff]
    have hc : eQ * toConv z = toConv z * eQ := mul_comm _ _
    have hm := congrArg (fun q => (ψ (TauCeti.AlgHom.mapDomain π q) : ModGL τ k)) hc
    rw [map_mul, map_mul, map_mul, map_mul, heQ, ψ.apply_symm_apply] at hm
    exact hm.symm
  let f : GLCoord k (Label τ) →ₐc[k] Q := π.comp
    (Bialgebra.Quotient.mkBialgHom (subgroupIdeal (K.map (modGLPoint τ k).toMonoidHom)))
  have hf : ∀ z : Q →ₐ[k] k, z.comp f.toAlgHom ∈ transportPoints (modGLPoint τ k) (N : Set (ModGL τ k)) := by
    intro z
    refine ⟨ψ (TauCeti.AlgHom.mapDomain π (toConv z)), hqc z, ?_⟩
    change (modGLPoint τ k (ψ (TauCeti.AlgHom.mapDomain π (toConv z)) : ModGL τ k)).ofConv = _
    rw [MatrixComponents.coordinatePointsMulEquiv_coe, MulEquiv.apply_symm_apply, ofConv_toConv]
    rfl
  have hred : IsReduced Q := hJ.geometricallyReduced.isReduced
  let θ : MatrixComponents.coordinateHopf N →ₐc[k] Q := bialgHomQuotientLift
    (subgroupIdeal (N.map (modGLPoint τ k).toMonoidHom)) f (by
      intro a ha
      exact map_eq_zero_of_comp_mem (transportPoints (modGLPoint τ k) (N : Set (ModGL τ k)))
        f.toAlgHom hf (by simpa only [subgroupIdeal, subgroupPoints_map] using ha))
  have hconn : ConnectedSpace (PrimeSpectrum Q) :=
    TauCeti.geometricallyConnectedCommHopfAlgProperty.connectedSpace k Q.obj hJ.geometricallyConnected
  have hcmp := componentPointsHom_map_eq_one (MatrixComponents.coordinateHopf N) Q
    (CommHopfAlgCat.ofHom θ) hconn x
  have hmem : (MatrixComponents.coordinatePointsMulEquiv N hN
      (TauCeti.AlgHom.mapDomain θ x) : ModGL τ k) ∈ closedIdentityComponent N := by
    apply (MatrixComponents.coordinatePoints_mem_closedIdentityComponent_iff N hN _).2
    apply (TauCeti.FiniteTypeCommHopfAlgCat.rationalComponentMap_eq_one_iff _ _).1
    exact (componentPointsHom_eq_one_iff _ _).1 hcmp
  convert hmem using 1
  rw [MatrixComponents.coordinatePointsMulEquiv_coe, MatrixComponents.coordinatePointsMulEquiv_coe]
  apply congrArg (modGLPoint τ k).symm
  apply WithConv.ext
  ext a
  change x.ofConv (f a) = x.ofConv (θ (Ideal.Quotient.mk _ a))
  exact congrArg x.ofConv (bialgHomQuotientLift_mk _ _ _ a).symm

theorem isMaximalTorus_connected_centralizer_of_mem
    (K : Subgroup (ModGL τ k))
    (hK : IsPointClosed k (transportPoints (modGLPoint τ k) (K : Set (ModGL τ k))))
    (e : ModGL τ k)
    (heS : e ∈ closedIdentityComponent (K ⊓ centralizer {e}))
    (htor : TauCeti.torusCommHopfAlgProperty k
      (TauCeti.FiniteTypeCommHopfAlgCat.of k (closedIdentityCoordinateRing (K ⊓ centralizer {e})))) :
    let KP := K.map (modGLPoint τ k).toMonoidHom
    TauCeti.HopfIdeal.IsMaximalTorus k (CommHopfAlgCat.of k (GLCoord k (Label τ) ⧸ subgroupIdeal KP))
      (subgroupHopfIdeal (Subgroup.map_mono
        ((closedIdentityComponent_le (K ⊓ centralizer {e})).trans inf_le_left))) := by
  let S := closedIdentityComponent (K ⊓ centralizer {e})
  let SP := S.map (modGLPoint τ k).toMonoidHom
  let KP := K.map (modGLPoint τ k).toMonoidHom
  have hSP := isConnectedAlgebraicSubgroup_closedIdentityComponent
    (isPointClosed_inf hK (isPointClosed_centralizer {e}))
  have hKP := MatrixComponents.pointsZero_subgroupIdeal_map_modGLPoint K hK
  have hSK : S ≤ K := (closedIdentityComponent_le _).trans inf_le_left
  have heK : e ∈ K := hSK heS
  apply subgroupHopfIdeal_isMaximalTorus_of_point_maximal
    (map_mono hSK) hSP.pointsZero_eq hKP htor
  intro J hJ hJI x hx
  let ep := (subgroupQuotientPointsEquiv KP hKP).symm
    ⟨modGLPoint τ k e, mem_map_of_mem (modGLPoint τ k).toMonoidHom heK⟩
  have heI : ep ∈ ofTauCeti (TauCeti.CommHopfAlgCat.quotientPointsSubgroup
      (CommHopfAlgCat.of k (GLCoord k (Label τ) ⧸ subgroupIdeal KP))
      (subgroupHopfIdeal (map_mono hSK)) (CommAlgCat.of k k)) := by
    have hmap := quotientPoints_subgroupHopfIdeal_eq (map_mono hSK) hSP.pointsZero_eq hKP
    have hm : (subgroupQuotientPointsEquiv KP hKP) ep ∈ SP.subgroupOf KP := by
      change ((subgroupQuotientPointsEquiv KP hKP) ep : WithConv (GLCoord k (Label τ) →ₐ[k] k)) ∈ SP
      rw [MulEquiv.apply_symm_apply]
      exact mem_map_of_mem (modGLPoint τ k).toMonoidHom heS
    rw [← hmap] at hm
    have h := Subgroup.mem_map_equiv.mp hm
    rw [MulEquiv.symm_apply_apply] at h
    exact h
  have heJ := (TauCeti.CommHopfAlgCat.quotientPointsSubgroup_le_of_le _ hJI
      (CommAlgCat.of k k)) (mem_ofTauCeti.mp heI)
  have heJ' : (MatrixComponents.coordinatePointsMulEquiv K hK).symm ⟨e,heK⟩ ∈
      TauCeti.CommHopfAlgCat.quotientPointsSubgroup (MatrixComponents.coordinateHopf K).obj J
        (CommAlgCat.of k k) := by
    have heq : (MatrixComponents.coordinatePointsMulEquiv K hK).symm ⟨e,heK⟩ = ep := by
      apply WithConv.ext
      apply Ideal.Quotient.algHom_ext k
      ext a
      rfl
    exact heq ▸ heJ
  obtain ⟨xQ, hxQ⟩ : ∃ xQ, TauCeti.CommHopfAlgCat.quotientPointsHom
      (MatrixComponents.coordinateHopf K).obj J (CommAlgCat.of k k) xQ = x := by
    exact mem_ofTauCeti.mp hx
  have hxS := torus_hopf_points_le_connected_centralizer K hK e heK J hJ heJ' xQ
  rw [hxQ] at hxS
  change ((subgroupQuotientPointsEquiv KP hKP) x : WithConv (GLCoord k (Label τ) →ₐ[k] k)) ∈ SP
  have hval : ((subgroupQuotientPointsEquiv KP hKP) x : WithConv (GLCoord k (Label τ) →ₐ[k] k)) =
      modGLPoint τ k (MatrixComponents.coordinatePointsMulEquiv K hK x : ModGL τ k) := by
    apply WithConv.ext
    rw [subgroupQuotientPointsEquiv_apply, MatrixComponents.coordinatePointsMulEquiv_coe,
      MulEquiv.apply_symm_apply, ofConv_toConv]
  rw [hval]
  exact mem_map_of_mem (modGLPoint τ k).toMonoidHom hxS


omit [IsAlgClosed k] in
theorem connected_centralizer_le_hyperplane
    (G E H : Subgroup (ModGL τ k)) (hHE : H ≤ E) :
    closedIdentityComponent (G ⊓ centralizer (E : Set (ModGL τ k))) ≤
      closedIdentityComponent (G ⊓ centralizer (H : Set (ModGL τ k))) :=
  closedIdentityComponent_mono (inf_le_inf_left G (centralizer_le hHE))

omit [IsAlgClosed k] in
theorem centralizer_inf_connected_hyperplane_eq
    (G E H : Subgroup (ModGL τ k)) (e : ModGL τ k)
    (hE : E = H ⊔ zpowers e)
    (heS : e ∈ closedIdentityComponent (G ⊓ centralizer (E : Set (ModGL τ k))))
    (hcomm : ∀ x ∈ G ⊓ centralizer (E : Set (ModGL τ k)),
      ∀ y ∈ G ⊓ centralizer (E : Set (ModGL τ k)), x * y = y * x) :
    centralizer (closedIdentityComponent (G ⊓ centralizer (E : Set (ModGL τ k))) : Set (ModGL τ k)) ⊓
      closedIdentityComponent (G ⊓ centralizer (H : Set (ModGL τ k))) =
    centralizer (E : Set (ModGL τ k)) ⊓
      closedIdentityComponent (G ⊓ centralizer (H : Set (ModGL τ k))) := by
  let S := closedIdentityComponent (G ⊓ centralizer (E : Set (ModGL τ k)))
  apply le_antisymm
  · intro x hx
    have hxH : x ∈ centralizer (H : Set (ModGL τ k)) := (closedIdentityComponent_le _ hx.2).2
    have hHC : H ≤ centralizer {x} := by
      intro h hh
      rw [mem_centralizer_singleton_iff]
      exact mem_centralizer_iff.mp hxH h hh
    have heC : zpowers e ≤ centralizer {x} := by
      apply zpowers_le.mpr
      rw [mem_centralizer_singleton_iff]
      exact mem_centralizer_iff.mp hx.1 e heS
    have hEC : E ≤ centralizer {x} := by rw [hE]; exact sup_le hHC heC
    refine ⟨?_, hx.2⟩
    change x ∈ centralizer (E : Set (ModGL τ k))
    rw [mem_centralizer_iff]
    intro a ha
    exact mem_centralizer_singleton_iff.mp (hEC ha)
  · intro x hx
    refine ⟨?_, hx.2⟩
    change x ∈ centralizer (S : Set (ModGL τ k))
    rw [mem_centralizer_iff]
    intro s hs
    exact hcomm s (closedIdentityComponent_le _ hs) x
      ⟨(closedIdentityComponent_le _ hx.2).1, hx.1⟩

theorem isMaximalTorus_connected_hyperplane_centralizer
    (G E H : Subgroup (ModGL τ k)) (e : ModGL τ k)
    (hE : E = H ⊔ zpowers e)
    (hG : IsPointClosed k (transportPoints (modGLPoint τ k) (G : Set (ModGL τ k))))
    (heS : e ∈ closedIdentityComponent (G ⊓ centralizer (E : Set (ModGL τ k))))
    (htor : TauCeti.torusCommHopfAlgProperty k
      (TauCeti.FiniteTypeCommHopfAlgCat.of k (closedIdentityCoordinateRing
        (G ⊓ centralizer (E : Set (ModGL τ k)))))) :
    let K := closedIdentityComponent (G ⊓ centralizer (H : Set (ModGL τ k)))
    TauCeti.HopfIdeal.IsMaximalTorus k (MatrixComponents.coordinateHopf K).obj
      (subgroupHopfIdeal (Subgroup.map_mono (f := (modGLPoint τ k).toMonoidHom)
        (connected_centralizer_le_hyperplane G E H
        (by rw [hE]; exact le_sup_left)))) := by
  let K := closedIdentityComponent (G ⊓ centralizer (H : Set (ModGL τ k)))
  have hK : IsPointClosed k (transportPoints (modGLPoint τ k) (K : Set (ModGL τ k))) :=
    isPointClosed_closedIdentityComponent (isPointClosed_inf hG (isPointClosed_centralizer _))
  have heK : e ∈ closedIdentityComponent (K ⊓ centralizer {e}) := by
    rw [closedIdentityComponent_hyperplane_centralizer_eq G E H e hE]
    exact heS
  have htK : TauCeti.torusCommHopfAlgProperty k
      (TauCeti.FiniteTypeCommHopfAlgCat.of k (closedIdentityCoordinateRing (K ⊓ centralizer {e}))) := by
    change TauCeti.torusCommHopfAlgProperty k (TauCeti.FiniteTypeCommHopfAlgCat.of k
      (GLCoord k (Label τ) ⧸ subgroupIdeal
        ((closedIdentityComponent (K ⊓ centralizer {e})).map (modGLPoint τ k).toMonoidHom)))
    rw [closedIdentityComponent_hyperplane_centralizer_eq G E H e hE]
    exact htor
  have hm := isMaximalTorus_connected_centralizer_of_mem K hK e heK htK
  have heq := closedIdentityComponent_hyperplane_centralizer_eq G E H e hE
  have hi : subgroupHopfIdeal (Subgroup.map_mono (f := (modGLPoint τ k).toMonoidHom)
      ((closedIdentityComponent_le (K ⊓ centralizer {e})).trans inf_le_left)) =
      subgroupHopfIdeal (Subgroup.map_mono (f := (modGLPoint τ k).toMonoidHom)
        (connected_centralizer_le_hyperplane G E H
        (by rw [hE]; exact le_sup_left))) := by
    apply TauCeti.HopfIdeal.ext
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [mem_subgroupHopfIdeal_mk, mem_subgroupHopfIdeal_mk, heq]
  change TauCeti.HopfIdeal.IsMaximalTorus k (MatrixComponents.coordinateHopf K).obj
      (subgroupHopfIdeal (Subgroup.map_mono (f := (modGLPoint τ k).toMonoidHom)
        (connected_centralizer_le_hyperplane G E H (by rw [hE]; exact le_sup_left))))
  exact hi ▸ hm


end CFSG.LieType.AlgebraicGroups
