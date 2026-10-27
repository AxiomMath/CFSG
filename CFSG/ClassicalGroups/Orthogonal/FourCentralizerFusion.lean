module

public import CFSG.ClassicalGroups.Orthogonal.FourCentralizerPlaneNegation
public import CFSG.ClassicalGroups.Orthogonal.FiveDimensionalPlaneConjugacy
public import CFSG.ClassicalGroups.Orthogonal.FiveDimensionalCentralizerParity
public import CFSG.GroupTheory.CentralizerMap
import all CFSG.ClassicalGroups.Orthogonal.FiveDimensionalCentralizer

public noncomputable section

namespace CFSG.ClassicalGroups.Orthogonal.FourCentralizerFusion

open CFSG.ClassicalGroups.Orthogonal.FiveDimensionalLocalModel
open TauCeti QuadraticMap

variable {K : Type} [Field K] [Finite K]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {Q : QuadraticForm K V}

private noncomputable def unitVec (F : FrameData Q) (i : Fin 4) : U F :=
  ⟨F.e (Fin.castAdd 1 i), by
    rw [U, Module.End.mem_eigenspace_iff]
    change F.z (F.e (Fin.castAdd 1 i)) = (-1 : K) • F.e (Fin.castAdd 1 i)
    rw [F.z_e]
    simp⟩

private theorem unitVec_linearIndependent (F : FrameData Q) :
    LinearIndependent K (unitVec F) := by
  apply LinearIndependent.of_comp (U F).subtype
  exact F.e.linearIndependent.comp (Fin.castAdd 1) (fun i j h => Fin.castAdd_inj.mp h)

private noncomputable def fourUnitBasis (F : FrameData Q) : Module.Basis (Fin 4) K (U F) :=
  basisOfLinearIndependentOfCardEqFinrank (unitVec_linearIndependent F) (by
    rw [Fintype.card_fin, finrank_U F])

private theorem fourUnitBasis_apply (F : FrameData Q) (i : Fin 4) :
    fourUnitBasis F i = unitVec F i := by
  have h := coe_basisOfLinearIndependentOfCardEqFinrank (unitVec_linearIndependent F)
    (by rw [Fintype.card_fin, finrank_U F])
  simpa [fourUnitBasis] using congrFun h i

private theorem fourUnitBasis_norm (F : FrameData Q) (i : Fin 4) :
    (Q.comp (U F).subtype) (fourUnitBasis F i) = 1 := by
  rw [fourUnitBasis_apply]
  change Q (F.e (Fin.castAdd 1 i)) = 1
  exact F.norm (Fin.castAdd 1 i) (by simp)

private theorem fourUnitBasis_orth (F : FrameData Q) (i j : Fin 4) (hij : i ≠ j) :
    (Q.comp (U F).subtype).polarBilin (fourUnitBasis F i) (fourUnitBasis F j) = 0 := by
  rw [fourUnitBasis_apply, fourUnitBasis_apply]
  change Q.polarBilin (F.e (Fin.castAdd 1 i)) (F.e (Fin.castAdd 1 j)) = 0
  exact F.orth _ _ (fun h => hij (Fin.castAdd_inj.mp h))

private noncomputable def centralizerEquivU (F : FrameData Q) :
    C0 F ≃* TauCeti.QuadraticMap.orthogonalGroup (Q.comp (U F).subtype) :=
  (centralizerSubtypeEquiv F).symm.trans (centralizerEquiv F)

private theorem centralizerEquivU_apply (F : FrameData Q) (c : C0 F) :
    centralizerEquivU F c = restrictU F (C0toH F c) := rfl

private theorem restrictU_action (F : FrameData Q) (c : C0 F) (x : U F) :
    (((centralizerEquivU F c : U F ≃ₗ[K] U F) x : U F) : V) =
      ((c : TauCeti.QuadraticMap.orthogonalGroup Q) : V ≃ₗ[K] V) (x : V) := by
  rw [centralizerEquivU_apply]
  have h : ∀ (g : H F) (y : U F),
      (((restrictU F g : U F ≃ₗ[K] U F) y : U F) : V) = g.val.val.val y := by
    intro g y
    unfold restrictU soCentralizerToOperator
    rfl
  exact h (C0toH F c) x

private def zC0 (F : FrameData Q) : C0 F :=
  ⟨F.zO, F.z_so, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

private theorem zC0_val (F : FrameData Q) :
    ((zC0 F : C0 F) : TauCeti.QuadraticMap.orthogonalGroup Q) = F.zO := rfl

private theorem centralizerEquivU_zC0_eq_neg_one (F : FrameData Q) :
    ((centralizerEquivU F (zC0 F) : U F ≃ₗ[K] U F) : U F →ₗ[K] U F) = -1 := by
  ext x
  change (((centralizerEquivU F (zC0 F) : U F ≃ₗ[K] U F) x : U F) : V) = -(x : V)
  rw [restrictU_action]
  have hx : F.z (x : V) = -(x : V) := by
    have h := Module.End.mem_eigenspace_iff.mp x.property
    simpa [zOp] using h
  rw [zC0_val]
  exact hx



private theorem iota_eq_subtype_comp_centralizerEquivU (F : FrameData Q) :
    iota F = (C0 F).subtype.comp (centralizerEquivU F).symm.toMonoidHom := by
  ext h
  rfl

private noncomputable def centralizerEquivOfCentralizer (F : FrameData Q) (a : C0 F) :
    Subgroup.centralizer ({a} : Set (C0 F)) ≃*
      Subgroup.centralizer ({centralizerEquivU F a} :
        Set (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (U F).subtype))) :=
  ((centralizerEquivU F).subgroupMap (Subgroup.centralizer ({a} : Set (C0 F)))).trans
    (MulEquiv.subgroupCongr (by
      change (Subgroup.centralizer ({a} : Set (C0 F))).map (↑(centralizerEquivU F)) =
        Subgroup.centralizer ({centralizerEquivU F a} :
          Set (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (U F).subtype)))
      rw [← MulEquiv.toMonoidHom_eq_coe]
      exact CFSG.centralizer_singleton_map (centralizerEquivU F) a))

private theorem centralizerEquivU_apply_ne_neg_one
    (F : FrameData Q) (a : C0 F)
    (haz : (a : TauCeti.QuadraticMap.orthogonalGroup Q) ≠ F.zO) :
    ((centralizerEquivU F a : U F ≃ₗ[K] U F) : U F →ₗ[K] U F) ≠ -1 := by
  intro h
  have hz := centralizerEquivU_zC0_eq_neg_one F
  have hlin : (centralizerEquivU F a : U F ≃ₗ[K] U F) =
      (centralizerEquivU F (zC0 F) : U F ≃ₗ[K] U F) :=
    LinearEquiv.toLinearMap_injective (h.trans hz.symm)
  have haz0 : a = zC0 F := (centralizerEquivU F).injective (Subtype.ext hlin)
  apply haz
  rw [haz0]
  exact zC0_val F

private theorem mem_center_of_comap_eq_existing
    {G H : Type*} [Group G] [Group H]
    (k : G →* H) (hk : Function.Injective k)
    (R : Sylow 2 G) (Rt : Sylow 2 H)
    (hRt : (Rt : Subgroup H).comap k = (R : Subgroup G))
    (rt : ↥Rt) (hrtcenter : rt ∈ Subgroup.center Rt)
    (ba : G) (hkba : k ba = (rt : H))
    (br : ↥R) (hbr : (br : G) = ba) :
    br ∈ Subgroup.center R := by
  have hRS : (R : Subgroup G).map k ≤ (Rt : Subgroup H) :=
    Subgroup.map_le_iff_le_comap.mpr (le_of_eq hRt.symm)
  let kR : R →* Rt :=
    (Subgroup.inclusion hRS).comp (k.subgroupMap (R : Subgroup G))
  have hkR : Function.Injective kR :=
    (Subgroup.inclusion_injective hRS).comp
      (k.subgroupMap_injective (R : Subgroup G) hk)
  have hkRbr : kR br = rt := by
    apply Subtype.ext
    change k (br : G) = (rt : H)
    rw [hbr]
    exact hkba
  have hcomap : br ∈ (Subgroup.center Rt).comap kR :=
    Subgroup.mem_comap.mpr (by rw [hkRbr]; exact hrtcenter)
  exact Subgroup.comap_center_le_center hkR hcomap

private noncomputable def sylowMapImage (F : FrameData Q) (a : C0 F)
    (R0 : Sylow 2 (Subgroup.centralizer ({a} : Set (C0 F)))) :
    Sylow 2 (Subgroup.centralizer ({centralizerEquivU F a} :
      Set (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (U F).subtype)))) :=
  Sylow.mapSurjective (f := (centralizerEquivOfCentralizer F a).toMonoidHom)
    (centralizerEquivOfCentralizer F a).surjective R0

private theorem exists_center_preimage_frame
    (F : FrameData Q) (a : C0 F)
    (R0 : Sylow 2 (Subgroup.centralizer ({a} : Set (C0 F))))
    (R4 : Sylow 2 (Subgroup.centralizer ({centralizerEquivU F a} :
      Set (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (U F).subtype)))))
    (hR4coe : (R4 : Subgroup (Subgroup.centralizer ({centralizerEquivU F a} :
      Set (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (U F).subtype))))) =
      (R0 : Subgroup (Subgroup.centralizer ({a} : Set (C0 F)))).map
        (centralizerEquivOfCentralizer F a).toMonoidHom)
    (r4 : ↥R4) (hr4center : r4 ∈ Subgroup.center R4) :
    ∃ r : R0, r ∈ Subgroup.center R0 ∧
      (centralizerEquivOfCentralizer F a).toMonoidHom
          (r : Subgroup.centralizer ({a} : Set (C0 F))) =
        (r4 : Subgroup.centralizer ({centralizerEquivU F a} :
          Set (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (U F).subtype)))) := by
  classical
  let CA : Subgroup (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (U F).subtype)) :=
    Subgroup.centralizer ({centralizerEquivU F a} :
      Set (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (U F).subtype)))
  let eR : R0 ≃* R4 :=
    ((centralizerEquivOfCentralizer F a).subgroupMap R0).trans
      (MulEquiv.subgroupCongr hR4coe.symm)
  obtain ⟨z, hz⟩ := (Subgroup.centerCongr eR).surjective ⟨r4, hr4center⟩
  refine ⟨z.val, z.property, ?_⟩
  have hrmap : eR z.val = r4 := by
    have h := congrArg (fun c : Subgroup.center R4 => (c : R4)) hz
    exact (Subgroup.centerCongr_apply_coe eR z).trans h
  exact congrArg (fun z : R4 => (z : CA)) hrmap

private theorem iota_mem_center_map_of_mem_center_map
    (F : FrameData Q) (a : C0 F)
    (R0 : Sylow 2 (Subgroup.centralizer ({a} : Set (C0 F))))
    (b : TauCeti.QuadraticMap.orthogonalGroup (Q.comp (U F).subtype))
    (hbcenter : b ∈ (Subgroup.center (sylowMapImage F a R0)).map
      ((Subgroup.centralizer ({centralizerEquivU F a} :
        Set (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (U F).subtype)))).subtype.comp
        (sylowMapImage F a R0 : Subgroup (Subgroup.centralizer ({centralizerEquivU F a} :
          Set (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (U F).subtype))))).subtype)) :
    iota F b ∈ (Subgroup.center R0).map
      ((C0 F).subtype.comp
        ((Subgroup.centralizer ({a} : Set (C0 F))).subtype.comp
          (R0 : Subgroup (Subgroup.centralizer ({a} : Set (C0 F)))).subtype)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Ca0 : Subgroup (C0 F) := Subgroup.centralizer ({a} : Set (C0 F))
  let CA : Subgroup (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (U F).subtype)) :=
    Subgroup.centralizer ({centralizerEquivU F a} :
      Set (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (U F).subtype)))
  let f : Ca0 →* CA := (centralizerEquivOfCentralizer F a).toMonoidHom
  have hf_inj : Function.Injective f := (centralizerEquivOfCentralizer F a).injective
  have hf_surj : Function.Surjective f := (centralizerEquivOfCentralizer F a).surjective
  let R4 : Sylow 2 CA := sylowMapImage F a R0
  let incl0 : ↥R0 →* TauCeti.QuadraticMap.orthogonalGroup Q :=
    (C0 F).subtype.comp (Ca0.subtype.comp (R0 : Subgroup Ca0).subtype)
  obtain ⟨r4, hr4center, hr4val⟩ := Subgroup.mem_map.mp hbcenter
  have hR4coe : (R4 : Subgroup CA) = (R0 : Subgroup Ca0).map f :=
    Sylow.coe_mapSurjective (f := f) hf_surj R0
  obtain ⟨r0, hr, hfx⟩ :=
    exists_center_preimage_frame F a R0 R4 hR4coe r4 hr4center
  have hEx : centralizerEquivU F (r0 : Ca0) = b := by
    have h1 : (f (r0 : Ca0) : CA) = (r4 : CA) := hfx
    calc centralizerEquivU F (r0 : Ca0) = ((f (r0 : Ca0) : CA) :
          TauCeti.QuadraticMap.orthogonalGroup (Q.comp (U F).subtype)) := rfl
      _ = ((r4 : CA) :
          TauCeti.QuadraticMap.orthogonalGroup (Q.comp (U F).subtype)) := by rw [h1]
      _ = b := hr4val
  have hxi : (((r0 : Ca0) : C0 F) : TauCeti.QuadraticMap.orthogonalGroup Q) = iota F b := by
    have hx : ((r0 : Ca0) : C0 F) = (centralizerEquivU F).symm b := by
      rw [← hEx, (centralizerEquivU F).symm_apply_apply]
    rw [hx, iota_eq_subtype_comp_centralizerEquivU]
    rfl
  have hmem : iota F b ∈ (Subgroup.center R0).map incl0 := by
    rw [← hxi]
    exact Subgroup.mem_map_of_mem incl0 hr
  exact hmem

theorem exists_C0_conj_tO_mem_center_sylow
    (F : FrameData Q) (hodd : Odd (Nat.card K))
    (a : C0 F) (ha2 : a * a = 1) (ha1 : a ≠ 1)
    (haz : (a : TauCeti.QuadraticMap.orthogonalGroup Q) ≠ F.zO)
    (R0 : Sylow 2 (Subgroup.centralizer ({a} : Set (C0 F)))) :
    let Ca0 : Subgroup (C0 F) := Subgroup.centralizer ({a} : Set (C0 F))
    ∃ u : C0 F,
      (u : TauCeti.QuadraticMap.orthogonalGroup Q) * F.tO *
        (u : TauCeti.QuadraticMap.orthogonalGroup Q)⁻¹ ∈
      (Subgroup.center R0).map
        ((C0 F).subtype.comp (Ca0.subtype.comp (R0 : Subgroup Ca0).subtype)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro Ca0
  let CA : Subgroup (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (U F).subtype)) :=
    Subgroup.centralizer ({centralizerEquivU F a} :
      Set (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (U F).subtype)))
  let f : Ca0 →* CA := (centralizerEquivOfCentralizer F a).toMonoidHom
  have hf_surj : Function.Surjective f := (centralizerEquivOfCentralizer F a).surjective
  have hA2 : centralizerEquivU F a * centralizerEquivU F a = 1 := by
    have h := congrArg (centralizerEquivU F) ha2
    simpa using h
  have hA1 : centralizerEquivU F a ≠ 1 := by
    intro h
    exact ha1 ((centralizerEquivU F).injective h)
  have hAneg : ((centralizerEquivU F a : U F ≃ₗ[K] U F) : U F →ₗ[K] U F) ≠ -1 :=
    centralizerEquivU_apply_ne_neg_one F a haz
  let R4 : Sylow 2 CA := Sylow.mapSurjective (f := f) hf_surj R0
  obtain ⟨b, hbcenter, hb2, hb1, u, v, huQ, hvQ, huv, hbu, hbv, hbfix⟩ :=
    CFSG.ClassicalGroups.Orthogonal.FourCentralizerPlaneNegation.exists_central_plane_negation_of_sylow
      (Q.comp (U F).subtype) hodd (U_polar_nondegenerate F)
      (fourUnitBasis F) (fourUnitBasis_norm F) (fourUnitBasis_orth F)
      (centralizerEquivU F a) hA2 hA1 hAneg R4
  obtain ⟨g, hgconj⟩ :=
    exists_C0_conj_tO_eq_iota_of_unit_plane_actions F b huQ hvQ huv hbu hbv hbfix
  have hmem : iota F b ∈ (Subgroup.center R0).map
      ((C0 F).subtype.comp
        ((Subgroup.centralizer ({a} : Set (C0 F))).subtype.comp
          (R0 : Subgroup (Subgroup.centralizer ({a} : Set (C0 F)))).subtype)) :=
    iota_mem_center_map_of_mem_center_map (F := F) (a := a) (R0 := R0) (b := b) hbcenter
  exact ⟨g, by rw [hgconj]; exact hmem⟩

theorem exists_conj_tO_mem_center_sylow
    (F : FrameData Q) (hodd : Odd (Nat.card K))
    (G : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hDG : commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ≤ G)
    (hGSO : G ≤ Q.specialOrthogonalWithin) :
    let HG : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q) :=
      G ⊓ Subgroup.centralizer ({F.zO} : Set (TauCeti.QuadraticMap.orthogonalGroup Q))
    ∀ (a : HG), a * a = 1 → a ≠ 1 →
      (a : TauCeti.QuadraticMap.orthogonalGroup Q) ≠ F.zO →
      let Ca : Subgroup HG := Subgroup.centralizer ({a} : Set HG)
      ∀ R : Sylow 2 Ca,
        let incl : R →* TauCeti.QuadraticMap.orthogonalGroup Q :=
          HG.subtype.comp (Ca.subtype.comp (R : Subgroup Ca).subtype)
        ∃ h : HG,
          (h : TauCeti.QuadraticMap.orthogonalGroup Q) * F.tO *
            (h : TauCeti.QuadraticMap.orthogonalGroup Q)⁻¹ ∈
              (Subgroup.center R).map incl := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro HG a ha2 ha1 haz Ca R incl
  let j : HG →* C0 F :=
    { toFun := fun x => ⟨(x : TauCeti.QuadraticMap.orthogonalGroup Q),
        ⟨hGSO (Subgroup.mem_inf.mp x.property).1, (Subgroup.mem_inf.mp x.property).2⟩⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : C0 F => (z : TauCeti.QuadraticMap.orthogonalGroup Q)) h
  let a0 : C0 F := j a
  have ha2' : a0 * a0 = 1 := by
    have h := congrArg j ha2
    simpa [a0] using h
  have ha1' : a0 ≠ 1 := by
    intro h
    apply ha1
    exact hj (by simpa [a0] using h)
  have haz' : (a0 : TauCeti.QuadraticMap.orthogonalGroup Q) ≠ F.zO := by
    intro h
    exact haz h
  let Ca0 : Subgroup (C0 F) := Subgroup.centralizer ({a0} : Set (C0 F))
  let k : Ca →* Ca0 :=
    { toFun := fun x => ⟨j (x : HG), by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hx : (x : HG) * a = a * (x : HG) :=
          Subgroup.mem_centralizer_singleton_iff.mp x.property
        calc j (x : HG) * a0 = j ((x : HG) * a) := by
              rw [j.map_mul]
          _ = j (a * (x : HG)) := by rw [hx]
          _ = a0 * j (x : HG) := by
              rw [j.map_mul]⟩
      map_one' := by
        apply Subtype.ext
        exact j.map_one
      map_mul' := by
        intro x y
        apply Subtype.ext
        exact j.map_mul x y }
  have hk : Function.Injective k := by
    intro x y h
    apply Subtype.ext
    apply hj
    exact congrArg (fun z : Ca0 => (z : C0 F)) h
  obtain ⟨Rt, hRt⟩ := Sylow.exists_comap_eq_of_injective R (f := k) hk
  have hRt' : (Rt : Subgroup Ca0).comap k = (R : Subgroup Ca) := hRt
  obtain ⟨u, hu_mem⟩ :=
    exists_C0_conj_tO_mem_center_sylow F hodd a0 ha2' ha1' haz' Rt
  let b : TauCeti.QuadraticMap.orthogonalGroup Q :=
    (u : TauCeti.QuadraticMap.orthogonalGroup Q) * F.tO *
      (u : TauCeti.QuadraticMap.orthogonalGroup Q)⁻¹
  have hu_mem' : b ∈ (Subgroup.center Rt).map
      ((C0 F).subtype.comp (Ca0.subtype.comp (Rt : Subgroup Ca0).subtype)) := hu_mem
  obtain ⟨rt, hrtcenter, hrtval⟩ := Subgroup.mem_map.mp hu_mem'
  obtain ⟨h, hhC0, hhD, hhconj⟩ :=
    CFSG.ClassicalGroups.Orthogonal.FiveDimensionalCentralizerParity.exists_commutator_conjugator_same_t
      F hodd u u.property
  have htD : F.tO ∈ commutator (TauCeti.QuadraticMap.orthogonalGroup Q) := by
    rw [← Subgroup.mem_map_iff_mem
      (f := (TauCeti.QuadraticMap.orthogonalGroup Q).subtype)
      (Subgroup.subtype_injective _)]
    rw [Subgroup.map_subtype_commutator]
    exact F.t_mem_commutator
  have hbD : b ∈ commutator (TauCeti.QuadraticMap.orthogonalGroup Q) := by
    rw [show b = h * F.tO * h⁻¹ from hhconj.symm]
    exact (commutator _).mul_mem ((commutator _).mul_mem hhD htD)
      ((commutator _).inv_mem hhD)
  have hbG : b ∈ G := hDG hbD
  have hbC0 : b ∈ C0 F := by
    rw [show b = h * F.tO * h⁻¹ from hhconj.symm]
    exact (C0 F).mul_mem ((C0 F).mul_mem hhC0 (tO_mem_C0 F)) ((C0 F).inv_mem hhC0)
  have hbHG : b ∈ HG := Subgroup.mem_inf.mpr ⟨hbG, hbC0.2⟩
  have hba : b * (a : TauCeti.QuadraticMap.orthogonalGroup Q) =
      (a : TauCeti.QuadraticMap.orthogonalGroup Q) * b := by
    have h := Subgroup.mem_centralizer_singleton_iff.mp (rt : Ca0).property
    have h' := congrArg (fun z : C0 F => (z : TauCeti.QuadraticMap.orthogonalGroup Q)) h
    simp only [Subgroup.coe_mul] at h'
    change (((C0 F).subtype.comp (Ca0.subtype.comp (Rt : Subgroup Ca0).subtype)) rt) *
        (a0 : TauCeti.QuadraticMap.orthogonalGroup Q) =
      (a0 : TauCeti.QuadraticMap.orthogonalGroup Q) *
        (((C0 F).subtype.comp (Ca0.subtype.comp (Rt : Subgroup Ca0).subtype)) rt) at h'
    rw [hrtval] at h'
    exact h'
  let ba : Ca := ⟨⟨b, hbHG⟩, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact hba⟩
  have hkba : k ba = (rt : Ca0) := by
    apply Subtype.ext
    apply Subtype.ext
    change ((k ba : C0 F) : TauCeti.QuadraticMap.orthogonalGroup Q) =
      (((C0 F).subtype.comp (Ca0.subtype.comp (Rt : Subgroup Ca0).subtype)) rt)
    rw [hrtval]
    rfl
  have hbaR : ba ∈ (R : Subgroup Ca) := by
    have h : ba ∈ (Rt : Subgroup Ca0).comap k :=
      Subgroup.mem_comap.mpr (by rw [hkba]; exact rt.property)
    rwa [hRt'] at h
  let br : R := ⟨ba, hbaR⟩
  have hbacenter : br ∈ Subgroup.center R :=
    mem_center_of_comap_eq_existing k hk R Rt hRt' rt hrtcenter ba hkba br rfl
  let hHG : HG := ⟨h, Subgroup.mem_inf.mpr ⟨hDG hhD, hhC0.2⟩⟩
  refine ⟨hHG, ?_⟩
  rw [show (hHG : TauCeti.QuadraticMap.orthogonalGroup Q) * F.tO *
      (hHG : TauCeti.QuadraticMap.orthogonalGroup Q)⁻¹ = b from hhconj]
  have hincl : incl br = b := rfl
  have hmem : incl br ∈ (Subgroup.center R).map incl :=
    Subgroup.mem_map_of_mem incl hbacenter
  rw [hincl] at hmem
  exact hmem

end CFSG.ClassicalGroups.Orthogonal.FourCentralizerFusion
