module

public import CFSG.LieType.AlgebraicGroups.FiniteCentralizerSemisimple
public import CFSG.LieType.AlgebraicGroups.MatrixComponentQuotient

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley WithConv Subgroup
open scoped CFSG.ConvolutionPoints

variable {τ : Tag} {k : Type} [Field k] [IsAlgClosed k]

theorem not_finite_centralizer_subgroup_of_cube_eq_one_of_ne_one
    (K : Subgroup (ModGL τ k))
    (hK : IsConnectedAlgebraicSubgroup k (K.map (modGLPoint τ k).toMonoidHom))
    {e : ModGL τ k} (heK : e ∈ K) (he3 : e ^ 3 = 1) (he1 : e ≠ 1) (h3 : (3 : k) ≠ 0) :
    ¬ {x : K | Commute x ⟨e, heK⟩}.Finite := by
  classical
  have hpc : IsPointClosed k (transportPoints (modGLPoint τ k) (K : Set (ModGL τ k))) := by
    simpa only [subgroupPoints_map] using hK.isPointClosed
  let H := MatrixComponents.coordinateHopf (τ := τ) (k := k) K
  let ψ : WithConv (H →ₐ[k] k) ≃* K :=
    MatrixComponents.coordinatePointsMulEquiv K hpc
  let x : WithConv (H →ₐ[k] k) := ψ.symm ⟨e, heK⟩
  have hx3 : x ^ 3 = 1 := by
    apply ψ.injective
    rw [map_pow, map_one, MulEquiv.apply_symm_apply]
    exact Subtype.ext (by simpa using he3)
  have hx1 : x ≠ 1 := by
    intro hx
    apply he1
    have h : (⟨e, heK⟩ : K) = 1 := by
      have := congrArg ψ hx
      rwa [map_one, MulEquiv.apply_symm_apply] at this
    simpa using congrArg Subtype.val h
  have hcore : ¬ {z : WithConv (H →ₐ[k] k) | Commute z x}.Finite := by
    haveI : IsDomain H := hK.isDomain
    exact not_finite_centralizer_of_cube_eq_one_of_ne_one H h3 hx3 hx1
  intro hfin
  apply hcore
  have himage : (fun y : K => (ψ.symm y : WithConv (H →ₐ[k] k))) ''
      {y : K | Commute y ⟨e, heK⟩} = {z : WithConv (H →ₐ[k] k) | Commute z x} := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      change Commute (ψ.symm y) (ψ.symm ⟨e, heK⟩)
      exact hy.map ψ.symm
    · intro hz
      refine ⟨ψ z, ?_, ψ.symm_apply_apply z⟩
      have h := hz.map ψ
      rwa [show ψ x = ⟨e, heK⟩ from ψ.apply_symm_apply ⟨e, heK⟩] at h
  rw [← himage]
  exact hfin.image (fun y : K => ψ.symm y)

theorem ne_centralizer_of_isConnected_of_eq_sup_zpowers
    {G E H K0 : Subgroup (ModGL τ k)} [Finite E] (e : ModGL τ k)
    (hK : IsConnectedAlgebraicSubgroup k (K0.map (modGLPoint τ k).toMonoidHom))
    (hE : E = H ⊔ zpowers e)
    (hK0 : K0 ≤ G ⊓ centralizer (H : Set (ModGL τ k)))
    (heK : e ∈ K0) (he3 : e ^ 3 = 1) (he1 : e ≠ 1) (h3 : (3 : k) ≠ 0) :
    G ⊓ centralizer (E : Set (ModGL τ k)) ≠ E := by
  intro hself
  have hfin : {x : K0 | Commute x ⟨e, heK⟩}.Finite := by
    have hsub : (fun x : K0 => (x : ModGL τ k)) ''
        {x : K0 | Commute x ⟨e, heK⟩} ⊆ (E : Set (ModGL τ k)) := by
      rintro _ ⟨x, hx, rfl⟩
      have hxG : (x : ModGL τ k) ∈ G ⊓ centralizer (H : Set (ModGL τ k)) := hK0 x.2
      have hxCE : (x : ModGL τ k) ∈ centralizer (E : Set (ModGL τ k)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hH : H ≤ Subgroup.centralizer ({(x : ModGL τ k)} : Set (ModGL τ k)) := by
          intro h hh
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact Subgroup.mem_centralizer_iff.mp hxG.2 h hh
        have hem : zpowers e ≤
            Subgroup.centralizer ({(x : ModGL τ k)} : Set (ModGL τ k)) := by
          apply Subgroup.zpowers_le.mpr
          rw [Subgroup.mem_centralizer_singleton_iff]
          simpa only [Subgroup.coe_mul] using Subtype.ext_iff.mp hx.symm
        have hE' : E ≤ Subgroup.centralizer ({(x : ModGL τ k)} : Set (ModGL τ k)) := by
          rw [hE]
          exact sup_le hH hem
        exact Subgroup.mem_centralizer_singleton_iff.mp (hE' hy)
      have hxE : (x : ModGL τ k) ∈ G ⊓ centralizer (E : Set (ModGL τ k)) := ⟨hxG.1, hxCE⟩
      rwa [hself] at hxE
    exact Set.Finite.of_finite_image
      (Set.Finite.subset (Set.toFinite (E : Set (ModGL τ k))) hsub)
      (fun x _ y _ h => Subtype.ext h)
  exact not_finite_centralizer_subgroup_of_cube_eq_one_of_ne_one K0 hK heK he3 he1 h3 hfin

end CFSG.LieType.AlgebraicGroups
