module

public import CFSG.ClassicalInvolution.Q3.Q3VFrameComm
public import CFSG.ClassicalInvolution.Q3.Q3VLocDef
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCAdaptModel

public section

namespace CFSG.ClassicalInvolution.Q3.Q3V.Frame

open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Models.SymplecticPairs (planeGroup IsHyperbolicPlane
  planeGroup_map_conj mem_center_of_conj_mem_center)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)

variable {m : ℕ} {G : Type} [Group G] {Ω : Set (Subgroup G)} {L : Subgroup G}
  {Θ : StatedSp m (GaloisField 3 1) →* G}

theorem map_conj_comp (g : G) (H : Subgroup (StatedSp m (GaloisField 3 1))) :
    H.map ((MulAut.conj g).toMonoidHom.comp Θ) = conjSub g (H.map Θ) :=
  (Subgroup.map_map _ _ _).symm

theorem IsLocLift.conj (hΩ : ConjInvariant Ω) (h : IsLocLift m Ω L Θ) (g : G) :
    IsLocLift m Ω (conjSub g L) ((MulAut.conj g).toMonoidHom.comp Θ) where
  ker_le := fun x hx => h.ker_le (by
    have h1 : (MulAut.conj g) (Θ x) = (MulAut.conj g) 1 := by
      rw [map_one]
      exact MonoidHom.mem_ker.1 hx
    exact MonoidHom.mem_ker.2 ((MulAut.conj g).injective h1))
  comm := by
    have hr : ((MulAut.conj g).toMonoidHom.comp Θ).range = conjSub g Θ.range := by
      rw [MonoidHom.range_comp]
      rfl
    rw [hr]
    exact h.comm.conjSub g
  plane_mem := fun P hP => by
    rw [map_conj_comp]
    exact hΩ g _ (h.plane_mem P hP)
  members := fun M hM hML hMc => by
    have hM' : conjSub g⁻¹ M ∈ Ω := hΩ g⁻¹ M hM
    have hne : conjSub g⁻¹ M ≠ L := by
      intro h'
      apply hML
      rw [← conjSub_conjSub_inv g M, h']
    have hc : Commutes (conjSub g⁻¹ M) L := by
      have := hMc.conjSub g⁻¹
      rwa [conjSub_inv_conjSub] at this
    obtain ⟨P, hP, hMP⟩ := h.members _ hM' hne hc
    refine ⟨P, hP, ?_⟩
    rw [map_conj_comp, ← hMP, conjSub_conjSub_inv]

theorem IsLocLift.relabel (h : IsLocLift m Ω L Θ) (γ : StatedSp m (GaloisField 3 1)) :
    IsLocLift m Ω L (Θ.comp (MulAut.conj γ).toMonoidHom) where
  ker_le := fun x hx => by
    have h1 : γ * x * γ⁻¹ ∈ Θ.ker := hx
    exact mem_center_of_conj_mem_center (h.ker_le h1)
  comm := by
    have hr : (Θ.comp (MulAut.conj γ).toMonoidHom).range = Θ.range := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨_, rfl⟩
      · rintro ⟨x, rfl⟩
        exact ⟨γ⁻¹ * x * γ, by simp [mul_assoc]⟩
    rw [hr]
    exact h.comm
  plane_mem := fun P hP => by
    have e : (planeGroup P).map (Θ.comp (MulAut.conj γ).toMonoidHom) =
        (planeGroup (P.map (Matrix.mulVecLin (mat m (GaloisField 3 1) γ)))).map Θ := by
      rw [planeGroup_map_conj, Subgroup.map_map]
    rw [e]
    exact h.plane_mem _ (isHyperbolicPlane_map γ hP)
  members := fun M hM hML hMc => by
    obtain ⟨P, hP, hMP⟩ := h.members M hM hML hMc
    refine ⟨P.map (Matrix.mulVecLin (mat m (GaloisField 3 1) γ⁻¹)),
      isHyperbolicPlane_map γ⁻¹ hP, ?_⟩
    have e : (planeGroup (P.map (Matrix.mulVecLin (mat m (GaloisField 3 1) γ⁻¹)))).map
        (Θ.comp (MulAut.conj γ).toMonoidHom) = (planeGroup P).map Θ := by
      rw [← Subgroup.map_map, ← planeGroup_map_conj, ← Submodule.map_comp]
      have : (Matrix.mulVecLin (mat m (GaloisField 3 1) γ)).comp
          (Matrix.mulVecLin (mat m (GaloisField 3 1) γ⁻¹)) = LinearMap.id :=
        LinearMap.ext fun v => by
          simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, LinearMap.id_apply]
          exact Models.SymplecticPairs.mulVec_mulVec_inv γ v
      rw [this, Submodule.map_id]
    rw [e, hMP]

end CFSG.ClassicalInvolution.Q3.Q3V.Frame
