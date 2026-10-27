module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotFieldNormalize

public section

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Quasithin (perfectCore)

section Conj

variable (K : Type) [Field K]

theorem map_conj_rep_levi_high (N : E8Neighbour) :
    (E8Neighbour.high.levi K).map (MulAut.conj (N.rep K)).toMonoidHom = N.levi K := by
  rw [E8Neighbour.levi_high]
  exact map_conj_rep_e7Levi N

@[expose] noncomputable def highLeviConjEquiv (N : E8Neighbour) :
    ↥(E8Neighbour.high.levi K) ≃* ↥(N.levi K) :=
  ((MulAut.conj (N.rep K)).subgroupMap (E8Neighbour.high.levi K)).trans
    (MulEquiv.subgroupCongr (map_conj_rep_levi_high K N))

variable {K}

theorem coe_highLeviConjEquiv (N : E8Neighbour) (g : E8Neighbour.high.levi K) :
    (((highLeviConjEquiv K N g : N.levi K) : adjointGroup .E8 K) : ModGL .E8 K) =
      (N.rep K : ModGL .E8 K) * ((g : adjointGroup .E8 K) : ModGL .E8 K) *
        (N.rep K : ModGL .E8 K)⁻¹ :=
  rfl

theorem baseChangeGL_weylElt_one_E8 {k : Type} [Field k] (ι : k →+* K) (i : Fin (Tag.rank .E8)) :
    baseChangeGL ι (weylElt .E8 k i 1) = weylElt .E8 K i 1 := by
  rw [CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul, map_mul, map_mul, baseChangeGL_xUnit,
    baseChangeGL_yUnit, CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul]
  simp

theorem baseChangeGL_rep {k : Type} [Field k] (ι : k →+* K) (N : E8Neighbour) :
    baseChangeGL ι (N.rep k : ModGL .E8 k) = (N.rep K : ModGL .E8 K) := by
  rw [E8Neighbour.coe_rep, E8Neighbour.coe_rep, map_list_prod, List.map_map]
  congr 1
  exact List.map_congr_left fun i _ => baseChangeGL_weylElt_one_E8 ι i

theorem leviBaseChange_highLeviConjEquiv {k : Type} [Field k] (ι : k →+* K) (N : E8Neighbour)
    (x : E8Neighbour.high.levi k) :
    leviBaseChange ι N (highLeviConjEquiv k N x) =
      highLeviConjEquiv K N (leviBaseChange ι .high x) := by
  refine Subtype.ext (Subtype.ext ?_)
  rw [coe_leviBaseChange, coe_highLeviConjEquiv, coe_highLeviConjEquiv, map_mul, map_mul, map_inv,
    baseChangeGL_rep, coe_leviBaseChange]

variable {σ : K ≃+* K} {G : Type} [Group G] [Finite G] {L : Subgroup G}
  {e : L ≃* adjointGroup .E8 (fixSubfield σ)}

variable (e) in
@[expose] noncomputable def neighbourCoreConjEquiv (N : E8Neighbour) :
    ↥(neighbourCore e .high) ≃* ↥(neighbourCore e N) :=
  ((MulAut.conj ((e.symm (N.rep (fixSubfield σ)) : L) : G)).subgroupMap
    (neighbourCore e .high)).trans (MulEquiv.subgroupCongr (neighbourCore_eq_map_conj e N).symm)

@[expose] noncomputable def FieldNeighbourIso.toNeighbour (h : FieldNeighbourIso σ e .high)
    (N : E8Neighbour) : FieldNeighbourIso σ e N where
  Φ := ((highLeviConjEquiv K N).symm.trans h.Φ).trans (neighbourCoreConjEquiv e N)
  fix x := by
    obtain ⟨x₀, rfl⟩ := (highLeviConjEquiv (fixSubfield σ) N).surjective x
    change ((e.symm (N.rep (fixSubfield σ)) : L) : G) *
        (h.Φ ((highLeviConjEquiv K N).symm (leviInclusion σ N
          (highLeviConjEquiv (fixSubfield σ) N x₀))) : G) *
          ((e.symm (N.rep (fixSubfield σ)) : L) : G)⁻¹ =
      ((e.symm (N.rep (fixSubfield σ) * (x₀ : adjointGroup .E8 (fixSubfield σ)) *
        (N.rep (fixSubfield σ))⁻¹) : L) : G)
    rw [leviInclusion, leviBaseChange_highLeviConjEquiv, MulEquiv.symm_apply_apply, ← leviInclusion,
      h.fix x₀, map_mul, map_mul, map_inv, L.coe_mul, L.coe_mul, L.coe_inv]

end Conj

section OwnLevi

variable {K : Type} [Field K] {σ : K ≃+* K} {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* adjointGroup .E8 (fixSubfield σ)}

theorem FieldNeighbourIso.map_conj_of_mem {N : E8Neighbour} (h : FieldNeighbourIso σ e N)
    (y : N.levi (fixSubfield σ)) (x : N.levi K) :
    ((h.Φ (leviInclusion σ N y * x * (leviInclusion σ N y)⁻¹) : neighbourCore e N) : G) =
      ((e.symm (y : adjointGroup .E8 (fixSubfield σ)) : L) : G) * (h.Φ x : G) *
        ((e.symm (y : adjointGroup .E8 (fixSubfield σ)) : L) : G)⁻¹ := by
  rw [map_mul, map_mul, map_inv, coe_mul, coe_mul, coe_inv, h.fix y]

end OwnLevi

section Twist

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* adjointGroup .E8 (fixSubfield σ)}

variable (K) in
theorem finite_levi (N : E8Neighbour) : Finite (N.levi K) :=
  have : Finite (ModGL .E8 K) := finite_modGL
  inferInstance

@[expose] noncomputable def leviEntrywiseEquiv (ρ : K ≃+* K) (N : E8Neighbour) :
    N.levi K ≃* N.levi K :=
  have := finite_levi K N
  MulEquiv.ofBijective (leviBaseChange (ρ : K →+* K) N)
    ⟨leviBaseChange_injective _ N, Finite.surjective_of_injective (leviBaseChange_injective _ N)⟩

theorem coe_leviEntrywiseEquiv (ρ : K ≃+* K) (N : E8Neighbour) (x : N.levi K) :
    (((leviEntrywiseEquiv ρ N x : N.levi K) : adjointGroup .E8 K) : ModGL .E8 K) =
      baseChangeGL (ρ : K →+* K) ((x : adjointGroup .E8 K) : ModGL .E8 K) :=
  rfl

@[expose] noncomputable def FieldNeighbourIso.twist {N : E8Neighbour}
    (h : FieldNeighbourIso σ e N) (ρ : K ≃+* K) (hρ : ∀ c : fixSubfield σ, ρ c = c) :
    FieldNeighbourIso σ e N where
  Φ := (leviEntrywiseEquiv ρ N).trans h.Φ
  fix x := by
    have hx : leviEntrywiseEquiv ρ N (leviInclusion σ N x) = leviInclusion σ N x := by
      refine Subtype.ext (Subtype.ext ?_)
      have hcomp : (ρ : K →+* K).comp (fixSubfield σ).subtype = (fixSubfield σ).subtype :=
        RingHom.ext fun c => hρ c
      rw [coe_leviEntrywiseEquiv, coe_leviInclusion, F4Pilot.baseChangeGL_baseChangeGL, hcomp]
    rw [MulEquiv.trans_apply, hx]
    exact h.fix x

theorem FieldNeighbourIso.twist_apply {N : E8Neighbour} (h : FieldNeighbourIso σ e N)
    (ρ : K ≃+* K) (hρ : ∀ c : fixSubfield σ, ρ c = c) (x : N.levi K) :
    (h.twist ρ hρ).Φ x = h.Φ (leviEntrywiseEquiv ρ N x) :=
  rfl

end Twist

end CFSG.SeitzReduction.E8Pilot
