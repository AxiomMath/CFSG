module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L107bAux
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Comb

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem sec123_perm_unique {φ : (Fin 5 → ZMod 2) → G}
    (hinj : ∀ v w, IsEvenVec v → IsEvenVec w → φ v = φ w → v = w) {x : G}
    {σ σ' : Equiv.Perm (Fin 5)} (h : ∀ v, IsEvenVec v → x * φ v * x⁻¹ = φ (permVec σ v))
    (h' : ∀ v, IsEvenVec v → x * φ v * x⁻¹ = φ (permVec σ' v)) : σ = σ' := by
  refine permVec_injective_five fun v hv => ?_
  exact hinj _ _ (isEvenVec_permVec σ hv) (isEvenVec_permVec σ' hv)
    ((h v hv).symm.trans (h' v hv))

theorem sec123_exists_hom {φ : (Fin 5 → ZMod 2) → G} {H : Subgroup G}
    (hinj : ∀ v w, IsEvenVec v → IsEvenVec w → φ v = φ w → v = w)
    (hact : ∀ x ∈ H, ∃ σ : Equiv.Perm (Fin 5),
      ∀ v, IsEvenVec v → x * φ v * x⁻¹ = φ (permVec σ v)) :
    ∃ Θ : ↥H →* Equiv.Perm (Fin 5), ∀ x : ↥H, ∀ v, IsEvenVec v →
      (x : G) * φ v * (x : G)⁻¹ = φ (permVec (Θ x) v) := by
  have huniq : ∀ σ σ' : Equiv.Perm (Fin 5),
      (∀ v, IsEvenVec v → φ (permVec σ v) = φ (permVec σ' v)) → σ = σ' := by
    intro σ σ' h
    refine permVec_injective_five fun v hv => ?_
    exact hinj _ _ (isEvenVec_permVec σ hv) (isEvenVec_permVec σ' hv) (h v hv)
  have hact' : ∀ x : G, ∃ σ : Equiv.Perm (Fin 5),
      x ∈ H → ∀ v, IsEvenVec v → x * φ v * x⁻¹ = φ (permVec σ v) := by
    intro x
    by_cases hx : x ∈ H
    · obtain ⟨σ, hσ⟩ := hact x hx
      exact ⟨σ, fun _ => hσ⟩
    · exact ⟨1, fun hx' => absurd hx' hx⟩
  choose θ hθ using hact'
  let Θ : ↥H →* Equiv.Perm (Fin 5) :=
    { toFun := fun x => θ x
      map_one' := by
        apply huniq
        intro v hv
        rw [permVec_one]
        simpa using (hθ 1 H.one_mem v hv).symm
      map_mul' := by
        intro x y
        apply huniq
        intro v hv
        rw [permVec_mul]
        have hxy := hθ ((x : G) * (y : G)) (H.mul_mem x.2 y.2) v hv
        rw [Subgroup.coe_mul]
        rw [← hxy]
        calc (x : G) * (y : G) * φ v * ((x : G) * (y : G))⁻¹
            = (x : G) * ((y : G) * φ v * (y : G)⁻¹) * (x : G)⁻¹ := by group
          _ = (x : G) * φ (permVec (θ (y : G)) v) * (x : G)⁻¹ := by
                rw [hθ (y : G) y.2 v hv]
          _ = φ (permVec (θ (x : G)) (permVec (θ (y : G)) v)) :=
                hθ (x : G) x.2 _ (isEvenVec_permVec _ hv) }
  exact ⟨Θ, fun x v hv => hθ (x : G) x.2 v hv⟩

end CFSG.OddStandard.SmallF3.Omega
