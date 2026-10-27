module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L107bAux
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Comb

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem sec122_theta {φ : (Fin 5 → ZMod 2) → G} {B X : Subgroup G}
    (hinj : ∀ v w, IsEvenVec v → IsEvenVec w → φ v = φ w → v = w)
    (hB : ∀ x, x ∈ B ↔ ∃ v, IsEvenVec v ∧ φ v = x)
    (hact : ∀ x ∈ X, ∃ σ : Equiv.Perm (Fin 5),
      ∀ v, IsEvenVec v → x * φ v * x⁻¹ = φ (permVec σ v))
    (hker : ∀ x ∈ X, (∀ b ∈ B, x * b = b * x) → x = 1)
    (hsurj : ∀ σ ∈ alternatingGroup (Fin 5), ∃ x ∈ X,
      ∀ v, IsEvenVec v → x * φ v * x⁻¹ = φ (permVec σ v)) :
    (Nonempty (↥X ≃* ↥(alternatingGroup (Fin 5))) ∧
        ∀ x ∈ X, ∃ σ ∈ alternatingGroup (Fin 5),
          ∀ v, IsEvenVec v → x * φ v * x⁻¹ = φ (permVec σ v)) ∨
      (Nonempty (↥X ≃* Equiv.Perm (Fin 5)) ∧
        ∀ σ : Equiv.Perm (Fin 5), ∃ x ∈ X,
          ∀ v, IsEvenVec v → x * φ v * x⁻¹ = φ (permVec σ v)) := by
  let θ : ↥X → Equiv.Perm (Fin 5) := fun x => Classical.choose (hact x x.2)
  have hθact : ∀ x : ↥X, ∀ v : Fin 5 → ZMod 2, IsEvenVec v →
      (x : G) * φ v * (x : G)⁻¹ = φ (permVec (θ x) v) :=
    fun x => Classical.choose_spec (hact x x.2)
  have huniq : ∀ σ σ' : Equiv.Perm (Fin 5),
      (∀ v, IsEvenVec v → φ (permVec σ v) = φ (permVec σ' v)) → σ = σ' := by
    intro σ σ' h
    refine permVec_injective_five fun v hv => ?_
    exact hinj _ _ (isEvenVec_permVec σ hv) (isEvenVec_permVec σ' hv) (h v hv)
  have hθ_mul : ∀ x y : ↥X, θ (x * y) = θ x * θ y := by
    intro x y
    apply huniq
    intro v hv
    rw [permVec_mul]
    have hxy := hθact (x * y) v hv
    have hx := hθact x (permVec (θ y) v) (isEvenVec_permVec (θ y) hv)
    have hy := hθact y v hv
    rw [Subgroup.coe_mul] at hxy
    rw [← hxy]
    calc (x : G) * (y : G) * φ v * ((x : G) * (y : G))⁻¹
        = (x : G) * ((y : G) * φ v * (y : G)⁻¹) * (x : G)⁻¹ := by group
      _ = (x : G) * φ (permVec (θ y) v) * (x : G)⁻¹ := by rw [hy]
      _ = φ (permVec (θ x) (permVec (θ y) v)) := hx
  let Θ : ↥X →* Equiv.Perm (Fin 5) := MonoidHom.mk' θ hθ_mul
  have hΘinj : Function.Injective Θ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    apply Subtype.ext
    apply hker (x : G) x.2
    intro b hb
    obtain ⟨v, hv, rfl⟩ := (hB b).1 hb
    have hθx : θ x = 1 := by simpa [Θ] using hx
    have h := hθact x v hv
    rw [hθx, permVec_one] at h
    calc (x : G) * φ v = (x : G) * φ v * (x : G)⁻¹ * (x : G) := by group
      _ = φ v * (x : G) := by rw [h]
  have halt_le : alternatingGroup (Fin 5) ≤ Θ.range := by
    intro σ hσ
    obtain ⟨x, hxX, hactn⟩ := hsurj σ hσ
    rw [MonoidHom.mem_range]
    refine ⟨⟨x, hxX⟩, ?_⟩
    apply huniq
    intro v hv
    change φ (permVec (θ ⟨x, hxX⟩) v) = φ (permVec σ v)
    rw [← hθact ⟨x, hxX⟩ v hv, hactn v hv]
  rcases eq_alt_or_top_five (X := Θ.range) halt_le with hrange | hrange
  · left
    refine ⟨⟨(MonoidHom.ofInjective hΘinj).trans (MulEquiv.subgroupCongr hrange)⟩, ?_⟩
    intro x hxX
    refine ⟨θ ⟨x, hxX⟩, ?_, hθact ⟨x, hxX⟩⟩
    have hmem : Θ ⟨x, hxX⟩ ∈ Θ.range := MonoidHom.mem_range.mpr ⟨⟨x, hxX⟩, rfl⟩
    rw [hrange] at hmem
    simpa [Θ] using hmem
  · right
    refine ⟨⟨(MonoidHom.ofInjective hΘinj).trans
      ((MulEquiv.subgroupCongr hrange).trans (Subgroup.topEquiv))⟩, ?_⟩
    intro σ
    have hσmem : σ ∈ Θ.range := hrange.symm ▸ Subgroup.mem_top σ
    rw [MonoidHom.mem_range] at hσmem
    obtain ⟨y, hy⟩ := hσmem
    refine ⟨(y : G), y.2, ?_⟩
    intro v hv
    rw [← hy]
    simpa [Θ] using hθact y v hv

end CFSG.OddStandard.SmallF3.Omega
