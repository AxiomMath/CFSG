module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Swap.Factors
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Swap.Normalize

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Swap

open Module CFSG.EvenSporadicStandard.HNRecog.Fpf

variable {V V' : Type} [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup V'] [Module (ZMod 2) V']

@[expose] def transport (a : V ≃ₗ[ZMod 2] V') (b : V ≃ₗ[ZMod 2] V) : V' ≃ₗ[ZMod 2] V' :=
  a.symm.trans (b.trans a)

theorem transport_apply (a : V ≃ₗ[ZMod 2] V') (b : V ≃ₗ[ZMod 2] V) (v : V') :
    transport a b v = a (b (a.symm v)) := rfl

private theorem transport_symm_apply (a : V ≃ₗ[ZMod 2] V') (b : V ≃ₗ[ZMod 2] V) (v : V') :
    (transport a b)⁻¹ v = a (b⁻¹ (a.symm v)) := by
  change (transport a b).symm v = a (b.symm (a.symm v))
  rw [transport, LinearEquiv.trans_symm, LinearEquiv.trans_symm, LinearEquiv.symm_symm]
  rfl

theorem transport_mul_self (a : V ≃ₗ[ZMod 2] V') {b : V ≃ₗ[ZMod 2] V} (hb : b * b = 1) :
    transport a b * transport a b = 1 := by
  ext v
  rw [LinearEquiv.mul_apply, transport_apply, transport_apply,
    LinearEquiv.symm_apply_apply]
  have hbb : b (b (a.symm v)) = a.symm v := by
    have := congrArg (fun f : V ≃ₗ[ZMod 2] V => f (a.symm v)) hb
    simpa [LinearEquiv.mul_apply] using this
  rw [hbb, LinearEquiv.apply_symm_apply]
  rfl

theorem isometry_transport {B : LinearMap.BilinForm (ZMod 2) V} {B' : LinearMap.BilinForm (ZMod 2) V'}
    (a : V ≃ₗ[ZMod 2] V') (hBa : ∀ x y, B' (a x) (a y) = B x y) {b : V ≃ₗ[ZMod 2] V}
    (hBb : ∀ x y, B (b x) (b y) = B x y) :
    ∀ x y, B' (transport a b x) (transport a b y) = B' x y := by
  intro x y
  rw [transport_apply, transport_apply, hBa, hBb, ← hBa, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

theorem finrank_range_transport (a : V ≃ₗ[ZMod 2] V') (b : V ≃ₗ[ZMod 2] V) :
    finrank (ZMod 2) (LinearMap.range ((transport a b : V' →ₗ[ZMod 2] V') + 1)) =
      finrank (ZMod 2) (LinearMap.range ((b : V →ₗ[ZMod 2] V) + 1)) := by
  have hmap : ((transport a b : V' →ₗ[ZMod 2] V') + 1) =
      (a : V →ₗ[ZMod 2] V').comp
        (((b : V →ₗ[ZMod 2] V) + 1).comp (a.symm : V' →ₗ[ZMod 2] V)) := by
    ext v
    show transport a b v + v = a (b (a.symm v) + a.symm v)
    rw [transport_apply, LinearEquiv.map_add, LinearEquiv.apply_symm_apply]
  rw [hmap, LinearMap.range_comp, LinearMap.range_comp,
    LinearMap.range_eq_top.mpr (a.symm).surjective, Submodule.map_top]
  exact LinearEquiv.finrank_map_eq a _

theorem swapsFactors_of_aut (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) (b : V ≃ₗ[ZMod 2] V)
    (s : A5 × A5 ≃* A5 × A5) (hs : SwapsFactorsAut s) (hb : ∀ g, b * σ g * b⁻¹ = σ (s g)) :
    SwapsFactors σ b := by
  constructor
  · intro x
    obtain ⟨y, hy⟩ := hs.1 x
    exact ⟨y, by rw [hb, hy]⟩
  · intro y
    obtain ⟨x, hx⟩ := hs.2 y
    exact ⟨x, by rw [hb, hx]⟩

theorem swapsFactors_transport (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) (σ' : A5 × A5 →* (V' ≃ₗ[ZMod 2] V'))
    (a : V ≃ₗ[ZMod 2] V') (ψ : A5 × A5 ≃* A5 × A5) (hψ : ∀ g v, a (σ g v) = σ' (ψ g) (a v))
    (b₀ : V ≃ₗ[ZMod 2] V) (s : A5 × A5 ≃* A5 × A5) (hs : SwapsFactorsAut s)
    (hb₀ : ∀ g, b₀ * σ g * b₀⁻¹ = σ (s g)) : SwapsFactors σ' (transport a b₀) := by
  have hsigma : ∀ g w, σ' g w = a (σ (ψ.symm g) (a.symm w)) := by
    intro g w
    rw [hψ (ψ.symm g) (a.symm w), MulEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have hs'g : ∀ g', (ψ.symm.trans (s.trans ψ)) g' = ψ (s (ψ.symm g')) := by
    intro g'
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply]
  have hconj : ∀ g', transport a b₀ * σ' g' * (transport a b₀)⁻¹ =
      σ' ((ψ.symm.trans (s.trans ψ)) g') := by
    intro g'
    ext v'
    calc
      (transport a b₀ * σ' g' * (transport a b₀)⁻¹) v'
          = transport a b₀ (σ' g' ((transport a b₀)⁻¹ v')) := by
            rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
      _ = transport a b₀
            (a (σ (ψ.symm g') (a.symm ((transport a b₀)⁻¹ v')))) := by
            rw [hsigma g']
      _ = a (b₀ (σ (ψ.symm g') (b₀⁻¹ (a.symm v')))) := by
            rw [transport_apply, LinearEquiv.symm_apply_apply, transport_symm_apply,
              LinearEquiv.symm_apply_apply]
      _ = a ((b₀ * σ (ψ.symm g') * b₀⁻¹) (a.symm v')) := by
            rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
      _ = a (σ (s (ψ.symm g')) (a.symm v')) := by rw [hb₀ (ψ.symm g')]
      _ = σ' (ψ (s (ψ.symm g'))) v' := by
            rw [hψ (s (ψ.symm g')) (a.symm v'), LinearEquiv.apply_symm_apply]
      _ = σ' ((ψ.symm.trans (s.trans ψ)) g') v' := by rw [hs'g g']
  exact swapsFactors_of_aut σ' (transport a b₀) (ψ.symm.trans (s.trans ψ)) (hs.conj ψ) hconj

theorem intertwine_of_surjective {L L' : Type} [Group L] [Group L'] (θ : L →* A5 × A5)
    (hθ : Function.Surjective θ) (θ' : L' →* A5 × A5)
    (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) (σ' : A5 × A5 →* (V' ≃ₗ[ZMod 2] V'))
    (ρ : L →* (V ≃ₗ[ZMod 2] V)) (ρ' : L' →* (V' ≃ₗ[ZMod 2] V'))
    (hσ : ∀ l, σ (θ l) = ρ l) (hσ' : ∀ l, σ' (θ' l) = ρ' l) (α : L ≃* L')
    (a : V ≃ₗ[ZMod 2] V') (ha : ∀ l v, a (ρ l v) = ρ' (α l) (a v))
    (ψ : A5 × A5 ≃* A5 × A5) (hψ : ∀ l, ψ (θ l) = θ' (α l)) :
    ∀ g v, a (σ g v) = σ' (ψ g) (a v) := by
  intro g v
  obtain ⟨l, rfl⟩ := hθ g
  rw [hσ l, ha l v, ← hσ' (α l), ← hψ l]

theorem exists_mulEquiv_of_ker {L L' G G' : Type} [Group L] [Group L'] [Group G] [Group G']
    (θ : L →* G) (θ' : L' →* G') (hθ : Function.Surjective θ) (hθ' : Function.Surjective θ')
    (α : L ≃* L') (hker : ∀ l, θ l = 1 ↔ θ' (α l) = 1) :
    ∃ ψ : G ≃* G', ∀ l, ψ (θ l) = θ' (α l) := by
  have hmap : θ.ker.map (α : L →* L') = θ'.ker := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [MonoidHom.mem_ker] at hy ⊢
      exact (hker y).mp hy
    · intro hx
      rw [MonoidHom.mem_ker] at hx
      refine ⟨α.symm x, ?_, α.apply_symm_apply x⟩
      rw [MonoidHom.mem_ker]
      exact (hker (α.symm x)).mpr (by rw [α.apply_symm_apply]; exact hx)
  let e : L ⧸ θ.ker ≃* G := QuotientGroup.quotientKerEquivOfSurjective θ hθ
  let e' : L' ⧸ θ'.ker ≃* G' := QuotientGroup.quotientKerEquivOfSurjective θ' hθ'
  let c : L ⧸ θ.ker ≃* L' ⧸ θ'.ker := QuotientGroup.congr θ.ker θ'.ker α hmap
  refine ⟨e.symm.trans (c.trans e'), ?_⟩
  intro l
  have he : e (QuotientGroup.mk l) = θ l := QuotientGroup.kerLift_mk θ l
  have he1 : e.symm (θ l) = QuotientGroup.mk l := by rw [← he, MulEquiv.symm_apply_apply]
  have hc : c (QuotientGroup.mk l) = QuotientGroup.mk (α l) :=
    QuotientGroup.congr_mk θ.ker θ'.ker α hmap l
  have he' : e' (QuotientGroup.mk (α l)) = θ' (α l) := QuotientGroup.kerLift_mk θ' (α l)
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, he1, hc, he']

end CFSG.EvenSporadicStandard.HNRecog.Swap
