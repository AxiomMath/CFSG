module

public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieLTTwin

public section

open scoped MatrixGroups

namespace CFSG.CGT.PushingUpLit.SolKNA.LTAbs

open CFSG.CGT.PushingUpLit.SolKNA

theorem isQuasisimple_quotient_oddCore {E : Type*} [Group E] [Finite E]
    (h : CFSG.IsQuasisimple E) :
    CFSG.Open.IsQuasisimple (E ⧸ CFSG.Open.classicalInvolutionOddCore E) := by
  have h' : CFSG.Open.IsQuasisimple E := ⟨h.1.commutator_eq_top, h.2.1⟩
  exact CFSG.ComponentClassification.Quasisimple.central_quotient h' _
    (CFSG.ClassicalInvolution.Balance.oddCore_le_center_of_isQuasisimple h')

theorem component_of_normal {K X : Type*} [Group K] [Group X] [Finite X] (ψ : K →* X)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center K) {i : K} {E₀ : Subgroup K}
    (hC : ∀ y ∈ E₀, y * i = i * y)
    (hN : ∀ a : K, a * i * a⁻¹ * i⁻¹ ∈ Subgroup.center K → ∀ y ∈ E₀, a * y * a⁻¹ ∈ E₀)
    (hq : CFSG.IsQuasisimple ↥(E₀.map ψ)) :
    ∃ E : Subgroup X, CFSG.Open.IsSubnormal E (Subgroup.centralizer ({ψ i} : Set X)) ∧
      CFSG.Open.IsQuasisimple (E ⧸ CFSG.Open.classicalInvolutionOddCore E) := by
  refine ⟨E₀.map ψ, ?_, isQuasisimple_quotient_oddCore hq⟩
  have hEC : E₀.map ψ ≤ Subgroup.centralizer ({ψ i} : Set X) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hC y hy]
  refine CFSG.Open.IsSubnormal.step hEC ?_ (CFSG.Open.IsSubnormal.refl _)
  rw [Subgroup.normal_subgroupOf_iff hEC]
  intro h x hh hx
  obtain ⟨y, hy, rfl⟩ := hh
  obtain ⟨a, rfl⟩ := hψ x
  have hx' := Subgroup.mem_centralizer_singleton_iff.mp hx
  have hcen : a * i * a⁻¹ * i⁻¹ ∈ Subgroup.center K := by
    apply hker
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [hx']
    group
  exact ⟨a * y * a⁻¹, hN a hcen y hy, by simp⟩

theorem isQuasisimple_map {K X : Type} [Group K] [Group X] (ψ : K →* X)
    (hker : ψ.ker ≤ Subgroup.center K) {E : Subgroup K}
    (hE : ∀ y ∈ E, y ∈ Subgroup.center K → y = 1) (hq : CFSG.IsQuasisimple ↥E) :
    CFSG.IsQuasisimple ↥(E.map ψ) := by
  have hinj : Function.Injective (ψ.subgroupMap E) := by
    intro u v h
    have h1 : ψ u = ψ v := congrArg Subtype.val h
    have h2 : (u : K)⁻¹ * v ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
    have h3 : (u : K)⁻¹ * v = 1 := hE _ (E.mul_mem (E.inv_mem u.2) v.2) (hker h2)
    exact Subtype.ext (inv_mul_eq_one.mp h3)
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (MulEquiv.ofBijective (ψ.subgroupMap E) ⟨hinj, ψ.subgroupMap_surjective E⟩) hq

theorem component_of_family {K X : Type} [Group K] [Group X] [Finite X] (ψ : K →* X)
    (hψ : Function.Surjective ψ) (hker : ψ.ker = Subgroup.center K) (𝓕 : Set (Subgroup K))
    (hsl2 : ∀ R ∈ 𝓕, Nonempty (R ≃* SL(2, GaloisField 3 1)))
    (hnc : ∀ R ∈ 𝓕, ∀ r ∈ R, (∀ y : K, r * y * r⁻¹ * y⁻¹ ∈ Subgroup.center K) → r = 1)
    {R₀ : Subgroup K} (hcls : ∀ R ∈ 𝓕, ∃ y : K, R = R₀.map (MulAut.conj y).toMonoidHom)
    {z₀ : K} (hz₀R : z₀ ∈ R₀) (hz₀2 : z₀ * z₀ = 1) (hz₀1 : z₀ ≠ 1)
    {E₀ : Subgroup K} (hC : ∀ y ∈ E₀, y * z₀ = z₀ * y)
    (hN : ∀ a : K, a * z₀ * a⁻¹ * z₀⁻¹ ∈ Subgroup.center K → ∀ y ∈ E₀, a * y * a⁻¹ ∈ E₀)
    (hq : CFSG.IsQuasisimple ↥E₀) (hE : ∀ y ∈ E₀, y ∈ Subgroup.center K → y = 1) :
    ∀ R ∈ 𝓕, ∀ t : X, t ∈ R.map ψ → orderOf t = 2 →
      ∃ E : Subgroup X, CFSG.Open.IsSubnormal E (Subgroup.centralizer ({t} : Set X)) ∧
        CFSG.Open.IsQuasisimple (E ⧸ CFSG.Open.classicalInvolutionOddCore E) := by
  intro R hR t ht ht2
  obtain ⟨y, -, rfl⟩ := LTTwin.involution_of_family ψ hker 𝓕 hsl2 hnc hcls hz₀R hz₀2 hz₀1 R hR t
    ht ht2
  have hconj : ∀ x : K, (MulAut.conj y).toMonoidHom x = y * x * y⁻¹ := fun x => rfl
  have hqy : CFSG.IsQuasisimple ↥(E₀.map (MulAut.conj y).toMonoidHom) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (E₀.equivMapOfInjective (MulAut.conj y).toMonoidHom (MulAut.conj y).injective) hq
  have hEy : ∀ u ∈ E₀.map (MulAut.conj y).toMonoidHom, u ∈ Subgroup.center K → u = 1 := by
    rintro _ ⟨e, he, rfl⟩ hu
    rw [hconj] at hu ⊢
    have hc : e ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff] at hu ⊢
      intro g
      have := hu (y * g * y⁻¹)
      have e1 : g * e = y⁻¹ * (y * g * y⁻¹ * (y * e * y⁻¹)) * y := by group
      have e2 : e * g = y⁻¹ * (y * e * y⁻¹ * (y * g * y⁻¹)) * y := by group
      rw [e1, e2, this]
    rw [hE e he hc]
    group
  refine component_of_normal ψ hψ hker.le (i := y * z₀ * y⁻¹)
    (E₀ := E₀.map (MulAut.conj y).toMonoidHom) ?_ ?_ (isQuasisimple_map ψ hker.le hEy hqy)
  · rintro _ ⟨e, he, rfl⟩
    rw [hconj]
    calc y * e * y⁻¹ * (y * z₀ * y⁻¹) = y * (e * z₀) * y⁻¹ := by group
      _ = y * (z₀ * e) * y⁻¹ := by rw [hC e he]
      _ = y * z₀ * y⁻¹ * (y * e * y⁻¹) := by group
  · rintro a ha _ ⟨e, he, rfl⟩
    have ha' : (y⁻¹ * a * y) * z₀ * (y⁻¹ * a * y)⁻¹ * z₀⁻¹ ∈ Subgroup.center K := by
      have := (inferInstance : (Subgroup.center K).Normal).conj_mem _ ha y⁻¹
      have e1 : y⁻¹ * (a * (y * z₀ * y⁻¹) * a⁻¹ * (y * z₀ * y⁻¹)⁻¹) * y⁻¹⁻¹ =
          (y⁻¹ * a * y) * z₀ * (y⁻¹ * a * y)⁻¹ * z₀⁻¹ := by group
      rwa [e1] at this
    refine ⟨(y⁻¹ * a * y) * e * (y⁻¹ * a * y)⁻¹, hN _ ha' e he, ?_⟩
    simp only [hconj]
    group

end CFSG.CGT.PushingUpLit.SolKNA.LTAbs
