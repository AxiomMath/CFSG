module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM1C2B
public import CFSG.RankThree.Classical.SteinbergBJOrthogonalDerivedCentralizer

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E3S3O

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KCOrthogonalDescent CFSG.RankThree.PartOne.KCOrthogonalAut
  CFSG.LocalAnalysis.ComponentInitial

section Aux

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

section Three

variable [Finite K]

omit [Finite K] in
theorem three_eq_zero_of_card_three (hK : Nat.card K = 3) : (3 : K) = 0 := by
  have h := card_nsmul_eq_zero' (G := K) (x := 1)
  rw [hK, nsmul_eq_mul, mul_one] at h
  exact_mod_cast h

omit [Finite K] in
theorem two_ne_zero_of_card_three (hK : Nat.card K = 3) : (2 : K) ≠ 0 := by
  intro h
  have h1 : (1 : K) = 0 := by linear_combination three_eq_zero_of_card_three hK - h
  exact one_ne_zero h1

theorem eq_zero_or_one_or_neg_one_of_card_three (hK : Nat.card K = 3) (c : K) :
    c = 0 ∨ c = 1 ∨ c = -1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have h1 : (1 : K) ≠ -1 := fun h =>
    two_ne_zero_of_card_three hK (by linear_combination h)
  have hcard : ({0, 1, -1} : Finset K).card = Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, hK]
    exact Finset.card_eq_three.2 ⟨0, 1, -1, zero_ne_one, by simp, h1, rfl⟩
  have h := (Finset.eq_univ_of_card _ hcard) ▸ Finset.mem_univ c
  simpa using h

theorem ringEquiv_apply_of_card_three (hK : Nat.card K = 3) (σ : K ≃+* K) (c : K) : σ c = c := by
  rcases eq_zero_or_one_or_neg_one_of_card_three hK c with rfl | rfl | rfl
  · exact map_zero σ
  · exact map_one σ
  · rw [map_neg, map_one]

theorem exists_linear_of_induced (hK : Nat.card K = 3) {Q : QuadraticForm K V}
    {α : MulAut (ProjOrthDerived Q)} (h : InducedBySemilinear Q α) :
    ∃ (g : V ≃ₗ[K] V) (μ : K), μ ≠ 0 ∧ (∀ v, Q (g v) = μ * Q v) ∧
      ∀ g₁ g₁' : orthDerived Q,
        (∀ v, (g₁' : V ≃ₗ[K] V) v = g ((g₁ : V ≃ₗ[K] V) (g.symm v))) →
          α (QuotientGroup.mk g₁) = QuotientGroup.mk g₁' := by
  obtain ⟨σ, F, hF, μ, hμ, hQ, hind⟩ := h
  have hσ := ringEquiv_apply_of_card_three hK σ
  refine ⟨F.toLinearEquiv fun c v => by rw [hF, hσ], μ, hμ, fun v => ?_, hind⟩
  rw [← hσ (Q v)]
  exact hQ v

end Three

theorem conj_mem_orthDerived {Q : QuadraticForm K V} {g : V ≃ₗ[K] V} {μ : K} (hμ : μ ≠ 0)
    (hg : ∀ v, Q (g v) = μ * Q v) {h : V ≃ₗ[K] V} (hh : h ∈ orthDerived Q) :
    g * h * g⁻¹ ∈ orthDerived Q := by
  rw [← map_orthDerived g (Units.mk0 μ hμ) hg]
  exact ⟨h, hh, LinearEquiv.ext fun v => rfl⟩

theorem orthElementaryMap_cube {Q : QuadraticForm K V} (h3 : (3 : K) = 0) {u v : V}
    (hu : Q u = 0) (hv : polar Q u v = 0) (x : V) :
    orthElementaryMap Q u v (orthElementaryMap Q u v (orthElementaryMap Q u v x)) = x := by
  obtain ⟨h0, hadd, -, -⟩ := orthogonal_elementary_addition Q hu hv hv
  have hv2 : polar Q u (v + v) = 0 := by rw [polar_add_right, hv, add_zero]
  obtain ⟨-, hadd2, -, -⟩ := orthogonal_elementary_addition Q hu hv hv2
  have h3v : v + (v + v) = 0 := by
    rw [show v + (v + v) = (3 : K) • v by module, h3, zero_smul]
  change ((orthElementaryMap Q u v).comp ((orthElementaryMap Q u v).comp
    (orthElementaryMap Q u v))) x = x
  rw [hadd, hadd2, h3v, h0, LinearMap.id_apply]

theorem exists_sq_eq_smul [Finite K] [FiniteDimensional K V] (hK : Nat.card K = 3)
    {Q : QuadraticForm K V} (hQ : (polarBilin Q).Nondegenerate) (hdim : 3 ≤ finrank K V)
    {S : Type} [Group S] (θ : orthDerived Q →* S)
    (hker : θ.ker = (scalars K V).subgroupOf (orthDerived Q)) {γ : MulAut S} (hγ : γ * γ = 1)
    {g : V ≃ₗ[K] V} (hg : ∀ h ∈ orthDerived Q, g * h * g⁻¹ ∈ orthDerived Q)
    (hact : ∀ h : orthDerived Q, γ (θ h) = θ ⟨g * h * g⁻¹, hg h h.2⟩) :
    ∃ c : K, ∀ v, g (g v) = c • v := by
  have h3 := three_eq_zero_of_card_three hK
  have hsc : ∀ h : orthDerived Q, ∃ ζ : K, ∀ v,
      g (g ((h : V ≃ₗ[K] V) (g.symm (g.symm v)))) = ζ • (h : V ≃ₗ[K] V) v := by
    intro h
    set h' : orthDerived Q := ⟨g * h * g⁻¹, hg h h.2⟩ with hh'
    set h'' : orthDerived Q := ⟨g * (h' : V ≃ₗ[K] V) * g⁻¹, hg h' h'.2⟩ with hh''
    have hθ : θ h'' = θ h := by
      rw [← hact h', ← hact h, ← MulAut.mul_apply, hγ, MulAut.one_apply]
    have hmem : h'' * h⁻¹ ∈ θ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hθ, mul_inv_cancel]
    rw [hker, Subgroup.mem_subgroupOf, mem_scalars] at hmem
    obtain ⟨ζ, hζ⟩ := hmem
    refine ⟨ζ, fun v => ?_⟩
    have e1 := hζ ((h : V ≃ₗ[K] V) v)
    change (h'' : V ≃ₗ[K] V) ((h : V ≃ₗ[K] V).symm ((h : V ≃ₗ[K] V) v)) = _ at e1
    rw [LinearEquiv.symm_apply_apply] at e1
    exact e1
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  obtain ⟨w₀, hw₀⟩ := exists_ne (0 : V)
  have hcomm : ∀ E ∈ orthDerived Q, (∀ v, E (E (E v)) = v) →
      ∀ v, g (g (E v)) = E (g (g v)) := by
    intro E hE hE3 v
    obtain ⟨ζ, hζ⟩ := hsc ⟨E, hE⟩
    change ∀ v, g (g (E (g.symm (g.symm v)))) = ζ • E v at hζ
    have hy : ∀ w : V, (ζ * ζ * ζ) • w = w := by
      intro w
      have e2 : g (g (E (g.symm (g.symm (g (g (E (g.symm (g.symm (g (g (E (g.symm
          (g.symm w)))))))))))))) = w := by
        simp only [LinearEquiv.symm_apply_apply, hE3, LinearEquiv.apply_symm_apply]
      rw [hζ, hζ, hζ, map_smul, map_smul, map_smul, smul_smul, smul_smul, hE3] at e2
      exact e2
    have hζ1 : ζ = 1 := by
      have h1 : ζ * ζ * ζ = 1 := by
        have e : (ζ * ζ * ζ - 1) • w₀ = 0 := by rw [sub_smul, hy, one_smul, sub_self]
        rcases smul_eq_zero.mp e with h | h
        · exact sub_eq_zero.mp h
        · exact absurd h hw₀
      have h2 : (ζ - 1) ^ 3 = 0 := by linear_combination h1 + (ζ - ζ ^ 2) * h3
      exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h2)
    have := hζ (g (g v))
    rwa [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, hζ1, one_smul] at this
  obtain ⟨-, ⟨P⟩, hP⟩ :=
    CFSG.RankThree.Classical.finite_orthogonal_derived_natural_linear_centralizer_scalar
      (by omega) Q hQ hdim
  obtain ⟨hmemP, hcrit⟩ := hP P
  have hR : ∀ u : V, Q u = 0 → ∀ w : V, polar Q u w = 0 →
      (∃ E ∈ orthDerived Q, (E : V →ₗ[K] V) = orthElementaryMap Q u w) →
      ((g * g : V ≃ₗ[K] V) : V →ₗ[K] V) ∘ₗ orthElementaryMap Q u w =
        orthElementaryMap Q u w ∘ₗ ((g * g : V ≃ₗ[K] V) : V →ₗ[K] V) := by
    rintro u hu w hw ⟨E, hE, hER⟩
    have hE3 : ∀ v, E (E (E v)) = v := fun v => by
      have h1 := orthElementaryMap_cube h3 hu hw v
      rwa [← hER] at h1
    refine LinearMap.ext fun v => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← hER]
    exact hcomm E hE hE3 v
  obtain ⟨c, hc⟩ := hcrit _ fun w hw a => by
    have hw' := HypPair.mem_perp.mp hw
    have he : polar Q P.e (a • w) = 0 := by rw [polar_smul_right, hw'.1, smul_zero]
    have hf : polar Q P.f (a • w) = 0 := by rw [polar_smul_right, hw'.2, smul_zero]
    exact ⟨hR _ P.Q_e _ he (hmemP w hw a).1, hR _ P.Q_f _ hf (hmemP w hw a).2⟩
  exact ⟨c, fun v => LinearMap.congr_fun hc v⟩

end Aux

theorem exists_similarity_of_involutive {K V S : Type} [Field K] [Finite K] (hK : Nat.card K = 3)
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate) (hdim : 7 ≤ finrank K V) [Group S]
    (θ : orthDerived Q →* S) (hθ : Function.Surjective θ)
    (hker : θ.ker = (scalars K V).subgroupOf (orthDerived Q)) (α : MulAut S) (hα : α * α = 1) :
    ∃ (β : MulAut S) (g : V ≃ₗ[K] V) (μ : K), μ ≠ 0 ∧ (∀ v, Q (g v) = μ * Q v) ∧
      ∃ hg : ∀ h ∈ orthDerived Q, g * h * g⁻¹ ∈ orthDerived Q,
        (∃ c : K, ∀ v, g (g v) = c • v) ∧
          ∀ h : orthDerived Q, (β * α * β⁻¹) (θ h) = θ ⟨g * h * g⁻¹, hg h h.2⟩ := by
  classical
  set ψ : ProjOrthDerived Q ≃* S := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective θ hθ) with hψdef
  have hψ : ∀ h : orthDerived Q, ψ (QuotientGroup.mk h) = θ h := fun h => rfl
  obtain ⟨β₀, hβ₀⟩ := exists_conj_induced_of_seven_le Q hQ hdim ((MulAut.congr ψ).symm α)
    (by rw [← map_mul, hα, map_one])
  obtain ⟨g, μ, hμ, hgQ, hind⟩ := exists_linear_of_induced hK hβ₀
  have hg : ∀ h ∈ orthDerived Q, g * h * g⁻¹ ∈ orthDerived Q := fun h hh =>
    conj_mem_orthDerived hμ hgQ hh
  have hconj : MulAut.congr ψ β₀ * α * (MulAut.congr ψ β₀)⁻¹ =
      MulAut.congr ψ (β₀ * (MulAut.congr ψ).symm α * β₀⁻¹) := by
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have hact : ∀ h : orthDerived Q, (MulAut.congr ψ β₀ * α * (MulAut.congr ψ β₀)⁻¹) (θ h) =
      θ ⟨g * h * g⁻¹, hg h h.2⟩ := by
    intro h
    rw [hconj, ← hψ, ← hψ]
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    exact congrArg ψ (hind h ⟨_, hg h h.2⟩ fun v => rfl)
  have hinv : MulAut.congr ψ β₀ * α * (MulAut.congr ψ β₀)⁻¹ *
      (MulAut.congr ψ β₀ * α * (MulAut.congr ψ β₀)⁻¹) = 1 := by
    calc _ = MulAut.congr ψ β₀ * (α * α) * (MulAut.congr ψ β₀)⁻¹ := by group
      _ = 1 := by rw [hα, mul_one, mul_inv_cancel]
  exact ⟨MulAut.congr ψ β₀, g, μ, hμ, hgQ, hg,
    exists_sq_eq_smul hK hQ (by omega) θ hker hinv hg hact, hact⟩

end CFSG.ClassicalInvolution.Q3.TL4.E3S3O
