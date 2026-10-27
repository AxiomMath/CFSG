module

public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerSpAdapted
public import CFSG.ClassicalInvolution.SmallOrth.Orth3OddCoreAll

public section

namespace CFSG.ClassicalGroups.Orthogonal.Small

open QuadraticMap CFSG.ClassicalInvolution.Q3

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

structure AdaptedBasis (Q : QuadraticForm F V) (g : V ≃ₗ[F] V) (m : ℕ) where
  basis : Module.Basis (Fin m ⊕ Fin m) F V
  orth : ∀ i j, polar Q (basis i) (basis j) = if i = j then 1 else 0
  inr_eq : ∀ k, basis (Sum.inr k) = g (basis (Sum.inl k))

theorem linearIndependent_of_orthonormal {ι : Type} [Fintype ι] [DecidableEq ι]
    (β : LinearMap.BilinForm F V) (v : ι → V) (hv : ∀ i j, β (v i) (v j) = if i = j then 1 else 0) :
    LinearIndependent F v := by
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have := congrArg (β (v j)) hc
  simpa [map_sum, hv] using this

theorem even_finrank_of_sq_eq_neg_one [Finite F] [FiniteDimensional F V] (hF : Nat.card F = 3)
    {g : V ≃ₗ[F] V} (hg2 : ∀ x, g (g x) = -x) : ∃ m, Module.finrank F V = 2 * m := by
  have : Fintype F := Fintype.ofFinite F
  have h2 : (2 : F) ≠ 0 := by
    have := three_eq_zero_two_ne_zero_of_card_eq_three hF
    exact this.2
  set d : F := LinearMap.det (g : V →ₗ[F] V) with hd
  have hdd : d * d = (-1 : F) ^ Module.finrank F V := by
    rw [hd, ← map_mul]
    have : (g : V →ₗ[F] V) * (g : V →ₗ[F] V) = (-1 : F) • LinearMap.id :=
      LinearMap.ext fun x => by simp [hg2]
    rw [this, LinearMap.det_smul, LinearMap.det_id, mul_one]
  have hd0 : d ≠ 0 := fun h => by
    rw [h, mul_zero] at hdd
    exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero) hdd.symm
  have hd2 : d * d = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one d hd0
    rw [← Nat.card_eq_fintype_card, hF] at this
    simpa [pow_two] using this
  have hm1 : (-1 : F) ≠ 1 := fun h => h2 (by linear_combination -h)
  obtain ⟨m, hm⟩ := (neg_one_pow_eq_one_iff_even hm1).mp (hdd.symm.trans hd2)
  exact ⟨m, by omega⟩

theorem exists_adaptedBasis [Finite F] [FiniteDimensional F V] (hF : Nat.card F = 3)
    (hQ : (polarBilin Q).Nondegenerate) {g : V ≃ₗ[F] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg2 : ∀ x, g (g x) = -x) :
    ∃ m, Module.finrank F V = 2 * m ∧ Nonempty (AdaptedBasis Q g m) := by
  have : Fact (Nat.card F = 3) := ⟨hF⟩
  obtain ⟨m, hm⟩ := even_finrank_of_sq_eq_neg_one hF hg2
  obtain ⟨-, h2⟩ := three_eq_zero_two_ne_zero_of_card_eq_three hF
  let _ : Invertible (2 : F) := invertibleOfNonzero h2
  set β : LinearMap.BilinForm F V := polarBilin Q with hβ
  have hsymm : β.IsSymm := ⟨fun x y => by
    simp only [hβ, polarBilin_apply_apply]
    exact polar_comm Q x y⟩
  have hgβ : ∀ x y, β (g x) (g y) = β x y := fun x y => by
    simp only [hβ, polarBilin_apply_apply]
    exact polar_map_of_mem hg x y
  obtain ⟨e, hee, hge⟩ := exists_adapted_family exists_sq_add_sq_mul_eq_one' m β
    (g : V →ₗ[F] V) hsymm hQ hg2 hgβ hm
  set v : Fin m ⊕ Fin m → V := Sum.elim e (fun k => g (e k)) with hv
  have hvv : ∀ i j, β (v i) (v j) = if i = j then 1 else 0 := by
    rintro (k | k) (l | l)
    · simpa [hv] using hee k l
    · simpa [hv] using hge k l
    · have := (hsymm.eq (g (e k)) (e l)).trans (hge l k)
      simpa [hv] using this
    · have := hgβ (e k) (e l)
      simp only [hv, Sum.elim_inr, Sum.inr.injEq]
      rw [this]
      exact hee k l
  have hli : LinearIndependent F v := linearIndependent_of_orthonormal β v hvv
  have hcard : Fintype.card (Fin m ⊕ Fin m) = Module.finrank F V := by
    rw [Fintype.card_sum, Fintype.card_fin, hm]
    ring
  let b : Module.Basis (Fin m ⊕ Fin m) F V :=
    Module.Basis.mk hli (hli.span_eq_top_of_card_eq_finrank' hcard).ge
  refine ⟨m, hm, ⟨⟨b, fun i j => ?_, fun k => ?_⟩⟩⟩
  · have := hvv i j
    simpa [b, hβ] using this
  · simp [b, hv]

end CFSG.ClassicalGroups.Orthogonal.Small
