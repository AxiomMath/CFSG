module

public import CFSG.LieType.Chevalley.OddTrialityAutomorphismNormalForm

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K]

theorem exists_conj_eq_compatDiagAutHom_D4_even
    {f : ℕ} (hK : Nat.card K = (2 ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    (u : (a : Fin TwistTag.D4.foldedTag.rank) → (orbitField TwistTag.D4 K σ.toRingHom a)ˣ) :
    ∃ h : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      MulAut.conj h = compatDiagAutHom TwistTag.D4 K σ.toRingHom u := by
  obtain ⟨-, -, hscal⟩ := even_triality_pair_scalars_inner K hK σ hσ
  obtain ⟨s, t, -, -, -, hmem, hx0, hy0, hx1, hy1⟩ := hscal (u ⟨0, by decide⟩) (u ⟨1, by decide⟩)
  have hcases : ∀ a : Fin TwistTag.D4.foldedTag.rank,
      a = ⟨0, by decide⟩ ∨ a = ⟨1, by decide⟩ := by decide
  refine ⟨⟨_, hmem⟩, graphFixedRootGroup_mulAut_ext σ.surjective (fun a c => ?_) fun a c => ?_⟩
  · rw [compatDiagAutHom_fixedOrbitX, MulAut.conj_apply]
    refine Subtype.ext ?_
    rcases hcases a with rfl | rfl
    · exact hx0 c
    · exact hx1 c
  · rw [compatDiagAutHom_fixedOrbitY, MulAut.conj_apply]
    refine Subtype.ext ?_
    rcases hcases a with rfl | rfl
    · exact hy0 c
    · exact hy1 c


theorem even_triality_exact_automorphism_normal_form
    {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    (∀ (δ : K ≃+* K) (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      ((fieldActor σ δ g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
        ModGL TwistTag.D4.tag K) = Units.map (entrywiseHom δ.toRingHom) g) ∧
    (∀ α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      ∃! gδ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom × (K ≃+* K),
        α = MulAut.conj gδ.1 * fieldActor σ gδ.2) ∧
    (∃ Θ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →* (K ≃+* K),
      (∀ α g δ, α = MulAut.conj g * fieldActor σ δ → Θ α = δ) ∧
      Function.Surjective Θ ∧
      Θ.ker = (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range ∧
      ∀ α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), α ^ 2 = 1 →
        Θ α = 1 ∨ (Even f ∧ ∀ c, Θ α c = c ^ (2 ^ (3 * f / 2)))) ∧
    IsCyclic (K ≃+* K) ∧ Nat.card (K ≃+* K) = 3 * f ∧
    ⁅twistedFixedGroup TwistTag.D4 K σ.toRingHom, twistedFixedGroup TwistTag.D4 K σ.toRingHom⁆ =
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom ∧
    Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ ∧
    Nonempty (DerivedCentralQuotient (twistedFixedGroup TwistTag.D4 K σ.toRingHom) ≃*
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  classical
  set C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom
  have hK3 : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h0 : orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ = ⊤ :=
    orbitField_D4_zero_eq_top σ (ringEquiv_cube_apply_eq hK hσ)
  have hZ : Subgroup.center C = ⊥ := exceptional_fixed_center_trivial TwistTag.D4 K σ
  set E : (K ≃+* K) → MulAut C := fun δ => fieldActor σ δ
  have hE1 : E 1 = 1 := fieldActor_one σ
  have hEmul : ∀ δ ε : K ≃+* K, E (δ * ε) = E δ * E ε := fun δ ε => fieldActor_mul σ δ ε
  have hex : ∀ α : MulAut C, ∃ g δ, α = MulAut.conj g * E δ := by
    intro α
    obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
    obtain ⟨c, β, hU, hV, rfl⟩ :=
      (exceptional_fixed_Sylow_opposition TwistTag.D4 K 2 σ w₀ hw₀).2.2.2.2.2 α
    obtain ⟨u, δ, rfl⟩ := exists_normalActor_eq_D4 Nat.prime_two hf hK σ hσ (β := β) ⟨hU, hV⟩
    obtain ⟨h, hh⟩ := exists_conj_eq_compatDiagAutHom_D4_even hK σ hσ u
    refine ⟨c * h, δ, ?_⟩
    rw [normalActor, ← hh, map_mul, mul_assoc]
  have huniq : ∀ (g g' : C) (δ δ' : K ≃+* K),
      MulAut.conj g * E δ = MulAut.conj g' * E δ' → g = g' ∧ δ = δ' := by
    intro g g' δ δ' h
    have e : E δ' * (E δ)⁻¹ = MulAut.conj (g'⁻¹ * g) := by
      have h' : E δ' = (MulAut.conj g')⁻¹ * MulAut.conj g * E δ := by
        rw [mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [h', mul_inv_cancel_right, map_mul, map_inv]
    have hEmem : ∀ ε : K ≃+* K,
        E ε ∈ graphFixedUnipotentStabilizer TwistTag.D4 K σ.toRingHom := fun ε => by
      have := normalActor_mem (t := TwistTag.D4) σ 1 ε
      rwa [normalActor_one_left] at this
    have hA : MulAut.conj (g'⁻¹ * g) ∈ graphFixedUnipotentStabilizer TwistTag.D4 K σ.toRingHom := by
      rw [← e]
      exact mul_mem (hEmem δ') (inv_mem (hEmem δ))
    obtain ⟨w, hw⟩ := exists_conj_eq_compatDiagAutHom σ.surjective hA
    have e2 : normalActor σ w δ = normalActor σ 1 δ' := by
      rw [normalActor_one_left, normalActor, ← hw, ← e, inv_mul_cancel_right]
    have hδ := eq_of_normalActor_eq_D4 h0 e2
    subst hδ
    refine ⟨?_, rfl⟩
    have hw1 : compatDiagAutHom TwistTag.D4 K σ.toRingHom w = 1 := by
      have e3 : compatDiagAutHom TwistTag.D4 K σ.toRingHom w * E δ = 1 * E δ := by
        rw [one_mul]
        change normalActor σ w δ = _
        rw [e2, normalActor_one_left]
      exact mul_right_cancel e3
    have h1 : MulAut.conj (g'⁻¹ * g) = 1 := hw.trans hw1
    have h2 := mulAut_conj_injective_of_center_eq_bot hZ (h1.trans (map_one _).symm)
    exact (inv_mul_eq_one.1 h2).symm
  choose gF δF hF using hex
  have hΘ : ∀ α g δ, α = MulAut.conj g * E δ → δF α = δ := fun α g δ h =>
    (huniq _ _ _ _ ((hF α).symm.trans h)).2
  have hmul : ∀ α β : MulAut C, δF (α * β) = δF α * δF β := by
    intro α β
    refine hΘ _ (gF α * E (δF α) (gF β)) _ ?_
    calc α * β = MulAut.conj (gF α) * E (δF α) * (MulAut.conj (gF β) * E (δF β)) := by
          rw [← hF α, ← hF β]
      _ = MulAut.conj (gF α) * (E (δF α) * MulAut.conj (gF β)) * E (δF β) := by
          simp only [mul_assoc]
      _ = MulAut.conj (gF α) * (MulAut.conj (E (δF α) (gF β)) * E (δF α)) * E (δF β) := by
          rw [mulAut_mul_conj]
      _ = MulAut.conj (gF α * E (δF α) (gF β)) * (E (δF α) * E (δF β)) := by
          rw [map_mul]
          simp only [mul_assoc]
      _ = MulAut.conj (gF α * E (δF α) (gF β)) * E (δF α * δF β) := by
          rw [hEmul]
  have hone : δF 1 = 1 := hΘ 1 1 1 (by rw [map_one, one_mul, hE1])
  let Θ : MulAut C →* (K ≃+* K) :=
    { toFun := δF
      map_one' := hone
      map_mul' := hmul }
  obtain ⟨hcardAut, hcyc⟩ := card_ringAut_and_isCyclic Nat.prime_two K hK3
  obtain ⟨-, -, hperf, -, -⟩ :=
    finite_fixed_root_group_perfect TwistTag.D4 Nat.prime_two hf K hK σ.toRingHom hσ
  refine ⟨fun δ g => coe_fieldActor σ δ g, fun α => ?_, ⟨Θ, hΘ, fun δ => ?_, ?_,
    fun α hα => ?_⟩, hcyc, hcardAut, hperf, hZ, nonempty_derivedCentralQuotient_equiv hperf hZ⟩
  ·
    refine ⟨(gF α, δF α), hF α, fun x hx => ?_⟩
    obtain ⟨h1, h2⟩ := huniq _ _ _ _ (hx.symm.trans (hF α))
    exact Prod.ext h1 h2
  ·
    exact ⟨E δ, hΘ _ 1 δ (by rw [map_one, one_mul])⟩
  ·
    ext α
    rw [MonoidHom.mem_ker]
    constructor
    · intro h1
      change δF α = 1 at h1
      have h' := hF α
      rw [h1, hE1, mul_one] at h'
      exact ⟨gF α, h'.symm⟩
    · rintro ⟨g, rfl⟩
      exact hΘ _ g 1 (by rw [hE1, mul_one])
  ·
    have h2 : δF α ^ 2 = 1 := by
      rw [pow_two, ← hmul, ← pow_two, hα, hone]
    by_cases h1 : δF α = 1
    · exact Or.inl h1
    · obtain ⟨hev, hpow, -⟩ := ringEquiv_sq_eq_one_facts Nat.prime_two (by omega) hK3 h2 h1
      refine Or.inr ⟨?_, hpow⟩
      rcases Nat.even_mul.1 hev with h3 | h3
      · exact absurd h3 (by decide)
      · exact h3

end CFSG.LieType.Chevalley
