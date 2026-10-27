module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6ClassListFrames

public section

namespace CFSG.SeitzReduction

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Adjoint

variable {K : Type} [Field K]

@[expose] def TwistedE6CascadeReduction
    (K : Type) [Field K] (σ : K →+* K) : Prop :=
  ∀ ℓ ∈ graphFixedPosUnipotent TwistTag.E6 K σ, ℓ ^ 2 = 1 →
    ∃ g ∈ graphFixedRootGroup TwistTag.E6 K σ, ∃ S : List (Fin TwistTag.E6.tag.rank → ℤ),
      S.Sublist twistedE6Cascade ∧ ∃ c : (Fin TwistTag.E6.tag.rank → ℤ) → K,
        (∀ γ ∈ S, c γ ≠ 0 ∧ σ (c γ) = c γ) ∧
          g * ℓ * g⁻¹ = (S.map fun γ => pinnedX TwistTag.E6.tag K γ (c γ)).prod

theorem twistedE6ClassList_exists_sigma_ne {f : ℕ} (hf : 1 ≤ f) [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    ∃ d : K, σ d ≠ d := by
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  rw [Nat.card_units, hK] at hζ
  have hq : 2 ≤ 2 ^ f := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf)
  refine ⟨ζ, fun h => ?_⟩
  rw [hσ] at h
  have h1 : ζ ^ (2 ^ f - 1) = 1 := by
    refine Units.ext ?_
    have e : (ζ : K) ^ (2 ^ f - 1) * ζ = 1 * ζ := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega), one_mul, h]
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact mul_right_cancel₀ ζ.ne_zero e
  have h2 := orderOf_dvd_of_pow_eq_one h1
  rw [hζ] at h2
  have h3 := Nat.le_of_dvd (by omega) h2
  have h4 : 2 ^ f < (2 ^ f) ^ 2 := by nlinarith
  omega

theorem exists_twistedE6_add_sigma_eq_one [CharP K 2] {f : ℕ} (hf : 1 ≤ f) [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    ∃ δ : K, δ + σ δ = 1 := by
  obtain ⟨d, hd⟩ := twistedE6ClassList_exists_sigma_ne hf hK hσ
  have hσσ : ∀ x : K, σ (σ x) = x := fun x => by
    have h := congrArg (fun g : K ≃+* K => g x) (twistedE6_sigma_pow_order hK hσ)
    simpa [TwistTag.order, pow_two] using h
  have hne : d + σ d ≠ 0 := fun h => hd (by
    have h' : σ d = -d := by linear_combination h
    rw [h', CharTwo.neg_eq])
  refine ⟨d / (d + σ d), ?_⟩
  rw [map_div₀, map_add, hσσ, add_comm (σ d) d, ← add_div, div_self hne]


theorem exists_conj_mem_twistedE6Reps_of_cascade_prod [Finite K] [CharP K 2] {σ : K →+* K}
    (hσσ : ∀ x, σ (σ x) = x) {δ : K} (hδ : δ + σ δ = 1)
    {S : List (Fin TwistTag.E6.tag.rank → ℤ)} (hS : S.Sublist twistedE6Cascade) (hS0 : S ≠ [])
    (c : (Fin TwistTag.E6.tag.rank → ℤ) → K) (hc : ∀ γ ∈ S, c γ ≠ 0 ∧ σ (c γ) = c γ) :
    ∃ g ∈ graphFixedRootGroup TwistTag.E6 K σ,
      g * (S.map fun γ => pinnedX TwistTag.E6.tag K γ (c γ)).prod * g⁻¹ =
          pinnedX TwistTag.E6.tag K e6HighestRoot 1 ∨
        g * (S.map fun γ => pinnedX TwistTag.E6.tag K γ (c γ)).prod * g⁻¹ = twistedE6ClassU K ∨
          g * (S.map fun γ => pinnedX TwistTag.E6.tag K γ (c γ)).prod * g⁻¹ =
            twistedE6ClassV K := by
  have hF : ∀ γ ∈ S, IsRoot TwistTag.E6.tag γ ∧ permLattice TwistTag.E6.perm γ = γ :=
    fun γ hγ => ⟨isRoot_of_mem_twistedE6Cascade (hS.subset hγ),
      (twistedE6Cascade_facts.2.1 γ (hS.subset hγ)).1⟩
  obtain ⟨h, hh, -, hhe⟩ := exists_twistedE6_torus_conj_frame_prod σ hF
    (twistedE6Cascade_facts.2.2.sublist hS) c hc
  obtain ⟨g, hg, hge⟩ := exists_conj_mem_twistedE6Reps_of_cascade_sublist hσσ hδ hS hS0
  have e : g * h * (S.map fun γ => pinnedX TwistTag.E6.tag K γ (c γ)).prod * (g * h)⁻¹ =
      g * (S.map fun γ => pinnedX TwistTag.E6.tag K γ 1).prod * g⁻¹ := by
    rw [← hhe]
    group
  refine ⟨g * h, mul_mem hg hh, ?_⟩
  rw [e]
  exact hge

theorem exists_conj_mem_twistedE6ClassReps {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (hred : TwistedE6CascadeReduction K σ.toRingHom)
    {x : graphFixedRootGroup TwistTag.E6 K σ.toRingHom} (hx : x ^ 2 = 1) (hx1 : x ≠ 1) :
    ∃ g : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
      g * x * g⁻¹ ∈ twistedE6ClassReps K σ.toRingHom := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega : 1 ≤ 2 * f) (by rw [hK, ← pow_mul, mul_comm])
  have hσσ : ∀ y : K, σ (σ y) = y := fun y => by
    have h := congrArg (fun g : K ≃+* K => g y) (twistedE6_sigma_pow_order hK hσ)
    simpa [TwistTag.order, pow_two] using h
  obtain ⟨δ, hδ⟩ := exists_twistedE6_add_sigma_eq_one hf hK hσ
  obtain ⟨a, ha⟩ := exists_conj_mem_graphFixedPosUnipotent_of_sq_eq_one σ hx
  set ℓ : ModGL TwistTag.E6.tag K :=
    ((a * x * a⁻¹ : graphFixedRootGroup TwistTag.E6 K σ.toRingHom) : ModGL TwistTag.E6.tag K)
    with hℓ
  have hℓ2 : ℓ ^ 2 = 1 := by
    rw [hℓ, ← Subgroup.coe_pow, conj_pow, hx, mul_one, mul_inv_cancel, Subgroup.coe_one]
  obtain ⟨g, hg, S, hS, c, hc, hge⟩ := hred ℓ ha hℓ2
  have hS0 : S ≠ [] := by
    rintro rfl
    apply hx1
    have h1 : ℓ = 1 := by
      have h := hge
      rw [List.map_nil, List.prod_nil, mul_inv_eq_one, mul_eq_left] at h
      exact h
    have h2 : a * x * a⁻¹ = 1 := Subtype.ext h1
    rw [mul_inv_eq_one, mul_eq_left] at h2
    exact h2
  obtain ⟨k, hk, hke⟩ := exists_conj_mem_twistedE6Reps_of_cascade_prod hσσ hδ hS hS0 c hc
  refine ⟨⟨k * g, mul_mem hk hg⟩ * a, ?_⟩
  have e : ((⟨k * g, mul_mem hk hg⟩ * a * x * (⟨k * g, mul_mem hk hg⟩ * a)⁻¹ :
      graphFixedRootGroup TwistTag.E6 K σ.toRingHom) : ModGL TwistTag.E6.tag K) =
      k * (S.map fun γ => pinnedX TwistTag.E6.tag K γ (c γ)).prod * k⁻¹ := by
    rw [← hge, hℓ]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  change _ ∨ _ ∨ _
  rw [e]
  exact hke

theorem twistedE6_hrep_of_cascadeReduction {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) (hred : TwistedE6CascadeReduction K σ.toRingHom)
    (t : graphFixedRootGroup TwistTag.E6 K σ.toRingHom) (ht : orderOf (MulAut.conj t) = 2) :
    ∃ ψ : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      ∃ s ∈ twistedE6ClassReps K σ.toRingHom, ψ s = t := by
  have hcen := center_graphFixedRootGroup_eq_bot (t := TwistTag.E6) (K := K)
    (σ := σ.toRingHom) σ.surjective
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have ht2 : t ^ 2 = 1 := by
    have h : MulAut.conj (t ^ 2) = 1 := by rw [map_pow, ← ht, pow_orderOf_eq_one]
    have hz : t ^ 2 ∈ Subgroup.center (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := by
      refine Subgroup.mem_center_iff.2 fun y => ?_
      have hy := congrArg (fun φ => φ y) h
      simp only [MulAut.conj_apply, MulAut.one_apply] at hy
      have hy' : t ^ 2 * y = y * t ^ 2 := by
        calc t ^ 2 * y = t ^ 2 * y * (t ^ 2)⁻¹ * t ^ 2 := by group
          _ = y * t ^ 2 := by rw [hy]
      exact hy'.symm
    rw [hcen, Subgroup.mem_bot] at hz
    exact hz
  obtain ⟨g, hg⟩ := exists_conj_mem_twistedE6ClassReps hf hK hσ hred ht2 ht1
  refine ⟨MulAut.conj g⁻¹, g * t * g⁻¹, hg, ?_⟩
  rw [MulAut.conj_apply]
  group

@[expose] def TwistedE6FrameReduction (K : Type) [Field K] (σ : K →+* K) : Prop :=
  ∀ ℓ ∈ graphFixedPosUnipotent TwistTag.E6 K σ, ℓ ^ 2 = 1 →
    ∃ g ∈ graphFixedRootGroup TwistTag.E6 K σ, ∃ R : List (Fin TwistTag.E6.tag.rank → ℤ),
      (R.flatMap twistedE6Unit).Nodup ∧
      (∀ β ∈ R.flatMap twistedE6Unit, IsRoot TwistTag.E6.tag β ∧ 0 < height β) ∧
      (R.flatMap twistedE6Unit).Pairwise (fun β β' => iform β β' = 0) ∧
      ∃ c : (Fin TwistTag.E6.tag.rank → ℤ) → K,
        (∀ γ ∈ R, c γ ≠ 0 ∧ (permLattice TwistTag.E6.perm γ = γ → σ (c γ) = c γ)) ∧
          g * ℓ * g⁻¹ = (R.map fun γ => twistedE6RelX K σ γ (c γ)).prod

theorem TwistedE6CascadeReduction.frameReduction {σ : K →+* K}
    (h : TwistedE6CascadeReduction K σ) : TwistedE6FrameReduction K σ := by
  intro ℓ hℓ h2
  obtain ⟨g, hg, S, hS, c, hc, he⟩ := h ℓ hℓ h2
  have hfix : ∀ γ ∈ S, permLattice TwistTag.E6.perm γ = γ := fun γ hγ =>
    (twistedE6Cascade_facts.2.1 γ (hS.subset hγ)).1
  have hunit : S.flatMap twistedE6Unit = S := by
    have : ∀ γ ∈ S, twistedE6Unit γ = [γ] := fun γ hγ => by
      simp [twistedE6Unit, hfix γ hγ]
    rw [List.flatMap_congr this, List.flatMap_singleton']
  refine ⟨g, hg, S, ?_, ?_, ?_, c, fun γ hγ => ⟨(hc γ hγ).1, fun _ => (hc γ hγ).2⟩, ?_⟩
  · rw [hunit]
    exact twistedE6Cascade_facts.1.sublist hS
  · rw [hunit]
    exact fun β hβ => ⟨isRoot_of_mem_twistedE6Cascade (hS.subset hβ),
      (twistedE6Cascade_facts.2.1 β (hS.subset hβ)).2.1⟩
  · rw [hunit]
    exact twistedE6Cascade_facts.2.2.sublist hS
  · rw [he]
    congr 1
    refine List.map_congr_left fun γ hγ => ?_
    simp [twistedE6RelX, hfix γ hγ]

theorem exists_conj_mem_twistedE6ClassReps_of_frameReduction {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (hred : TwistedE6FrameReduction K σ.toRingHom)
    {x : graphFixedRootGroup TwistTag.E6 K σ.toRingHom} (hx : x ^ 2 = 1) (hx1 : x ≠ 1) :
    ∃ g : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
      g * x * g⁻¹ ∈ twistedE6ClassReps K σ.toRingHom := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega : 1 ≤ 2 * f) (by rw [hK, ← pow_mul, mul_comm])
  have hσσ : ∀ y : K, σ (σ y) = y := fun y => by
    have h := congrArg (fun g : K ≃+* K => g y) (twistedE6_sigma_pow_order hK hσ)
    simpa [TwistTag.order, pow_two] using h
  obtain ⟨δ, hδ⟩ := exists_twistedE6_add_sigma_eq_one hf hK hσ
  obtain ⟨a, ha⟩ := exists_conj_mem_graphFixedPosUnipotent_of_sq_eq_one σ hx
  set ℓ : ModGL TwistTag.E6.tag K :=
    ((a * x * a⁻¹ : graphFixedRootGroup TwistTag.E6 K σ.toRingHom) : ModGL TwistTag.E6.tag K)
    with hℓ
  have hℓ2 : ℓ ^ 2 = 1 := by
    rw [hℓ, ← Subgroup.coe_pow, conj_pow, hx, mul_one, mul_inv_cancel, Subgroup.coe_one]
  obtain ⟨g, hg, R, hnd, hpos, hpw, c, hc, hge⟩ := hred ℓ ha hℓ2
  set F := R.flatMap twistedE6Unit with hF
  have hmemU : ∀ γ, γ ∈ twistedE6Unit γ := fun γ => by
    by_cases h : permLattice TwistTag.E6.perm γ = γ <;> simp [twistedE6Unit, h]
  have hρU : ∀ γ β, β ∈ twistedE6Unit γ → permLattice TwistTag.E6.perm β ∈ twistedE6Unit γ := by
    intro γ β hβ
    by_cases h : permLattice TwistTag.E6.perm γ = γ
    · have hu : twistedE6Unit γ = [γ] := by simp [twistedE6Unit, h]
      rw [hu, List.mem_singleton] at hβ ⊢
      rw [hβ, h]
    · have hu : twistedE6Unit γ = [γ, permLattice TwistTag.E6.perm γ] := by
        simp [twistedE6Unit, h]
      rw [hu] at hβ ⊢
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hβ ⊢
      rcases hβ with rfl | rfl
      · exact Or.inr rfl
      · exact Or.inl (permLattice_twistedE6_perm_perm _)
  have hRF : ∀ γ ∈ R, ∀ β ∈ twistedE6Unit γ, β ∈ F := fun γ hγ β hβ =>
    List.mem_flatMap.2 ⟨γ, hγ, hβ⟩
  have hsym : ∀ a ∈ F, ∀ b ∈ F, a ≠ b → iform a b = 0 := by
    clear hnd hpos hge
    generalize F = L at hpw ⊢
    induction L with
    | nil => intro a ha; exact absurd ha List.not_mem_nil
    | cons x l ih =>
      obtain ⟨hx, hl⟩ := List.pairwise_cons.1 hpw
      intro a ha b hb hab
      rcases List.mem_cons.1 ha with rfl | ha'
      · rcases List.mem_cons.1 hb with rfl | hb'
        · exact absurd rfl hab
        · exact hx b hb'
      · rcases List.mem_cons.1 hb with rfl | hb'
        · rw [iform_comm]
          exact hx a ha'
        · exact ih hl a ha' b hb' hab
  have hR0 : R ≠ [] := by
    rintro rfl
    apply hx1
    have h1 : ℓ = 1 := by
      have h := hge
      rw [List.map_nil, List.prod_nil, mul_inv_eq_one, mul_eq_left] at h
      exact h
    have h2 : a * x * a⁻¹ = 1 := Subtype.ext h1
    rw [mul_inv_eq_one, mul_eq_left] at h2
    exact h2
  have hpair : ∀ γ ∈ R, permLattice TwistTag.E6.perm γ ≠ γ →
      iform γ (permLattice TwistTag.E6.perm γ) = 0 := fun γ hγ hne =>
    hsym γ (hRF γ hγ γ (hmemU γ)) _ (hRF γ hγ _ (hρU γ γ (hmemU γ))) (Ne.symm hne)
  obtain ⟨h, hh, hhe⟩ := exists_twistedE6_torus_conj_relX_prod (σ := σ.toRingHom) hσσ
    (fun γ hγ => (hpos γ (hRF γ hγ γ (hmemU γ))).1) hpair
    ((List.pairwise_flatMap.1 hpw).2) c hc
  have hFne : F ≠ [] := by
    obtain ⟨γ, hγ⟩ := List.exists_mem_of_ne_nil R hR0
    exact List.ne_nil_of_mem (hRF γ hγ γ (hmemU γ))
  have hFρ : ∀ β ∈ F, permLattice TwistTag.E6.perm β ∈ F := fun β hβ => by
    obtain ⟨γ, hγ, hβγ⟩ := List.mem_flatMap.1 hβ
    exact hRF γ hγ _ (hρU γ β hβγ)
  obtain ⟨k, hk, hke⟩ := exists_conj_mem_twistedE6Reps_of_frame (σ := σ.toRingHom) hσσ hδ hnd
    (fun β hβ => ⟨(hpos β hβ).1, (hpos β hβ).2, hFρ β hβ⟩) hpw hFne
  rw [← list_prod_twistedE6RelX_one] at hke
  refine ⟨⟨k * h * g, mul_mem (mul_mem hk hh) hg⟩ * a, ?_⟩
  have e : ((⟨k * h * g, mul_mem (mul_mem hk hh) hg⟩ * a * x *
      (⟨k * h * g, mul_mem (mul_mem hk hh) hg⟩ * a)⁻¹ :
      graphFixedRootGroup TwistTag.E6 K σ.toRingHom) : ModGL TwistTag.E6.tag K) =
      k * (R.map fun γ => twistedE6RelX K σ.toRingHom γ 1).prod * k⁻¹ := by
    rw [← hhe, ← hge, hℓ]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  change _ ∨ _ ∨ _
  rw [e]
  exact hke

theorem twistedE6_hrep_of_frameReduction {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) (hred : TwistedE6FrameReduction K σ.toRingHom)
    (t : graphFixedRootGroup TwistTag.E6 K σ.toRingHom) (ht : orderOf (MulAut.conj t) = 2) :
    ∃ ψ : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      ∃ s ∈ twistedE6ClassReps K σ.toRingHom, ψ s = t := by
  have hcen := center_graphFixedRootGroup_eq_bot (t := TwistTag.E6) (K := K)
    (σ := σ.toRingHom) σ.surjective
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have ht2 : t ^ 2 = 1 := by
    have h : MulAut.conj (t ^ 2) = 1 := by rw [map_pow, ← ht, pow_orderOf_eq_one]
    have hz : t ^ 2 ∈ Subgroup.center (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := by
      refine Subgroup.mem_center_iff.2 fun y => ?_
      have hy := congrArg (fun φ => φ y) h
      simp only [MulAut.conj_apply, MulAut.one_apply] at hy
      have hy' : t ^ 2 * y = y * t ^ 2 := by
        calc t ^ 2 * y = t ^ 2 * y * (t ^ 2)⁻¹ * t ^ 2 := by group
          _ = y * t ^ 2 := by rw [hy]
      exact hy'.symm
    rw [hcen, Subgroup.mem_bot] at hz
    exact hz
  obtain ⟨g, hg⟩ := exists_conj_mem_twistedE6ClassReps_of_frameReduction hf hK hσ hred ht2 ht1
  refine ⟨MulAut.conj g⁻¹, g * t * g⁻¹, hg, ?_⟩
  rw [MulAut.conj_apply]
  group

end CFSG.SeitzReduction
