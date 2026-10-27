module

public import CFSG.LieType.BorelTits.WeightedMatrix

public section

namespace CFSG.LieType.BorelTits.Weighted

open CFSG.Open
open scoped RealInnerProductSpace

variable {E W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Group W]

theorem act_mul_apply (act : W →* (E ≃ₗᵢ[ℝ] E)) (a c : W) (x : E) :
    act (a * c) x = act a (act c x) := by
  rw [map_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply]

theorem act_inv_act (act : W →* (E ≃ₗᵢ[ℝ] E)) (a : W) (x : E) : act a⁻¹ (act a x) = x := by
  rw [← act_mul_apply, inv_mul_cancel, map_one, LinearIsometryEquiv.coe_one, id]

theorem act_act_inv (act : W →* (E ≃ₗᵢ[ℝ] E)) (a : W) (x : E) : act a (act a⁻¹ x) = x := by
  rw [← act_mul_apply, mul_inv_cancel, map_one, LinearIsometryEquiv.coe_one, id]

@[expose] noncomputable def restrictAct (act : W →* (E ≃ₗᵢ[ℝ] E)) (W' : Subgroup W)
    (E' : Submodule ℝ E) (hE' : ∀ w ∈ W', ∀ x ∈ E', act w x ∈ E') :
    W' →* (E' ≃ₗᵢ[ℝ] E') where
  toFun w :=
    { toFun := fun x => ⟨act w x, hE' w w.2 x x.2⟩
      invFun := fun x => ⟨act (w : W)⁻¹ x, hE' _ (inv_mem w.2) x x.2⟩
      map_add' := fun x y => Subtype.ext (map_add (act w) (x : E) y)
      map_smul' := fun c x => Subtype.ext (map_smul (act w) c (x : E))
      left_inv := fun x => Subtype.ext (act_inv_act act w x)
      right_inv := fun x => Subtype.ext (act_act_inv act w x)
      norm_map' := fun x => (act w).norm_map (x : E) }
  map_one' := LinearIsometryEquiv.ext fun x => Subtype.ext (by
    change act ((1 : W') : W) x = x
    rw [OneMemClass.coe_one, map_one, LinearIsometryEquiv.coe_one, id])
  map_mul' w w' := LinearIsometryEquiv.ext fun x => Subtype.ext (act_mul_apply act w w' x)

theorem coe_restrictAct_apply (act : W →* (E ≃ₗᵢ[ℝ] E)) (W' : Subgroup W) (E' : Submodule ℝ E)
    (hE' : ∀ w ∈ W', ∀ x ∈ E', act w x ∈ E') (w : W') (x : E') :
    (restrictAct act W' E' hE' w x : E) = act w x :=
  rfl

theorem starProjection_act (act : W →* (E ≃ₗᵢ[ℝ] E)) {W' : Subgroup W} {E' : Submodule ℝ E}
    [E'.HasOrthogonalProjection] (hE' : ∀ w ∈ W', ∀ x ∈ E', act w x ∈ E') {w : W}
    (hw : w ∈ W') (x : E) : E'.starProjection (act w x) = act w (E'.starProjection x) := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (hE' w hw _ (E'.starProjection_apply_mem x)) fun y hy => ?_
  rw [← act_act_inv act w y, ← map_sub, LinearIsometryEquiv.inner_map_map]
  exact Submodule.starProjection_inner_eq_zero x _ (hE' _ (inv_mem hw) y hy)

theorem exists_sylow_eq_of_normalizer {Γ : Type*} [Group Γ] [Finite Γ] (p : ℕ) [Fact p.Prime]
    {S : Subgroup Γ} (hS : IsPGroup p S)
    (hN : ∀ t ∈ Subgroup.normalizer (S : Set Γ), (∃ k : ℕ, t ^ p ^ k = 1) → t ∈ S) :
    ∃ T : Sylow p Γ, (T : Subgroup Γ) = S := by
  obtain ⟨T, hT⟩ := hS.exists_le_sylow
  refine ⟨T, le_antisymm ?_ hT⟩
  by_contra hne
  have : Group.IsNilpotent (T : Subgroup Γ) := T.isPGroup'.isNilpotent
  have hlt : S.subgroupOf T < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hne fun x hx => ?_
    have : (⟨x, hx⟩ : (T : Subgroup Γ)) ∈ S.subgroupOf T := htop ▸ Subgroup.mem_top _
    exact this
  obtain ⟨s, hsN, hsS⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  have hsS' : (s : Γ) ∉ S := hsS
  have hsNG : (s : Γ) ∈ Subgroup.normalizer (S : Set Γ) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact (Subgroup.mem_normalizer_iff.mp hsN ⟨x, hT hx⟩).mp hx
    · intro hx
      have hxT : x ∈ (T : Subgroup Γ) := by
        have := mul_mem (mul_mem (inv_mem s.2) (hT hx)) s.2
        simpa [mul_assoc] using this
      exact (Subgroup.mem_normalizer_iff.mp hsN ⟨x, hxT⟩).mpr hx
  obtain ⟨k, hk⟩ := T.isPGroup' s
  exact hsS' (hN s hsNG ⟨k, by simpa using congrArg Subtype.val hk⟩)

variable {G : Type*} [Group G]

theorem normalizer_le_of_fixedData (n : W → G) (B U Γ : Subgroup G) (W' : Subgroup W)
    (hbruhat : ∀ g ∈ Γ, ∃ w ∈ W', ∃ b₁ ∈ B, b₁ ∈ Γ ∧ ∃ b₂ ∈ B, b₂ ∈ Γ ∧ g = b₁ * n w * b₂)
    (hBU : B ≤ Subgroup.normalizer (U : Set G)) (hn1 : n 1 ∈ B)
    (hUw : ∀ w ∈ W', w ≠ 1 → ∃ u ∈ U, u ∈ Γ ∧ n w * u * (n w)⁻¹ ∉ U) {g : Γ}
    (hg : g ∈ Subgroup.normalizer ((U.comap Γ.subtype : Subgroup Γ) : Set Γ)) : (g : G) ∈ B := by
  obtain ⟨w, hw, b₁, hb₁, hb₁Γ, b₂, hb₂, hb₂Γ, hgeq⟩ := hbruhat g g.2
  by_cases hw1 : w = 1
  · subst hw1
    rw [hgeq]
    exact mul_mem (mul_mem hb₁ hn1) hb₂
  exfalso
  obtain ⟨u, hu, huΓ, hnu⟩ := hUw w hw hw1
  have h1 : b₂⁻¹ * u * b₂ ∈ U := by
    have := (Subgroup.mem_normalizer_iff.mp (hBU (inv_mem hb₂)) u).mp hu
    simpa using this
  have h1Γ : b₂⁻¹ * u * b₂ ∈ Γ := mul_mem (mul_mem (inv_mem hb₂Γ) huΓ) hb₂Γ
  have h2 : (g : G) * (b₂⁻¹ * u * b₂) * (g : G)⁻¹ ∈ U := by
    have := (Subgroup.mem_normalizer_iff.mp hg ⟨_, h1Γ⟩).mp h1
    exact this
  have h3 : (g : G) * (b₂⁻¹ * u * b₂) * (g : G)⁻¹ = b₁ * (n w * u * (n w)⁻¹) * b₁⁻¹ := by
    rw [hgeq]
    group
  rw [h3] at h2
  apply hnu
  have := (Subgroup.mem_normalizer_iff.mp (hBU (inv_mem hb₁)) _).mp h2
  simpa [mul_assoc] using this

variable {ι K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {b : Module.Basis ι K V} {wt : ι → E}

theorem holds_of_fixedData [Finite G] [Finite W] [Finite ι] [FiniteDimensional ℝ E]
    (ρ : G →* Module.End K V) (p : ℕ) [Fact p.Prime] [CharP K p] (hρ : Function.Injective ρ)
    (act : W →* (E ≃ₗᵢ[ℝ] E)) (n : W → G) (B U : Subgroup G) (D : Set E) (v₀ : E)
    (Γ : Subgroup G) (W' : Subgroup W) (E' : Submodule ℝ E)
    (hspan : Submodule.span ℝ (Set.range wt) = ⊤)
    (hmono : ∀ w ∈ W', ∀ i j, b.repr (ρ (n w) (b j)) i ≠ 0 → wt i = act w (wt j))
    (hmono_inv : ∀ w ∈ W', ∀ i j, b.repr (ρ (n w)⁻¹ (b j)) i ≠ 0 → act w (wt i) = wt j)
    (hborel : ∀ x ∈ B, ∀ v ∈ D, ∀ i j, b.repr (ρ x (b j)) i ≠ 0 → ⟪wt j, v⟫ ≤ ⟪wt i, v⟫)
    (hunip : ∀ u ∈ U, ∀ i j, b.repr (ρ u (b j) - b j) i ≠ 0 → ⟪wt j, v₀⟫ < ⟪wt i, v₀⟫)
    (hpU : IsPGroup p U) (hBU : B ≤ Subgroup.normalizer (U : Set G))
    (hBp : ∀ t ∈ B, (∃ k : ℕ, t ^ p ^ k = 1) → t ∈ U) (hn1 : n 1 ∈ B)
    (hE' : ∀ w ∈ W', ∀ x ∈ E', act w x ∈ E') (hnΓ : ∀ w ∈ W', n w ∈ Γ)
    (hfix : ∀ v ∈ E', (∀ w ∈ W', act w v = v) → v = 0)
    (hcover : ∀ x ∈ E', ∃ w ∈ W', ∃ y ∈ E', y ∈ D ∧ x = act w y)
    (hbruhat : ∀ g ∈ Γ, ∃ w ∈ W', ∃ b₁ ∈ B, b₁ ∈ Γ ∧ ∃ b₂ ∈ B, b₂ ∈ Γ ∧ g = b₁ * n w * b₂)
    (hUw : ∀ w ∈ W', w ≠ 1 → ∃ u ∈ U, u ∈ Γ ∧ n w * u * (n w)⁻¹ ∉ U) (hv₀ : v₀ ∈ E') :
    Holds Γ p := by
  classical
  set S₀ : Subgroup Γ := U.comap Γ.subtype with hS₀
  have hNS : ∀ g ∈ Subgroup.normalizer (S₀ : Set Γ), (g : G) ∈ B := fun g hg =>
    normalizer_le_of_fixedData n B U Γ W' hbruhat hBU hn1 hUw hg
  have hS₀p : IsPGroup p S₀ := hpU.comap_of_injective Γ.subtype Subtype.val_injective
  obtain ⟨S, hS⟩ := exists_sylow_eq_of_normalizer p hS₀p fun t ht ⟨k, hk⟩ =>
    hBp t (hNS t ht) ⟨k, by simpa using congrArg Subtype.val hk⟩
  let wt' : ι → E' := fun i => E'.orthogonalProjectionOnto (wt i)
  let act' := restrictAct act W' E' hE'
  let n' : W' → Γ := fun w => ⟨n w, hnΓ w w.2⟩
  let ρ' : Γ →* Module.End K V := ρ.comp Γ.subtype
  have hρ' : Function.Injective ρ' := hρ.comp Subtype.val_injective
  have hinner : ∀ i, ∀ v : E', ⟪wt' i, v⟫ = ⟪wt i, (v : E)⟫ := fun i v =>
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right v (wt i)
  have hdat : WeightedBruhat b wt' ρ' act' n' (B.comap Γ.subtype) S {v : E' | (v : E) ∈ D}
      ⟨v₀, hv₀⟩ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    ·
      rw [eq_top_iff]
      intro x _
      have hx : (x : E) ∈ Submodule.span ℝ (Set.range wt) := hspan ▸ Submodule.mem_top
      have := Submodule.mem_map_of_mem (f := (E'.orthogonalProjectionOnto : E →ₗ[ℝ] E')) hx
      rw [Submodule.map_span, ← Set.range_comp] at this
      have hx' : x ∈ Submodule.span ℝ (Set.range (E'.orthogonalProjectionOnto ∘ wt)) := by
        simpa [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self] using this
      exact hx'
    · intro v hv
      exact Subtype.ext (hfix v v.2 fun w hw => congrArg Subtype.val (hv ⟨w, hw⟩))
    · intro w i j hij
      have h := hmono w w.2 i j hij
      apply Subtype.ext
      change E'.starProjection (wt i) = act w (E'.starProjection (wt j))
      rw [h, starProjection_act act hE' w.2]
    · intro w i j hij
      have h := hmono_inv w w.2 i j hij
      apply Subtype.ext
      change act w (E'.starProjection (wt i)) = E'.starProjection (wt j)
      rw [← starProjection_act act hE' w.2, h]
    · intro x
      obtain ⟨w, hw, y, hyE, hyD, hxy⟩ := hcover x x.2
      exact ⟨⟨w, hw⟩, ⟨y, hyE⟩, hyD, Subtype.ext hxy⟩
    · intro x hx v hv i j hij
      rw [hinner, hinner]
      exact hborel x hx v hv i j hij
    · intro g
      obtain ⟨w, hw, b₁, hb₁, hb₁Γ, b₂, hb₂, hb₂Γ, hg⟩ := hbruhat g g.2
      exact ⟨⟨w, hw⟩, ⟨b₁, hb₁Γ⟩, hb₁, ⟨b₂, hb₂Γ⟩, hb₂, Subtype.ext hg⟩
    · intro u hu i j hij
      rw [hinner, hinner]
      have huU : (u : G) ∈ U := by
        have : u ∈ S₀ := hS ▸ hu
        exact this
      exact hunip u huU i j hij
  exact holds_of_weightedBruhat ρ' p hρ' S hdat fun g hg => hNS g (hS ▸ hg)

end CFSG.LieType.BorelTits.Weighted
