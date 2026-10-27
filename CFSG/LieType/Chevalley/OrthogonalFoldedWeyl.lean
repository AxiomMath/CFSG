module

public import CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootData

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint

section WeylReal

variable {τ : Tag}

@[expose] def weylReal
    (w : WeylGroup τ) : Module.End ℝ (Fin τ.rank → ℝ) :=
  (RootSpace.linearEquivPi τ).toLinearMap ∘ₗ weylLinear τ w ∘ₗ
    (RootSpace.linearEquivPi τ).symm.toLinearMap

theorem weylReal_toReal
    (w : WeylGroup τ) (v : Fin τ.rank → ℤ) :
    weylReal w (toReal v) = toReal (w • v) := by
  change RootSpace.toPi (weylLinear τ w (RootSpace.ofLattice v)) = toReal (w • v)
  rw [weylLinear_ofLattice]
  rfl

theorem weylReal_mul
    (w w' : WeylGroup τ) (x : Fin τ.rank → ℝ) :
    weylReal (w * w') x = weylReal w (weylReal w' x) := by
  change RootSpace.toPi (weylLinear τ (w * w') (RootSpace.ofPi x)) =
    RootSpace.toPi (weylLinear τ w (RootSpace.ofPi (RootSpace.toPi
      (weylLinear τ w' (RootSpace.ofPi x)))))
  rw [map_mul, Module.End.mul_apply, RootSpace.ofPi_toPi]

theorem weylReal_one
    (x : Fin τ.rank → ℝ) : weylReal (1 : WeylGroup τ) x = x := by
  change RootSpace.toPi (weylLinear τ 1 (RootSpace.ofPi x)) = x
  rw [map_one, Module.End.one_apply, RootSpace.toPi_ofPi]

end WeylReal

section OrthogonalWords

variable {τ : Tag}

theorem reflectionWordProd_smul_of_forall_iform_eq_zero
    {l : List (Fin τ.rank → ℤ)}
    (hl : ∀ β ∈ l, IsRoot τ β) {v : Fin τ.rank → ℤ} (hv : ∀ β ∈ l, iform β v = 0) :
    reflectionWordProd l • v = v := by
  induction l with
  | nil => rw [reflectionWordProd_nil, one_smul]
  | cons β l ih =>
    rw [reflectionWordProd_cons, mul_smul,
      ih (fun γ hγ => hl γ (List.mem_cons_of_mem _ hγ))
        (fun γ hγ => hv γ (List.mem_cons_of_mem _ hγ)),
      rootReflection_smul_of_iform_eq_zero (hl β List.mem_cons_self) (hv β List.mem_cons_self)]

theorem reflectionWordProd_smul_of_mem
    {l : List (Fin τ.rank → ℤ)} (hl : ∀ β ∈ l, IsRoot τ β)
    (horth : l.Pairwise fun β γ => iform β γ = 0) {γ : Fin τ.rank → ℤ} (hγ : γ ∈ l) :
    reflectionWordProd l • γ = -γ := by
  induction l with
  | nil => exact absurd hγ List.not_mem_nil
  | cons β l ih =>
    rw [List.pairwise_cons] at horth
    have hβ := hl β List.mem_cons_self
    have hl' : ∀ δ ∈ l, IsRoot τ δ := fun δ hδ => hl δ (List.mem_cons_of_mem _ hδ)
    rw [reflectionWordProd_cons, mul_smul]
    rcases List.mem_cons.1 hγ with rfl | hγl
    · rw [reflectionWordProd_smul_of_forall_iform_eq_zero hl' fun δ hδ => by
        rw [iform_comm]; exact horth.1 δ hδ, rootReflection_smul_self hβ]
    · rw [ih hl' horth.2 hγl, smul_neg, rootReflection_smul_of_iform_eq_zero hβ (horth.1 γ hγl)]

theorem reflectionWordProd_mul_self
    {l : List (Fin τ.rank → ℤ)} (hl : ∀ β ∈ l, IsRoot τ β)
    (horth : l.Pairwise fun β γ => iform β γ = 0) :
    reflectionWordProd l * reflectionWordProd l = 1 := by
  induction l with
  | nil => rw [reflectionWordProd_nil, one_mul]
  | cons β l ih =>
    rw [List.pairwise_cons] at horth
    have hβ := hl β List.mem_cons_self
    have hl' : ∀ δ ∈ l, IsRoot τ δ := fun δ hδ => hl δ (List.mem_cons_of_mem _ hδ)
    have hc : Commute (rootReflection β) (reflectionWordProd l) := by
      refine Commute.list_prod_right _ _ fun x hx => ?_
      obtain ⟨δ, hδ, rfl⟩ := List.mem_map.1 hx
      exact commute_rootReflection_of_iform_eq_zero hβ (hl' δ hδ) (horth.1 δ hδ)
    rw [reflectionWordProd_cons, mul_assoc, ← mul_assoc (reflectionWordProd l), ← hc.eq,
      mul_assoc, ih hl' horth.2, mul_one, rootReflection_mul_self hβ]

theorem mul_reflectionWordProd_mul_inv
    (u : WeylGroup τ) {l : List (Fin τ.rank → ℤ)}
    (hl : ∀ β ∈ l, IsRoot τ β) :
    u * reflectionWordProd l * u⁻¹ = reflectionWordProd (l.map (u • ·)) := by
  induction l with
  | nil => rw [reflectionWordProd_nil, List.map_nil, reflectionWordProd_nil, mul_one,
      mul_inv_cancel]
  | cons β l ih =>
    rw [reflectionWordProd_cons, List.map_cons, reflectionWordProd_cons,
      rootReflection_smul_root u (hl β List.mem_cons_self),
      ← ih fun δ hδ => hl δ (List.mem_cons_of_mem _ hδ)]
    group

end OrthogonalWords

section UnionWeyl

variable {τ : Tag} {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
  {J : Set (KernelComponent χ)}

theorem exists_componentWeylGroup_smul_eq
    {w : WeylGroup τ} (hw : w ∈ unionWeylGroup χ J)
    (i : KernelComponent χ) :
    ∃ u ∈ componentWeylGroup (componentRoots χ i), ∀ α ∈ componentRoots χ i, w • α = u • α := by
  have hΨ := isRootComponent_componentRoots (χ := χ) i
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨β, ⟨j, -, hβj⟩, rfl⟩ := hx
    by_cases hji : j = i
    · subst hji
      exact ⟨rootReflection β, rootReflection_mem_componentWeylGroup hβj, fun _ _ => rfl⟩
    · exact ⟨1, one_mem _, fun α hα => by
        rw [one_smul, rootReflection_smul_eq_of_ne hji (simpleRoots_subset hβj) hα]⟩
  | one => exact ⟨1, one_mem _, fun _ _ => rfl⟩
  | mul x y _ _ hx hy =>
    obtain ⟨u, hu, hxu⟩ := hx
    obtain ⟨v, hv, hyv⟩ := hy
    refine ⟨u * v, mul_mem hu hv, fun α hα => ?_⟩
    rw [mul_smul, mul_smul, hyv α hα, hxu _ (smul_mem_of_mem_componentWeylGroup hΨ hv α hα)]
  | inv x _ hx =>
    obtain ⟨u, hu, hxu⟩ := hx
    refine ⟨u⁻¹, inv_mem hu, fun α hα => ?_⟩
    have h := hxu _ (smul_mem_of_mem_componentWeylGroup hΨ (inv_mem hu) α hα)
    rw [smul_inv_smul] at h
    calc x⁻¹ • α = x⁻¹ • (x • (u⁻¹ • α)) := by rw [h]
      _ = u⁻¹ • α := inv_smul_smul x _

theorem smul_mem_componentRoots
    {w : WeylGroup τ} (hw : w ∈ unionWeylGroup χ J)
    {i : KernelComponent χ} {α : Fin τ.rank → ℤ} (hα : α ∈ componentRoots χ i) :
    w • α ∈ componentRoots χ i := by
  obtain ⟨u, hu, h⟩ := exists_componentWeylGroup_smul_eq hw i
  rw [h α hα]
  exact smul_mem_of_mem_componentWeylGroup (isRootComponent_componentRoots i) hu α hα

theorem exists_unionSimpleRoots_smul_mem_negRoots
    {w : WeylGroup τ}
    (hw : w ∈ unionWeylGroup χ J) (hne : w ≠ 1) :
    ∃ β ∈ unionSimpleRoots χ J, w • β ∈ negRoots (unionRoots χ J) := by
  by_contra h
  push Not at h
  apply hne
  refine eq_one_of_forall_smul_eq hw fun α hα => ?_
  obtain ⟨i, hi, hαi⟩ := mem_unionRoots_iff.1 hα
  obtain ⟨u, hu, hwu⟩ := exists_componentWeylGroup_smul_eq hw i
  have hu1 : u = 1 := by
    by_contra hu1
    obtain ⟨β, hβ, hneg⟩ := exists_smul_mem_negRoots (isRootComponent_componentRoots i) hu hu1
    apply h β ⟨i, hi, hβ⟩
    rw [hwu β (simpleRoots_subset hβ)]
    exact ⟨componentRoots_subset_unionRoots hi hneg.1, hneg.2⟩
  rw [hwu α hαi, hu1, one_smul]

theorem finite_unionRoots : (unionRoots χ J).Finite :=
  (finite_setOf_isRoot τ).subset fun _ hα => isRoot_of_mem_unionRoots hα

theorem not_mem_negRoots_of_mem_posRoots_unionRoots
    {α : Fin τ.rank → ℤ}
    (hα : α ∈ posRoots (unionRoots χ J)) : α ∉ negRoots (unionRoots χ J) := fun h => by
  have h1 := hα.2
  have h2 := h.2
  rw [height_neg] at h2
  omega

theorem mem_negRoots_iff_height_neg
    {α : Fin τ.rank → ℤ} (hα : α ∈ unionRoots χ J) :
    α ∈ negRoots (unionRoots χ J) ↔ height α < 0 := by
  constructor
  · intro h
    have := h.2
    rw [height_neg] at this
    omega
  · intro h
    exact ⟨neg_mem_unionRoots hα, by rw [height_neg]; omega⟩

theorem ncard_unionInversionRoots_mul_rootReflection
    {w : WeylGroup τ}
    {β : Fin τ.rank → ℤ} (hβ : β ∈ unionSimpleRoots χ J) (hneg : height (w • β) < 0) :
    (unionInversionRoots χ J (w * rootReflection β)).ncard + 1 =
      (unionInversionRoots χ J w).ncard := by
  have hβr := isRoot_of_mem_unionSimpleRoots hβ
  have hβpos := mem_posRoots_of_mem_unionSimpleRoots hβ
  have heq : unionInversionRoots χ J (w * rootReflection β) =
      (rootReflection β • ·) '' (unionInversionRoots χ J w \ {β}) := by
    ext α
    constructor
    · rintro ⟨hα, hht⟩
      have hne : α ≠ β := by
        rintro rfl
        rw [mul_smul, rootReflection_smul_self hβr, smul_neg, height_neg] at hht
        omega
      refine ⟨rootReflection β • α,
        ⟨⟨rootReflection_smul_mem_posRoots_unionRoots hβ hα hne, ?_⟩, fun h => ?_⟩, ?_⟩
      · rwa [mul_smul] at hht
      · have h2 : α = -β := by
          have h3 := congrArg (rootReflection β • ·) (Set.mem_singleton_iff.1 h)
          simp only [smul_smul, rootReflection_mul_self hβr, one_smul] at h3
          rw [h3, rootReflection_smul_self hβr]
        have h4 := hα.2
        rw [h2, height_neg] at h4
        have := hβpos.2
        omega
      · simp only [smul_smul, rootReflection_mul_self hβr, one_smul]
    · rintro ⟨α', ⟨⟨hα', hht'⟩, hne'⟩, rfl⟩
      refine ⟨rootReflection_smul_mem_posRoots_unionRoots hβ hα' hne', ?_⟩
      show height ((w * rootReflection β) • (rootReflection β • α')) < 0
      rw [mul_smul, smul_smul (rootReflection β) (rootReflection β), rootReflection_mul_self hβr,
        one_smul]
      exact hht'
  have hfin : (unionInversionRoots χ J w).Finite := finite_unionRoots.subset fun _ h => h.1.1
  have hmem : β ∈ unionInversionRoots χ J w := ⟨hβpos, hneg⟩
  rw [heq, Set.ncard_image_of_injective _ (MulAction.injective _),
    Set.ncard_sdiff_singleton_of_mem hmem]
  have := (Set.ncard_pos hfin).2 ⟨β, hmem⟩
  omega

theorem ncard_unionInversionRoots_mul_reflectionWordProd
    {l : List (Fin τ.rank → ℤ)}
    (hl : ∀ β ∈ l, β ∈ unionSimpleRoots χ J) (horth : l.Pairwise fun β γ => iform β γ = 0)
    {w : WeylGroup τ} (hneg : ∀ γ ∈ l, height (w • γ) < 0) :
    (unionInversionRoots χ J (w * reflectionWordProd l)).ncard + l.length =
      (unionInversionRoots χ J w).ncard := by
  induction l generalizing w with
  | nil => rw [reflectionWordProd_nil, mul_one, List.length_nil, add_zero]
  | cons β l ih =>
    rw [List.pairwise_cons] at horth
    have hβ := hl β List.mem_cons_self
    have hβr := isRoot_of_mem_unionSimpleRoots hβ
    have h1 := ncard_unionInversionRoots_mul_rootReflection (w := w) hβ
      (hneg β List.mem_cons_self)
    have h2 := ih (fun γ hγ => hl γ (List.mem_cons_of_mem _ hγ)) horth.2
      (w := w * rootReflection β) (fun γ hγ => by
        rw [mul_smul, rootReflection_smul_of_iform_eq_zero hβr (horth.1 γ hγ)]
        exact hneg γ (List.mem_cons_of_mem _ hγ))
    rw [reflectionWordProd_cons, ← mul_assoc, List.length_cons]
    omega

theorem reflectionWordProd_mem_unionWeylGroup
    {l : List (Fin τ.rank → ℤ)}
    (hl : ∀ β ∈ l, β ∈ unionSimpleRoots χ J) : reflectionWordProd l ∈ unionWeylGroup χ J := by
  induction l with
  | nil => exact one_mem _
  | cons β l ih =>
    rw [reflectionWordProd_cons]
    exact mul_mem (rootReflection_mem_unionWeylGroup (hl β List.mem_cons_self))
      (ih fun γ hγ => hl γ (List.mem_cons_of_mem _ hγ))

theorem reflectionWordProd_smul_mem_posRoots
    {l : List (Fin τ.rank → ℤ)}
    (hl : ∀ β ∈ l, β ∈ unionSimpleRoots χ J) (horth : l.Pairwise fun β γ => iform β γ = 0)
    {α : Fin τ.rank → ℤ} (hα : α ∈ posRoots (unionRoots χ J)) (hαl : α ∉ l) :
    reflectionWordProd l • α ∈ posRoots (unionRoots χ J) ∧ reflectionWordProd l • α ∉ l := by
  induction l with
  | nil => exact ⟨by rwa [reflectionWordProd_nil, one_smul], List.not_mem_nil⟩
  | cons β l ih =>
    rw [List.pairwise_cons] at horth
    have hβ := hl β List.mem_cons_self
    have hβr := isRoot_of_mem_unionSimpleRoots hβ
    have hl' : ∀ γ ∈ l, γ ∈ unionSimpleRoots χ J := fun γ hγ => hl γ (List.mem_cons_of_mem _ hγ)
    have hαβ : α ≠ β := fun h => hαl (h ▸ List.mem_cons_self)
    obtain ⟨h1, h2⟩ := ih hl' horth.2 fun h => hαl (List.mem_cons_of_mem _ h)
    have hfix : reflectionWordProd l • β = β :=
      reflectionWordProd_smul_of_forall_iform_eq_zero
        (fun γ hγ => isRoot_of_mem_unionSimpleRoots (hl' γ hγ))
        fun γ hγ => by rw [iform_comm]; exact horth.1 γ hγ
    have hne : reflectionWordProd l • α ≠ β := fun h => hαβ (by
      rw [← hfix] at h
      exact smul_left_cancel _ h)
    rw [reflectionWordProd_cons, mul_smul]
    have hback : reflectionWordProd l • α =
        rootReflection β • (rootReflection β • (reflectionWordProd l • α)) := by
      rw [smul_smul, rootReflection_mul_self hβr, one_smul]
    refine ⟨rootReflection_smul_mem_posRoots_unionRoots hβ h1 hne, fun h => ?_⟩
    rcases List.mem_cons.1 h with h3 | h3
    · rw [h3, rootReflection_smul_self hβr] at hback
      have h5 := h1.2
      rw [hback, height_neg] at h5
      have := (mem_posRoots_of_mem_unionSimpleRoots hβ).2
      omega
    · rw [rootReflection_smul_of_iform_eq_zero hβr (horth.1 _ h3)] at hback
      exact h2 (by rw [hback]; exact h3)

theorem isUnionWeylConj_reflectionWordProd
    {θ : (Fin τ.rank → ℝ) →ₗ[ℝ] (Fin τ.rank → ℝ)}
    (hθ : ∀ x y, rform (θ x) (θ y) = rform x y) {l l' : List (Fin τ.rank → ℤ)}
    (hl : ∀ β ∈ l, β ∈ unionSimpleRoots χ J) (hl' : ∀ β ∈ l', β ∈ unionSimpleRoots χ J)
    (h : List.Forall₂ (fun β β' => θ (toReal β) = toReal β') l l') :
    IsUnionWeylConj χ J θ (reflectionWordProd l) (reflectionWordProd l') := by
  induction h with
  | nil => exact isUnionWeylConj_one
  | @cons β β' l₁ l₂ hββ' _ ih =>
    rw [reflectionWordProd_cons, reflectionWordProd_cons]
    have t1 : ∀ γ ∈ l₁, γ ∈ unionSimpleRoots χ J :=
      fun γ hγ => hl γ (List.mem_cons_of_mem _ hγ)
    have t2 : ∀ γ ∈ l₂, γ ∈ unionSimpleRoots χ J :=
      fun γ hγ => hl' γ (List.mem_cons_of_mem _ hγ)
    exact (isUnionWeylConj_rootReflection hθ
      (isRoot_of_mem_unionSimpleRoots (hl β List.mem_cons_self))
      (isRoot_of_mem_unionSimpleRoots (hl' β' List.mem_cons_self)) hββ').mul (ih t1 t2)
      (reflectionWordProd_mem_unionWeylGroup t1) (reflectionWordProd_mem_unionWeylGroup t2)

theorem iform_nonpos_of_mem_unionSimpleRoots
    {β γ : Fin τ.rank → ℤ}
    (hβ : β ∈ unionSimpleRoots χ J) (hγ : γ ∈ unionSimpleRoots χ J) (hne : β ≠ γ) :
    iform β γ ≤ 0 := by
  obtain ⟨i, -, hβi⟩ := hβ
  obtain ⟨j, -, hγj⟩ := hγ
  by_cases hij : i = j
  · subst hij
    exact iform_simpleRoots_nonpos (isRootComponent_componentRoots i) hβi hγj hne
  · rw [iform_eq_zero_of_mem_componentRoots hij (simpleRoots_subset hβi)
      (simpleRoots_subset hγj)]

end UnionWeyl

section ThetaOrbits

variable {τ : Tag}

theorem thetaOrbit_subset_of_mem (θ : (Fin τ.rank → ℝ) →ₗ[ℝ] (Fin τ.rank → ℝ))
    {α β : Fin τ.rank → ℤ} (h : β ∈ thetaOrbit θ α) : thetaOrbit θ β ⊆ thetaOrbit θ α := by
  obtain ⟨m, hm⟩ := h
  rintro γ ⟨j, hj⟩
  exact ⟨j + m, by rw [pow_add, Module.End.mul_apply, hm, hj]⟩

theorem pow_apply_mem_of_mapsTo {θ : (Fin τ.rank → ℝ) →ₗ[ℝ] (Fin τ.rank → ℝ)}
    {S : Set (Fin τ.rank → ℤ)} (h : Set.MapsTo θ (toReal '' S) (toReal '' S))
    {x : Fin τ.rank → ℝ} (hx : x ∈ toReal '' S) (m : ℕ) : (θ ^ m) x ∈ toReal '' S := by
  induction m with
  | zero => rwa [pow_zero, Module.End.one_apply]
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact h ih

theorem thetaOrbit_subset_of_mapsTo {θ : (Fin τ.rank → ℝ) →ₗ[ℝ] (Fin τ.rank → ℝ)}
    {S : Set (Fin τ.rank → ℤ)} (h : Set.MapsTo θ (toReal '' S) (toReal '' S))
    {α : Fin τ.rank → ℤ} (hα : α ∈ S) : thetaOrbit θ α ⊆ S := by
  rintro γ ⟨m, hm⟩
  obtain ⟨δ, hδ, e⟩ := pow_apply_mem_of_mapsTo h ⟨α, hα, rfl⟩ m
  rw [hm] at e
  rwa [← toReal_injective e]

end ThetaOrbits

namespace OrthogonalSemilinearFixedRootDatum

variable
    {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  (D : OrthogonalSemilinearFixedRootDatum τ p₀ k)

theorem exists_pow_eq_on_kernelRoots :
    ∃ n, 0 < n ∧ ∀ α ∈ kernelRoots D.χ, (D.θ ^ n) (toReal α) = toReal α := by
  have hfin : Finite (kernelRoots D.χ) := D.finite_kernelRoots.to_subtype
  let f : ℕ → kernelRoots D.χ → kernelRoots D.χ := fun m α =>
    ⟨thetaPowVec D.θ m α, (D.thetaPowVec_spec α.2 m).2.2⟩
  have key : ∀ a b : ℕ, a < b → f a = f b →
      ∃ n, 0 < n ∧ ∀ α ∈ kernelRoots D.χ, (D.θ ^ n) (toReal α) = toReal α := by
    intro a b hab hfab
    refine ⟨b - a, by omega, fun α hα => ?_⟩
    have h1 := congrArg (fun g => toReal (g ⟨α, hα⟩ : Fin τ.rank → ℤ)) hfab
    simp only [f] at h1
    rw [(D.thetaPowVec_spec hα a).1, (D.thetaPowVec_spec hα b).1] at h1
    have h2 : (D.θ ^ b) (toReal α) = (D.θ ^ a) ((D.θ ^ (b - a)) (toReal α)) := by
      rw [← Module.End.mul_apply, ← pow_add, Nat.add_sub_cancel' hab.le]
    rw [h2] at h1
    have hinj : Function.Injective (D.θ ^ a) := by
      rw [Module.End.coe_pow]
      exact D.theta_injective.iterate a
    exact (hinj h1).symm
  obtain ⟨m₁, m₂, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite f
  rcases lt_or_gt_of_ne hne with h | h
  · exact key m₁ m₂ h heq
  · exact key m₂ m₁ h heq.symm

theorem mem_thetaOrbit_symm
    {α β : Fin τ.rank → ℤ} (hα : α ∈ kernelRoots D.χ)
    (hβ : β ∈ thetaOrbit D.θ α) : α ∈ thetaOrbit D.θ β := by
  obtain ⟨n, hn, hper⟩ := D.exists_pow_eq_on_kernelRoots
  obtain ⟨m, hm⟩ := hβ
  refine ⟨(n - 1) * m, ?_⟩
  have e : (n - 1) * m + m = n * m := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hn]
  rw [← hm, ← Module.End.mul_apply, ← pow_add, e, pow_mul, Module.End.pow_apply]
  exact Function.iterate_fixed (hper α hα) m

theorem thetaOrbit_eq_of_mem
    {α β : Fin τ.rank → ℤ} (hα : α ∈ kernelRoots D.χ)
    (hβ : β ∈ thetaOrbit D.θ α) : thetaOrbit D.θ β = thetaOrbit D.θ α :=
  (thetaOrbit_subset_of_mem _ hβ).antisymm
    (thetaOrbit_subset_of_mem _ (D.mem_thetaOrbit_symm hα hβ))

theorem exists_theta_eq_of_mem_thetaOrbit
    {α β : Fin τ.rank → ℤ} (hα : α ∈ kernelRoots D.χ)
    (hβ : β ∈ thetaOrbit D.θ α) :
    ∃ γ ∈ thetaOrbit D.θ α, D.θ (toReal γ) = toReal β := by
  obtain ⟨n, hn, hper⟩ := D.exists_pow_eq_on_kernelRoots
  have hβK := D.thetaOrbit_subset_kernelRoots hα hβ
  have hspec := D.thetaPowVec_spec hβK (n - 1)
  refine ⟨thetaPowVec D.θ (n - 1) β, by
    rw [← D.thetaOrbit_eq_of_mem hα hβ]
    exact hspec.2.1, ?_⟩
  rw [hspec.1, ← Module.End.mul_apply, ← pow_succ', Nat.sub_add_cancel hn, hper β hβK]

theorem mapsTo_negRoots :
    Set.MapsTo D.θ (toReal '' negRoots D.roots) (toReal '' negRoots D.roots) := by
  rintro _ ⟨α, hα, rfl⟩
  obtain ⟨α', hα', e⟩ := D.bijOn_posRootsJ.mapsTo ⟨-α, (show -α ∈ D.posRootsJ from hα), rfl⟩
  refine ⟨-α', ?_, ?_⟩
  · show - -α' ∈ posRoots D.roots
    rw [neg_neg]
    exact hα'
  · rw [toReal_neg, e, toReal_neg, map_neg, neg_neg]

theorem thetaOrbit_subset_roots
    {α : Fin τ.rank → ℤ} (hα : α ∈ D.roots) :
    thetaOrbit D.θ α ⊆ D.roots :=
  thetaOrbit_subset_of_mapsTo D.mapsTo_roots hα

theorem thetaOrbit_subset_posRootsJ
    {α : Fin τ.rank → ℤ} (hα : α ∈ D.posRootsJ) :
    thetaOrbit D.θ α ⊆ D.posRootsJ :=
  thetaOrbit_subset_of_mapsTo D.bijOn_posRootsJ.mapsTo hα

theorem thetaOrbit_subset_negRoots
    {α : Fin τ.rank → ℤ} (hα : α ∈ negRoots D.roots) :
    thetaOrbit D.θ α ⊆ negRoots D.roots :=
  thetaOrbit_subset_of_mapsTo D.mapsTo_negRoots hα

theorem thetaOrbit_subset_simpleRootsJ
    {β : Fin τ.rank → ℤ} (hβ : β ∈ D.simpleRootsJ) :
    thetaOrbit D.θ β ⊆ D.simpleRootsJ :=
  thetaOrbit_subset_of_mapsTo D.mapsTo_simpleRootsJ hβ

theorem mem_simpleRootsJ_iff
    {β : Fin τ.rank → ℤ} :
    β ∈ D.simpleRootsJ ↔ β ∈ unionSimpleRoots D.χ D.J := by
  rw [D.simpleRootsJ_eq]

theorem eq_thetaOrbit_of_mem_orbits
    {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    {β : Fin τ.rank → ℤ} (hβ : β ∈ O) : O = thetaOrbit D.θ β := by
  obtain ⟨β₀, hβ₀, rfl⟩ := hO
  exact (D.thetaOrbit_eq_of_mem (D.mem_kernelRoots_of_mem_simpleRootsJ hβ₀) hβ).symm

theorem subset_simpleRootsJ_of_mem_orbits
    {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) :
    O ⊆ D.simpleRootsJ := by
  obtain ⟨β₀, hβ₀, rfl⟩ := hO
  exact D.thetaOrbit_subset_simpleRootsJ hβ₀

theorem mem_unionSimpleRoots_of_mem_orbits
    {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    {β : Fin τ.rank → ℤ} (hβ : β ∈ O) : β ∈ unionSimpleRoots D.χ D.J :=
  D.mem_simpleRootsJ_iff.1 (D.subset_simpleRootsJ_of_mem_orbits hO hβ)

theorem thetaOrbit_mem_orbits
    {β : Fin τ.rank → ℤ} (hβ : β ∈ D.simpleRootsJ) :
    thetaOrbit D.θ β ∈ D.orbits :=
  ⟨β, hβ, rfl⟩

theorem exists_list_of_mem_orbits
    {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) :
    ∃ l : List (Fin τ.rank → ℤ), l.Nodup ∧ (∀ β, β ∈ l ↔ β ∈ O) ∧
      l.Pairwise (fun β γ => iform β γ = 0) ∧ setReflection O = reflectionWordProd l := by
  obtain ⟨β₀, hβ₀, rfl⟩ := hO
  have hβ₀K := D.mem_kernelRoots_of_mem_simpleRootsJ hβ₀
  have hfin := D.finite_thetaOrbit hβ₀K
  have hmem : ∀ β, β ∈ hfin.toFinset.toList ↔ β ∈ thetaOrbit D.θ β₀ := fun β =>
    Finset.mem_toList.trans hfin.mem_toFinset
  refine ⟨hfin.toFinset.toList, Finset.nodup_toList _, hmem,
    (Finset.nodup_toList _).imp_of_mem fun ha hb hne =>
      D.orbit_orthogonal β₀ hβ₀K _ ((hmem _).1 ha) _ ((hmem _).1 hb) hne,
    D.setReflection_thetaOrbit_eq_list_prod hβ₀K (Finset.nodup_toList _) hmem⟩

end OrthogonalSemilinearFixedRootDatum

namespace OrthogonalSemilinearFixedRootDatum

variable
    {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  (D : OrthogonalSemilinearFixedRootDatum τ p₀ k)

theorem isRoot_of_mem_orbits
    {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    {β : Fin τ.rank → ℤ} (hβ : β ∈ O) : IsRoot τ β :=
  isRoot_of_mem_unionSimpleRoots (D.mem_unionSimpleRoots_of_mem_orbits hO hβ)

theorem mem_kernelRoots_of_mem_orbits
    {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    {β : Fin τ.rank → ℤ} (hβ : β ∈ O) : β ∈ kernelRoots D.χ :=
  D.mem_kernelRoots_of_mem_simpleRootsJ (D.subset_simpleRootsJ_of_mem_orbits hO hβ)

theorem finite_of_mem_orbits
    {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) : O.Finite := by
  obtain ⟨β₀, hβ₀, rfl⟩ := hO
  exact D.finite_thetaOrbit (D.mem_kernelRoots_of_mem_simpleRootsJ hβ₀)

theorem pairwise_commute_of_mem_orbits
    {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) :
    O.Pairwise fun β γ => Commute (rootReflection β) (rootReflection γ) := by
  obtain ⟨β₀, hβ₀, rfl⟩ := hO
  exact D.pairwise_commute_thetaOrbit (D.mem_kernelRoots_of_mem_simpleRootsJ hβ₀)

theorem setReflection_mem_unionWeylGroup
    {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) :
    setReflection O ∈ unionWeylGroup D.χ D.J := by
  obtain ⟨l, -, hmem, -, hset⟩ := D.exists_list_of_mem_orbits hO
  rw [hset]
  exact reflectionWordProd_mem_unionWeylGroup fun β hβ =>
    D.mem_unionSimpleRoots_of_mem_orbits hO ((hmem β).1 hβ)

theorem setReflection_smul_of_mem
    {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    {β : Fin τ.rank → ℤ} (hβ : β ∈ O) : setReflection O • β = -β := by
  obtain ⟨l, -, hmem, horth, hset⟩ := D.exists_list_of_mem_orbits hO
  rw [hset]
  exact reflectionWordProd_smul_of_mem (fun γ hγ => D.isRoot_of_mem_orbits hO ((hmem γ).1 hγ))
    horth ((hmem β).2 hβ)

theorem setReflection_mul_self
    {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) :
    setReflection O * setReflection O = 1 := by
  obtain ⟨l, -, hmem, horth, hset⟩ := D.exists_list_of_mem_orbits hO
  rw [hset]
  exact reflectionWordProd_mul_self (fun γ hγ => D.isRoot_of_mem_orbits hO ((hmem γ).1 hγ)) horth

theorem setReflection_inv
    {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) :
    (setReflection O)⁻¹ = setReflection O :=
  inv_eq_of_mul_eq_one_right (D.setReflection_mul_self hO)

theorem setReflection_smul_mem_posRootsJ
    {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    {α : Fin τ.rank → ℤ} (hα : α ∈ D.posRootsJ) (hαO : α ∉ O) :
    setReflection O • α ∈ D.posRootsJ ∧ setReflection O • α ∉ O := by
  obtain ⟨l, -, hmem, horth, hset⟩ := D.exists_list_of_mem_orbits hO
  rw [hset]
  have h := reflectionWordProd_smul_mem_posRoots
    (fun γ hγ => D.mem_unionSimpleRoots_of_mem_orbits hO ((hmem γ).1 hγ)) horth hα
    (fun h => hαO ((hmem α).1 h))
  exact ⟨h.1, fun h' => h.2 ((hmem _).2 h')⟩

theorem isUnionWeylConj_setReflection
    {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) :
    IsUnionWeylConj D.χ D.J D.θ (setReflection O) (setReflection O) := by
  obtain ⟨l, hnd, hmem, -, hset⟩ := D.exists_list_of_mem_orbits hO
  have hK : ∀ β ∈ O, β ∈ kernelRoots D.χ := fun β hβ => D.mem_kernelRoots_of_mem_orbits hO hβ
  have hθl : ∀ β ∈ O, D.θ (toReal β) = toReal (thetaPowVec D.θ 1 β) := fun β hβ => by
    rw [(D.thetaPowVec_spec (hK β hβ) 1).1, pow_one]
  have hmem' : ∀ β', β' ∈ l.map (thetaPowVec D.θ 1) ↔ β' ∈ O := by
    intro β'
    rw [List.mem_map]
    constructor
    · rintro ⟨β, hβ, rfl⟩
      have hβO := (hmem β).1 hβ
      rw [D.eq_thetaOrbit_of_mem_orbits hO hβO]
      exact (D.thetaPowVec_spec (hK β hβO) 1).2.1
    · intro hβ'
      obtain ⟨γ, hγ, e⟩ := D.exists_theta_eq_of_mem_thetaOrbit (hK β' hβ')
        (self_mem_thetaOrbit _ β')
      rw [← D.eq_thetaOrbit_of_mem_orbits hO hβ'] at hγ
      exact ⟨γ, (hmem γ).2 hγ, thetaPowVec_eq (by rw [pow_one]; exact e.symm)⟩
  have hnd' : (l.map (thetaPowVec D.θ 1)).Nodup := by
    refine hnd.map_on fun x hx y hy hxy => ?_
    have h1 := hθl x ((hmem x).1 hx)
    rw [hxy, ← hθl y ((hmem y).1 hy)] at h1
    exact toReal_injective (D.theta_injective h1)
  have hset' := setReflection_eq_list_prod (D.finite_of_mem_orbits hO)
    (D.pairwise_commute_of_mem_orbits hO) hnd' hmem'
  have h := isUnionWeylConj_reflectionWordProd (χ := D.χ) (J := D.J) D.isometry
    (fun β hβ => D.mem_unionSimpleRoots_of_mem_orbits hO ((hmem β).1 hβ))
    (fun β hβ => D.mem_unionSimpleRoots_of_mem_orbits hO ((hmem' β).1 hβ))
    (List.forall₂_map_right_iff.2 (List.forall₂_same.2 fun β hβ => hθl β ((hmem β).1 hβ)))
  rw [← hset] at h
  exact hset' ▸ h

theorem mul_setReflection_mul_inv
    (u : WeylGroup τ) {O : Set (Fin τ.rank → ℤ)}
    (hO : O ∈ D.orbits) :
    u * setReflection O * u⁻¹ = setReflection ((fun γ => u • γ) '' O) := by
  obtain ⟨l, hnd, hmem, horth, hset⟩ := D.exists_list_of_mem_orbits hO
  have hroots : ∀ β ∈ l, IsRoot τ β := fun β hβ => D.isRoot_of_mem_orbits hO ((hmem β).1 hβ)
  rw [hset, mul_reflectionWordProd_mul_inv u hroots]
  have hcomm : ((fun γ => u • γ) '' O).Pairwise
      fun β γ => Commute (rootReflection β) (rootReflection γ) := by
    rintro _ ⟨β, hβ, rfl⟩ _ ⟨γ, hγ, rfl⟩ hne
    have hβγ : β ≠ γ := fun h => hne (by rw [h])
    obtain ⟨β₀, hβ₀, rfl⟩ := hO
    have hβ₀K := D.mem_kernelRoots_of_mem_simpleRootsJ hβ₀
    have h0 : iform β γ = 0 := D.orbit_orthogonal β₀ hβ₀K β hβ γ hγ hβγ
    exact commute_rootReflection_of_iform_eq_zero
      (IsRoot.smul (D.thetaOrbit_subset_kernelRoots hβ₀K hβ).1 u)
      (IsRoot.smul (D.thetaOrbit_subset_kernelRoots hβ₀K hγ).1 u) (by rw [iform_smul, h0])
  refine (setReflection_eq_list_prod ((D.finite_of_mem_orbits hO).image _) hcomm
    (hnd.map (MulAction.injective u)) fun β' => ?_).symm
  rw [List.mem_map, Set.mem_image]
  exact ⟨fun ⟨β, hβ, e⟩ => ⟨β, (hmem β).1 hβ, e⟩, fun ⟨β, hβ, e⟩ => ⟨β, (hmem β).2 hβ, e⟩⟩

@[expose] def weylJ
    : Subgroup (WeylGroup τ) :=
  Subgroup.closure (rootReflection '' D.simpleRootsJ)

theorem weylJ_eq
    : D.weylJ = unionWeylGroup D.χ D.J := by
  rw [weylJ, D.simpleRootsJ_eq, unionWeylGroup]

theorem weylReal_mem_span
    {w : WeylGroup τ} (hw : w ∈ D.weylJ) {x : Fin τ.rank → ℝ}
    (hx : x ∈ Submodule.span ℝ (toReal '' D.roots)) :
    weylReal w x ∈ Submodule.span ℝ (toReal '' D.roots) := by
  rw [D.weylJ_eq] at hw
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨α, hα, rfl⟩ := hy
    rw [weylReal_toReal]
    exact Submodule.subset_span ⟨_, smul_mem_unionRoots hw hα, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ c hy

@[expose] def fixedWeyl
    : Subgroup (WeylGroup τ) where
  carrier := {w | w ∈ D.weylJ ∧ ∀ x ∈ Submodule.span ℝ (toReal '' D.roots),
    D.θ (weylReal w x) = weylReal w (D.θ x)}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, fun x hx => ?_⟩
    rw [weylReal_mul, weylReal_mul, ha' _ (D.weylReal_mem_span hb hx), hb' x hx]
  one_mem' := ⟨one_mem _, fun x _ => by rw [weylReal_one, weylReal_one]⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, fun x hx => ?_⟩
    have h1 := ha' _ (D.weylReal_mem_span (inv_mem ha) hx)
    rw [← weylReal_mul, mul_inv_cancel, weylReal_one] at h1
    calc D.θ (weylReal a⁻¹ x) = weylReal a⁻¹ (weylReal a (D.θ (weylReal a⁻¹ x))) := by
          rw [← weylReal_mul, inv_mul_cancel, weylReal_one]
      _ = weylReal a⁻¹ (D.θ x) := by rw [← h1]

theorem mem_fixedWeyl
    {w : WeylGroup τ} :
    w ∈ D.fixedWeyl ↔ w ∈ D.weylJ ∧ ∀ x ∈ Submodule.span ℝ (toReal '' D.roots),
      D.θ (weylReal w x) = weylReal w (D.θ x) :=
  Iff.rfl

theorem mem_fixedWeyl_iff
    {w : WeylGroup τ} :
    w ∈ D.fixedWeyl ↔ w ∈ unionWeylGroup D.χ D.J ∧ IsUnionWeylConj D.χ D.J D.θ w w := by
  rw [mem_fixedWeyl, D.weylJ_eq]
  refine and_congr_right fun _ => ⟨fun h α hα α' _ hαα' => ?_, fun h x hx => ?_⟩
  · have := h (toReal α) (Submodule.subset_span ⟨α, hα, rfl⟩)
    rw [weylReal_toReal, hαα', weylReal_toReal] at this
    exact this
  · induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨α, hα, rfl⟩ := hy
      obtain ⟨α', hα', e⟩ := D.mapsTo_roots ⟨α, hα, rfl⟩
      rw [weylReal_toReal, ← e, weylReal_toReal]
      exact h α hα α' hα' e.symm
    | zero => rw [map_zero, map_zero, map_zero]
    | add y z _ _ hy hz => rw [map_add, map_add, map_add, map_add, hy, hz]
    | smul c y _ hy => rw [map_smul, map_smul, map_smul, map_smul, hy]

theorem mem_unionWeylGroup_of_mem_fixedWeyl
    {w : WeylGroup τ} (hw : w ∈ D.fixedWeyl) :
    w ∈ unionWeylGroup D.χ D.J :=
  (D.mem_fixedWeyl_iff.1 hw).1

theorem setReflection_mem_fixedWeyl
    {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) :
    setReflection O ∈ D.fixedWeyl :=
  D.mem_fixedWeyl_iff.2 ⟨D.setReflection_mem_unionWeylGroup hO, D.isUnionWeylConj_setReflection hO⟩

theorem pow_toReal_smul
    {w : WeylGroup τ} (hw : w ∈ D.fixedWeyl) {α : Fin τ.rank → ℤ}
    (hα : α ∈ D.roots) {m : ℕ} {γ : Fin τ.rank → ℤ} (hγ : toReal γ = (D.θ ^ m) (toReal α)) :
    (D.θ ^ m) (toReal (w • α)) = toReal (w • γ) := by
  obtain ⟨-, hc⟩ := D.mem_fixedWeyl_iff.1 hw
  induction m generalizing γ with
  | zero =>
    rw [pow_zero, Module.End.one_apply] at hγ ⊢
    rw [toReal_injective hγ]
  | succ m ih =>
    have hspec := D.thetaPowVec_spec hα.1 m
    have hγ₀ : thetaPowVec D.θ m α ∈ D.roots := D.thetaOrbit_subset_roots hα hspec.2.1
    have hγΨ : γ ∈ D.roots := D.thetaOrbit_subset_roots hα ⟨m + 1, hγ.symm⟩
    rw [pow_succ', Module.End.mul_apply, ih hspec.1]
    refine hc _ hγ₀ γ hγΨ ?_
    rw [hspec.1, ← Module.End.mul_apply, ← pow_succ', hγ]

theorem image_smul_thetaOrbit
    {w : WeylGroup τ} (hw : w ∈ D.fixedWeyl) {α : Fin τ.rank → ℤ}
    (hα : α ∈ D.roots) :
    (fun γ => w • γ) '' thetaOrbit D.θ α = thetaOrbit D.θ (w • α) := by
  ext δ
  constructor
  · rintro ⟨γ, ⟨m, hm⟩, rfl⟩
    exact ⟨m, D.pow_toReal_smul hw hα hm.symm⟩
  · rintro ⟨m, hm⟩
    have hspec := D.thetaPowVec_spec hα.1 m
    refine ⟨thetaPowVec D.θ m α, hspec.2.1, ?_⟩
    apply toReal_injective
    rw [← hm, D.pow_toReal_smul hw hα hspec.1]

end OrthogonalSemilinearFixedRootDatum

namespace OrthogonalSemilinearFixedRootDatum

variable
    {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  (D : OrthogonalSemilinearFixedRootDatum τ p₀ k)

@[expose] def posOrbits :
    Set (Set (Fin τ.rank → ℤ)) :=
  {P | ∃ α ∈ D.posRootsJ, P = thetaOrbit D.θ α}

theorem nonempty_of_mem_orbits
    {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) : O.Nonempty := by
  obtain ⟨β₀, -, rfl⟩ := hO
  exact ⟨β₀, self_mem_thetaOrbit _ _⟩

theorem mem_roots_of_mem_orbits
    {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    {β : Fin τ.rank → ℤ} (hβ : β ∈ O) : β ∈ D.roots :=
  (D.subset_simpleRootsJ_of_mem_orbits hO hβ).2

theorem mem_posRootsJ_of_mem_orbits
    {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    {β : Fin τ.rank → ℤ} (hβ : β ∈ O) : β ∈ D.posRootsJ :=
  mem_posRoots_of_mem_unionSimpleRoots (D.mem_unionSimpleRoots_of_mem_orbits hO hβ)

theorem image_subset_negRoots_iff
    {w : WeylGroup τ} (hw : w ∈ D.fixedWeyl)
    {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) {β : Fin τ.rank → ℤ} (hβ : β ∈ O) :
    (fun γ => w • γ) '' O ⊆ negRoots D.roots ↔ w • β ∈ negRoots D.roots := by
  refine ⟨fun h => h ⟨β, hβ, rfl⟩, fun h => ?_⟩
  rw [D.eq_thetaOrbit_of_mem_orbits hO hβ,
    D.image_smul_thetaOrbit hw (D.mem_roots_of_mem_orbits hO hβ)]
  exact D.thetaOrbit_subset_negRoots h

theorem not_image_subset_negRoots_iff
    {w : WeylGroup τ} (hw : w ∈ D.fixedWeyl)
    {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) {β : Fin τ.rank → ℤ} (hβ : β ∈ O) :
    ¬(fun γ => w • γ) '' O ⊆ negRoots D.roots ↔ w • β ∈ D.posRootsJ := by
  rw [D.image_subset_negRoots_iff hw hO hβ]
  have hmem := smul_mem_unionRoots (D.mem_unionWeylGroup_of_mem_fixedWeyl hw)
    (D.mem_roots_of_mem_orbits hO hβ)
  refine ⟨fun h => (mem_posRoots_or_mem_negRoots_unionRoots hmem).resolve_right h,
    fun h => not_mem_negRoots_of_mem_posRoots_unionRoots h⟩

theorem exists_orbits_image_subset_negRoots
    {w : WeylGroup τ} (hw : w ∈ D.fixedWeyl)
    (hne : w ≠ 1) : ∃ O ∈ D.orbits, (fun γ => w • γ) '' O ⊆ negRoots D.roots := by
  obtain ⟨β, hβ, hneg⟩ :=
    exists_unionSimpleRoots_smul_mem_negRoots (D.mem_unionWeylGroup_of_mem_fixedWeyl hw) hne
  have hβ' : β ∈ D.simpleRootsJ := D.mem_simpleRootsJ_iff.2 hβ
  exact ⟨_, D.thetaOrbit_mem_orbits hβ',
    (D.image_subset_negRoots_iff hw (D.thetaOrbit_mem_orbits hβ') (self_mem_thetaOrbit _ β)).2
      hneg⟩

theorem ncard_unionInversionRoots_mul_setReflection_lt
    {w : WeylGroup τ}
    {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    (hneg : (fun γ => w • γ) '' O ⊆ negRoots D.roots) :
    (unionInversionRoots D.χ D.J (w * setReflection O)).ncard <
      (unionInversionRoots D.χ D.J w).ncard := by
  obtain ⟨l, -, hmem, horth, hset⟩ := D.exists_list_of_mem_orbits hO
  have h := ncard_unionInversionRoots_mul_reflectionWordProd (χ := D.χ) (J := D.J)
    (fun β hβ => D.mem_unionSimpleRoots_of_mem_orbits hO ((hmem β).1 hβ)) horth (w := w)
    (fun γ hγ => by
      have h1 : 0 < height (-(w • γ)) := (hneg ⟨γ, (hmem γ).1 hγ, rfl⟩).2
      rw [height_neg] at h1
      omega)
  obtain ⟨β, hβ⟩ := D.nonempty_of_mem_orbits hO
  have hpos : 0 < l.length := List.length_pos_of_mem ((hmem β).2 hβ)
  rw [hset]
  omega

theorem fixedWeyl_le_closure
    : D.fixedWeyl ≤ Subgroup.closure (setReflection '' D.orbits) := by
  suffices h : ∀ n, ∀ w ∈ D.fixedWeyl, (unionInversionRoots D.χ D.J w).ncard = n →
      w ∈ Subgroup.closure (setReflection '' D.orbits) from
    fun w hw => h _ w hw rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro w hw hn
    by_cases h1 : w = 1
    · rw [h1]
      exact one_mem _
    obtain ⟨O, hO, hneg⟩ := D.exists_orbits_image_subset_negRoots hw h1
    have hlt := D.ncard_unionInversionRoots_mul_setReflection_lt hO hneg
    have hmem := ih _ (hn ▸ hlt) (w * setReflection O)
      (mul_mem hw (D.setReflection_mem_fixedWeyl hO)) rfl
    have e : w = w * setReflection O * setReflection O := by
      rw [mul_assoc, D.setReflection_mul_self hO, mul_one]
    rw [e]
    exact mul_mem hmem (Subgroup.subset_closure ⟨O, hO, rfl⟩)

theorem fixedWeyl_eq_closure
    : D.fixedWeyl = Subgroup.closure (setReflection '' D.orbits) :=
  le_antisymm D.fixedWeyl_le_closure ((Subgroup.closure_le _).2 (by
    rintro _ ⟨O, hO, rfl⟩
    exact D.setReflection_mem_fixedWeyl hO))

theorem eq_one_of_forall_image_thetaOrbit
    {w : WeylGroup τ} (hw : w ∈ D.fixedWeyl)
    (h : ∀ α ∈ D.roots, (fun γ => w • γ) '' thetaOrbit D.θ α = thetaOrbit D.θ α) : w = 1 := by
  by_contra hne
  obtain ⟨O, hO, hneg⟩ := D.exists_orbits_image_subset_negRoots hw hne
  obtain ⟨β, hβ⟩ := D.nonempty_of_mem_orbits hO
  have h1 : w • β ∈ thetaOrbit D.θ β := by
    rw [← h β (D.mem_roots_of_mem_orbits hO hβ)]
    exact ⟨β, self_mem_thetaOrbit _ _, rfl⟩
  exact not_mem_negRoots_of_mem_posRoots_unionRoots
    (D.thetaOrbit_subset_posRootsJ (D.mem_posRootsJ_of_mem_orbits hO hβ) h1) (hneg ⟨β, hβ, rfl⟩)

theorem image_setReflection_self
    {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) :
    (fun γ => setReflection O • γ) '' O = (fun γ => -γ) '' O :=
  Set.image_congr fun _ hβ => D.setReflection_smul_of_mem hO hβ

theorem bijOn_image_setReflection
    {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) :
    Set.BijOn (fun P => (fun γ => setReflection O • γ) '' P) (D.posOrbits \ {O})
      (D.posOrbits \ {O}) := by
  have hrO := D.setReflection_mem_fixedWeyl hO
  have hmaps : Set.MapsTo (fun P => (fun γ => setReflection O • γ) '' P) (D.posOrbits \ {O})
      (D.posOrbits \ {O}) := by
    rintro P ⟨⟨α, hα, rfl⟩, hPO⟩
    have hαO : α ∉ O := fun h =>
      hPO (Set.mem_singleton_iff.2 (D.eq_thetaOrbit_of_mem_orbits hO h).symm)
    obtain ⟨h1, h2⟩ := D.setReflection_smul_mem_posRootsJ hO hα hαO
    refine ⟨⟨_, h1, D.image_smul_thetaOrbit hrO hα.1⟩, fun h => h2 ?_⟩
    have h' : (fun γ => setReflection O • γ) '' thetaOrbit D.θ α = O := h
    have h3 : setReflection O • α ∈ (fun γ => setReflection O • γ) '' thetaOrbit D.θ α :=
      ⟨α, self_mem_thetaOrbit _ _, rfl⟩
    rwa [h'] at h3
  refine Set.InvOn.bijOn ⟨fun P _ => ?_, fun P _ => ?_⟩ hmaps hmaps <;>
    simp only [Set.image_image, smul_smul, D.setReflection_mul_self hO, one_smul, Set.image_id']

end OrthogonalSemilinearFixedRootDatum

section OrbitWords

variable {τ : Tag}

@[expose] def orbitWordProd
    (l : List (Set (Fin τ.rank → ℤ))) : WeylGroup τ :=
  (l.map setReflection).prod

theorem orbitWordProd_nil
    : orbitWordProd ([] : List (Set (Fin τ.rank → ℤ))) = 1 :=
  rfl

theorem orbitWordProd_cons
    (O : Set (Fin τ.rank → ℤ)) (l : List (Set (Fin τ.rank → ℤ))) :
    orbitWordProd (O :: l) = setReflection O * orbitWordProd l := by
  simp [orbitWordProd]

theorem orbitWordProd_append
    (l l' : List (Set (Fin τ.rank → ℤ))) :
    orbitWordProd (l ++ l') = orbitWordProd l * orbitWordProd l' := by
  simp [orbitWordProd]

theorem orbitWordProd_prefix_succ
    {l : List (Set (Fin τ.rank → ℤ))} {j : ℕ}
    (hj : j < l.length) :
    orbitWordProd (l.take (j + 1)) = orbitWordProd (l.take j) * setReflection l[j] := by
  rw [List.take_succ_eq_append_getElem hj, orbitWordProd_append]
  simp [orbitWordProd]

theorem list_reverse_eraseIdx_reverse {α : Type*} (l : List α) {j : ℕ} (hj : j < l.length) :
    (l.reverse.eraseIdx j).reverse = l.eraseIdx (l.length - 1 - j) := by
  rw [List.eraseIdx_eq_take_drop_succ, List.eraseIdx_eq_take_drop_succ, List.reverse_append,
    List.take_reverse, List.drop_reverse, List.reverse_reverse, List.reverse_reverse]
  congr 2 <;> omega

end OrbitWords

namespace OrthogonalSemilinearFixedRootDatum

variable
    {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  (D : OrthogonalSemilinearFixedRootDatum τ p₀ k)

@[expose] def IsOrbitWord
    (l : List (Set (Fin τ.rank → ℤ))) : Prop :=
  ∀ O ∈ l, O ∈ D.orbits

@[expose] def foldedLength
    (w : WeylGroup τ) : ℕ :=
  sInf {n | ∃ l, D.IsOrbitWord l ∧ l.length = n ∧ orbitWordProd l = w}

variable {D}

theorem IsOrbitWord.cons
    {O : Set (Fin τ.rank → ℤ)} {l : List (Set (Fin τ.rank → ℤ))}
    (hO : O ∈ D.orbits) (hl : D.IsOrbitWord l) : D.IsOrbitWord (O :: l) := by
  intro P hP
  rcases List.mem_cons.1 hP with rfl | h
  · exact hO
  · exact hl P h

theorem IsOrbitWord.append
    {l l' : List (Set (Fin τ.rank → ℤ))} (hl : D.IsOrbitWord l)
    (hl' : D.IsOrbitWord l') : D.IsOrbitWord (l ++ l') := fun O hO => by
  rcases List.mem_append.1 hO with h | h
  · exact hl O h
  · exact hl' O h

theorem IsOrbitWord.reverse
    {l : List (Set (Fin τ.rank → ℤ))} (hl : D.IsOrbitWord l) :
    D.IsOrbitWord l.reverse := fun O hO => hl O (List.mem_reverse.1 hO)

theorem IsOrbitWord.sublist
    {l l' : List (Set (Fin τ.rank → ℤ))} (hl : D.IsOrbitWord l)
    (h : l'.Sublist l) : D.IsOrbitWord l' := fun O hO => hl O (h.subset hO)

variable (D)

theorem orbitWordProd_inv
    {l : List (Set (Fin τ.rank → ℤ))} (hl : D.IsOrbitWord l) :
    (orbitWordProd l)⁻¹ = orbitWordProd l.reverse := by
  induction l with
  | nil => simp [orbitWordProd]
  | cons O l ih =>
    rw [orbitWordProd_cons, mul_inv_rev, ih (fun P hP => hl P (List.mem_cons_of_mem _ hP)),
      List.reverse_cons, orbitWordProd_append, orbitWordProd_cons, orbitWordProd_nil, mul_one,
      D.setReflection_inv (hl O List.mem_cons_self)]

theorem orbitWordProd_mem
    {l : List (Set (Fin τ.rank → ℤ))} (hl : D.IsOrbitWord l) :
    orbitWordProd l ∈ D.fixedWeyl := by
  induction l with
  | nil => exact one_mem _
  | cons O l ih =>
    rw [orbitWordProd_cons]
    exact mul_mem (D.setReflection_mem_fixedWeyl (hl O List.mem_cons_self))
      (ih fun P hP => hl P (List.mem_cons_of_mem _ hP))

theorem mem_fixedWeyl_iff_exists_word
    {w : WeylGroup τ} :
    w ∈ D.fixedWeyl ↔ ∃ l, D.IsOrbitWord l ∧ orbitWordProd l = w := by
  refine ⟨fun hw => ?_, fun ⟨l, hl, e⟩ => e ▸ D.orbitWordProd_mem hl⟩
  rw [D.fixedWeyl_eq_closure] at hw
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨O, hO, rfl⟩ := hx
    exact ⟨[O], fun P hP => by rw [List.mem_singleton.1 hP]; exact hO, by
      simp [orbitWordProd]⟩
  | one => exact ⟨[], fun _ h => absurd h List.not_mem_nil, rfl⟩
  | mul x y _ _ hx hy =>
    obtain ⟨l, hl, rfl⟩ := hx
    obtain ⟨l', hl', rfl⟩ := hy
    exact ⟨l ++ l', hl.append hl', orbitWordProd_append l l'⟩
  | inv x _ hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    exact ⟨l.reverse, hl.reverse, (D.orbitWordProd_inv hl).symm⟩

theorem exists_reduced_word
    {w : WeylGroup τ} (hw : w ∈ D.fixedWeyl) :
    ∃ l, D.IsOrbitWord l ∧ l.length = D.foldedLength w ∧ orbitWordProd l = w := by
  obtain ⟨l, hl, e⟩ := D.mem_fixedWeyl_iff_exists_word.1 hw
  have h : D.foldedLength w ∈
      {n | ∃ l, D.IsOrbitWord l ∧ l.length = n ∧ orbitWordProd l = w} :=
    Nat.sInf_mem ⟨l.length, l, hl, rfl, e⟩
  exact h

theorem foldedLength_le
    {l : List (Set (Fin τ.rank → ℤ))} (hl : D.IsOrbitWord l) :
    D.foldedLength (orbitWordProd l) ≤ l.length :=
  Nat.sInf_le ⟨l, hl, rfl, rfl⟩

theorem foldedLength_one
    : D.foldedLength (1 : WeylGroup τ) = 0 :=
  Nat.eq_zero_of_le_zero (D.foldedLength_le (l := []) fun _ h => absurd h List.not_mem_nil)

theorem foldedLength_inv
    {w : WeylGroup τ} (hw : w ∈ D.fixedWeyl) :
    D.foldedLength w⁻¹ = D.foldedLength w := by
  have key : ∀ x ∈ D.fixedWeyl, D.foldedLength x⁻¹ ≤ D.foldedLength x := by
    intro x hx
    obtain ⟨l, hl, hlen, e⟩ := D.exists_reduced_word hx
    rw [← hlen, ← e, D.orbitWordProd_inv hl, ← List.length_reverse]
    exact D.foldedLength_le hl.reverse
  refine le_antisymm (key w hw) ?_
  have := key w⁻¹ (inv_mem hw)
  rwa [inv_inv] at this

theorem foldedLength_setReflection_mul_le
    {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    {w : WeylGroup τ} (hw : w ∈ D.fixedWeyl) :
    D.foldedLength (setReflection O * w) ≤ D.foldedLength w + 1 := by
  obtain ⟨l, hl, hlen, e⟩ := D.exists_reduced_word hw
  have := D.foldedLength_le (hl.cons hO)
  rwa [orbitWordProd_cons, e, List.length_cons, hlen] at this

theorem exists_eraseIdx_of_smul_mem_negRoots
    {l : List (Set (Fin τ.rank → ℤ))}
    (hl : D.IsOrbitWord l) {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    {β : Fin τ.rank → ℤ} (hβ : β ∈ O) (hneg : (orbitWordProd l)⁻¹ • β ∈ negRoots D.roots) :
    ∃ j < l.length, setReflection O * orbitWordProd l = orbitWordProd (l.eraseIdx j) := by
  classical
  have hβpos := D.mem_posRootsJ_of_mem_orbits hO hβ
  have hlne : l ≠ [] := by
    rintro rfl
    rw [orbitWordProd_nil, inv_one, one_smul] at hneg
    exact not_mem_negRoots_of_mem_posRoots_unionRoots hβpos hneg
  have hex : ∃ k, k < l.length ∧ (orbitWordProd (l.take (k + 1)))⁻¹ • β ∉ D.posRootsJ := by
    refine ⟨l.length - 1, by
      have := List.length_pos_iff.2 hlne
      omega, ?_⟩
    have : l.length - 1 + 1 = l.length := by
      have := List.length_pos_iff.2 hlne
      omega
    rw [this, List.take_length]
    exact fun h => not_mem_negRoots_of_mem_posRoots_unionRoots h hneg
  set j := Nat.find hex with hjdef
  obtain ⟨hjlt, hjneg⟩ := Nat.find_spec hex
  have hδj : (orbitWordProd (l.take j))⁻¹ • β ∈ D.posRootsJ := by
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · rw [h0, List.take_zero, orbitWordProd_nil, inv_one, one_smul]
      exact hβpos
    · have hmin := Nat.find_min hex (show j - 1 < j by omega)
      push Not at hmin
      have : j - 1 + 1 = j := by omega
      rw [this] at hmin
      exact hmin (by omega)
  have hlj : l[j] ∈ D.orbits := hl _ (List.getElem_mem hjlt)
  have hPw : orbitWordProd (l.take j) ∈ D.fixedWeyl :=
    D.orbitWordProd_mem (hl.sublist (List.take_sublist _ _))
  set P := orbitWordProd (l.take j) with hP
  have hδmem : P⁻¹ • β ∈ l[j] := by
    by_contra hne
    apply hjneg
    rw [orbitWordProd_prefix_succ hjlt, mul_inv_rev, D.setReflection_inv hlj, mul_smul]
    exact (D.setReflection_smul_mem_posRootsJ hlj hδj hne).1
  have himg : (fun γ => P⁻¹ • γ) '' O = l[j] := by
    rw [D.eq_thetaOrbit_of_mem_orbits hO hβ,
      D.image_smul_thetaOrbit (inv_mem hPw) (D.mem_roots_of_mem_orbits hO hβ),
      ← D.eq_thetaOrbit_of_mem_orbits hlj hδmem]
  have hr : setReflection l[j] = P⁻¹ * setReflection O * P := by
    rw [← himg, ← D.mul_setReflection_mul_inv P⁻¹ hO, inv_inv]
  set Q := orbitWordProd (l.drop (j + 1)) with hQ
  have hsplit : orbitWordProd l = P * setReflection l[j] * Q := by
    conv_lhs => rw [← List.take_append_drop (j + 1) l]
    rw [orbitWordProd_append, orbitWordProd_prefix_succ hjlt]
  have herase : orbitWordProd (l.eraseIdx j) = P * Q := by
    rw [List.eraseIdx_eq_take_drop_succ, orbitWordProd_append]
  refine ⟨j, hjlt, ?_⟩
  rw [hsplit, herase, hr]
  calc setReflection O * (P * (P⁻¹ * setReflection O * P) * Q) =
      (setReflection O * setReflection O) * P * Q := by group
    _ = P * Q := by rw [D.setReflection_mul_self hO, one_mul]

theorem foldedLength_setReflection_mul_of_neg
    {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    {β : Fin τ.rank → ℤ} (hβ : β ∈ O) {w : WeylGroup τ} (hw : w ∈ D.fixedWeyl)
    (hneg : w⁻¹ • β ∈ negRoots D.roots) :
    D.foldedLength (setReflection O * w) = D.foldedLength w - 1 ∧ 1 ≤ D.foldedLength w := by
  obtain ⟨l, hl, hlen, rfl⟩ := D.exists_reduced_word hw
  obtain ⟨j, hj, hj'⟩ := D.exists_eraseIdx_of_smul_mem_negRoots hl hO hβ hneg
  have h1 : D.foldedLength (setReflection O * orbitWordProd l) ≤
      D.foldedLength (orbitWordProd l) - 1 := by
    rw [hj']
    refine (D.foldedLength_le (hl.sublist (List.eraseIdx_sublist l j))).trans ?_
    rw [List.length_eraseIdx_of_lt hj, hlen]
  have h2 := D.foldedLength_setReflection_mul_le hO
    (mul_mem (D.setReflection_mem_fixedWeyl hO) hw)
  rw [← mul_assoc, D.setReflection_mul_self hO, one_mul] at h2
  have h3 : 1 ≤ D.foldedLength (orbitWordProd l) := by
    rw [← hlen]
    rcases l with _ | ⟨γ, l⟩
    · simp at hj
    · simp
  exact ⟨by omega, h3⟩

theorem foldedLength_setReflection_mul_of_pos
    {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    {β : Fin τ.rank → ℤ} (hβ : β ∈ O) {w : WeylGroup τ} (hw : w ∈ D.fixedWeyl)
    (hpos : w⁻¹ • β ∈ D.posRootsJ) :
    D.foldedLength (setReflection O * w) = D.foldedLength w + 1 := by
  have hw' := mul_mem (D.setReflection_mem_fixedWeyl hO) hw
  have hneg : (setReflection O * w)⁻¹ • β ∈ negRoots D.roots := by
    rw [mul_inv_rev, mul_smul, D.setReflection_inv hO, D.setReflection_smul_of_mem hO hβ,
      smul_neg]
    show - -(w⁻¹ • β) ∈ posRoots D.roots
    rw [neg_neg]
    exact hpos
  obtain ⟨h1, h2⟩ := D.foldedLength_setReflection_mul_of_neg hO hβ hw' hneg
  rw [← mul_assoc, D.setReflection_mul_self hO, one_mul] at h1
  omega

theorem foldedLength_setReflection_mul
    {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    {w : WeylGroup τ} (hw : w ∈ D.fixedWeyl) :
    (D.foldedLength (setReflection O * w) = D.foldedLength w - 1 ↔
      (fun γ => w⁻¹ • γ) '' O ⊆ negRoots D.roots) ∧
    (¬(fun γ => w⁻¹ • γ) '' O ⊆ negRoots D.roots →
      D.foldedLength (setReflection O * w) = D.foldedLength w + 1) := by
  obtain ⟨β, hβ⟩ := D.nonempty_of_mem_orbits hO
  have hw' := inv_mem hw
  have hpos : ¬(fun γ => w⁻¹ • γ) '' O ⊆ negRoots D.roots → w⁻¹ • β ∈ D.posRootsJ :=
    (D.not_image_subset_negRoots_iff hw' hO hβ).1
  rw [D.image_subset_negRoots_iff hw' hO hβ] at hpos ⊢
  refine ⟨⟨fun h => ?_, fun h => (D.foldedLength_setReflection_mul_of_neg hO hβ hw h).1⟩,
    fun h => D.foldedLength_setReflection_mul_of_pos hO hβ hw (hpos h)⟩
  by_contra hn
  have := D.foldedLength_setReflection_mul_of_pos hO hβ hw (hpos hn)
  omega

theorem foldedLength_mul_setReflection
    {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    {w : WeylGroup τ} (hw : w ∈ D.fixedWeyl) :
    (D.foldedLength (w * setReflection O) = D.foldedLength w - 1 ↔
      (fun γ => w • γ) '' O ⊆ negRoots D.roots) ∧
    (¬(fun γ => w • γ) '' O ⊆ negRoots D.roots →
      D.foldedLength (w * setReflection O) = D.foldedLength w + 1) := by
  have hw' := mul_mem hw (D.setReflection_mem_fixedWeyl hO)
  have e : D.foldedLength (w * setReflection O) = D.foldedLength (setReflection O * w⁻¹) := by
    rw [← D.foldedLength_inv hw', mul_inv_rev, D.setReflection_inv hO]
  have h := D.foldedLength_setReflection_mul hO (inv_mem hw)
  rw [inv_inv, D.foldedLength_inv hw] at h
  rw [e]
  exact h

theorem exists_eraseIdx_mul_setReflection
    {l : List (Set (Fin τ.rank → ℤ))}
    (hl : D.IsOrbitWord l) {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    {β : Fin τ.rank → ℤ} (hβ : β ∈ O) (hneg : orbitWordProd l • β ∈ negRoots D.roots) :
    ∃ j < l.length, orbitWordProd l * setReflection O = orbitWordProd (l.eraseIdx j) := by
  have hl' := hl.reverse
  have hneg' : (orbitWordProd l.reverse)⁻¹ • β ∈ negRoots D.roots := by
    rw [← D.orbitWordProd_inv hl, inv_inv]
    exact hneg
  obtain ⟨j, hj, e⟩ := D.exists_eraseIdx_of_smul_mem_negRoots hl' hO hβ hneg'
  rw [List.length_reverse] at hj
  have e2 : orbitWordProd l * setReflection O = orbitWordProd (l.reverse.eraseIdx j).reverse := by
    rw [← D.orbitWordProd_inv (hl'.sublist (List.eraseIdx_sublist _ _)), ← e, mul_inv_rev,
      D.setReflection_inv hO, D.orbitWordProd_inv hl', List.reverse_reverse]
  exact ⟨l.length - 1 - j, by omega, by rw [e2, list_reverse_eraseIdx_reverse l hj]⟩

end OrthogonalSemilinearFixedRootDatum

namespace OrthogonalSemilinearFixedRootDatum

variable
    {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  (D : OrthogonalSemilinearFixedRootDatum τ p₀ k)

theorem exists_longest :
    ∃ w₀ ∈ D.fixedWeyl, (fun α => w₀ • α) '' D.posRootsJ = negRoots D.roots := by
  classical
  have hfin : (D.fixedWeyl : Set (WeylGroup τ)).Finite := Set.toFinite _
  obtain ⟨w₀, hw₀, hmax⟩ := hfin.exists_maximalFor D.foldedLength _ ⟨1, one_mem D.fixedWeyl⟩
  have hw₀J := D.mem_unionWeylGroup_of_mem_fixedWeyl hw₀
  have hsimple : ∀ β ∈ unionSimpleRoots D.χ D.J, height (w₀ • β) < 0 := by
    intro β hβ
    have hβ' : β ∈ D.simpleRootsJ := D.mem_simpleRootsJ_iff.2 hβ
    have hO := D.thetaOrbit_mem_orbits hβ'
    have hneg : (fun γ => w₀ • γ) '' thetaOrbit D.θ β ⊆ negRoots D.roots := by
      by_contra hn
      have h := (D.foldedLength_mul_setReflection hO hw₀).2 hn
      have := hmax (mul_mem hw₀ (D.setReflection_mem_fixedWeyl hO)) (by omega)
      omega
    have h1 : 0 < height (-(w₀ • β)) := (hneg ⟨β, self_mem_thetaOrbit _ _, rfl⟩).2
    rw [height_neg] at h1
    omega
  have hpos : ∀ α ∈ D.posRootsJ, w₀ • α ∈ negRoots D.roots := by
    intro α hα
    obtain ⟨i, hi, hαi⟩ := mem_unionRoots_iff.1 hα.1
    obtain ⟨c, hc, e⟩ := exists_nonneg_coords (isRootComponent_componentRoots i) ⟨hαi, hα.2⟩
    have hmem := smul_mem_unionRoots hw₀J hα.1
    have hht : height (w₀ • α) ≤ 0 := by
      rw [e, Finset.smul_sum, height_finset_sum]
      refine Finset.sum_nonpos fun β hβ => ?_
      rw [smul_comm w₀ (c β) β, height_zsmul]
      exact mul_nonpos_of_nonneg_of_nonpos (hc β hβ) (hsimple β ⟨i, hi, hβ⟩).le
    rcases mem_posRoots_or_mem_negRoots_unionRoots hmem with h | h
    · exact absurd h.2 (by omega)
    · exact h
  refine ⟨w₀, hw₀, Set.Subset.antisymm ?_ fun γ hγ => ?_⟩
  · rintro _ ⟨α, hα, rfl⟩
    exact hpos α hα
  · have hγΨ : γ ∈ D.roots := by
      have := neg_mem_unionRoots hγ.1
      rwa [neg_neg] at this
    have hmem := smul_mem_unionRoots (inv_mem hw₀J) hγΨ
    refine ⟨w₀⁻¹ • γ, ?_, smul_inv_smul w₀ γ⟩
    rcases mem_posRoots_or_mem_negRoots_unionRoots hmem with h | h
    · exact h
    · exfalso
      have h1 := hpos _ h
      rw [smul_neg, smul_inv_smul] at h1
      have h2 := h1.2
      rw [neg_neg] at h2
      have h3 := hγ.2
      rw [height_neg] at h3
      omega

theorem mk_eq_of_pow
    {a b : kernelRoots D.χ} (hab : (⟦a⟧ : KernelComponent D.χ) = ⟦b⟧) (m : ℕ)
    {a' b' : kernelRoots D.χ} (ha : (D.θ ^ m) (toReal a) = toReal a')
    (hb : (D.θ ^ m) (toReal b) = toReal b') : (⟦a'⟧ : KernelComponent D.χ) = ⟦b'⟧ := by
  induction m generalizing a' b' with
  | zero =>
    rw [pow_zero, Module.End.one_apply] at ha hb
    have e1 : a = a' := Subtype.ext (toReal_injective ha)
    have e2 : b = b' := Subtype.ext (toReal_injective hb)
    rw [← e1, ← e2]
    exact hab
  | succ m ih =>
    have hsa := D.thetaPowVec_spec a.2 m
    have hsb := D.thetaPowVec_spec b.2 m
    refine D.mk_eq_of_theta (ih (a' := ⟨_, hsa.2.2⟩) (b' := ⟨_, hsb.2.2⟩) hsa.1.symm hsb.1.symm)
      ?_ ?_
    · show D.θ (toReal (thetaPowVec D.θ m a)) = toReal a'
      rw [hsa.1, ← Module.End.mul_apply, ← pow_succ']
      exact ha
    · show D.θ (toReal (thetaPowVec D.θ m b)) = toReal b'
      rw [hsb.1, ← Module.End.mul_apply, ← pow_succ']
      exact hb

theorem exists_eq_thetaOrbit_of_mem_orbits
    {i₀ : KernelComponent D.χ}
    (hJ : D.J = {i | ∃ m : ℕ, ∃ α ∈ componentRoots D.χ i₀, ∃ β ∈ componentRoots D.χ i,
      (D.θ ^ m) (toReal α) = toReal β}) {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) :
    ∃ β₀ ∈ simpleRoots (componentRoots D.χ i₀), O = thetaOrbit D.θ β₀ := by
  obtain ⟨n, hn, hper⟩ := D.exists_pow_eq_on_kernelRoots
  obtain ⟨β, hβ, rfl⟩ := hO
  obtain ⟨i, hi, hβi⟩ := D.mem_simpleRootsJ_iff.1 hβ
  have hi' := hi
  rw [hJ] at hi'
  obtain ⟨m, α, ⟨hαK, hαi₀⟩, α', ⟨hα'K, hα'i⟩, hm⟩ := hi'
  obtain ⟨hβK, hβi'⟩ := simpleRoots_subset hβi
  have hspec := D.thetaPowVec_spec hβK ((n - 1) * m)
  have hβ₀ := D.thetaOrbit_subset_simpleRootsJ hβ hspec.2.1
  have hback : (D.θ ^ ((n - 1) * m)) (toReal α') = toReal α := by
    have e : (n - 1) * m + m = n * m := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hn]
    rw [← hm, ← Module.End.mul_apply, ← pow_add, e, pow_mul, Module.End.pow_apply]
    exact Function.iterate_fixed (hper α hαK) m
  have hcls := D.mk_eq_of_pow (a := ⟨β, hβK⟩) (b := ⟨α', hα'K⟩) (hβi'.trans hα'i.symm)
    ((n - 1) * m) (a' := ⟨_, hspec.2.2⟩) (b' := ⟨α, hαK⟩) hspec.1.symm hback
  have hmem : thetaPowVec D.θ ((n - 1) * m) β ∈ componentRoots D.χ i₀ :=
    ⟨hspec.2.2, hcls.trans hαi₀⟩
  obtain ⟨j, -, hj⟩ := D.mem_simpleRootsJ_iff.1 hβ₀
  rw [eq_of_mem_componentRoots (simpleRoots_subset hj) hmem] at hj
  exact ⟨_, hj, (D.thetaOrbit_eq_of_mem hβK hspec.2.1).symm⟩

theorem reflTransGen_thetaOrbit
    {i : KernelComponent D.χ} (hi : i ∈ D.J)
    {β γ : Fin τ.rank → ℤ} (h : Relation.ReflTransGen (SimpleAdj (componentRoots D.χ i)) β γ) :
    Relation.ReflTransGen (fun O P => O ∈ D.orbits ∧ P ∈ D.orbits ∧ O ≠ P ∧
      ∃ β ∈ O, ∃ γ ∈ P, iform β γ ≠ 0) (thetaOrbit D.θ β) (thetaOrbit D.θ γ) := by
  have hsub : ∀ δ ∈ simpleRoots (componentRoots D.χ i), δ ∈ D.simpleRootsJ :=
    fun δ hδ => D.mem_simpleRootsJ_iff.2 ⟨i, hi, hδ⟩
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail y z _ hyz ih =>
    obtain ⟨hy, hz, hyz'⟩ := hyz
    by_cases he : thetaOrbit D.θ y = thetaOrbit D.θ z
    · rwa [← he]
    · exact ih.tail ⟨D.thetaOrbit_mem_orbits (hsub y hy), D.thetaOrbit_mem_orbits (hsub z hz), he,
        y, self_mem_thetaOrbit _ _, z, self_mem_thetaOrbit _ _, hyz'⟩

theorem orbits_connected
    {O P : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) (hP : P ∈ D.orbits) :
    Relation.ReflTransGen (fun O P => O ∈ D.orbits ∧ P ∈ D.orbits ∧ O ≠ P ∧
      ∃ β ∈ O, ∃ γ ∈ P, iform β γ ≠ 0) O P := by
  obtain ⟨i₀, hJ⟩ := D.isThetaOrbit
  have hi₀ : i₀ ∈ D.J := by
    obtain ⟨a, ha⟩ := Quotient.exists_rep i₀
    rw [hJ]
    exact ⟨0, a, ⟨a.2, ha⟩, a, ⟨a.2, ha⟩, by rw [pow_zero, Module.End.one_apply]⟩
  obtain ⟨β₀, hβ₀, rfl⟩ := D.exists_eq_thetaOrbit_of_mem_orbits hJ hO
  obtain ⟨γ₀, hγ₀, rfl⟩ := D.exists_eq_thetaOrbit_of_mem_orbits hJ hP
  exact D.reflTransGen_thetaOrbit hi₀
    (simpleRoots_connected (isRootComponent_componentRoots i₀) hβ₀ hγ₀)

theorem foldedLength_braid
    {O P : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) (hP : P ∈ D.orbits)
    (hne : O ≠ P) (hadj : ∃ β ∈ O, ∃ γ ∈ P, iform β γ ≠ 0) :
    D.foldedLength (setReflection P * setReflection O * setReflection P) = 3 := by
  obtain ⟨β, hβO, γ, hγP, hβγ⟩ := hadj
  have hrO := D.setReflection_mem_fixedWeyl hO
  have hrP := D.setReflection_mem_fixedWeyl hP
  have hβP : β ∉ P := fun h => hne ((D.eq_thetaOrbit_of_mem_orbits hO hβO).trans
    (D.eq_thetaOrbit_of_mem_orbits hP h).symm)
  have hγO : γ ∉ O := fun h => hne ((D.eq_thetaOrbit_of_mem_orbits hO h).trans
    (D.eq_thetaOrbit_of_mem_orbits hP hγP).symm)
  have h1 : D.foldedLength (setReflection P) = 1 := by
    have := (D.foldedLength_mul_setReflection hP (one_mem _)).2
      ((D.not_image_subset_negRoots_iff (one_mem _) hP hγP).2 (by
        rw [one_smul]
        exact D.mem_posRootsJ_of_mem_orbits hP hγP))
    rwa [one_mul, D.foldedLength_one] at this
  have h2 : D.foldedLength (setReflection P * setReflection O) = 2 := by
    have := (D.foldedLength_mul_setReflection hO hrP).2
      ((D.not_image_subset_negRoots_iff hrP hO hβO).2
        (D.setReflection_smul_mem_posRootsJ hP (D.mem_posRootsJ_of_mem_orbits hO hβO) hβP).1)
    rw [this, h1]
  have hrγ := D.setReflection_smul_mem_posRootsJ hO (D.mem_posRootsJ_of_mem_orbits hP hγP) hγO
  have hrγP : setReflection O • γ ∉ P := by
    intro h
    have hform : iform β (setReflection O • γ) = -iform β γ := by
      rw [← iform_smul (setReflection O) β (setReflection O • γ), smul_smul,
        D.setReflection_mul_self hO, one_smul, D.setReflection_smul_of_mem hO hβO,
        ← neg_one_smul ℤ β, iform_smul_left]
      ring
    have h3 := iform_nonpos_of_mem_unionSimpleRoots (D.mem_unionSimpleRoots_of_mem_orbits hO hβO)
      (D.mem_unionSimpleRoots_of_mem_orbits hP h) (fun h' => hβP (h' ▸ h))
    have h4 := iform_nonpos_of_mem_unionSimpleRoots (D.mem_unionSimpleRoots_of_mem_orbits hO hβO)
      (D.mem_unionSimpleRoots_of_mem_orbits hP hγP) (fun h' => hβP (h' ▸ hγP))
    rw [hform] at h3
    exact hβγ (by omega)
  have h3 := (D.foldedLength_mul_setReflection hP (mul_mem hrP hrO)).2
    ((D.not_image_subset_negRoots_iff (mul_mem hrP hrO) hP hγP).2 (by
      rw [mul_smul]
      exact (D.setReflection_smul_mem_posRootsJ hP hrγ.1 hrγP).1))
  rw [h3, h2]

end OrthogonalSemilinearFixedRootDatum

theorem orthogonal_folded_Weyl_descent
    {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k]
    [CharP k p₀] [IsAlgClosed k] (D : OrthogonalSemilinearFixedRootDatum τ p₀ k) :
    D.fixedWeyl = Subgroup.closure (setReflection '' D.orbits) ∧
    (∀ w ∈ D.fixedWeyl, ∀ α ∈ D.roots, w • α ∈ D.roots ∧
      (fun γ => w • γ) '' thetaOrbit D.θ α = thetaOrbit D.θ (w • α)) ∧
    (∀ w ∈ D.fixedWeyl,
      (∀ α ∈ D.roots, (fun γ => w • γ) '' thetaOrbit D.θ α = thetaOrbit D.θ α) → w = 1) ∧
    (∀ O ∈ D.orbits, (fun γ => setReflection O • γ) '' O = (fun γ => -γ) '' O ∧
      Set.BijOn (fun P => (fun γ => setReflection O • γ) '' P) (D.posOrbits \ {O})
        (D.posOrbits \ {O})) ∧
    (∀ w ∈ D.fixedWeyl, ∀ O ∈ D.orbits,
      (D.foldedLength (setReflection O * w) = D.foldedLength w - 1 ↔
        (fun γ => w⁻¹ • γ) '' O ⊆ negRoots D.roots) ∧
      (¬(fun γ => w⁻¹ • γ) '' O ⊆ negRoots D.roots →
        D.foldedLength (setReflection O * w) = D.foldedLength w + 1)) ∧
    (∀ w ∈ D.fixedWeyl, ∀ O ∈ D.orbits,
      (D.foldedLength (w * setReflection O) = D.foldedLength w - 1 ↔
        (fun γ => w • γ) '' O ⊆ negRoots D.roots) ∧
      (¬(fun γ => w • γ) '' O ⊆ negRoots D.roots →
        D.foldedLength (w * setReflection O) = D.foldedLength w + 1)) ∧
    (∀ w ∈ D.fixedWeyl, ∀ O ∈ D.orbits, (fun γ => w⁻¹ • γ) '' O ⊆ negRoots D.roots →
      ∀ l, D.IsOrbitWord l → l.length = D.foldedLength w → orbitWordProd l = w →
        ∃ j < l.length, setReflection O * w = orbitWordProd (l.eraseIdx j)) ∧
    (∀ w ∈ D.fixedWeyl, ∀ O ∈ D.orbits, (fun γ => w • γ) '' O ⊆ negRoots D.roots →
      ∀ l, D.IsOrbitWord l → l.length = D.foldedLength w → orbitWordProd l = w →
        ∃ j < l.length, w * setReflection O = orbitWordProd (l.eraseIdx j)) ∧
    (∀ w ∈ D.fixedWeyl, w ≠ 1 → ∃ O ∈ D.orbits, (fun γ => w • γ) '' O ⊆ negRoots D.roots) ∧
    (∃ w₀ ∈ D.fixedWeyl, (fun α => w₀ • α) '' D.posRootsJ = negRoots D.roots) ∧
    (∀ O ∈ D.orbits, ∀ P ∈ D.orbits, Relation.ReflTransGen (fun O P => O ∈ D.orbits ∧
      P ∈ D.orbits ∧ O ≠ P ∧ ∃ β ∈ O, ∃ γ ∈ P, iform β γ ≠ 0) O P) ∧
    (∀ O ∈ D.orbits, ∀ P ∈ D.orbits, O ≠ P → (∃ β ∈ O, ∃ γ ∈ P, iform β γ ≠ 0) →
      D.foldedLength (setReflection P * setReflection O * setReflection P) = 3) := by
  refine ⟨D.fixedWeyl_eq_closure,
    fun w hw α hα => ⟨smul_mem_unionRoots (D.mem_unionWeylGroup_of_mem_fixedWeyl hw) hα,
      D.image_smul_thetaOrbit hw hα⟩,
    fun w hw h => D.eq_one_of_forall_image_thetaOrbit hw h,
    fun O hO => ⟨D.image_setReflection_self hO, D.bijOn_image_setReflection hO⟩,
    fun w hw O hO => D.foldedLength_setReflection_mul hO hw,
    fun w hw O hO => D.foldedLength_mul_setReflection hO hw,
    fun w _ O hO hneg l hl _ e => ?_, fun w _ O hO hneg l hl _ e => ?_,
    fun w hw hne => D.exists_orbits_image_subset_negRoots hw hne, D.exists_longest,
    fun O hO P hP => D.orbits_connected hO hP,
    fun O hO P hP hne hadj => D.foldedLength_braid hO hP hne hadj⟩
  · obtain ⟨β, hβ⟩ := D.nonempty_of_mem_orbits hO
    subst e
    exact D.exists_eraseIdx_of_smul_mem_negRoots hl hO hβ (hneg ⟨β, hβ, rfl⟩)
  · obtain ⟨β, hβ⟩ := D.nonempty_of_mem_orbits hO
    subst e
    exact D.exists_eraseIdx_mul_setReflection hl hO hβ (hneg ⟨β, hβ, rfl⟩)

end CFSG.LieType.Chevalley
