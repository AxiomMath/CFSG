module

public import CFSG.LieType.Chevalley.TrialityCoverWeights

public noncomputable section

namespace CFSG.LieType.Chevalley.TrialityCover

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.ExceptionalCover CFSG.LieType.Chevalley.TwistedE6Cover

variable {K : Type} [Field K] (σ : K ≃+* K)

@[expose] def orbitGroup
    (α : Fin TwistTag.D4.tag.rank → ℤ) : Subgroup (ModGL TwistTag.D4.tag K) :=
  rootSpan TwistTag.D4.tag K (TwistTag.D4.diagramOrbit α : Set (Fin TwistTag.D4.tag.rank → ℤ)) ⊓
    twistedFixedGroup TwistTag.D4 K σ.toRingHom

theorem orbitGroup_le_of_subset
    {S : Set (Fin TwistTag.D4.tag.rank → ℤ)}
    (hSρ : ∀ α ∈ S, permLattice TwistTag.D4.perm α ∈ S) {α : Fin TwistTag.D4.tag.rank → ℤ}
    (hα : α ∈ S) :
    orbitGroup σ α ≤ rootSpan TwistTag.D4.tag K S ⊓ twistedFixedGroup TwistTag.D4 K σ.toRingHom :=
  inf_le_inf_right _ (rootSpan_mono (diagramOrbit_subset hSρ hα))

theorem exists_ordering_orbits
    (S : Set (Fin TwistTag.D4.tag.rank → ℤ)) :
    ∃ (k : ℕ) (O : Fin k → Finset (Fin TwistTag.D4.tag.rank → ℤ)), Function.Injective O ∧
      Set.range O = {O' | O' ∈ TwistTag.D4.diagramRootOrbits ∧
        (O' : Set (Fin TwistTag.D4.tag.rank → ℤ)) ⊆ S} := by
  have hfin : {O' | O' ∈ TwistTag.D4.diagramRootOrbits ∧
      (O' : Set (Fin TwistTag.D4.tag.rank → ℤ)) ⊆ S}.Finite :=
    ((finite_setOf_isRoot TwistTag.D4.tag).image TwistTag.D4.diagramOrbit).subset
      fun O' ⟨⟨α, hα, hαO⟩, _⟩ => ⟨α, hα, hαO⟩
  obtain ⟨k, O, hO⟩ := hfin.fin_embedding
  exact ⟨k, O, O.injective, hO⟩

theorem rootSpan_inf_le_closure
    {S : Set (Fin TwistTag.D4.tag.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot TwistTag.D4.tag α ∧ 0 < height α)
    (hSρ : ∀ α ∈ S, permLattice TwistTag.D4.perm α ∈ S)
    (hclosed : ∀ α ∈ S, ∀ β ∈ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot TwistTag.D4.tag (a • α + b • β) →
      a • α + b • β ∈ S) :
    rootSpan TwistTag.D4.tag K S ⊓ twistedFixedGroup TwistTag.D4 K σ.toRingHom ≤
      Subgroup.closure {g | ∃ α ∈ S, g ∈ orbitGroup σ α} := by
  obtain ⟨k, O, hO, hrange⟩ := exists_ordering_orbits S
  have hbij := bijOn_prod_graphFixed (K := K) (σ := σ.toRingHom) σ.surjective hS hSρ hclosed O hO
    hrange
  intro g hg
  obtain ⟨u, -, rfl⟩ := hbij.surjOn hg
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
  have hOj : O j ∈ Set.range O := Set.mem_range_self j
  rw [hrange] at hOj
  obtain ⟨⟨α, -, hα⟩, hsub⟩ := hOj
  refine Subgroup.subset_closure ⟨α, hsub (hα ▸ TwistTag.D4.self_mem_diagramOrbit α), ?_⟩
  rw [orbitGroup, hα]
  exact (u j).2

theorem closure_le_rootSpan_inf
    {S : Set (Fin TwistTag.D4.tag.rank → ℤ)}
    (hSρ : ∀ α ∈ S, permLattice TwistTag.D4.perm α ∈ S) :
    Subgroup.closure {g | ∃ α ∈ S, g ∈ orbitGroup σ α} ≤
      rootSpan TwistTag.D4.tag K S ⊓ twistedFixedGroup TwistTag.D4 K σ.toRingHom :=
  (Subgroup.closure_le _).2 fun _ ⟨_, hα, hg⟩ => orbitGroup_le_of_subset σ hSρ hα hg

theorem form_eq_zero_of_orbitPairs
    {S S' : Set (Fin TwistTag.D4.tag.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot TwistTag.D4.tag α ∧ 0 < height α)
    (hSρ : ∀ α ∈ S, permLattice TwistTag.D4.perm α ∈ S)
    (hclosed : ∀ α ∈ S, ∀ β ∈ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot TwistTag.D4.tag (a • α + b • β) →
      a • α + b • β ∈ S)
    (hS' : ∀ α ∈ S', IsRoot TwistTag.D4.tag α ∧ 0 < height α)
    (hSρ' : ∀ α ∈ S', permLattice TwistTag.D4.perm α ∈ S')
    (hclosed' : ∀ α ∈ S', ∀ β ∈ S', ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot TwistTag.D4.tag (a • α + b • β) → a • α + b • β ∈ S')
    (b : ModGL TwistTag.D4.tag K → ModGL TwistTag.D4.tag K → ZMod 2)
    (hb₁ : ∀ x ∈ rootSpan TwistTag.D4.tag K S ⊓ twistedFixedGroup TwistTag.D4 K σ.toRingHom,
      ∀ x' ∈ rootSpan TwistTag.D4.tag K S ⊓ twistedFixedGroup TwistTag.D4 K σ.toRingHom,
      ∀ y ∈ rootSpan TwistTag.D4.tag K S' ⊓ twistedFixedGroup TwistTag.D4 K σ.toRingHom,
        b (x * x') y = b x y + b x' y)
    (hb₂ : ∀ x ∈ rootSpan TwistTag.D4.tag K S ⊓ twistedFixedGroup TwistTag.D4 K σ.toRingHom,
      ∀ y ∈ rootSpan TwistTag.D4.tag K S' ⊓ twistedFixedGroup TwistTag.D4 K σ.toRingHom,
      ∀ y' ∈ rootSpan TwistTag.D4.tag K S' ⊓ twistedFixedGroup TwistTag.D4 K σ.toRingHom,
        b x (y * y') = b x y + b x y')
    (hpair : ∀ α ∈ S, ∀ β ∈ S', ∀ x ∈ orbitGroup σ α, ∀ y ∈ orbitGroup σ β, b x y = 0) :
    ∀ x ∈ rootSpan TwistTag.D4.tag K S ⊓ twistedFixedGroup TwistTag.D4 K σ.toRingHom,
      ∀ y ∈ rootSpan TwistTag.D4.tag K S' ⊓ twistedFixedGroup TwistTag.D4 K σ.toRingHom,
        b x y = 0 := by
  have hcl := closure_le_rootSpan_inf σ hSρ
  have hcl' := closure_le_rootSpan_inf σ hSρ'
  have hleft : ∀ α ∈ S, ∀ x ∈ orbitGroup σ α,
      ∀ y ∈ rootSpan TwistTag.D4.tag K S' ⊓ twistedFixedGroup TwistTag.D4 K σ.toRingHom,
        b x y = 0 := by
    intro α hα x hx y hy
    have hxS := orbitGroup_le_of_subset σ hSρ hα hx
    refine eq_zero_of_closure (b x) (fun y hy y' hy' => hb₂ x hxS y (hcl' hy) y' (hcl' hy'))
      ?_ y (rootSpan_inf_le_closure σ hS' hSρ' hclosed' hy)
    rintro _ ⟨β, hβ, hy⟩
    exact hpair α hα β hβ x hx _ hy
  intro x hx y hy
  refine eq_zero_of_closure (fun x => b x y)
    (fun x hx x' hx' => hb₁ x (hcl hx) x' (hcl hx') y hy) ?_ x
    (rootSpan_inf_le_closure σ hS hSρ hclosed hx)
  rintro _ ⟨α, hα, hx⟩
  exact hleft α hα _ hx y hy

theorem param_form_eq_zero_right {L L' : Type*} [Field L'] (F : L → L' → ZMod 2)
    (hF₂ : ∀ c d₁ d₂, F c (d₁ + d₂) = F c d₁ + F c d₂) {μ : L'} (hμ : μ ≠ 1)
    (hinv : ∀ c d, F c (μ * d) = F c d) : ∀ c d, F c d = 0 := by
  intro c d
  have key : ∀ d, F c ((μ - 1) * d) = 0 := fun d => by
    have h := hinv c d
    rw [show μ * d = d + (μ - 1) * d by ring, hF₂] at h
    simpa using h
  have h := key ((μ - 1)⁻¹ * d)
  rwa [← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.2 hμ), one_mul] at h

theorem form_param_eq_zero {G T : Type*} [Group G] (τ : T → G) {L L' : Type*} [Field L]
    [Field L'] (P : L → G) (P' : L' → G) (hP : ∀ s s', P (s + s') = P s * P s')
    (hP' : ∀ s s', P' (s + s') = P' s * P' s') (χ : T → L) (χ' : T → L')
    (hconj : ∀ t s, τ t * P s * (τ t)⁻¹ = P (χ t * s))
    (hconj' : ∀ t s, τ t * P' s * (τ t)⁻¹ = P' (χ' t * s)) (t : T)
    (ht : (χ t = 1 ∧ χ' t ≠ 1) ∨ (χ' t = 1 ∧ χ t ≠ 1)) (b : G → G → ZMod 2)
    (hb₁ : ∀ s₁ s₂ s', b (P s₁ * P s₂) (P' s') = b (P s₁) (P' s') + b (P s₂) (P' s'))
    (hb₂ : ∀ s s₁' s₂', b (P s) (P' s₁' * P' s₂') = b (P s) (P' s₁') + b (P s) (P' s₂'))
    (hbT : ∀ s s', b (τ t * P s * (τ t)⁻¹) (τ t * P' s' * (τ t)⁻¹) = b (P s) (P' s')) :
    ∀ s s', b (P s) (P' s') = 0 := by
  rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine param_form_eq_zero_right (fun s s' => b (P s) (P' s'))
      (fun c d₁ d₂ => by simp only [hP', hb₂]) h2 fun c d => ?_
    have h := hbT c d
    rwa [hconj, hconj', h1, one_mul] at h
  · intro s s'
    refine param_form_eq_zero_right (fun s' s => b (P s) (P' s'))
      (fun c d₁ d₂ => by simp only [hP, hb₁]) h2 (fun c d => ?_) s' s
    have h := hbT d c
    rwa [hconj, hconj', h1, one_mul] at h

theorem toRingHom_pow_three (hσ : σ ^ 3 = 1) : σ.toRingHom ^ 3 = 1 :=
  RingHom.ext fun c => pow_three_apply_eq σ hσ c

@[expose] def paramField (j : Fin 6) : Subfield K :=
  if j = 0 ∨ j = 2 ∨ j = 3 then ⊤ else trialityFixedField K σ.toRingHom

@[expose] def paramX
    (j : Fin 6) (c : paramField σ j) : ModGL TwistTag.D4.tag K :=
  if j = 0 ∨ j = 2 ∨ j = 3 then
    (trialityOrbitProd K σ.toRingHom (trialityRoot j) c : ModGL TwistTag.D4.tag K)
  else pinnedX TwistTag.D4.tag K (trialityRoot j) c

abbrev trialityGroup
    (j : Fin 6) : Subgroup (ModGL TwistTag.D4.tag K) :=
  rootSpan TwistTag.D4.tag K (trialityOrbit j : Set (Fin TwistTag.D4.tag.rank → ℤ)) ⊓
    twistedFixedGroup TwistTag.D4 K σ.toRingHom

theorem paramX_add
    [CharP K 2] (j : Fin 6) (c c' : paramField σ j) :
    paramX σ j (c + c') = paramX σ j c * paramX σ j c' := by
  unfold paramX
  split_ifs with hj
  · rw [Subfield.coe_add, trialityOrbitProd_add' hj, Subgroup.coe_mul]
  · rw [Subfield.coe_add, pinnedX_add]

theorem paramX_mem
    [CharP K 2] (hσ : σ ^ 3 = 1) (j : Fin 6) (c : paramField σ j) :
    paramX σ j c ∈ trialityGroup σ j := by
  unfold paramX
  split_ifs with hj
  · exact trialityOrbitProd_mem hj (toRingHom_pow_three σ hσ) c
  · have hj' : j = 1 ∨ j = 4 ∨ j = 5 := by fin_cases j <;> simp_all
    have hpf : paramField σ j = trialityFixedField K σ.toRingHom := ite_eq_right hj
    have hc : (c : K) ∈ trialityFixedField K σ.toRingHom := (SetLike.ext_iff.1 hpf (c : K)).1 c.2
    exact pinnedX_trialityRoot_mem (K := K) (σ := σ.toRingHom) hj' ⟨(c : K), hc⟩

theorem exists_paramX_eq
    [CharP K 2] (j : Fin 6) {u : ModGL TwistTag.D4.tag K}
    (hu : u ∈ trialityGroup σ j) : ∃ c, paramX σ j c = u := by
  unfold paramX
  by_cases hj : j = 0 ∨ j = 2 ∨ j = 3
  · obtain ⟨c, hc⟩ := exists_trialityOrbitProd_eq' hj hu
    have hpf : paramField σ j = ⊤ := ite_eq_left hj
    have hc' : c ∈ paramField σ j := (SetLike.ext_iff.1 hpf c).2 (Subfield.mem_top c)
    exact ⟨⟨c, hc'⟩, by rw [ite_eq_left hj]; exact hc⟩
  · have hj' : j = 1 ∨ j = 4 ∨ j = 5 := by fin_cases j <;> simp_all
    obtain ⟨c, hc⟩ := exists_pinnedX_trialityRoot_eq hj' hu
    have hpf : paramField σ j = trialityFixedField K σ.toRingHom := ite_eq_right hj
    have hc' : (c : K) ∈ paramField σ j := (SetLike.ext_iff.1 hpf (c : K)).2 c.2
    exact ⟨⟨c, hc'⟩, by rw [ite_eq_right hj]; exact hc⟩

theorem rootChar_mem_paramField (hσ : σ ^ 3 = 1) (j : Fin 6)
    (p : Kˣ × (trialityFixedField K σ.toRingHom)ˣ) :
    (rootChar K (trialityRoot j) (torusParam σ p) : K) ∈ paramField σ j := by
  by_cases hj : j = 0 ∨ j = 2 ∨ j = 3
  · have hpf : paramField σ j = ⊤ := ite_eq_left hj
    exact (SetLike.ext_iff.1 hpf _).2 (Subfield.mem_top _)
  · have hj' : j = 1 ∨ j = 4 ∨ j = 5 := by fin_cases j <;> simp_all
    have hpf : paramField σ j = trialityFixedField K σ.toRingHom := ite_eq_right hj
    refine (SetLike.ext_iff.1 hpf _).2 ?_
    have h := rootChar_permLattice_torusParam σ hσ (trialityRoot j) p
    rw [trialityRoot_fixed hj'] at h
    rw [mem_trialityFixedField]
    exact (congrArg (fun u : Kˣ => (u : K)) h).symm

@[expose] def paramWeight (hσ : σ ^ 3 = 1) (j : Fin 6)
    (p : Kˣ × (trialityFixedField K σ.toRingHom)ˣ) : paramField σ j :=
  ⟨(rootChar K (trialityRoot j) (torusParam σ p) : K), rootChar_mem_paramField σ hσ j p⟩

theorem paramWeight_eq_one_iff (hσ : σ ^ 3 = 1) (j : Fin 6)
    (p : Kˣ × (trialityFixedField K σ.toRingHom)ˣ) :
    paramWeight σ hσ j p = 1 ↔ rootChar K (trialityRoot j) (torusParam σ p) = 1 := by
  constructor
  · intro h
    exact Units.ext (congrArg Subtype.val h)
  · intro h
    refine Subtype.ext ?_
    change (rootChar K (trialityRoot j) (torusParam σ p) : K) = 1
    rw [h, Units.val_one]

theorem trialityTorus_conj_paramX
    (hσ : σ ^ 3 = 1) (j : Fin 6)
    (p : Kˣ × (trialityFixedField K σ.toRingHom)ˣ) (c : paramField σ j) :
    trialityTorus σ p * paramX σ j c * (trialityTorus σ p)⁻¹ =
      paramX σ j (paramWeight σ hσ j p * c) := by
  unfold paramX
  split_ifs with hj
  · rw [trialityTorus_conj_orbitProd σ hσ (isRoot_trialityRoot j) p]
    rfl
  · rw [trialityTorus_conj_pinnedX σ (isRoot_trialityRoot' j) p]
    rfl

theorem form_trialityGroup_eq_zero
    [CharP K 2] (hσ : σ ^ 3 = 1) {i j : Fin 6}
    (hsep : Separated σ i j) (b : ModGL TwistTag.D4.tag K → ModGL TwistTag.D4.tag K → ZMod 2)
    (hb₁ : ∀ x ∈ trialityGroup σ i, ∀ x' ∈ trialityGroup σ i, ∀ y ∈ trialityGroup σ j,
      b (x * x') y = b x y + b x' y)
    (hb₂ : ∀ x ∈ trialityGroup σ i, ∀ y ∈ trialityGroup σ j, ∀ y' ∈ trialityGroup σ j,
      b x (y * y') = b x y + b x y')
    (hbT : ∀ p, ∀ x ∈ trialityGroup σ i, ∀ y ∈ trialityGroup σ j,
      b (trialityTorus σ p * x * (trialityTorus σ p)⁻¹)
        (trialityTorus σ p * y * (trialityTorus σ p)⁻¹) = b x y) :
    ∀ x ∈ trialityGroup σ i, ∀ y ∈ trialityGroup σ j, b x y = 0 := by
  obtain ⟨p, hp⟩ := hsep
  have hF := form_param_eq_zero (trialityTorus σ) (paramX σ i) (paramX σ j) (paramX_add σ i)
    (paramX_add σ j) (paramWeight σ hσ i) (paramWeight σ hσ j)
    (trialityTorus_conj_paramX σ hσ i) (trialityTorus_conj_paramX σ hσ j) p (by
      simp only [paramWeight_eq_one_iff, ne_eq]
      exact hp) b
    (fun s₁ s₂ s' => hb₁ _ (paramX_mem σ hσ i s₁) _ (paramX_mem σ hσ i s₂) _
      (paramX_mem σ hσ j s'))
    (fun s s₁' s₂' => hb₂ _ (paramX_mem σ hσ i s) _ (paramX_mem σ hσ j s₁') _
      (paramX_mem σ hσ j s₂'))
    (fun s s' => hbT p _ (paramX_mem σ hσ i s) _ (paramX_mem σ hσ j s'))
  intro x hx y hy
  obtain ⟨c, rfl⟩ := exists_paramX_eq σ i hx
  obtain ⟨d, rfl⟩ := exists_paramX_eq σ j hy
  exact hF c d

theorem exists_orbitGroup_eq
    {α : Fin TwistTag.D4.tag.rank → ℤ} (hα : IsRoot TwistTag.D4.tag α)
    (hpos : 0 < height α) :
    ∃ j : Fin 6, TwistTag.D4.diagramOrbit α = trialityOrbit j ∧
      orbitGroup σ α = trialityGroup σ j := by
  obtain ⟨k, hk, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).1 hα
  obtain ⟨j, hj⟩ := exists_trialityOrbit_eq ⟨k, hk⟩ hpos
  exact ⟨j, hj, by rw [orbitGroup, hj]⟩

theorem form_orbit_eq_zero
    [CharP K 2] (hσ : σ ^ 3 = 1)
    (hsep : ∀ i j : Fin 6, i ≠ j → Separated σ i j) {α β : Fin TwistTag.D4.tag.rank → ℤ}
    (hα : IsRoot TwistTag.D4.tag α) (hαp : 0 < height α) (hβ : IsRoot TwistTag.D4.tag β)
    (hβp : 0 < height β) (hne : β ∉ TwistTag.D4.diagramOrbit α)
    (b : ModGL TwistTag.D4.tag K → ModGL TwistTag.D4.tag K → ZMod 2)
    (hb₁ : ∀ x ∈ orbitGroup σ α, ∀ x' ∈ orbitGroup σ α, ∀ y ∈ orbitGroup σ β,
      b (x * x') y = b x y + b x' y)
    (hb₂ : ∀ x ∈ orbitGroup σ α, ∀ y ∈ orbitGroup σ β, ∀ y' ∈ orbitGroup σ β,
      b x (y * y') = b x y + b x y')
    (hbT : ∀ p, ∀ x ∈ orbitGroup σ α, ∀ y ∈ orbitGroup σ β,
      b (trialityTorus σ p * x * (trialityTorus σ p)⁻¹)
        (trialityTorus σ p * y * (trialityTorus σ p)⁻¹) = b x y) :
    ∀ x ∈ orbitGroup σ α, ∀ y ∈ orbitGroup σ β, b x y = 0 := by
  obtain ⟨i, hi, hRi⟩ := exists_orbitGroup_eq σ hα hαp
  obtain ⟨j, hj, hRj⟩ := exists_orbitGroup_eq σ hβ hβp
  have hij : i ≠ j := by
    rintro rfl
    refine hne ?_
    rw [hi, ← hj]
    exact TwistTag.D4.self_mem_diagramOrbit β
  rw [hRi, hRj] at hb₁ hb₂ hbT ⊢
  exact form_trialityGroup_eq_zero σ hσ (hsep i j hij) b hb₁ hb₂ hbT

theorem not_dvd_two_pow_add_two_pow {n i j : ℕ} (hn : 3 ≤ n) (hi : i < n) (hj : j < n) :
    ¬ (2 ^ n - 1) ∣ 2 ^ i + 2 ^ j := by
  rintro ⟨m, hm⟩
  have h8 : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hi' : 2 ^ i ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hj' : 2 ^ j ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hn2 : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hpos : 0 < 2 ^ i := by positivity
  have hpos' : 0 < 2 ^ j := by positivity
  have hm1 : m = 1 := by
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · interval_cases m
      · omega
      · rfl
    · have : (2 ^ n - 1) * 2 ≤ (2 ^ n - 1) * m := Nat.mul_le_mul_left _ hm2
      omega
  subst hm1
  rw [mul_one] at hm
  have key : ∀ k : ℕ, 2 ≤ k → 4 ∣ 2 ^ k := fun k hk => by
    have h := Nat.pow_dvd_pow 2 hk
    norm_num at h
    exact h
  obtain ⟨d, hd⟩ := key n (by omega)
  rcases Nat.lt_or_ge i 2 with hi2 | hi2 <;> rcases Nat.lt_or_ge j 2 with hj2 | hj2
  · interval_cases i <;> interval_cases j <;> simp at hm <;> omega
  · obtain ⟨c, hc⟩ := key j hj2
    interval_cases i <;> simp at hm <;> omega
  · obtain ⟨c, hc⟩ := key i hi2
    interval_cases j <;> simp at hm <;> omega
  · obtain ⟨c, hc⟩ := key i hi2
    obtain ⟨c', hc'⟩ := key j hj2
    omega

variable [Finite K] [CharP K 2]

omit [CharP K 2] in
theorem exists_weight_zero_pow_ne_one {n : ℕ} (hn : 3 ≤ n) (hK : Nat.card K = 2 ^ n) :
    ∀ i j : ℕ, i < n → j < n → ∃ t : Kˣ × (trialityFixedField K σ.toRingHom)ˣ,
      rootChar K (trialityRoot 0) (torusParam σ t) ^ 2 ^ i *
        rootChar K (trialityRoot 0) (torusParam σ t) ^ 2 ^ j ≠ 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  have hord : orderOf g = 2 ^ n - 1 := by rw [hg, Nat.card_units, hK]
  intro i j hi hj
  refine ⟨(g, 1), fun h => ?_⟩
  rw [rootChar_trialityRoot_zero, map_one, inv_one, mul_one, ← pow_mul, ← pow_mul,
    ← pow_add] at h
  have hdvd := orderOf_dvd_of_pow_eq_one h
  rw [hord] at hdvd
  have hodd : Nat.Coprime (2 ^ n - 1) 2 := by
    have : Odd (2 ^ n - 1) := by
      have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      have : Even (2 ^ n) := (Nat.even_pow.2 ⟨even_two, by omega⟩)
      obtain ⟨r, hr⟩ := this
      exact ⟨r - 1, by omega⟩
    exact Nat.Coprime.symm ((Nat.coprime_two_left).2 this)
  have hdvd' : 2 ^ n - 1 ∣ 2 * (2 ^ i + 2 ^ j) := by
    convert hdvd using 1
    ring
  exact not_dvd_two_pow_add_two_pow hn hi hj (hodd.dvd_of_dvd_mul_left hdvd')

theorem form_trialityGroup_zero_self_eq_zero
    (hσ : σ ^ 3 = 1) {n : ℕ} (hn : 3 ≤ n)
    (hK : Nat.card K = 2 ^ n) (b : ModGL TwistTag.D4.tag K → ModGL TwistTag.D4.tag K → ZMod 2)
    (hb₁ : ∀ x ∈ trialityGroup σ 0, ∀ x' ∈ trialityGroup σ 0, ∀ y ∈ trialityGroup σ 0,
      b (x * x') y = b x y + b x' y)
    (hb₂ : ∀ x ∈ trialityGroup σ 0, ∀ y ∈ trialityGroup σ 0, ∀ y' ∈ trialityGroup σ 0,
      b x (y * y') = b x y + b x y')
    (hbT : ∀ p, ∀ x ∈ trialityGroup σ 0, ∀ y ∈ trialityGroup σ 0,
      b (trialityTorus σ p * x * (trialityTorus σ p)⁻¹)
        (trialityTorus σ p * y * (trialityTorus σ p)⁻¹) = b x y) :
    ∀ x ∈ trialityGroup σ 0, ∀ y ∈ trialityGroup σ 0, b x y = 0 := by
  set P : K → ModGL TwistTag.D4.tag K := fun c =>
    (trialityOrbitProd K σ.toRingHom (trialityRoot 0) c : ModGL TwistTag.D4.tag K)
  have hPmem : ∀ c, P c ∈ trialityGroup σ 0 := fun c =>
    trialityOrbitProd_mem (Or.inl rfl) (toRingHom_pow_three σ hσ) c
  have hPadd : ∀ c c', P (c + c') = P c * P c' := fun c c' => by
    simp only [P, trialityOrbitProd_add' (Or.inl rfl), Subgroup.coe_mul]
  let χ : Kˣ × (trialityFixedField K σ.toRingHom)ˣ → Kˣ := fun p =>
    rootChar K (trialityRoot 0) (torusParam σ p)
  have hnd := exists_weight_zero_pow_ne_one σ hn hK
  have hF := form_eq_zero_of_chars (k := K) (by omega) hK χ χ hnd (fun c d => b (P c) (P d))
    (fun c₁ c₂ d => by
      simp only [hPadd]
      exact hb₁ _ (hPmem c₁) _ (hPmem c₂) _ (hPmem d))
    (fun c d₁ d₂ => by
      simp only [hPadd]
      exact hb₂ _ (hPmem c) _ (hPmem d₁) _ (hPmem d₂))
    (fun t c d => by
      have h := hbT t _ (hPmem c) _ (hPmem d)
      simp only [P] at h ⊢
      rwa [trialityTorus_conj_orbitProd σ hσ (isRoot_trialityRoot 0),
        trialityTorus_conj_orbitProd σ hσ (isRoot_trialityRoot 0)] at h)
  intro x hx y hy
  obtain ⟨c, rfl⟩ := exists_trialityOrbitProd_eq' (Or.inl rfl) hx
  obtain ⟨d, rfl⟩ := exists_trialityOrbitProd_eq' (Or.inl rfl) hy
  exact hF c d

end CFSG.LieType.Chevalley.TrialityCover
