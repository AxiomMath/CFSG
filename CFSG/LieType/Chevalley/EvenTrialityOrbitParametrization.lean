module

public import CFSG.LieType.Chevalley.EvenTrialityParameterData
public import CFSG.LieType.Chevalley.EvenDiagramRootParameters
public import CFSG.LieType.Chevalley.GraphFixedSylowOpposition

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley Matrix

@[expose] def trialityOrbit (j : Fin 6) : Finset (Fin TwistTag.D4.tag.rank → ℤ) :=
  TwistTag.D4.diagramOrbit (trialityRoot j)

theorem coe_diagramOrbit_D4 (α : Fin TwistTag.D4.tag.rank → ℤ) :
    (TwistTag.D4.diagramOrbit α : Set (Fin TwistTag.D4.tag.rank → ℤ)) =
      Set.range fun h : Fin 3 => permLattice (TwistTag.D4.perm ^ (h : ℕ)) α := by
  ext β
  simp only [TwistTag.diagramOrbit, Finset.coe_image, Finset.coe_range, Set.mem_image,
    Set.mem_Iio, Set.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, rfl⟩
  · rintro ⟨h, rfl⟩
    exact ⟨h, h.2, rfl⟩

theorem list_ofFn_prod_fin_three {G : Type*} [Monoid G] (f : Fin 3 → G) :
    (List.ofFn f).prod = f 0 * f 1 * f 2 := by
  simp [List.ofFn_succ, mul_assoc]

theorem list_ofFn_prod_fin_six {G : Type*} [Monoid G] (f : Fin 6 → G) :
    (List.ofFn f).prod = f 0 * f 1 * f 2 * f 3 * f 4 * f 5 := by
  simp [List.ofFn_succ, mul_assoc]

section Triple

variable {K : Type} [Field K] {α : Fin TwistTag.D4.tag.rank → ℤ}
  (hr : ∀ h : ℕ, IsRoot TwistTag.D4.tag (permLattice (TwistTag.D4.perm ^ h) α) ∧
    0 < height (permLattice (TwistTag.D4.perm ^ h) α))
  (hinj : Function.Injective fun h : Fin 3 => permLattice (TwistTag.D4.perm ^ (h : ℕ)) α)
  (horth : ∀ h h' : Fin 3, h ≠ h' → permLattice (TwistTag.D4.perm ^ (h : ℕ)) α ⬝ᵥ
    (TwistTag.D4.tag.symmetrizedCartan *ᵥ permLattice (TwistTag.D4.perm ^ (h' : ℕ)) α) = 0)

include hr horth in
theorem trialityTriple_commute
    (h h' : Fin 3) (a b : K) :
    Commute (pinnedX TwistTag.D4.tag K (permLattice (TwistTag.D4.perm ^ (h : ℕ)) α) a)
      (pinnedX TwistTag.D4.tag K (permLattice (TwistTag.D4.perm ^ (h' : ℕ)) α) b) := by
  by_cases hh : h = h'
  · subst hh
    rw [Commute, SemiconjBy, ← pinnedX_add, ← pinnedX_add, add_comm]
  · exact commute_pinnedX_of_rootForm_eq_zero K (hr h).1 (hr h').1 (horth h h' hh) a b

include hr horth in
theorem trialityTriple_commute01
    (a b : K) : Commute (pinnedX TwistTag.D4.tag K α a)
    (pinnedX TwistTag.D4.tag K (permLattice TwistTag.D4.perm α) b) :=
  trialityTriple_commute hr horth 0 1 a b

include hr horth in
theorem trialityTriple_commute02
    (a b : K) : Commute (pinnedX TwistTag.D4.tag K α a)
    (pinnedX TwistTag.D4.tag K (permLattice (TwistTag.D4.perm ^ 2) α) b) :=
  trialityTriple_commute hr horth 0 2 a b

include hr horth in
theorem trialityTriple_commute12
    (a b : K) :
    Commute (pinnedX TwistTag.D4.tag K (permLattice TwistTag.D4.perm α) a)
      (pinnedX TwistTag.D4.tag K (permLattice (TwistTag.D4.perm ^ 2) α) b) :=
  trialityTriple_commute hr horth 1 2 a b

include hr in
theorem trialityTriple_closed :
    ∀ β ∈ (TwistTag.D4.diagramOrbit α : Set (Fin TwistTag.D4.tag.rank → ℤ)),
      ∀ γ ∈ (TwistTag.D4.diagramOrbit α : Set (Fin TwistTag.D4.tag.rank → ℤ)),
        ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot TwistTag.D4.tag (a • β + b • γ) →
          a • β + b • γ ∈ (TwistTag.D4.diagramOrbit α : Set (Fin TwistTag.D4.tag.rank → ℤ)) :=
  fun _ hβ _ hγ _ _ ha hb hroot =>
    absurd hroot (TwistTag.D4.not_isRoot_nsmul_add_nsmul_of_mem_diagramOrbit (hr 0).1 hβ hγ ha hb)

include hr in
theorem trialityTriple_pos :
    ∀ β ∈ (TwistTag.D4.diagramOrbit α : Set (Fin TwistTag.D4.tag.rank → ℤ)),
      IsRoot TwistTag.D4.tag β ∧ 0 < height β := by
  intro β hβ
  rw [coe_diagramOrbit_D4] at hβ
  obtain ⟨h, rfl⟩ := hβ
  exact hr h

include hr hinj in
theorem trialityTriple_bijOn :
    Set.BijOn (fun c : Fin 3 → K => (List.ofFn fun i =>
      pinnedX TwistTag.D4.tag K (permLattice (TwistTag.D4.perm ^ (i : ℕ)) α) (c i)).prod)
      Set.univ (rootSpan TwistTag.D4.tag K
        (TwistTag.D4.diagramOrbit α : Set (Fin TwistTag.D4.tag.rank → ℤ))) :=
  bijOn_prod_pinnedX K (trialityTriple_pos hr) (trialityTriple_closed hr) _ hinj
    (coe_diagramOrbit_D4 α).symm

theorem coe_trialityOrbitProd_eq_ofFn
    (σ : K →+* K) (c : K) :
    (trialityOrbitProd K σ α c : ModGL TwistTag.D4.tag K) = (List.ofFn fun i : Fin 3 =>
      pinnedX TwistTag.D4.tag K (permLattice (TwistTag.D4.perm ^ (i : ℕ)) α)
        (![c, σ c, σ (σ c)] i)).prod := by
  rw [list_ofFn_prod_fin_three, coe_trialityOrbitProd]
  rfl

include hr hinj in
theorem trialityOrbitProd_injective
    (σ : K →+* K) :
    Function.Injective (trialityOrbitProd K σ α) := by
  intro a b hab
  have h := congrArg (fun g : adjointGroup TwistTag.D4.tag K => (g : ModGL TwistTag.D4.tag K)) hab
  simp only [coe_trialityOrbitProd_eq_ofFn] at h
  have := (trialityTriple_bijOn (K := K) hr hinj).injOn (Set.mem_univ _) (Set.mem_univ _) h
  exact congrFun this 0

include hr horth in
theorem trialityOrbitProd_add
    (σ : K →+* K) (a b : K) :
    trialityOrbitProd K σ α (a + b) = trialityOrbitProd K σ α a * trialityOrbitProd K σ α b := by
  have h01 := trialityTriple_commute01 (K := K) hr horth
  have h02 := trialityTriple_commute02 (K := K) hr horth
  have h12 := trialityTriple_commute12 (K := K) hr horth
  apply Subtype.ext
  rw [Subgroup.coe_mul, coe_trialityOrbitProd, coe_trialityOrbitProd, coe_trialityOrbitProd]
  simp only [map_add, pinnedX_add, mul_assoc]
  rw [(h01 b (σ a)).left_comm, (h12 (σ b) (σ (σ a))).left_comm, (h02 b (σ (σ a))).left_comm]

theorem permLattice_D4_perm_perm (α : Fin TwistTag.D4.tag.rank → ℤ) :
    permLattice TwistTag.D4.perm (permLattice TwistTag.D4.perm α) =
      permLattice (TwistTag.D4.perm ^ 2) α := by
  rw [← permLattice_mul, ← sq]

theorem permLattice_D4_perm_perm_sq (α : Fin TwistTag.D4.tag.rank → ℤ) :
    permLattice TwistTag.D4.perm (permLattice (TwistTag.D4.perm ^ 2) α) = α := by
  have h3 : TwistTag.D4.perm ^ 3 = 1 := by decide
  rw [← permLattice_mul, ← pow_succ', h3]
  rfl

theorem trialityTriple_prod_eq
    (f : Fin 3 → K) :
    (List.ofFn fun i : Fin 3 =>
      pinnedX TwistTag.D4.tag K (permLattice (TwistTag.D4.perm ^ (i : ℕ)) α) (f i)).prod =
      pinnedX TwistTag.D4.tag K α (f 0) *
        pinnedX TwistTag.D4.tag K (permLattice TwistTag.D4.perm α) (f 1) *
          pinnedX TwistTag.D4.tag K (permLattice (TwistTag.D4.perm ^ 2) α) (f 2) := by
  rw [list_ofFn_prod_fin_three]
  rfl

include hr horth in
theorem twistHom_trialityTriple_prod
    [CharP K 2] (σ : K →+* K) (a b c : K) :
    twistHom TwistTag.D4 K σ (pinnedX TwistTag.D4.tag K α a *
        pinnedX TwistTag.D4.tag K (permLattice TwistTag.D4.perm α) b *
          pinnedX TwistTag.D4.tag K (permLattice (TwistTag.D4.perm ^ 2) α) c) =
      pinnedX TwistTag.D4.tag K α (σ c) *
        pinnedX TwistTag.D4.tag K (permLattice TwistTag.D4.perm α) (σ a) *
          pinnedX TwistTag.D4.tag K (permLattice (TwistTag.D4.perm ^ 2) α) (σ b) := by
  have hα0 : IsRoot TwistTag.D4.tag α := (hr 0).1
  have hα1 : IsRoot TwistTag.D4.tag (permLattice TwistTag.D4.perm α) := (hr 1).1
  have hα2 : IsRoot TwistTag.D4.tag (permLattice (TwistTag.D4.perm ^ 2) α) := (hr 2).1
  rw [map_mul, map_mul, even_diagram_root_parameters _ σ hα0, even_diagram_root_parameters _ σ hα1,
    even_diagram_root_parameters _ σ hα2, permLattice_D4_perm_perm, permLattice_D4_perm_perm_sq,
    ← ((trialityTriple_commute01 hr horth (σ c) (σ a)).mul_right
      (trialityTriple_commute02 hr horth (σ c) (σ b))).eq, ← mul_assoc]

include hr horth in
theorem twistHom_trialityOrbitProd
    [CharP K 2] {σ : K →+* K} (hσ : σ ^ 3 = 1) (c : K) :
    twistHom TwistTag.D4 K σ (trialityOrbitProd K σ α c) = trialityOrbitProd K σ α c := by
  rw [coe_trialityOrbitProd, twistHom_trialityTriple_prod hr horth,
    ringHom_apply_apply_apply_of_pow_three hσ]

theorem trialityOrbitProd_mem_rootSpan
    (σ : K →+* K) (c : K) :
    (trialityOrbitProd K σ α c : ModGL TwistTag.D4.tag K) ∈
      rootSpan TwistTag.D4.tag K
        (TwistTag.D4.diagramOrbit α : Set (Fin TwistTag.D4.tag.rank → ℤ)) := by
  rw [coe_trialityOrbitProd_eq_ofFn]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
  exact pinnedX_mem_rootSpan (by rw [coe_diagramOrbit_D4]; exact ⟨i, rfl⟩) _

include hr hinj horth in
theorem exists_trialityOrbitProd_eq
    [CharP K 2] {σ : K →+* K} {u : ModGL TwistTag.D4.tag K}
    (hu : u ∈ rootSpan TwistTag.D4.tag K
      (TwistTag.D4.diagramOrbit α : Set (Fin TwistTag.D4.tag.rank → ℤ)) ⊓
        twistedFixedGroup TwistTag.D4 K σ) :
    ∃ c : K, (trialityOrbitProd K σ α c : ModGL TwistTag.D4.tag K) = u := by
  obtain ⟨hS, hΓ⟩ := Subgroup.mem_inf.1 hu
  obtain ⟨c', -, rfl⟩ := (trialityTriple_bijOn (K := K) hr hinj).surjOn hS
  have hfix := ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 hΓ).2
  dsimp only at hfix
  rw [trialityTriple_prod_eq, twistHom_trialityTriple_prod hr horth] at hfix
  have heq : (List.ofFn fun i : Fin 3 => pinnedX TwistTag.D4.tag K
      (permLattice (TwistTag.D4.perm ^ (i : ℕ)) α) (![σ (c' 2), σ (c' 0), σ (c' 1)] i)).prod =
      (List.ofFn fun i : Fin 3 => pinnedX TwistTag.D4.tag K
        (permLattice (TwistTag.D4.perm ^ (i : ℕ)) α) (c' i)).prod := by
    rw [trialityTriple_prod_eq, trialityTriple_prod_eq]
    exact hfix
  have hc := (trialityTriple_bijOn (K := K) hr hinj).injOn
    (Set.mem_univ ![σ (c' 2), σ (c' 0), σ (c' 1)]) (Set.mem_univ c') heq
  have h1 : c' 1 = σ (c' 0) := (congrFun hc 1).symm
  have h2 : c' 2 = σ (c' 1) := (congrFun hc 2).symm
  refine ⟨c' 0, ?_⟩
  dsimp only
  rw [trialityTriple_prod_eq, coe_trialityOrbitProd, h2, h1]

end Triple

section Singleton

variable {K : Type} [Field K] {α : Fin TwistTag.D4.tag.rank → ℤ}

theorem permLattice_D4_pow_of_fixed (hfix : permLattice TwistTag.D4.perm α = α) :
    ∀ h : ℕ, permLattice (TwistTag.D4.perm ^ h) α = α
  | 0 => rfl
  | h + 1 => by rw [pow_succ', permLattice_mul, permLattice_D4_pow_of_fixed hfix h, hfix]

theorem coe_diagramOrbit_D4_of_fixed (hfix : permLattice TwistTag.D4.perm α = α) :
    (TwistTag.D4.diagramOrbit α : Set (Fin TwistTag.D4.tag.rank → ℤ)) = {α} := by
  rw [coe_diagramOrbit_D4]
  ext β
  simp only [Set.mem_range, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h, rfl⟩
    exact permLattice_D4_pow_of_fixed hfix h
  · rintro rfl
    exact ⟨0, rfl⟩

theorem rootSpan_singleton_eq_rootSubgroup
    {τ : Tag} (R : Type*) [CommRing R] (α : Fin τ.rank → ℤ) :
    rootSpan τ R {α} = rootSubgroup τ R α := by
  rw [rootSpan_eq_closure, rootSubgroup]
  congr 1
  ext g
  simp

theorem twistHom_D4_pinnedX_of_fixed
    [CharP K 2] (σ : K →+* K) (hα : IsRoot TwistTag.D4.tag α)
    (hfix : permLattice TwistTag.D4.perm α = α) (c : K) :
    twistHom TwistTag.D4 K σ (pinnedX TwistTag.D4.tag K α c) =
      pinnedX TwistTag.D4.tag K α (σ c) := by
  rw [even_diagram_root_parameters _ σ hα, hfix]

theorem exists_pinnedX_D4_fixed_eq
    [CharP K 2] {σ : K →+* K} (hα : IsRoot TwistTag.D4.tag α)
    (hfix : permLattice TwistTag.D4.perm α = α) {u : ModGL TwistTag.D4.tag K}
    (hu : u ∈ rootSpan TwistTag.D4.tag K
      (TwistTag.D4.diagramOrbit α : Set (Fin TwistTag.D4.tag.rank → ℤ)) ⊓
        twistedFixedGroup TwistTag.D4 K σ) :
    ∃ c : trialityFixedField K σ, pinnedX TwistTag.D4.tag K α c = u := by
  obtain ⟨hS, hΓ⟩ := Subgroup.mem_inf.1 hu
  rw [coe_diagramOrbit_D4_of_fixed hfix, rootSpan_singleton_eq_rootSubgroup] at hS
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hS
  have h := ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 hΓ).2
  rw [twistHom_D4_pinnedX_of_fixed σ hα hfix] at h
  exact ⟨⟨c, pinnedX_injective _ _ _ h⟩, rfl⟩

theorem pinnedX_D4_mem_fixed
    [CharP K 2] {σ : K →+* K} (hα : IsRoot TwistTag.D4.tag α)
    (hfix : permLattice TwistTag.D4.perm α = α) (c : trialityFixedField K σ) :
    pinnedX TwistTag.D4.tag K α c ∈ rootSpan TwistTag.D4.tag K
      (TwistTag.D4.diagramOrbit α : Set (Fin TwistTag.D4.tag.rank → ℤ)) ⊓
        twistedFixedGroup TwistTag.D4 K σ := by
  refine Subgroup.mem_inf.2 ⟨?_, (mem_twistedFixedGroup_iff_twistHom _ _ _).2
    ⟨pinnedX_mem_adjointGroup _ _, ?_⟩⟩
  · rw [coe_diagramOrbit_D4_of_fixed hfix, rootSpan_singleton_eq_rootSubgroup]
    exact mem_rootSubgroup.2 ⟨_, rfl⟩
  · rw [twistHom_D4_pinnedX_of_fixed σ hα hfix, mem_trialityFixedField.1 c.2]

end Singleton

theorem trialityRoot_triple_injective : ∀ j : Fin 6, (j = 0 ∨ j = 2 ∨ j = 3) →
    Function.Injective fun h : Fin 3 =>
      permLattice (TwistTag.D4.perm ^ (h : ℕ)) (trialityRoot j) := by
  decide +kernel

theorem trialityRoot_triple_orthogonal : ∀ j : Fin 6, (j = 0 ∨ j = 2 ∨ j = 3) →
    ∀ h h' : Fin 3, h ≠ h' → permLattice (TwistTag.D4.perm ^ (h : ℕ)) (trialityRoot j) ⬝ᵥ
      (TwistTag.D4.tag.symmetrizedCartan *ᵥ
        permLattice (TwistTag.D4.perm ^ (h' : ℕ)) (trialityRoot j)) = 0 := by
  decide +kernel

theorem trialityOrbit_injective : Function.Injective trialityOrbit := by
  decide +kernel

theorem exists_trialityOrbit_eq : ∀ k : Fin 24,
    0 < height (TwistTag.D4.tag.rootCertificate.root k) →
      ∃ j : Fin 6, TwistTag.D4.diagramOrbit (TwistTag.D4.tag.rootCertificate.root k) =
        trialityOrbit j := by
  decide +kernel

theorem trialityOrbit_pos (j : Fin 6) :
    ∀ β ∈ (trialityOrbit j : Set (Fin TwistTag.D4.tag.rank → ℤ)),
      IsRoot TwistTag.D4.tag β ∧ 0 < height β :=
  trialityTriple_pos (isRoot_trialityRoot j)

theorem range_trialityOrbit : Set.range trialityOrbit =
    {O' | O' ∈ TwistTag.D4.diagramRootOrbits ∧ (O' : Set (Fin TwistTag.D4.tag.rank → ℤ)) ⊆
      {α | IsRoot TwistTag.D4.tag α ∧ 0 < height α}} := by
  ext O'
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨⟨trialityRoot j, (isRoot_trialityRoot j 0).1, rfl⟩, trialityOrbit_pos j⟩
  · rintro ⟨⟨β, hβ, rfl⟩, hsub⟩
    have hpos := (hsub (TwistTag.D4.self_mem_diagramOrbit β)).2
    obtain ⟨k, hk, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).1 hβ
    obtain ⟨j, hj⟩ := exists_trialityOrbit_eq ⟨k, hk⟩ hpos
    exact ⟨j, hj.symm⟩

theorem trialityOrbit_disjoint
    (i j : Fin 6) (hij : i ≠ j) :
    Disjoint (trialityOrbit i) (trialityOrbit j) :=
  TwistTag.D4.disjoint_diagramOrbit (trialityOrbit_injective.ne hij)

theorem trialityOrbit_not_isRoot
    (j : Fin 6) :
    ∀ β ∈ trialityOrbit j, ∀ γ ∈ trialityOrbit j, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      ¬IsRoot TwistTag.D4.tag (a • β + b • γ) := fun _ hβ _ hγ _ _ ha hb =>
  TwistTag.D4.not_isRoot_nsmul_add_nsmul_of_mem_diagramOrbit (isRoot_trialityRoot j 0).1 hβ hγ
    ha hb

section Maps

variable {K : Type} [Field K] [CharP K 2] {σ : K →+* K}

theorem trialityOrbitProd_mem
    {j : Fin 6} (hj : j = 0 ∨ j = 2 ∨ j = 3) (hσ : σ ^ 3 = 1)
    (c : K) : (trialityOrbitProd K σ (trialityRoot j) c : ModGL TwistTag.D4.tag K) ∈
      rootSpan TwistTag.D4.tag K (trialityOrbit j : Set (Fin TwistTag.D4.tag.rank → ℤ)) ⊓
        twistedFixedGroup TwistTag.D4 K σ :=
  Subgroup.mem_inf.2 ⟨trialityOrbitProd_mem_rootSpan σ c,
    (mem_twistedFixedGroup_iff_twistHom _ _ _).2 ⟨(trialityOrbitProd K σ _ c).2,
      twistHom_trialityOrbitProd (isRoot_trialityRoot j) (trialityRoot_triple_orthogonal j hj)
        hσ c⟩⟩

theorem exists_trialityOrbitProd_eq'
    {j : Fin 6} (hj : j = 0 ∨ j = 2 ∨ j = 3)
    {u : ModGL TwistTag.D4.tag K}
    (hu : u ∈ rootSpan TwistTag.D4.tag K (trialityOrbit j : Set (Fin TwistTag.D4.tag.rank → ℤ)) ⊓
      twistedFixedGroup TwistTag.D4 K σ) :
    ∃ c : K, (trialityOrbitProd K σ (trialityRoot j) c : ModGL TwistTag.D4.tag K) = u :=
  exists_trialityOrbitProd_eq (isRoot_trialityRoot j) (trialityRoot_triple_injective j hj)
    (trialityRoot_triple_orthogonal j hj) hu

omit [CharP K 2] in
theorem trialityOrbitProd_injective'
    {j : Fin 6} (hj : j = 0 ∨ j = 2 ∨ j = 3) :
    Function.Injective (trialityOrbitProd K σ (trialityRoot j)) :=
  trialityOrbitProd_injective (isRoot_trialityRoot j) (trialityRoot_triple_injective j hj) σ

omit [CharP K 2] in
theorem trialityOrbitProd_add'
    {j : Fin 6} (hj : j = 0 ∨ j = 2 ∨ j = 3) (a b : K) :
    trialityOrbitProd K σ (trialityRoot j) (a + b) =
      trialityOrbitProd K σ (trialityRoot j) a * trialityOrbitProd K σ (trialityRoot j) b :=
  trialityOrbitProd_add (isRoot_trialityRoot j) (trialityRoot_triple_orthogonal j hj) σ a b

theorem trialityRoot_fixed {j : Fin 6} (hj : j = 1 ∨ j = 4 ∨ j = 5) :
    permLattice TwistTag.D4.perm (trialityRoot j) = trialityRoot j := by
  obtain ⟨h1, h4, h5⟩ := permLattice_trialityRoot_fixed
  rcases hj with rfl | rfl | rfl
  · exact h1
  · exact h4
  · exact h5

theorem isRoot_trialityRoot'
    (j : Fin 6) : IsRoot TwistTag.D4.tag (trialityRoot j) :=
  (isRoot_trialityRoot j 0).1

theorem pinnedX_trialityRoot_mem
    {j : Fin 6} (hj : j = 1 ∨ j = 4 ∨ j = 5)
    (c : trialityFixedField K σ) : pinnedX TwistTag.D4.tag K (trialityRoot j) c ∈
      rootSpan TwistTag.D4.tag K (trialityOrbit j : Set (Fin TwistTag.D4.tag.rank → ℤ)) ⊓
        twistedFixedGroup TwistTag.D4 K σ :=
  pinnedX_D4_mem_fixed (isRoot_trialityRoot' j) (trialityRoot_fixed hj) c

theorem exists_pinnedX_trialityRoot_eq
    {j : Fin 6} (hj : j = 1 ∨ j = 4 ∨ j = 5)
    {u : ModGL TwistTag.D4.tag K}
    (hu : u ∈ rootSpan TwistTag.D4.tag K (trialityOrbit j : Set (Fin TwistTag.D4.tag.rank → ℤ)) ⊓
      twistedFixedGroup TwistTag.D4 K σ) :
    ∃ c : trialityFixedField K σ, pinnedX TwistTag.D4.tag K (trialityRoot j) c = u :=
  exists_pinnedX_D4_fixed_eq (isRoot_trialityRoot' j) (trialityRoot_fixed hj) hu

omit [CharP K 2] in
theorem rootSpan_trialityOrbit_le
    (j : Fin 6) :
    rootSpan TwistTag.D4.tag K (trialityOrbit j : Set (Fin TwistTag.D4.tag.rank → ℤ)) ⊓
        twistedFixedGroup TwistTag.D4 K σ ≤ graphFixedPosUnipotent TwistTag.D4 K σ :=
  inf_le_inf_right _ (rootSpan_mono (trialityOrbit_pos j))

end Maps

theorem even_triality_positive_orbit_parametrization
    (K : Type) [Field K] [Finite K] [CharP K 2]
    (σ : K ≃+* K) (hσ : σ.toRingHom ^ 3 = 1) :
    (∃ f : Multiplicative K →* graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom,
      Function.Injective f ∧ ∀ c : K, (f (Multiplicative.ofAdd c) : ModGL TwistTag.D4.tag K) =
        trialityX₁ K σ.toRingHom c) ∧
    (∃ f : Multiplicative (trialityFixedField K σ.toRingHom) →*
        graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom,
      Function.Injective f ∧ ∀ c, (f (Multiplicative.ofAdd c) : ModGL TwistTag.D4.tag K) =
        trialityX₂ K σ.toRingHom c) ∧
    (∃ f : Multiplicative K →* graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom,
      Function.Injective f ∧ ∀ c : K, (f (Multiplicative.ofAdd c) : ModGL TwistTag.D4.tag K) =
        trialityX₃ K σ.toRingHom c) ∧
    (∃ f : Multiplicative K →* graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom,
      Function.Injective f ∧ ∀ c : K, (f (Multiplicative.ofAdd c) : ModGL TwistTag.D4.tag K) =
        trialityX₄ K σ.toRingHom c) ∧
    (∃ f : Multiplicative (trialityFixedField K σ.toRingHom) →*
        graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom,
      Function.Injective f ∧ ∀ c, (f (Multiplicative.ofAdd c) : ModGL TwistTag.D4.tag K) =
        trialityX₅ K σ.toRingHom c) ∧
    (∃ f : Multiplicative (trialityFixedField K σ.toRingHom) →*
        graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom,
      Function.Injective f ∧ ∀ c, (f (Multiplicative.ofAdd c) : ModGL TwistTag.D4.tag K) =
        trialityX₆ K σ.toRingHom c) ∧
    Set.BijOn (fun p : K × trialityFixedField K σ.toRingHom × K × K ×
        trialityFixedField K σ.toRingHom × trialityFixedField K σ.toRingHom =>
      ((trialityX₁ K σ.toRingHom p.1 * trialityX₂ K σ.toRingHom p.2.1 *
        trialityX₃ K σ.toRingHom p.2.2.1 * trialityX₄ K σ.toRingHom p.2.2.2.1 *
        trialityX₅ K σ.toRingHom p.2.2.2.2.1 * trialityX₆ K σ.toRingHom p.2.2.2.2.2 :
          adjointGroup TwistTag.D4.tag K) : ModGL TwistTag.D4.tag K))
      Set.univ (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) ∧
    Nat.card (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) =
      Nat.card K ^ 3 * Nat.card (trialityFixedField K σ.toRingHom) ^ 3 ∧
    ∃ P : Sylow 2 (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      (P : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) =
        (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
          (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  set τ := σ.toRingHom with hτ
  set P := graphFixedPosUnipotent TwistTag.D4 K τ
  have tri : ∀ j : Fin 6, (j = 0 ∨ j = 2 ∨ j = 3) →
      ∃ f : Multiplicative K →* P, Function.Injective f ∧ ∀ c : K,
        (f (Multiplicative.ofAdd c) : ModGL TwistTag.D4.tag K) =
          trialityOrbitProd K τ (trialityRoot j) c := by
    intro j hj
    refine ⟨{ toFun := fun c => ⟨_, rootSpan_trialityOrbit_le j (trialityOrbitProd_mem hj hσ
        c.toAdd)⟩
              map_one' := Subtype.ext ?_
              map_mul' := fun a b => Subtype.ext ?_ }, fun a b hab => ?_, fun c => rfl⟩
    · have h := trialityOrbitProd_add' (σ := τ) hj 0 0
      rw [add_zero] at h
      have h1 : trialityOrbitProd K τ (trialityRoot j) 0 = 1 := by
        simpa using h
      simp [h1]
    · simp only [toAdd_mul, trialityOrbitProd_add' (σ := τ) hj, Subgroup.coe_mul]
    · have h := congrArg Subtype.val hab
      exact Multiplicative.toAdd.injective (trialityOrbitProd_injective' hj (Subtype.ext h))
  have sing : ∀ j : Fin 6, (j = 1 ∨ j = 4 ∨ j = 5) →
      ∃ f : Multiplicative (trialityFixedField K τ) →* P, Function.Injective f ∧ ∀ c,
        (f (Multiplicative.ofAdd c) : ModGL TwistTag.D4.tag K) =
          pinnedX TwistTag.D4.tag K (trialityRoot j) c := by
    intro j hj
    refine ⟨{ toFun := fun c => ⟨_, rootSpan_trialityOrbit_le j (pinnedX_trialityRoot_mem hj
        c.toAdd)⟩
              map_one' := Subtype.ext ?_
              map_mul' := fun a b => Subtype.ext ?_ }, fun a b hab => ?_, fun c => rfl⟩
    · simp [pinnedX_zero]
    · simp only [toAdd_mul, Subfield.coe_add, pinnedX_add, Subgroup.coe_mul]
    · have h := pinnedX_injective _ _ _ (congrArg Subtype.val hab)
      exact Multiplicative.toAdd.injective (Subtype.ext h)
  have hB := bijOn_prod_graphFixed (t := TwistTag.D4) (K := K) (σ := τ) σ.surjective
    (S := {α | IsRoot TwistTag.D4.tag α ∧ 0 < height α}) (fun _ h => h)
    (fun α hα => ⟨hα.1.permLattice TwistTag.D4.cartan_perm, by
      rw [height_permLattice]
      exact hα.2⟩)
    (fun α hα β hβ a b ha hb hr => ⟨hr, by
      have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
      have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
      rw [height_nsmul_add_nsmul]
      nlinarith [hα.2, hβ.2]⟩)
    trialityOrbit trialityOrbit_injective range_trialityOrbit
  set k := trialityFixedField K τ
  let v : K × k × K × K × k × k → Fin 6 → ModGL TwistTag.D4.tag K := fun p =>
    ![(trialityX₁ K τ p.1 : ModGL TwistTag.D4.tag K), (trialityX₂ K τ p.2.1 : ModGL _ _),
      (trialityX₃ K τ p.2.2.1 : ModGL _ _), (trialityX₄ K τ p.2.2.2.1 : ModGL _ _),
      (trialityX₅ K τ p.2.2.2.2.1 : ModGL _ _), (trialityX₆ K τ p.2.2.2.2.2 : ModGL _ _)]
  have hmap : ∀ p : K × k × K × K × k × k,
      ((trialityX₁ K τ p.1 * trialityX₂ K τ p.2.1 * trialityX₃ K τ p.2.2.1 *
        trialityX₄ K τ p.2.2.2.1 * trialityX₅ K τ p.2.2.2.2.1 * trialityX₆ K τ p.2.2.2.2.2 :
          adjointGroup TwistTag.D4.tag K) : ModGL TwistTag.D4.tag K) = (List.ofFn (v p)).prod := by
    intro p
    rw [list_ofFn_prod_fin_six]
    simp only [Subgroup.coe_mul]
    rfl
  have hv : ∀ p j, v p j ∈ rootSpan TwistTag.D4.tag K
      (trialityOrbit j : Set (Fin TwistTag.D4.tag.rank → ℤ)) := by
    intro p j
    fin_cases j
    · exact (Subgroup.mem_inf.1 (trialityOrbitProd_mem (j := 0) (by decide) hσ p.1)).1
    · exact (Subgroup.mem_inf.1 (pinnedX_trialityRoot_mem (j := 1) (by decide) p.2.1)).1
    · exact (Subgroup.mem_inf.1 (trialityOrbitProd_mem (j := 2) (by decide) hσ p.2.2.1)).1
    · exact (Subgroup.mem_inf.1 (trialityOrbitProd_mem (j := 3) (by decide) hσ p.2.2.2.1)).1
    · exact (Subgroup.mem_inf.1 (pinnedX_trialityRoot_mem (j := 4) (by decide) p.2.2.2.2.1)).1
    · exact (Subgroup.mem_inf.1 (pinnedX_trialityRoot_mem (j := 5) (by decide) p.2.2.2.2.2)).1
  have hbij : Set.BijOn (fun p : K × k × K × K × k × k =>
      ((trialityX₁ K τ p.1 * trialityX₂ K τ p.2.1 * trialityX₃ K τ p.2.2.1 *
        trialityX₄ K τ p.2.2.2.1 * trialityX₅ K τ p.2.2.2.2.1 * trialityX₆ K τ p.2.2.2.2.2 :
          adjointGroup TwistTag.D4.tag K) : ModGL TwistTag.D4.tag K)) Set.univ P := by
    refine ⟨fun p _ => ?_, fun p _ p' _ h => ?_, fun g hg => ?_⟩
    · dsimp only
      rw [hmap]
      refine Subgroup.list_prod_mem _ fun x hx => ?_
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
      fin_cases j
      · exact rootSpan_trialityOrbit_le 0 (trialityOrbitProd_mem (j := 0) (by decide) hσ p.1)
      · exact rootSpan_trialityOrbit_le 1 (pinnedX_trialityRoot_mem (j := 1) (by decide) p.2.1)
      · exact rootSpan_trialityOrbit_le 2
          (trialityOrbitProd_mem (j := 2) (by decide) hσ p.2.2.1)
      · exact rootSpan_trialityOrbit_le 3
          (trialityOrbitProd_mem (j := 3) (by decide) hσ p.2.2.2.1)
      · exact rootSpan_trialityOrbit_le 4
          (pinnedX_trialityRoot_mem (j := 4) (by decide) p.2.2.2.2.1)
      · exact rootSpan_trialityOrbit_le 5
          (pinnedX_trialityRoot_mem (j := 5) (by decide) p.2.2.2.2.2)
    · have h' : (List.ofFn (v p)).prod = (List.ofFn (v p')).prod := by
        rw [← hmap, ← hmap]
        exact h
      have huv := eq_of_prod_rootSpan_eq trialityOrbit_disjoint
        (fun j β hβ => trialityOrbit_pos j β hβ) trialityOrbit_not_isRoot (hv p) (hv p') h'
      have e0 : (trialityX₁ K τ p.1 : ModGL TwistTag.D4.tag K) = trialityX₁ K τ p'.1 :=
        congrFun huv 0
      have e1 : (trialityX₂ K τ p.2.1 : ModGL TwistTag.D4.tag K) = trialityX₂ K τ p'.2.1 :=
        congrFun huv 1
      have e2 : (trialityX₃ K τ p.2.2.1 : ModGL TwistTag.D4.tag K) = trialityX₃ K τ p'.2.2.1 :=
        congrFun huv 2
      have e3 : (trialityX₄ K τ p.2.2.2.1 : ModGL TwistTag.D4.tag K) =
          trialityX₄ K τ p'.2.2.2.1 := congrFun huv 3
      have e4 : (trialityX₅ K τ p.2.2.2.2.1 : ModGL TwistTag.D4.tag K) =
          trialityX₅ K τ p'.2.2.2.2.1 := congrFun huv 4
      have e5 : (trialityX₆ K τ p.2.2.2.2.2 : ModGL TwistTag.D4.tag K) =
          trialityX₆ K τ p'.2.2.2.2.2 := congrFun huv 5
      obtain ⟨a, b, c, d, e, f⟩ := p
      obtain ⟨a', b', c', d', e', f'⟩ := p'
      have ha : a = a' := trialityOrbitProd_injective' (j := 0) (by decide) (Subtype.ext e0)
      have hb : b = b' := Subtype.ext (pinnedX_injective _ _ _ e1)
      have hc : c = c' := trialityOrbitProd_injective' (j := 2) (by decide) (Subtype.ext e2)
      have hd : d = d' := trialityOrbitProd_injective' (j := 3) (by decide) (Subtype.ext e3)
      have he : e = e' := Subtype.ext (pinnedX_injective _ _ _ e4)
      have hf : f = f' := Subtype.ext (pinnedX_injective _ _ _ e5)
      rw [ha, hb, hc, hd, he, hf]
    · obtain ⟨u, -, hu⟩ := hB.surjOn hg
      obtain ⟨a, ha⟩ := exists_trialityOrbitProd_eq' (j := 0) (by decide) (u 0).2
      obtain ⟨b, hb⟩ := exists_pinnedX_trialityRoot_eq (j := 1) (by decide) (u 1).2
      obtain ⟨c, hc⟩ := exists_trialityOrbitProd_eq' (j := 2) (by decide) (u 2).2
      obtain ⟨d, hd⟩ := exists_trialityOrbitProd_eq' (j := 3) (by decide) (u 3).2
      obtain ⟨e, he⟩ := exists_pinnedX_trialityRoot_eq (j := 4) (by decide) (u 4).2
      obtain ⟨f, hf⟩ := exists_pinnedX_trialityRoot_eq (j := 5) (by decide) (u 5).2
      refine ⟨(a, b, c, d, e, f), Set.mem_univ _, ?_⟩
      dsimp only at hu ⊢
      rw [← hu, list_ofFn_prod_fin_six, ← ha, ← hb, ← hc, ← hd, ← he, ← hf]
      simp only [Subgroup.coe_mul]
      rfl
  have hcard : Nat.card P = Nat.card K ^ 3 * Nat.card k ^ 3 := by
    calc Nat.card P = Nat.card (Set.univ : Set (K × k × K × K × k × k)) :=
          (Nat.card_congr (hbij.equiv _)).symm
      _ = Nat.card (K × k × K × K × k × k) := Nat.card_univ
      _ = Nat.card K ^ 3 * Nat.card k ^ 3 := by
          simp only [Nat.card_prod]
          ring
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
  exact ⟨tri 0 (by decide), sing 1 (by decide), tri 2 (by decide), tri 3 (by decide),
    sing 4 (by decide), sing 5 (by decide), hbij, hcard,
    (exceptional_fixed_Sylow_opposition TwistTag.D4 K 2 σ w₀ hw₀).1⟩

end CFSG.LieType.Chevalley
