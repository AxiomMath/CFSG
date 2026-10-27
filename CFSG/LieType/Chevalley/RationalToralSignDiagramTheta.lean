module

public import CFSG.LieType.Chevalley.RationalToralSignDiagramDefs
public import CFSG.LieType.Chevalley.SignKernelPositiveRepresentatives

public section

namespace CFSG.LieType.Chevalley.ToralSign

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint Matrix

variable {τ : Tag}

theorem permLattice_symm_permLattice (π : Equiv.Perm (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    permLattice π.symm (permLattice π v) = v := by
  ext j
  simp [permLattice]

theorem permLattice_injective (π : Equiv.Perm (Fin τ.rank)) :
    Function.Injective (permLattice (τ := τ) π) := fun u v h => by
  rw [← permLattice_symm_permLattice π u, h, permLattice_symm_permLattice]

theorem height_permLattice (π : Equiv.Perm (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    height (permLattice π v) = height v := by
  simp only [height, permLattice, Function.comp_apply]
  exact Equiv.sum_comp π.symm v

theorem iform_permLattice {π : Equiv.Perm (Fin τ.rank)}
    (hB : ∀ i j, τ.symmetrizedCartan (π i) (π j) = τ.symmetrizedCartan i j)
    (u v : Fin τ.rank → ℤ) : iform (permLattice π u) (permLattice π v) = iform u v := by
  simp only [iform, permLattice, Function.comp_apply]
  rw [← Equiv.sum_comp π (fun i => ∑ j, u (π.symm i) * τ.symmetrizedCartan i j * v (π.symm j))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp π (fun j => u (π.symm (π i)) * τ.symmetrizedCartan (π i) j *
    v (π.symm j))]
  simp [hB]

variable
    {ρ : Equiv.Perm (Fin τ.rank)} {ω : WeylGroup τ}

theorem thetaMap_injective
    : Function.Injective (thetaMap ω ρ) := fun _ _ h =>
  permLattice_injective ρ (MulAction.injective ω h)

theorem thetaMap_add
    (u v : Fin τ.rank → ℤ) :
    thetaMap ω ρ (u + v) = thetaMap ω ρ u + thetaMap ω ρ v :=
  smul_add ω (permLattice ρ u) (permLattice ρ v)

theorem thetaMap_zsmul
    (c : ℤ) (v : Fin τ.rank → ℤ) :
    thetaMap ω ρ (c • v) = c • thetaMap ω ρ v :=
  smul_comm ω c (permLattice ρ v)

theorem thetaMap_sub
    (u v : Fin τ.rank → ℤ) :
    thetaMap ω ρ (u - v) = thetaMap ω ρ u - thetaMap ω ρ v :=
  smul_sub ω (permLattice ρ u) (permLattice ρ v)

theorem isRoot_thetaMap
    (hA : ∀ i j, τ.cartan (ρ i) (ρ j) = τ.cartan i j) {v : Fin τ.rank → ℤ}
    (hv : IsRoot τ v) : IsRoot τ (thetaMap ω ρ v) :=
  IsRoot.smul (hv.permLattice hA) ω

theorem iform_thetaMap
    (hB : ∀ i j, τ.symmetrizedCartan (ρ i) (ρ j) = τ.symmetrizedCartan i j)
    (u v : Fin τ.rank → ℤ) : iform (thetaMap ω ρ u) (thetaMap ω ρ v) = iform u v := by
  rw [thetaMap, thetaMap, iform_smul, iform_permLattice hB]

theorem thetaMap_rootReflection_smul
    (hA : ∀ i j, τ.cartan (ρ i) (ρ j) = τ.cartan i j)
    (hB : ∀ i j, τ.symmetrizedCartan (ρ i) (ρ j) = τ.symmetrizedCartan i j)
    {x : Fin τ.rank → ℤ} (hx : IsRoot τ x) (v : Fin τ.rank → ℤ) :
    thetaMap ω ρ (rootReflection x • v) = rootReflection (thetaMap ω ρ x) • thetaMap ω ρ v := by
  rw [rootReflection_smul hx, rootReflection_smul (isRoot_thetaMap hA hx), thetaMap_sub,
    thetaMap_zsmul, corootPair, corootPair, iform_thetaMap hB, iform_thetaMap hB]

theorem self_mem_iterOrbit {α : Type*} (f : α → α) (a : α) : a ∈ iterOrbit f a :=
  ⟨0, rfl⟩

theorem apply_mem_iterOrbit {α : Type*} {f : α → α} {a x : α} (hx : x ∈ iterOrbit f a) :
    f x ∈ iterOrbit f a := by
  obtain ⟨k, rfl⟩ := hx
  exact ⟨k + 1, Function.iterate_succ_apply' f k a⟩

theorem iterate_mem {α : Type*} {f : α → α} {S : Set α} (hS : ∀ x ∈ S, f x ∈ S) {a : α}
    (ha : a ∈ S) (k : ℕ) : f^[k] a ∈ S := by
  induction k with
  | zero => exact ha
  | succ k ih => rw [Function.iterate_succ_apply']; exact hS _ ih

theorem iterOrbit_subset {α : Type*} {f : α → α} {S : Set α} (hS : ∀ x ∈ S, f x ∈ S) {a : α}
    (ha : a ∈ S) : iterOrbit f a ⊆ S := by
  rintro _ ⟨k, rfl⟩
  exact iterate_mem hS ha k

theorem smul_iterate
    {θ : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ} {g : WeylGroup τ}
    (hg : ∀ v, g • θ v = θ (g • v)) (k : ℕ) (v : Fin τ.rank → ℤ) :
    g • θ^[k] v = θ^[k] (g • v) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hg, ih]

theorem image_smul_iterOrbit
    {θ : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ} {g : WeylGroup τ}
    (hg : ∀ v, g • θ v = θ (g • v)) (a : Fin τ.rank → ℤ) :
    (g • ·) '' iterOrbit θ a = iterOrbit θ (g • a) := by
  ext y
  constructor
  · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
    exact ⟨k, (smul_iterate hg k a).symm⟩
  · rintro ⟨k, rfl⟩
    exact ⟨θ^[k] a, ⟨k, rfl⟩, smul_iterate hg k a⟩

variable {χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ}

theorem chi_permLattice (hχ : permChar ρ χ = χ) (v : Fin τ.rank → ℤ) :
    χ (Multiplicative.ofAdd (permLattice ρ v)) = χ (Multiplicative.ofAdd v) := by
  have h := permChar_apply ρ χ (permLattice ρ v)
  rwa [permLattice_symm_permLattice, hχ] at h

theorem finite_kernelRoots
    (χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ) :
    (kernelRoots χ).Finite :=
  (finite_setOf_isRoot τ).subset fun _ h => h.1

theorem finite_posRoots_kernelRoots
    (χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ) :
    (posRoots (kernelRoots χ)).Finite :=
  (finite_kernelRoots χ).subset fun _ h => h.1

section Kernel

variable (hA : ∀ i j, τ.cartan (ρ i) (ρ j) = τ.cartan i j) (hχ : permChar ρ χ = χ)
include hA hχ

theorem thetaMap_mem_kernelRoots
    (hω : ω ∈ charStabilizer χ) {α : Fin τ.rank → ℤ}
    (hα : α ∈ kernelRoots χ) : thetaMap ω ρ α ∈ kernelRoots χ :=
  ⟨isRoot_thetaMap hA hα.1, ((hω _).trans (chi_permLattice hχ α)).trans hα.2⟩

theorem image_thetaMap_kernelRoots
    (hω : ω ∈ charStabilizer χ) :
    thetaMap ω ρ '' kernelRoots χ = kernelRoots χ :=
  (((finite_kernelRoots χ).injOn_iff_bijOn_of_mapsTo
    fun _ hα => thetaMap_mem_kernelRoots hA hχ hω hα).1 thetaMap_injective.injOn).image_eq

variable
    (hω : ω ∈ kernelPosStabilizer χ)
include hω

theorem thetaMap_mem_posRoots
    {α : Fin τ.rank → ℤ} (hα : α ∈ posRoots (kernelRoots χ)) :
    thetaMap ω ρ α ∈ posRoots (kernelRoots χ) := by
  have h1 : permLattice ρ α ∈ posRoots (kernelRoots χ) :=
    ⟨⟨hα.1.1.permLattice hA, (chi_permLattice hχ α).trans hα.1.2⟩,
      by rw [height_permLattice]; exact hα.2⟩
  rw [← hω.2]
  exact ⟨_, h1, rfl⟩

theorem image_thetaMap_posRoots :
    thetaMap ω ρ '' posRoots (kernelRoots χ) = posRoots (kernelRoots χ) :=
  (((finite_posRoots_kernelRoots χ).injOn_iff_bijOn_of_mapsTo
    fun _ hα => thetaMap_mem_posRoots hA hχ hω hα).1 thetaMap_injective.injOn).image_eq

theorem thetaMap_mem_simpleRoots
    {β : Fin τ.rank → ℤ}
    (hβ : β ∈ simpleRoots (kernelRoots χ)) : thetaMap ω ρ β ∈ simpleRoots (kernelRoots χ) := by
  rw [mem_simpleRoots] at hβ ⊢
  obtain ⟨hr, hpos, hns⟩ := hβ
  refine ⟨isRoot_thetaMap hA hr, thetaMap_mem_posRoots hA hχ hω hpos, fun γ hγ δ hδ e => ?_⟩
  have himg := image_thetaMap_posRoots hA hχ hω
  rw [← himg] at hγ hδ
  obtain ⟨γ', hγ', rfl⟩ := hγ
  obtain ⟨δ', hδ', rfl⟩ := hδ
  rw [← thetaMap_add] at e
  exact hns γ' hγ' δ' hδ' (thetaMap_injective e)

theorem image_thetaMap_simpleRoots :
    thetaMap ω ρ '' (simpleRoots (kernelRoots χ) : Set (Fin τ.rank → ℤ)) =
      simpleRoots (kernelRoots χ) :=
  (((simpleRoots (kernelRoots χ)).finite_toSet.injOn_iff_bijOn_of_mapsTo
    fun _ hβ => thetaMap_mem_simpleRoots hA hχ hω hβ).1 thetaMap_injective.injOn).image_eq

end Kernel

theorem simpleUnion_eq
    (χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ) :
    simpleUnion χ = (simpleRoots (kernelRoots χ) : Set (Fin τ.rank → ℤ)) := by
  ext β
  simp only [simpleUnion, Set.mem_iUnion, Finset.mem_coe]
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨hβk, hβi⟩ := simpleRoots_subset hi
    rw [mem_simpleRoots_kernelRoots_iff hβk, hβi]
    exact hi
  · intro h
    exact ⟨_, (mem_simpleRoots_kernelRoots_iff (simpleRoots_kernelRoots_mem h)).1 h⟩

theorem simpleUnion_subset
    (χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ) :
    simpleUnion χ ⊆ kernelRoots χ := by
  rw [simpleUnion_eq]
  exact fun _ h => simpleRoots_kernelRoots_mem h

theorem pairwise_commute_of_forall {M : Type*} [Monoid M] {l : List M}
    (h : ∀ x ∈ l, ∀ y ∈ l, Commute x y) : l.Pairwise Commute := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a l ih =>
    refine List.Pairwise.cons (fun y hy => h a (List.mem_cons_self ..) y
      (List.mem_cons_of_mem _ hy)) (ih fun x hx y hy => ?_)
    exact h x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)

theorem orbitReflection_eq_prod
    {O : Finset (Fin τ.rank → ℤ)} {l : List (Fin τ.rank → ℤ)}
    (hl : l.Nodup) (hO : ∀ x, x ∈ O ↔ x ∈ l)
    (hcomm : ∀ x ∈ O, ∀ y ∈ O, Commute (rootReflection x) (rootReflection y)) :
    orbitReflection O = (l.map rootReflection).prod := by
  classical
  have hp : O.toList.Perm l := by
    refine List.perm_of_nodup_nodup_toFinset_eq (Finset.nodup_toList O) hl ?_
    ext x
    simp [hO]
  refine (hp.map rootReflection).prod_eq' (pairwise_commute_of_forall fun x hx y hy => ?_)
  obtain ⟨x', hx', rfl⟩ := List.mem_map.1 hx
  obtain ⟨y', hy', rfl⟩ := List.mem_map.1 hy
  exact hcomm x' (Finset.mem_toList.1 hx') y' (Finset.mem_toList.1 hy')

theorem thetaMap_prod_smul
    (hA : ∀ i j, τ.cartan (ρ i) (ρ j) = τ.cartan i j)
    (hB : ∀ i j, τ.symmetrizedCartan (ρ i) (ρ j) = τ.symmetrizedCartan i j)
    {l : List (Fin τ.rank → ℤ)} (hl : ∀ x ∈ l, IsRoot τ x) (v : Fin τ.rank → ℤ) :
    thetaMap ω ρ ((l.map rootReflection).prod • v) =
      ((l.map fun x => rootReflection (thetaMap ω ρ x)).prod) • thetaMap ω ρ v := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.prod_cons, mul_smul]
    rw [thetaMap_rootReflection_smul hA hB (hl x (List.mem_cons_self ..)),
      ih fun y hy => hl y (List.mem_cons_of_mem _ hy)]

theorem orbitReflection_smul_thetaMap
    (hA : ∀ i j, τ.cartan (ρ i) (ρ j) = τ.cartan i j)
    (hB : ∀ i j, τ.symmetrizedCartan (ρ i) (ρ j) = τ.symmetrizedCartan i j)
    {O : Finset (Fin τ.rank → ℤ)} (hroot : ∀ x ∈ O, IsRoot τ x)
    (hθ : ∀ x ∈ O, thetaMap ω ρ x ∈ O)
    (hcomm : ∀ x ∈ O, ∀ y ∈ O, Commute (rootReflection x) (rootReflection y))
    (v : Fin τ.rank → ℤ) :
    orbitReflection O • thetaMap ω ρ v = thetaMap ω ρ (orbitReflection O • v) := by
  classical
  have himg : O.image (thetaMap ω ρ) = O :=
    Finset.eq_of_subset_of_card_le (fun y hy => by
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
      exact hθ x hx)
      (Finset.card_image_of_injective O thetaMap_injective).ge
  have hnd : (O.toList.map (thetaMap ω ρ)).Nodup :=
    (Finset.nodup_toList O).map thetaMap_injective
  have hmem : ∀ x, x ∈ O ↔ x ∈ O.toList.map (thetaMap ω ρ) := fun x => by
    rw [List.mem_map]
    constructor
    · intro hx
      rw [← himg] at hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
      exact ⟨y, Finset.mem_toList.2 hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact hθ y (Finset.mem_toList.1 hy)
  rw [orbitReflection, thetaMap_prod_smul hA hB (fun x hx => hroot x (Finset.mem_toList.1 hx))]
  congr 1
  rw [show (fun x => rootReflection (thetaMap ω ρ x)) = rootReflection ∘ thetaMap ω ρ from rfl,
    ← List.map_map, ← orbitReflection_eq_prod hnd hmem hcomm, orbitReflection]

section Group

variable
    (hA : ∀ i j, τ.cartan (ρ i) (ρ j) = τ.cartan i j) (hχ : permChar ρ χ = χ)
  (hω : ω ∈ kernelPosStabilizer χ)
include hA hχ hω

theorem thetaMap_mem_simpleUnion
    {β : Fin τ.rank → ℤ} (hβ : β ∈ simpleUnion χ) :
    thetaMap ω ρ β ∈ simpleUnion χ := by
  rw [simpleUnion_eq] at hβ ⊢
  exact thetaMap_mem_simpleRoots hA hχ hω hβ

theorem iterOrbit_subset_simpleUnion
    {β : Fin τ.rank → ℤ} (hβ : β ∈ simpleUnion χ) :
    iterOrbit (thetaMap ω ρ) β ⊆ simpleUnion χ :=
  iterOrbit_subset (fun _ hx => thetaMap_mem_simpleUnion hA hχ hω hx) hβ

theorem orbitReflectionGroup_le_kernelWeylGroup :
    orbitReflectionGroup (thetaMap ω ρ) (simpleUnion χ) ≤ kernelWeylGroup χ := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨β, hβ, O, hO, rfl⟩
  refine Subgroup.list_prod_mem _ fun r hr => ?_
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hr
  have hxO : x ∈ (O : Set (Fin τ.rank → ℤ)) := Finset.mem_toList.1 hx
  rw [hO] at hxO
  exact rootReflection_mem_kernelWeylGroup
    (simpleUnion_subset χ (iterOrbit_subset_simpleUnion hA hχ hω hβ hxO))

theorem smul_mem_kernelRoots_of_mem
    {g : WeylGroup τ}
    (hg : g ∈ orbitReflectionGroup (thetaMap ω ρ) (simpleUnion χ)) {α : Fin τ.rank → ℤ}
    (hα : α ∈ kernelRoots χ) : g • α ∈ kernelRoots χ :=
  smul_mem_kernelRoots (kernelWeylGroup_le (orbitReflectionGroup_le_kernelWeylGroup hA hχ hω hg))
    hα

variable (hpair : ∀ α ∈ kernelRoots χ,
  (iterOrbit (thetaMap ω ρ) α).Pairwise fun x y => x ⬝ᵥ (τ.symmetrizedCartan *ᵥ y) = 0)
include hpair

theorem commute_rootReflection_of_mem
    {β : Fin τ.rank → ℤ} (hβ : β ∈ simpleUnion χ)
    {x y : Fin τ.rank → ℤ} (hx : x ∈ iterOrbit (thetaMap ω ρ) β)
    (hy : y ∈ iterOrbit (thetaMap ω ρ) β) : Commute (rootReflection x) (rootReflection y) := by
  have hsub := iterOrbit_subset_simpleUnion hA hχ hω hβ
  by_cases hxy : x = y
  · rw [hxy]
  · have h : x ⬝ᵥ (τ.symmetrizedCartan *ᵥ y) = 0 := hpair β (simpleUnion_subset χ hβ) hx hy hxy
    rw [dotProduct_mulVec_eq_iform] at h
    exact rootReflection_commute (simpleUnion_subset χ (hsub hx)).1
      (simpleUnion_subset χ (hsub hy)).1 h

variable (hB : ∀ i j, τ.symmetrizedCartan (ρ i) (ρ j) = τ.symmetrizedCartan i j)
include hB

theorem smul_thetaMap_of_mem
    {g : WeylGroup τ}
    (hg : g ∈ orbitReflectionGroup (thetaMap ω ρ) (simpleUnion χ)) (v : Fin τ.rank → ℤ) :
    g • thetaMap ω ρ v = thetaMap ω ρ (g • v) := by
  induction hg using Subgroup.closure_induction generalizing v with
  | mem g hg =>
    obtain ⟨β, hβ, O, hO, rfl⟩ := hg
    have hsub := iterOrbit_subset_simpleUnion hA hχ hω hβ
    have hO' : ∀ x, x ∈ O ↔ x ∈ iterOrbit (thetaMap ω ρ) β := fun x => by
      rw [← hO]
      rfl
    refine orbitReflection_smul_thetaMap hA hB
      (fun x hx => (simpleUnion_subset χ (hsub ((hO' x).1 hx))).1)
      (fun x hx => (hO' _).2 (apply_mem_iterOrbit ((hO' x).1 hx)))
      (fun x hx y hy => commute_rootReflection_of_mem hA hχ hω hpair hβ ((hO' x).1 hx)
        ((hO' y).1 hy)) v
  | one => simp
  | mul x y _ _ hx hy => rw [mul_smul, hy, hx, mul_smul]
  | inv x _ hx =>
    have h := hx (x⁻¹ • v)
    rw [smul_inv_smul] at h
    rw [← h, inv_smul_smul]

theorem ThetaProperties.of_orbits
    {p : ℕ}
    (hcard : ∀ α ∈ kernelRoots χ,
      (iterOrbit (thetaMap ω ρ) α).ncard = 1 ∨ (iterOrbit (thetaMap ω ρ) α).ncard = p)
    (hcarry : ∀ α ∈ kernelRoots χ, ∃ g ∈ orbitReflectionGroup (thetaMap ω ρ) (simpleUnion χ),
      g • α ∈ simpleUnion χ) :
    ThetaProperties ρ p χ ω where
  image_kernelRoots := image_thetaMap_kernelRoots hA hχ hω.1
  image_simpleUnion := by
    rw [simpleUnion_eq]
    exact image_thetaMap_simpleRoots hA hχ hω
  ncard_iterOrbit := hcard
  pairwise_iterOrbit := hpair
  commute_rootReflection := fun _ hβ _ hx _ hy =>
    commute_rootReflection_of_mem hA hχ hω hpair hβ hx hy
  smul_mem_kernelRoots := fun _ hg _ hα => smul_mem_kernelRoots_of_mem hA hχ hω hg hα
  smul_thetaMap := fun _ hg v => smul_thetaMap_of_mem hA hχ hω hpair hB hg v
  exists_image_iterOrbit := fun α hα => by
    obtain ⟨g, hg, hgα⟩ := hcarry α hα
    exact ⟨g, hg, g • α, hgα,
      image_smul_iterOrbit (fun v => smul_thetaMap_of_mem hA hχ hω hpair hB hg v) α⟩

end Group

end CFSG.LieType.Chevalley.ToralSign
