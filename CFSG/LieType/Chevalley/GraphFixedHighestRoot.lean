module

public import CFSG.LieType.Chevalley.GraphFixedOrbitCollection
public import CFSG.LieType.Chevalley.MinimalBorelOvergroups

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.RootWalk
open scoped Pointwise

theorem eq_one_of_mul_self_eq_one_of_two_eq_zero {K : Type*} [Field K] (h2 : (2 : K) = 0)
    {ε : K} (hε : ε * ε = 1) : ε = 1 := by
  have h : (ε - 1) ^ 2 = 0 := by linear_combination hε + (1 - ε) * h2
  exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h)

theorem canonicalRep_mul_pinnedX_mul_inv_of_two
    {τ : Tag} {K : Type} [Field K]
    (h2 : (2 : K) = 0) (w : WeylGroup τ) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (c : K) :
    canonicalRep (coxeterSystem τ) K w * pinnedX τ K α c *
      (canonicalRep (coxeterSystem τ) K w)⁻¹ = pinnedX τ K (w • α) c := by
  obtain ⟨ε, hε, h⟩ := exists_canonicalRep_mul_pinnedX_mul_inv K w hα
  rw [h, eq_one_of_mul_self_eq_one_of_two_eq_zero h2 hε, one_mul]

variable {t : TwistTag} {K : Type} [Field K]

theorem twistHom_id_pinnedX
    (h2 : (2 : K) = 0) {α : Fin t.tag.rank → ℤ} (hα : IsRoot t.tag α)
    (c : K) :
    twistHom t K (RingHom.id K) (pinnedX t.tag K α c) =
      pinnedX t.tag K (permLattice t.perm α) c := by
  obtain ⟨w, i, rfl⟩ := isRoot_iff_exists_smul_single.1 hα
  rw [← canonicalRep_mul_pinnedX_mul_inv_of_two h2 w (isRoot_single _ i), map_mul, map_mul,
    map_inv, twistHom_canonicalRep, pinnedX_single, twistHom_xUnit, RingHom.id_apply,
    ← pinnedX_single, canonicalRep_mul_pinnedX_mul_inv_of_two h2 _ (isRoot_single _ _),
    ← permLattice_single, weylTwist_smul_permLattice]

@[expose] def e6HighestRoot : Fin TwistTag.E6.tag.rank → ℤ :=
  (![1, 2, 2, 3, 2, 1] : Fin 6 → ℤ)

theorem isRoot_e6HighestRoot : IsRoot TwistTag.E6.tag e6HighestRoot :=
  (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).2 ⟨70, by decide, by decide⟩

theorem height_e6HighestRoot : height e6HighestRoot = 11 := by decide

theorem permLattice_e6HighestRoot :
    permLattice TwistTag.E6.perm e6HighestRoot = e6HighestRoot := by decide

theorem height_le_eleven
    {α : Fin TwistTag.E6.tag.rank → ℤ} (hα : IsRoot TwistTag.E6.tag α) :
    height α ≤ 11 := by
  obtain ⟨k, hk, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).1 hα
  have h : (List.range TwistTag.E6.tag.rootCertificate.roots.length).all fun k =>
      decide (height (TwistTag.E6.tag.rootCertificate.root k) ≤ 11) := by decide
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h k hk

theorem not_isRoot_nsmul_add_nsmul_e6HighestRoot
    {β : Fin TwistTag.E6.tag.rank → ℤ}
    (hβp : 0 < height β) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ¬IsRoot TwistTag.E6.tag (a • β + b • e6HighestRoot) := by
  intro h
  have h1 := height_le_eleven h
  rw [height_nsmul_add_nsmul, height_e6HighestRoot] at h1
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  nlinarith

theorem commute_pinnedX_e6HighestRoot
    (R : Type) [CommRing R]
    {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : IsRoot TwistTag.E6.tag β) (hβp : 0 < height β)
    (a b : R) :
    Commute (pinnedX TwistTag.E6.tag R β a) (pinnedX TwistTag.E6.tag R e6HighestRoot b) := by
  by_cases hβr : β = e6HighestRoot
  · subst hβr
    rw [Commute, SemiconjBy, ← pinnedX_add, ← pinnedX_add, add_comm]
  · have hc := commutator_rootSubgroup_le R hβ isRoot_e6HighestRoot hβp
      (by rw [height_e6HighestRoot]; norm_num) hβr
    have hbot : (⨆ (γ : Fin TwistTag.E6.tag.rank → ℤ) (_ : IsRoot TwistTag.E6.tag γ ∧
        ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ γ = a • β + b • e6HighestRoot),
          rootSubgroup TwistTag.E6.tag R γ) = ⊥ := by
      refine iSup₂_eq_bot.2 ?_
      rintro γ ⟨hγ, a, b, ha, hb, rfl⟩
      exact absurd hγ (not_isRoot_nsmul_add_nsmul_e6HighestRoot hβp ha hb)
    rw [hbot] at hc
    have hmem := hc (Subgroup.commutator_mem_commutator (mem_rootSubgroup.2 ⟨a, rfl⟩)
      (mem_rootSubgroup.2 ⟨b, rfl⟩))
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem

theorem commute_e6HighestRoot_of_mem_posUnipotent
    (R : Type) [CommRing R]
    {g : (Module.End R (RootModule TwistTag.E6.tag R))ˣ} (hg : g ∈ posUnipotent TwistTag.E6.tag R)
    (b : R) : Commute g (pinnedX TwistTag.E6.tag R e6HighestRoot b) := by
  have hle : posUnipotent TwistTag.E6.tag R ≤
      Subgroup.centralizer {pinnedX TwistTag.E6.tag R e6HighestRoot b} := by
    refine iSup₂_le fun β hβ => (Subgroup.closure_le _).2 ?_
    rintro _ ⟨a, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact (commute_pinnedX_e6HighestRoot R hβ.1 hβ.2 a b).eq
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hg))

section Collection

theorem diagramOrbit_eq_singleton_of_fixed {α : Fin t.tag.rank → ℤ}
    (hα : permLattice t.perm α = α) : t.diagramOrbit α = {α} := by
  have hk : ∀ k : ℕ, permLattice (t.perm ^ k) α = α := by
    intro k
    induction k with
    | zero =>
      funext j
      rfl
    | succ k ih => rw [pow_succ', permLattice_mul, ih, hα]
  ext β
  simp only [TwistTag.diagramOrbit, Finset.mem_image, Finset.mem_range, Finset.mem_singleton]
  constructor
  · rintro ⟨k, -, rfl⟩
    exact hk k
  · rintro rfl
    exact ⟨0, t.order_pos, hk 0⟩

variable (t) in
open _root_.Classical in
@[expose] def orbitsAvoiding (S : Set (Fin t.tag.rank → ℤ)) (D : List (Fin t.tag.rank → ℤ)) :
    Finset (Finset (Fin t.tag.rank → ℤ)) :=
  (((rootFinset t.tag).filter (· ∈ S)).image t.diagramOrbit).filter fun O => ∀ d ∈ D, d ∉ O

theorem mem_orbitsAvoiding
    {S : Set (Fin t.tag.rank → ℤ)} {D : List (Fin t.tag.rank → ℤ)}
    {O : Finset (Fin t.tag.rank → ℤ)} :
    O ∈ orbitsAvoiding t S D ↔
      (∃ α, IsRoot t.tag α ∧ α ∈ S ∧ t.diagramOrbit α = O) ∧ ∀ d ∈ D, d ∉ O := by
  classical
  simp [orbitsAvoiding, mem_rootFinset, and_assoc]

variable (t) in
@[expose] def orbitAvoidingAt (S : Set (Fin t.tag.rank → ℤ)) (D : List (Fin t.tag.rank → ℤ))
    (j : Fin (orbitsAvoiding t S D).card) : Finset (Fin t.tag.rank → ℤ) :=
  ((orbitsAvoiding t S D).equivFin.symm j).1

variable (t) in
@[expose] def orbitEnum (S : Set (Fin t.tag.rank → ℤ)) (D : List (Fin t.tag.rank → ℤ)) :
    Fin ((orbitsAvoiding t S D).card + D.length) → Finset (Fin t.tag.rank → ℤ) :=
  Fin.append (orbitAvoidingAt t S D) fun i => {D.get i}

variable {S : Set (Fin t.tag.rank → ℤ)} {D : List (Fin t.tag.rank → ℤ)}

theorem orbitEnum_castAdd (j : Fin (orbitsAvoiding t S D).card) :
    orbitEnum t S D (Fin.castAdd D.length j) = orbitAvoidingAt t S D j :=
  Fin.append_left _ _ j

theorem orbitEnum_natAdd (i : Fin D.length) :
    orbitEnum t S D (Fin.natAdd (orbitsAvoiding t S D).card i) = {D.get i} :=
  Fin.append_right _ _ i

theorem exists_eq_diagramOrbit_of_mem_orbitsAvoiding
    (j : Fin (orbitsAvoiding t S D).card) :
    ∃ α, IsRoot t.tag α ∧ α ∈ S ∧ t.diagramOrbit α = orbitAvoidingAt t S D j ∧
      ∀ d ∈ D, d ∉ orbitAvoidingAt t S D j := by
  obtain ⟨⟨α, hα, hαS, he⟩, hD⟩ := mem_orbitsAvoiding.1 ((orbitsAvoiding t S D).equivFin.symm j).2
  exact ⟨α, hα, hαS, he, hD⟩

variable (hSρ : ∀ α ∈ S, permLattice t.perm α ∈ S)
  (hD : ∀ d ∈ D, d ∈ S ∧ permLattice t.perm d = d) (hDn : D.Nodup)

include hDn in
theorem orbitEnum_disjoint
    (i j : Fin ((orbitsAvoiding t S D).card + D.length)) (hij : i ≠ j) :
    Disjoint (orbitEnum t S D i) (orbitEnum t S D j) := by
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j =>
      rw [orbitEnum_castAdd, orbitEnum_castAdd]
      obtain ⟨α, -, -, hα, -⟩ := exists_eq_diagramOrbit_of_mem_orbitsAvoiding (D := D) i
      obtain ⟨β, -, -, hβ, -⟩ := exists_eq_diagramOrbit_of_mem_orbitsAvoiding (D := D) j
      rw [← hα, ← hβ]
      refine t.disjoint_diagramOrbit ?_
      rw [hα, hβ]
      intro h
      exact hij (congrArg _ ((orbitsAvoiding t S D).equivFin.symm.injective (Subtype.ext h)))
    | right j =>
      rw [orbitEnum_castAdd, orbitEnum_natAdd, Finset.disjoint_singleton_right]
      obtain ⟨-, -, -, -, hav⟩ := exists_eq_diagramOrbit_of_mem_orbitsAvoiding (D := D) i
      exact hav _ (List.get_mem _ _)
  | right i =>
    induction j using Fin.addCases with
    | left j =>
      rw [orbitEnum_castAdd, orbitEnum_natAdd, Finset.disjoint_singleton_left]
      obtain ⟨-, -, -, -, hav⟩ := exists_eq_diagramOrbit_of_mem_orbitsAvoiding (D := D) j
      exact hav _ (List.get_mem _ _)
    | right j =>
      rw [orbitEnum_natAdd, orbitEnum_natAdd, Finset.disjoint_singleton]
      intro h
      exact hij (congrArg _ ((List.nodup_iff_injective_get.1 hDn) h))

include hSρ hD in
theorem orbitEnum_subset
    (j : Fin ((orbitsAvoiding t S D).card + D.length)) :
    (orbitEnum t S D j : Set (Fin t.tag.rank → ℤ)) ⊆ S := by
  induction j using Fin.addCases with
  | left j =>
    rw [orbitEnum_castAdd]
    obtain ⟨α, -, hαS, hα, -⟩ := exists_eq_diagramOrbit_of_mem_orbitsAvoiding (D := D) j
    rw [← hα]
    exact diagramOrbit_subset hSρ hαS
  | right i =>
    rw [orbitEnum_natAdd, Finset.coe_singleton, Set.singleton_subset_iff]
    exact (hD _ (List.get_mem _ _)).1

include hD in
theorem orbitEnum_not_isRoot
    (hS : ∀ α ∈ S, IsRoot t.tag α ∧ 0 < height α)
    (j : Fin ((orbitsAvoiding t S D).card + D.length)) :
    ∀ α ∈ orbitEnum t S D j, ∀ β ∈ orbitEnum t S D j, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      ¬IsRoot t.tag (a • α + b • β) := by
  intro α hα β hβ a b ha hb
  induction j using Fin.addCases with
  | left j =>
    rw [orbitEnum_castAdd] at hα hβ
    obtain ⟨γ, hγ, -, he, -⟩ := exists_eq_diagramOrbit_of_mem_orbitsAvoiding (D := D) j
    rw [← he] at hα hβ
    exact t.not_isRoot_nsmul_add_nsmul_of_mem_diagramOrbit hγ hα hβ ha hb
  | right i =>
    rw [orbitEnum_natAdd] at hα hβ
    obtain ⟨hdS, hdρ⟩ := hD _ (List.get_mem D i)
    rw [← diagramOrbit_eq_singleton_of_fixed hdρ] at hα hβ
    exact t.not_isRoot_nsmul_add_nsmul_of_mem_diagramOrbit (hS _ hdS).1 hα hβ ha hb

include hSρ hD in
theorem mem_iff_exists_mem_orbitEnum
    (hS : ∀ α ∈ S, IsRoot t.tag α ∧ 0 < height α)
    (α : Fin t.tag.rank → ℤ) : α ∈ S ↔ ∃ j, α ∈ orbitEnum t S D j := by
  refine ⟨fun hα => ?_, fun ⟨j, hj⟩ => orbitEnum_subset hSρ hD j hj⟩
  by_cases hαD : α ∈ D
  · obtain ⟨i, rfl⟩ := List.get_of_mem hαD
    exact ⟨Fin.natAdd _ i, by rw [orbitEnum_natAdd]; exact Finset.mem_singleton_self _⟩
  · have hO : t.diagramOrbit α ∈ orbitsAvoiding t S D := by
      refine mem_orbitsAvoiding.2 ⟨⟨α, (hS α hα).1, hα, rfl⟩, fun d hd hdα => hαD ?_⟩
      have h1 := t.diagramOrbit_eq_of_mem hdα
      rw [diagramOrbit_eq_singleton_of_fixed (hD d hd).2] at h1
      have h2 := h1 ▸ t.self_mem_diagramOrbit α
      rw [Finset.mem_singleton] at h2
      exact h2 ▸ hd
    refine ⟨Fin.castAdd _ ((orbitsAvoiding t S D).equivFin ⟨_, hO⟩), ?_⟩
    rw [orbitEnum_castAdd, orbitAvoidingAt, Equiv.symm_apply_apply]
    exact t.self_mem_diagramOrbit α

include hSρ hD hDn in
theorem exists_orbitEnum_decomposition
    (hS : ∀ α ∈ S, IsRoot t.tag α ∧ 0 < height α)
    (hclosed : ∀ α ∈ S, ∀ β ∈ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot t.tag (a • α + b • β) →
      a • α + b • β ∈ S)
    {u : ModGL t.tag K} (hu : u ∈ rootSpan t.tag K S) :
    ∃ (a : Fin (orbitsAvoiding t S D).card → ModGL t.tag K) (c : Fin D.length → K),
      (∀ j, a j ∈ rootSpan t.tag K
        (orbitAvoidingAt t S D j : Set (Fin t.tag.rank → ℤ))) ∧
      (List.ofFn a).prod * (List.ofFn fun i => pinnedX t.tag K (D.get i) (c i)).prod = u := by
  obtain ⟨v, hv, rfl⟩ := exists_prod_rootSpan_eq (O := orbitEnum t S D)
    (fun i j hij => orbitEnum_disjoint hDn i j hij) hS hclosed
    (mem_iff_exists_mem_orbitEnum hSρ hD hS) hu
  have hb : ∀ i, ∃ c, pinnedX t.tag K (D.get i) c = v (Fin.natAdd _ i) := fun i => by
    have h := hv (Fin.natAdd _ i)
    rw [orbitEnum_natAdd, Finset.coe_singleton, rootSpan_singleton] at h
    exact mem_rootSubgroup.1 h
  choose c hc using hb
  refine ⟨fun j => v (Fin.castAdd _ j), c, fun j => ?_, ?_⟩
  · have h := hv (Fin.castAdd _ j)
    rwa [orbitEnum_castAdd] at h
  · conv_rhs => rw [← Fin.append_castAdd_natAdd (f := v)]
    rw [List.ofFn_fin_append, List.prod_append]
    simp only [hc]

include hSρ hD hDn in
theorem eq_of_orbitEnum_decomposition
    (hS : ∀ α ∈ S, IsRoot t.tag α ∧ 0 < height α)
    {a a' : Fin (orbitsAvoiding t S D).card → ModGL t.tag K} {c c' : Fin D.length → K}
    (ha : ∀ j, a j ∈ rootSpan t.tag K
      (orbitAvoidingAt t S D j : Set (Fin t.tag.rank → ℤ)))
    (ha' : ∀ j, a' j ∈ rootSpan t.tag K
      (orbitAvoidingAt t S D j : Set (Fin t.tag.rank → ℤ)))
    (h : (List.ofFn a).prod * (List.ofFn fun i => pinnedX t.tag K (D.get i) (c i)).prod =
      (List.ofFn a').prod * (List.ofFn fun i => pinnedX t.tag K (D.get i) (c' i)).prod) :
    a = a' ∧ c = c' := by
  have hmem : ∀ (a : Fin (orbitsAvoiding t S D).card → ModGL t.tag K) (c : Fin D.length → K),
      (∀ j, a j ∈ rootSpan t.tag K
        (orbitAvoidingAt t S D j : Set (Fin t.tag.rank → ℤ))) →
      ∀ j, Fin.append a (fun i => pinnedX t.tag K (D.get i) (c i)) j ∈
        rootSpan t.tag K (orbitEnum t S D j : Set (Fin t.tag.rank → ℤ)) := by
    intro a c ha j
    induction j using Fin.addCases with
    | left j =>
      rw [Fin.append_left, orbitEnum_castAdd]
      exact ha j
    | right i =>
      rw [Fin.append_right, orbitEnum_natAdd, Finset.coe_singleton, rootSpan_singleton]
      exact mem_rootSubgroup.2 ⟨c i, rfl⟩
  have e := eq_of_prod_rootSpan_eq (O := orbitEnum t S D)
    (fun i j hij => orbitEnum_disjoint hDn i j hij)
    (fun j α hα => hS α (orbitEnum_subset hSρ hD j hα)) (orbitEnum_not_isRoot hD hS)
    (hmem a c ha) (hmem a' c' ha') (by
      rw [List.ofFn_fin_append, List.ofFn_fin_append, List.prod_append, List.prod_append]
      exact h)
  refine ⟨funext fun j => ?_, funext fun i => pinnedX_injective t.tag K (D.get i) ?_⟩
  · simpa using congrFun e (Fin.castAdd _ j)
  · simpa using congrFun e (Fin.natAdd _ i)

theorem twistHom_mem_orbitsAvoiding
    (j : Fin (orbitsAvoiding t S D).card)
    {g : ModGL t.tag K} (hg : g ∈ rootSpan t.tag K
      (orbitAvoidingAt t S D j : Set (Fin t.tag.rank → ℤ))) :
    twistHom t K (RingHom.id K) g ∈ rootSpan t.tag K
      (orbitAvoidingAt t S D j : Set (Fin t.tag.rank → ℤ)) := by
  obtain ⟨α, hα, -, he, -⟩ := exists_eq_diagramOrbit_of_mem_orbitsAvoiding (D := D) j
  rw [← he] at hg ⊢
  have h := Subgroup.mem_map_of_mem (twistHom t K (RingHom.id K)) hg
  rw [map_twistHom_rootSpan t K (σ := RingHom.id K) (fun x => ⟨x, rfl⟩)
    fun β hβ => t.isRoot_of_mem_diagramOrbit hα hβ] at h
  refine rootSpan_mono ?_ h
  rintro _ ⟨β, hβ, rfl⟩
  exact t.permLattice_mem_diagramOrbit hβ

omit hSρ hD hDn in
theorem list_prod_ofFn_pinnedX_one
    (d : Fin t.tag.rank → ℤ) (c : Fin [d].length → K) :
    (List.ofFn fun i => pinnedX t.tag K ([d].get i) (c i)).prod =
      pinnedX t.tag K d (c ⟨0, by simp⟩) := by
  rw [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
  rfl

omit hSρ hD hDn in
theorem list_prod_ofFn_pinnedX_two
    (d₁ d₂ : Fin t.tag.rank → ℤ) (c : Fin [d₁, d₂].length → K) :
    (List.ofFn fun i => pinnedX t.tag K ([d₁, d₂].get i) (c i)).prod =
      pinnedX t.tag K d₁ (c ⟨0, by simp⟩) * pinnedX t.tag K d₂ (c ⟨1, by simp⟩) := by
  rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_cons,
    List.prod_nil, mul_one]
  rfl

omit hSρ hD hDn in
theorem eq_zero_of_twistHom_eq_mul
    (h2 : (2 : K) = 0)
    (hS : ∀ α ∈ S, IsRoot t.tag α ∧ 0 < height α) (hSρ : ∀ α ∈ S, permLattice t.perm α ∈ S)
    (hclosed : ∀ α ∈ S, ∀ β ∈ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot t.tag (a • α + b • β) →
      a • α + b • β ∈ S)
    {d : Fin t.tag.rank → ℤ} (hdS : d ∈ S) (hdρ : permLattice t.perm d = d)
    {u : ModGL t.tag K} (hu : u ∈ rootSpan t.tag K S) {e : K}
    (h : twistHom t K (RingHom.id K) u = u * pinnedX t.tag K d e) : e = 0 := by
  have hD : ∀ x ∈ [d], x ∈ S ∧ permLattice t.perm x = x := by
    intro x hx
    rw [List.mem_singleton] at hx
    subst hx
    exact ⟨hdS, hdρ⟩
  have hDn := List.nodup_singleton d
  obtain ⟨a, c, ha, rfl⟩ := exists_orbitEnum_decomposition hSρ hD hDn hS hclosed hu
  have hd : IsRoot t.tag d := (hS d hdS).1
  rw [list_prod_ofFn_pinnedX_one, map_mul, map_list_prod, List.map_ofFn,
    twistHom_id_pinnedX h2 hd, hdρ, mul_assoc, ← pinnedX_add] at h
  have h' : (List.ofFn (twistHom t K (RingHom.id K) ∘ a)).prod *
      (List.ofFn fun i => pinnedX t.tag K ([d].get i) (c i)).prod =
      (List.ofFn a).prod * (List.ofFn fun i =>
        pinnedX t.tag K ([d].get i) ((fun _ => c ⟨0, by simp⟩ + e) i)).prod := by
    rw [list_prod_ofFn_pinnedX_one, list_prod_ofFn_pinnedX_one]
    exact h
  obtain ⟨-, hc⟩ := eq_of_orbitEnum_decomposition hSρ hD hDn hS
    (fun j => twistHom_mem_orbitsAvoiding j (ha j)) ha h'
  have := congrFun hc ⟨0, by simp⟩
  simpa using this

omit hSρ hD hDn in
theorem eq_zero_of_twistHom_eq_mul_mul
    (h2 : (2 : K) = 0)
    (hS : ∀ α ∈ S, IsRoot t.tag α ∧ 0 < height α) (hSρ : ∀ α ∈ S, permLattice t.perm α ∈ S)
    (hclosed : ∀ α ∈ S, ∀ β ∈ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot t.tag (a • α + b • β) →
      a • α + b • β ∈ S)
    {d₁ d₂ : Fin t.tag.rank → ℤ} (hd₁S : d₁ ∈ S) (hd₁ρ : permLattice t.perm d₁ = d₁)
    (hd₂S : d₂ ∈ S) (hd₂ρ : permLattice t.perm d₂ = d₂) (hne : d₁ ≠ d₂)
    (hcomm : ∀ x y : K, Commute (pinnedX t.tag K d₁ x) (pinnedX t.tag K d₂ y))
    {u : ModGL t.tag K} (hu : u ∈ rootSpan t.tag K S) {e f : K}
    (h : twistHom t K (RingHom.id K) u = u * pinnedX t.tag K d₂ e * pinnedX t.tag K d₁ f) :
    e = 0 := by
  have hD : ∀ x ∈ [d₁, d₂], x ∈ S ∧ permLattice t.perm x = x := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    exacts [⟨hd₁S, hd₁ρ⟩, ⟨hd₂S, hd₂ρ⟩]
  have hDn : [d₁, d₂].Nodup := by simp [hne]
  obtain ⟨a, c, ha, rfl⟩ := exists_orbitEnum_decomposition hSρ hD hDn hS hclosed hu
  rw [list_prod_ofFn_pinnedX_two, map_mul, map_list_prod, List.map_ofFn, map_mul,
    twistHom_id_pinnedX h2 (hS d₁ hd₁S).1, twistHom_id_pinnedX h2 (hS d₂ hd₂S).1, hd₁ρ,
    hd₂ρ] at h
  have h' : (List.ofFn (twistHom t K (RingHom.id K) ∘ a)).prod *
      (List.ofFn fun i => pinnedX t.tag K ([d₁, d₂].get i) (c i)).prod =
      (List.ofFn a).prod * (List.ofFn fun i => pinnedX t.tag K ([d₁, d₂].get i)
        ((![c ⟨0, by simp⟩ + f, c ⟨1, by simp⟩ + e] : Fin 2 → K) i)).prod := by
    rw [list_prod_ofFn_pinnedX_two, list_prod_ofFn_pinnedX_two, h]
    show _ = _ * (pinnedX t.tag K d₁ (c ⟨0, by simp⟩ + f) *
      pinnedX t.tag K d₂ (c ⟨1, by simp⟩ + e))
    rw [pinnedX_add, pinnedX_add]
    have hc := (hcomm f (c ⟨1, by simp⟩ + e)).eq
    rw [pinnedX_add] at hc
    simp only [mul_assoc] at hc ⊢
    rw [hc]
  obtain ⟨-, hc⟩ := eq_of_orbitEnum_decomposition hSρ hD hDn hS
    (fun j => twistHom_mem_orbitsAvoiding j (ha j)) ha h'
  have := congrFun hc ⟨1, by simp⟩
  simpa using this

end Collection

theorem permLattice_mem_inversionSet
    {w : WeylGroup t.tag} (hw : weylTwist t w = w)
    {α : Fin t.tag.rank → ℤ} (hα : α ∈ inversionSet w) :
    permLattice t.perm α ∈ inversionSet w := by
  obtain ⟨hα, hpos, -, hneg⟩ := hα
  refine ⟨hα.permLattice t.cartan_perm, by rwa [height_permLattice],
    IsRoot.smul (hα.permLattice t.cartan_perm) w, ?_⟩
  rw [← hw, weylTwist_smul_permLattice, height_permLattice]
  exact hneg

theorem posRoots_closed {τ : Tag} :
    ∀ α ∈ {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α},
      ∀ β ∈ {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
        IsRoot τ (a • α + b • β) →
          a • α + b • β ∈ {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α} := by
  intro α hα β hβ a b ha hb hr
  refine ⟨hr, ?_⟩
  rw [height_nsmul_add_nsmul]
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  nlinarith [hα.2, hβ.2]

theorem permLattice_mem_posRoots
    {α : Fin t.tag.rank → ℤ}
    (hα : α ∈ {α : Fin t.tag.rank → ℤ | IsRoot t.tag α ∧ 0 < height α}) :
    permLattice t.perm α ∈ {α : Fin t.tag.rank → ℤ | IsRoot t.tag α ∧ 0 < height α} :=
  ⟨hα.1.permLattice t.cartan_perm, by rw [height_permLattice]; exact hα.2⟩

theorem torusGroup_le_normalizer_rootSubgroup
    {τ : Tag} {R : Type*} [CommRing R]
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    torusGroup τ R ≤
      Subgroup.normalizer (rootSubgroup τ R α : Set (Module.End R (RootModule τ R))ˣ) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨⟨i, s⟩, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
  intro g
  have h := map_conj_torusElt_rootSubgroup i s hα (R := R)
  constructor
  · intro hg
    rw [← h]
    exact ⟨g, hg, rfl⟩
  · intro hg
    rw [← h] at hg
    obtain ⟨g', hg', he⟩ := hg
    have : g' = g := by
      simpa [MulAut.conj_apply] using he
    rwa [← this]

variable {K : Type} [Field K]

theorem pinnedX_e6HighestRoot_mem_posUnipotent
    (c : K) :
    pinnedX TwistTag.E6.tag K e6HighestRoot c ∈ posUnipotent TwistTag.E6.tag K :=
  Subgroup.mem_iSup_of_mem e6HighestRoot (Subgroup.mem_iSup_of_mem
    ⟨isRoot_e6HighestRoot, by rw [height_e6HighestRoot]; norm_num⟩
    (Subgroup.subset_closure ⟨c, rfl⟩))

theorem twistHom_eq_of_conj_twistHom_eq
    (h2 : (2 : K) = 0) {c : K} (hc : c ≠ 0)
    {g : ModGL TwistTag.E6.tag K} (hg : g ∈ adjointGroup TwistTag.E6.tag K)
    (hζ : pinnedX TwistTag.E6.tag K e6HighestRoot c * twistHom TwistTag.E6 K (RingHom.id K) g *
      (pinnedX TwistTag.E6.tag K e6HighestRoot c)⁻¹ = g) :
    twistHom TwistTag.E6 K (RingHom.id K) g = g := by
  have hσ : Function.Surjective (RingHom.id K) := fun x => ⟨x, rfl⟩
  have hr : IsRoot TwistTag.E6.tag e6HighestRoot := isRoot_e6HighestRoot
  have hrpos : 0 < height e6HighestRoot := by rw [height_e6HighestRoot]; norm_num
  have htU := pinnedX_e6HighestRoot_mem_posUnipotent (K := K) c
  have htB : pinnedX TwistTag.E6.tag K e6HighestRoot c ∈ borelGroup TwistTag.E6.tag K :=
    Subgroup.mem_sup_right htU
  have hγt : twistHom TwistTag.E6 K (RingHom.id K) (pinnedX TwistTag.E6.tag K e6HighestRoot c) =
      pinnedX TwistTag.E6.tag K e6HighestRoot c := by
    rw [twistHom_id_pinnedX h2 hr, permLattice_e6HighestRoot]
  have hg' : g ∈ ⋃ w, bruhatCell TwistTag.E6.tag K w := by
    rw [← adjointGroup_eq_iUnion_bruhatCell]
    exact hg
  obtain ⟨w, hgw⟩ := Set.mem_iUnion.1 hg'
  obtain ⟨⟨b, v⟩, ⟨hb, hv⟩, hbv⟩ := (bijOn_bruhatCell w).surjOn hgw
  simp only at hbv
  have hδ : weylTwist TwistTag.E6 w = w := by
    by_contra hne
    have h1 := twistHom_mem_bruhatCell hσ hgw
    obtain ⟨b₁, hb₁, b₂, hb₂, he⟩ := mem_bruhatCell.1 h1
    have h3 : g ∈ bruhatCell TwistTag.E6.tag K (weylTwist TwistTag.E6 w) := by
      refine mem_bruhatCell.2 ⟨pinnedX TwistTag.E6.tag K e6HighestRoot c * b₁, mul_mem htB hb₁,
        b₂ * (pinnedX TwistTag.E6.tag K e6HighestRoot c)⁻¹, mul_mem hb₂ (inv_mem htB), ?_⟩
      rw [← hζ, ← he]
      group
    exact Set.disjoint_left.1 (disjoint_bruhatCell hne) h3 hgw
  have hγg : twistHom TwistTag.E6 K (RingHom.id K) g =
      twistHom TwistTag.E6 K (RingHom.id K) b * canonicalRep (coxeterSystem TwistTag.E6.tag) K w *
        twistHom TwistTag.E6 K (RingHom.id K) v := by
    rw [← hbv, map_mul, map_mul, twistHom_canonicalRep, hδ]
  have heq : pinnedX TwistTag.E6.tag K e6HighestRoot c * twistHom TwistTag.E6 K (RingHom.id K) b *
      canonicalRep (coxeterSystem TwistTag.E6.tag) K w * twistHom TwistTag.E6 K (RingHom.id K) v =
      b * canonicalRep (coxeterSystem TwistTag.E6.tag) K w * v *
        pinnedX TwistTag.E6.tag K e6HighestRoot c := by
    rw [hbv, ← hζ, hγg]
    group
  have hγb := twistHom_mem_borelGroup hσ hb (σ := RingHom.id K) (t := TwistTag.E6)
  have hγv := twistHom_mem_rootSpan_inversionSet (σ := RingHom.id K) hσ hδ hv
  have hinj := (bijOn_bruhatCell (K := K) w).injOn
  have hIpos : ∀ α ∈ inversionSet w, IsRoot TwistTag.E6.tag α ∧ 0 < height α :=
    fun α hα => ⟨hα.1, hα.2.1⟩
  rcases IsRoot.height_pos_or_neg (IsRoot.smul hr w) with hpos | hneg
  ·
    have hs : IsRoot TwistTag.E6.tag (w • e6HighestRoot) := IsRoot.smul hr w
    have hsρ : permLattice TwistTag.E6.perm (w • e6HighestRoot) = w • e6HighestRoot := by
      rw [← weylTwist_smul_permLattice, hδ, permLattice_e6HighestRoot]
    have hnt := canonicalRep_mul_pinnedX_mul_inv_of_two h2 w hr c
    have hvU : v ∈ posUnipotent TwistTag.E6.tag K :=
      rootSpan_le_posUnipotent (fun α hα => inversionSet_pos hα) hv
    have hvt := (commute_e6HighestRoot_of_mem_posUnipotent K hvU c).eq
    have hsU : pinnedX TwistTag.E6.tag K (w • e6HighestRoot) c ∈ posUnipotent TwistTag.E6.tag K :=
      Subgroup.mem_iSup_of_mem _ (Subgroup.mem_iSup_of_mem ⟨hs, hpos⟩
        (Subgroup.subset_closure ⟨c, rfl⟩))
    have hsB : pinnedX TwistTag.E6.tag K (w • e6HighestRoot) c ∈ borelGroup TwistTag.E6.tag K :=
      Subgroup.mem_sup_right hsU
    have hm1 : (pinnedX TwistTag.E6.tag K e6HighestRoot c *
        twistHom TwistTag.E6 K (RingHom.id K) b, twistHom TwistTag.E6 K (RingHom.id K) v) ∈
        (borelGroup TwistTag.E6.tag K : Set (ModGL TwistTag.E6.tag K)) ×ˢ
          (rootSpan TwistTag.E6.tag K (inversionSet w) : Set (ModGL TwistTag.E6.tag K)) :=
      Set.mk_mem_prod (mul_mem htB hγb) hγv
    have hm2 : (b * pinnedX TwistTag.E6.tag K (w • e6HighestRoot) c, v) ∈
        (borelGroup TwistTag.E6.tag K : Set (ModGL TwistTag.E6.tag K)) ×ˢ
          (rootSpan TwistTag.E6.tag K (inversionSet w) : Set (ModGL TwistTag.E6.tag K)) :=
      Set.mk_mem_prod (mul_mem hb hsB) hv
    have he : pinnedX TwistTag.E6.tag K e6HighestRoot c * twistHom TwistTag.E6 K (RingHom.id K) b *
        canonicalRep (coxeterSystem TwistTag.E6.tag) K w *
          twistHom TwistTag.E6 K (RingHom.id K) v =
        b * pinnedX TwistTag.E6.tag K (w • e6HighestRoot) c *
          canonicalRep (coxeterSystem TwistTag.E6.tag) K w * v := by
      rw [heq, ← hnt, mul_assoc (b * _) v _, hvt]
      group
    have h := Prod.ext_iff.1 (hinj hm1 hm2 he)
    have hb' := h.1
    have hv' := h.2
    simp only at hb' hv'
    have hBHU := (triangular_borel_structure.{0, 0} TwistTag.E6.tag K).2.2.2.2.1
    have hbmem : b ∈ (torusGroup TwistTag.E6.tag K : Set (ModGL TwistTag.E6.tag K)) *
        (posUnipotent TwistTag.E6.tag K : Set (ModGL TwistTag.E6.tag K)) := by
      rw [← hBHU]
      exact hb
    obtain ⟨x, hx, u, hu, rfl⟩ := Set.mem_mul.1 hbmem
    have hγx := twistHom_mem_torusGroup' hσ hx (σ := RingHom.id K) (t := TwistTag.E6)
    have hγu := twistHom_mem_posUnipotent hσ hu (σ := RingHom.id K) (t := TwistTag.E6)
    have huniq := (triangular_borel_structure.{0, 0} TwistTag.E6.tag K).2.2.2.2.2.2.1
    have hN := torusGroup_le_normalizer_posUnipotent (τ := TwistTag.E6.tag) (R := K)
    have hz : (twistHom TwistTag.E6 K (RingHom.id K) x)⁻¹ *
        pinnedX TwistTag.E6.tag K e6HighestRoot c * twistHom TwistTag.E6 K (RingHom.id K) x ∈
          posUnipotent TwistTag.E6.tag K := by
      have h1 := (Subgroup.mem_normalizer_iff.1 (hN (inv_mem hγx)) _).1 htU
      rwa [inv_inv] at h1
    have hfac : twistHom TwistTag.E6 K (RingHom.id K) x *
        ((twistHom TwistTag.E6 K (RingHom.id K) x)⁻¹ * pinnedX TwistTag.E6.tag K e6HighestRoot c *
          twistHom TwistTag.E6 K (RingHom.id K) x * twistHom TwistTag.E6 K (RingHom.id K) u) =
        x * (u * pinnedX TwistTag.E6.tag K (w • e6HighestRoot) c) := by
      rw [map_mul] at hb'
      rw [← mul_assoc x, ← hb']
      group
    obtain ⟨hxx, huu⟩ := huniq _ hγx _ hx _ (mul_mem hz hγu) _ (mul_mem hu hsU) hfac
    rw [hxx] at huu
    have hzr : x⁻¹ * pinnedX TwistTag.E6.tag K e6HighestRoot c * x⁻¹⁻¹ ∈
        rootSubgroup TwistTag.E6.tag K e6HighestRoot :=
      (Subgroup.mem_normalizer_iff.1 (torusGroup_le_normalizer_rootSubgroup hr (inv_mem hx))
        _).1 (mem_rootSubgroup.2 ⟨c, rfl⟩)
    rw [inv_inv] at hzr
    obtain ⟨a, ha⟩ := mem_rootSubgroup.1 hzr
    rw [← ha] at huu
    have hγu' : twistHom TwistTag.E6 K (RingHom.id K) u =
        u * pinnedX TwistTag.E6.tag K (w • e6HighestRoot) c *
          pinnedX TwistTag.E6.tag K e6HighestRoot (-a) := by
      have h1 : twistHom TwistTag.E6 K (RingHom.id K) u =
          (pinnedX TwistTag.E6.tag K e6HighestRoot a)⁻¹ *
            (u * pinnedX TwistTag.E6.tag K (w • e6HighestRoot) c) := by
        rw [← huu]
        group
      rw [h1, pinnedX_neg]
      exact (commute_e6HighestRoot_of_mem_posUnipotent K (mul_mem hu hsU) (-a)).eq.symm
    by_cases hsr : w • e6HighestRoot = e6HighestRoot
    · rw [hsr, mul_assoc, ← pinnedX_add] at hγu'
      have hca := eq_zero_of_twistHom_eq_mul h2 (fun α hα => hα)
        (fun α hα => permLattice_mem_posRoots hα) posRoots_closed ⟨hr, hrpos⟩
        permLattice_e6HighestRoot hu hγu'
      have hγu'' : twistHom TwistTag.E6 K (RingHom.id K) u = u := by
        rw [hγu', hca, pinnedX_zero, mul_one]
      rw [hγg, map_mul, hxx, hγu'', hv', ← hbv]
    · exfalso
      exact hc (eq_zero_of_twistHom_eq_mul_mul h2 (fun α hα => hα)
        (fun α hα => permLattice_mem_posRoots hα) posRoots_closed ⟨hr, hrpos⟩
        permLattice_e6HighestRoot ⟨hs, hpos⟩ hsρ (Ne.symm hsr)
        (fun x y => (commute_pinnedX_e6HighestRoot K hs hpos y x).symm) hu hγu')
  ·
    exfalso
    have hrI : e6HighestRoot ∈ inversionSet w := ⟨hr, hrpos, IsRoot.smul hr w, hneg⟩
    have htI : pinnedX TwistTag.E6.tag K e6HighestRoot c ∈
        rootSpan TwistTag.E6.tag K (inversionSet w) :=
      Subgroup.mem_iSup_of_mem e6HighestRoot (Subgroup.mem_iSup_of_mem hrI
        (Subgroup.subset_closure ⟨c, rfl⟩))
    have hm1 : (pinnedX TwistTag.E6.tag K e6HighestRoot c *
        twistHom TwistTag.E6 K (RingHom.id K) b, twistHom TwistTag.E6 K (RingHom.id K) v) ∈
        (borelGroup TwistTag.E6.tag K : Set (ModGL TwistTag.E6.tag K)) ×ˢ
          (rootSpan TwistTag.E6.tag K (inversionSet w) : Set (ModGL TwistTag.E6.tag K)) :=
      Set.mk_mem_prod (mul_mem htB hγb) hγv
    have hm2 : (b, v * pinnedX TwistTag.E6.tag K e6HighestRoot c) ∈
        (borelGroup TwistTag.E6.tag K : Set (ModGL TwistTag.E6.tag K)) ×ˢ
          (rootSpan TwistTag.E6.tag K (inversionSet w) : Set (ModGL TwistTag.E6.tag K)) :=
      Set.mk_mem_prod hb (mul_mem hv htI)
    have he : pinnedX TwistTag.E6.tag K e6HighestRoot c * twistHom TwistTag.E6 K (RingHom.id K) b *
        canonicalRep (coxeterSystem TwistTag.E6.tag) K w *
          twistHom TwistTag.E6 K (RingHom.id K) v =
        b * canonicalRep (coxeterSystem TwistTag.E6.tag) K w *
          (v * pinnedX TwistTag.E6.tag K e6HighestRoot c) := by
      rw [← mul_assoc, heq]
    have h := hinj hm1 hm2 he
    have hv' : twistHom TwistTag.E6 K (RingHom.id K) v =
        v * pinnedX TwistTag.E6.tag K e6HighestRoot c := congrArg Prod.snd h
    exact hc (eq_zero_of_twistHom_eq_mul h2 hIpos (fun α hα => permLattice_mem_inversionSet hδ hα)
      (inversionSet_closed w) hrI permLattice_e6HighestRoot hv hv')

theorem twistHom_id_eq (t : TwistTag) (K : Type) [Field K] (g : ModGL t.tag K) :
    twistHom t K (RingHom.id K) g = diagramMap t K * g * (diagramMap t K)⁻¹ := by
  rw [twistHom_apply]
  congr 2
  exact Units.ext (entrywise_id _)

theorem even_E6_highest_root_graph_fixed_centralizer_intersection
    (K : Type) [Field K]
    (hK : ringChar K = 2) {c : K} (hc : c ≠ 0) :
    pinnedX TwistTag.E6.tag K e6HighestRoot c ∈ adjointGroup TwistTag.E6.tag K ∧
    diagramMap TwistTag.E6 K * pinnedX TwistTag.E6.tag K e6HighestRoot c *
      (diagramMap TwistTag.E6 K)⁻¹ = pinnedX TwistTag.E6.tag K e6HighestRoot c ∧
    pinnedX TwistTag.E6.tag K e6HighestRoot c ^ 2 = 1 ∧
    {g ∈ (adjointGroup TwistTag.E6.tag K : Set (ModGL TwistTag.E6.tag K)) |
      pinnedX TwistTag.E6.tag K e6HighestRoot c *
        (diagramMap TwistTag.E6 K * g * (diagramMap TwistTag.E6 K)⁻¹) *
          (pinnedX TwistTag.E6.tag K e6HighestRoot c)⁻¹ = g} =
      {g ∈ (adjointGroup TwistTag.E6.tag K : Set (ModGL TwistTag.E6.tag K)) |
        diagramMap TwistTag.E6 K * g * (diagramMap TwistTag.E6 K)⁻¹ = g} ∩
      {g ∈ (adjointGroup TwistTag.E6.tag K : Set (ModGL TwistTag.E6.tag K)) |
        pinnedX TwistTag.E6.tag K e6HighestRoot c * g *
          (pinnedX TwistTag.E6.tag K e6HighestRoot c)⁻¹ = g} := by
  have : CharP K 2 := ringChar.of_eq hK
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have hB := ((triangular_borel_structure.{0, 0} TwistTag.E6.tag K).2.2.2.2.2.2.2.2.2.2.2 K).1
  refine ⟨hB (Subgroup.mem_sup_right (pinnedX_e6HighestRoot_mem_posUnipotent c)), ?_, ?_, ?_⟩
  · rw [← twistHom_id_eq, twistHom_id_pinnedX h2 isRoot_e6HighestRoot,
      permLattice_e6HighestRoot]
  · rw [pow_two, ← pinnedX_add, ← two_mul, h2, zero_mul, pinnedX_zero]
  · ext g
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hg, hζ⟩
      rw [← twistHom_id_eq] at hζ
      have hγ := twistHom_eq_of_conj_twistHom_eq h2 hc hg hζ
      rw [hγ] at hζ
      rw [← twistHom_id_eq]
      exact ⟨⟨hg, hγ⟩, hg, hζ⟩
    · rintro ⟨⟨hg, hγ⟩, -, ht⟩
      rw [hγ]
      exact ⟨hg, ht⟩

end CFSG.LieType.Chevalley
