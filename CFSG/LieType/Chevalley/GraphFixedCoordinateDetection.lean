module

public import CFSG.LieType.Chevalley.GraphFixedRootNormal
public import CFSG.LieType.Chevalley.FoldedRootOrbits
public import CFSG.LieType.Chevalley.PositiveRootCollection

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley

theorem list_prod_map_filter_of_eq_one {G ι : Type*} [Monoid G] (l : List ι) (p : ι → Bool)
    (g : ι → G) (h : ∀ x ∈ l, p x = false → g x = 1) :
    ((l.filter p).map g).prod = (l.map g).prod := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have ih' := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    by_cases hx : p x
    · rw [List.filter_cons_of_pos hx, List.map_cons, List.prod_cons, List.map_cons,
        List.prod_cons, ih']
    · rw [List.filter_cons_of_neg hx, List.map_cons, List.prod_cons,
        h x List.mem_cons_self (by simpa using hx), one_mul, ih']

theorem list_prod_map_eq_of_mem_iff {G ι : Type*} [Monoid G] {l₁ l₂ : List ι} (h₁ : l₁.Nodup)
    (h₂ : l₂.Nodup) (hmem : ∀ x, x ∈ l₁ ↔ x ∈ l₂) (g : ι → G)
    (hcomm : ∀ x ∈ l₁, ∀ y ∈ l₁, x ≠ y → Commute (g x) (g y)) :
    (l₁.map g).prod = (l₂.map g).prod :=
  (((List.perm_ext_iff_of_nodup h₁ h₂).2 hmem).map g).prod_eq'
    (List.pairwise_map.2 (h₁.pairwise_of_forall_ne hcomm))

section Transport

variable {τ : Tag}

theorem exists_prod_weylElt_mul_pinnedX_mul_inv
    (R : Type) [CommRing R] (ω : List (Fin τ.rank))
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    ∃ ε : R, ε * ε = 1 ∧ ∀ c : R,
      (ω.map fun i => weylElt τ R i 1).prod * pinnedX τ R α c *
          ((ω.map fun i => weylElt τ R i 1).prod)⁻¹ =
        pinnedX τ R ((coxeterSystem τ).wordProd ω • α) (ε * c) := by
  induction ω with
  | nil => exact ⟨1, one_mul 1, fun c => by simp⟩
  | cons i ω ih =>
    obtain ⟨ε, hε, h⟩ := ih
    obtain ⟨ε', hε', h'⟩ :=
      weylElt_mul_pinnedX_mul_inv R i (IsRoot.smul hα ((coxeterSystem τ).wordProd ω))
    refine ⟨ε' * ε, by linear_combination (ε' * ε') * hε + hε', fun c => ?_⟩
    have e : ∀ a b x : (Module.End R (RootModule τ R))ˣ,
        a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := fun a b x => by group
    rw [List.map_cons, List.prod_cons, e, h, h', (coxeterSystem τ).wordProd_cons, mul_smul,
      simple_smul, mul_assoc]

theorem exists_canonicalRep_mul_pinnedX_mul_inv
    (R : Type) [CommRing R] (w : WeylGroup τ)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    ∃ ε : R, ε * ε = 1 ∧ ∀ c : R,
      canonicalRep (coxeterSystem τ) R w * pinnedX τ R α c *
          (canonicalRep (coxeterSystem τ) R w)⁻¹ = pinnedX τ R (w • α) (ε * c) := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem τ).exists_isReduced w
  rw [canonicalRep_wordProd hω]
  exact exists_prod_weylElt_mul_pinnedX_mul_inv R ω hα

end Transport

variable {t : TwistTag} {K : Type} [Field K]

theorem exists_coordinates_conj_orbitXProd
    (w : WeylGroup t.tag) (a : Fin t.foldedTag.rank)
    (hpos : ∀ i ∈ t.orbit a, 0 < height (w • (Pi.single i 1 : Fin t.tag.rank → ℤ)))
    {m : ℕ} (β : Fin m → Fin t.tag.rank → ℤ) (hβ : Function.Injective β)
    (hrange : Set.range β = {α | IsRoot t.tag α ∧ 0 < height α}) :
    ∃ c : Fin m → K, canonicalRep (coxeterSystem t.tag) K w * orbitXProd t a (fun _ => 1) *
        (canonicalRep (coxeterSystem t.tag) K w)⁻¹ =
        (List.ofFn fun i => pinnedX t.tag K (β i) (c i)).prod ∧
      ∀ i, (c i ≠ 0 ↔
        β i ∈ (t.orbit a).image fun j => w • (Pi.single j 1 : Fin t.tag.rank → ℤ)) := by
  classical
  set O := (t.orbit a).image fun j => w • (Pi.single j 1 : Fin t.tag.rank → ℤ) with hO
  set n := canonicalRep (coxeterSystem t.tag) K w
  have hconj := fun i : Fin t.tag.rank =>
    exists_canonicalRep_mul_pinnedX_mul_inv K w (isRoot_single t.tag i)
  choose ε hε hconj using hconj
  have hε0 : ∀ j, ε j ≠ 0 := fun j h => by
    have := hε j
    rw [h, zero_mul] at this
    exact zero_ne_one this
  have hinj := t.injective_smul_single w
  set F : (Fin t.tag.rank → ℤ) → K := Function.extend
    (fun j => w • (Pi.single j 1 : Fin t.tag.rank → ℤ))
    (fun j => if j ∈ t.orbit a then ε j else 0) 0 with hFdef
  have hF : ∀ j, F (w • Pi.single j 1) = if j ∈ t.orbit a then ε j else 0 := fun j =>
    hinj.extend_apply _ _ j
  have hFne : ∀ γ, F γ ≠ 0 ↔ γ ∈ O := by
    intro γ
    refine ⟨fun h => ?_, fun h => ?_⟩
    · by_contra hγ
      refine h ?_
      by_cases hr : ∃ j, w • (Pi.single j 1 : Fin t.tag.rank → ℤ) = γ
      · obtain ⟨j, rfl⟩ := hr
        rw [hF]
        exact ite_eq_right_iff.2 fun hj => absurd (Finset.mem_image.2 ⟨j, hj, rfl⟩) hγ
      · exact Function.extend_apply' _ _ _ hr
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 h
      rw [hF, ite_eq_left_iff.2 fun h => absurd hj h]
      exact hε0 j
  refine ⟨fun i => F (β i), ?_, fun i => hFne (β i)⟩
  have h1 : n * orbitXProd t a (fun _ => 1) * n⁻¹ =
      (((t.orbitWord a).map fun j => w • (Pi.single j 1 : Fin t.tag.rank → ℤ)).map
        fun γ => pinnedX t.tag K γ (F γ)).prod := by
    have e : n * orbitXProd t a (fun _ => 1) * n⁻¹ = MulAut.conj n (orbitXProd t a fun _ => 1) :=
      rfl
    rw [e, orbitXProd, map_list_prod, List.map_map, List.map_map]
    congr 1
    refine List.map_congr_left fun j hj => ?_
    simp only [Function.comp_apply, MulAut.conj_apply]
    rw [← pinnedX_single, hconj, mul_one, hF, ite_eq_left_iff.2 fun h =>
      absurd ((t.mem_orbitWord).1 hj) h]
  have h2 : (List.ofFn fun i => pinnedX t.tag K (β i) (F (β i))).prod =
      (((List.ofFn β).filter fun γ => decide (γ ∈ O)).map
        fun γ => pinnedX t.tag K γ (F γ)).prod := by
    rw [list_prod_map_filter_of_eq_one, List.map_ofFn]
    · rfl
    · intro γ _ hγ
      have hγO : γ ∉ O := by simpa using hγ
      rw [show F γ = 0 by by_contra h; exact hγO ((hFne γ).1 h), pinnedX_zero]
  have hOpos : ∀ γ ∈ O, γ ∈ Set.range β := fun γ hγ => by
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hγ
    rw [hrange]
    exact ⟨IsRoot.smul (isRoot_single _ j) w, hpos j hj⟩
  rw [h1, h2]
  refine list_prod_map_eq_of_mem_iff ((t.nodup_orbitWord a).map hinj)
    ((List.nodup_ofFn.2 hβ).filter _) (fun γ => ?_) _ ?_
  · rw [List.mem_filter, List.mem_map, decide_eq_true_eq, List.mem_ofFn' β]
    constructor
    · rintro ⟨j, hj, rfl⟩
      have hγO : w • (Pi.single j 1 : Fin t.tag.rank → ℤ) ∈ O :=
        Finset.mem_image.2 ⟨j, (t.mem_orbitWord).1 hj, rfl⟩
      exact ⟨hOpos _ hγO, hγO⟩
    · rintro ⟨-, hγ⟩
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hγ
      exact ⟨j, (t.mem_orbitWord).2 hj, rfl⟩
  · intro γ hγ γ' hγ' hne
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hγ
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hγ'
    have hij : i ≠ j := fun h => hne (by rw [h])
    exact commute_pinnedX_of_rootForm_eq_zero K (IsRoot.smul (isRoot_single _ i) w)
      (IsRoot.smul (isRoot_single _ j) w)
      (t.rootForm_smul_single_eq_zero w ((t.mem_orbitWord).1 hi) ((t.mem_orbitWord).1 hj) hij) _ _

theorem exists_orbit_coordinate_element
    (σ : K →+* K) {O : Finset (Fin t.tag.rank → ℤ)}
    (hO : O ∈ t.diagramRootOrbits) (hpos : ∀ α ∈ O, 0 < height α) :
    ∃ z ∈ rootSpan t.tag K (O : Set (Fin t.tag.rank → ℤ)) ⊓ twistedFixedGroup t K σ,
      ∀ {m : ℕ} (β : Fin m → Fin t.tag.rank → ℤ), Function.Injective β →
        Set.range β = {α | IsRoot t.tag α ∧ 0 < height α} →
        (∃ c : Fin m → K, z = (List.ofFn fun i => pinnedX t.tag K (β i) (c i)).prod) ∧
        ∀ c : Fin m → K, z = (List.ofFn fun i => pinnedX t.tag K (β i) (c i)).prod →
          ∀ i, (c i ≠ 0 ↔ β i ∈ O) := by
  obtain ⟨α, hα, rfl⟩ := hO
  obtain ⟨w, hw, a, h⟩ := t.exists_diagramOrbit_eq hα
  rw [h] at hpos ⊢
  set n := canonicalRep (coxeterSystem t.tag) K w
  refine ⟨n * orbitXProd t a (fun _ => 1) * n⁻¹, Subgroup.mem_inf.2 ⟨?_, ?_⟩,
    fun β hβ hrange => ?_⟩
  · have hmem := Subgroup.mem_map_of_mem (MulAut.conj n).toMonoidHom
      (orbitXProd_mem_rootSpan t a (fun _ => (1 : K)))
    rw [(canonical_weyl_root_transport t.tag K).1 w
      ((fun i => (Pi.single i 1 : Fin t.tag.rank → ℤ)) '' ↑(t.orbit a)) fun γ hγ => by
        obtain ⟨j, -, rfl⟩ := hγ
        exact isRoot_single _ j, Set.image_image] at hmem
    rw [Finset.coe_image]
    exact hmem
  · have hn : n ∈ twistedFixedGroup t K σ :=
      canonicalRep_mem_twistedFixedGroup t K σ ((mem_relWeylTwist t).1 hw)
    exact mul_mem (mul_mem hn (graphFixedPosUnipotent_le t K σ
      (orbitXProd_one_mem_graphFixedPosUnipotent a))) (inv_mem hn)
  · obtain ⟨c, hc, hsupp⟩ := exists_coordinates_conj_orbitXProd (K := K) w a
      (fun i hi => hpos _ (Finset.mem_image_of_mem _ hi)) β hβ hrange
    refine ⟨⟨c, hc⟩, fun c' hc' => ?_⟩
    have hβpos : ∀ i, IsRoot t.tag (β i) ∧ 0 < height (β i) := fun i => by
      have hi : β i ∈ {α | IsRoot t.tag α ∧ 0 < height α} := hrange ▸ Set.mem_range_self i
      exact hi
    have hcc : c = c' :=
      (positive_root_product_injectivity t.tag K β hβ hβpos).2 (hc.symm.trans hc')
    exact hcc ▸ hsupp

theorem diagramOrbit_subset {S : Set (Fin t.tag.rank → ℤ)}
    (hS : ∀ α ∈ S, permLattice t.perm α ∈ S) {α : Fin t.tag.rank → ℤ} (hα : α ∈ S) :
    (t.diagramOrbit α : Set (Fin t.tag.rank → ℤ)) ⊆ S := by
  have hk : ∀ k : ℕ, permLattice (t.perm ^ k) α ∈ S := fun k => by
    induction k with
    | zero => exact hα
    | succ k ih =>
      change permLattice (t.perm * t.perm ^ k) α ∈ S
      exact hS _ ih
  intro γ hγ
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hγ
  exact hk k

theorem subset_of_rootSpan_inf_le
    (σ : K →+* K) {S T : Set (Fin t.tag.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot t.tag α ∧ 0 < height α) (hSρ : ∀ α ∈ S, permLattice t.perm α ∈ S)
    (hT : ∀ α ∈ T, IsRoot t.tag α ∧ 0 < height α)
    (hTc : ∀ α ∈ T, ∀ β ∈ T, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot t.tag (a • α + b • β) →
      a • α + b • β ∈ T)
    (h : rootSpan t.tag K S ⊓ twistedFixedGroup t K σ ≤
      rootSpan t.tag K T ⊓ twistedFixedGroup t K σ) :
    S ⊆ T := by
  classical
  intro α hα
  obtain ⟨hαr, hαp⟩ := hS α hα
  have hOpos : ∀ γ ∈ t.diagramOrbit α, 0 < height γ := fun γ hγ => by
    rw [t.height_of_mem_diagramOrbit hγ]
    exact hαp
  obtain ⟨z, hz, hcoord⟩ := exists_orbit_coordinate_element (K := K) σ ⟨α, hαr, rfl⟩ hOpos
  obtain ⟨hzO, hzΓ⟩ := Subgroup.mem_inf.1 hz
  have hzT : z ∈ rootSpan t.tag K T :=
    (Subgroup.mem_inf.1 (h (Subgroup.mem_inf.2 ⟨rootSpan_mono (diagramOrbit_subset hSρ hα) hzO,
      hzΓ⟩))).1
  obtain ⟨k, γ₁, hγ₁⟩ := ((finite_setOf_isRoot t.tag).subset fun γ hγ => (hT γ hγ).1).fin_embedding
  obtain ⟨l, γ₂, hγ₂⟩ := ((finite_setOf_isRoot t.tag).subset
    fun γ (hγ : γ ∈ {β | IsRoot t.tag β ∧ 0 < height β} \ T) => hγ.1.1).fin_embedding
  have hβinj : Function.Injective (Fin.append γ₁ γ₂) := by
    refine Fin.append_injective_iff.2 ⟨γ₁.injective, γ₂.injective, fun i j hij => ?_⟩
    have h₁ : γ₁ i ∈ T := hγ₁ ▸ Set.mem_range_self i
    have h₂ : γ₂ j ∈ {β | IsRoot t.tag β ∧ 0 < height β} \ T := hγ₂ ▸ Set.mem_range_self j
    exact h₂.2 (hij ▸ h₁)
  have hβrange : Set.range (Fin.append γ₁ γ₂) = {β | IsRoot t.tag β ∧ 0 < height β} := by
    ext γ
    constructor
    · rintro ⟨i, rfl⟩
      induction i using Fin.addCases with
      | left j =>
        rw [Fin.append_left]
        exact hT _ (hγ₁ ▸ Set.mem_range_self j)
      | right j =>
        rw [Fin.append_right]
        exact (hγ₂ ▸ Set.mem_range_self j : γ₂ j ∈ {β | IsRoot t.tag β ∧ 0 < height β} \ T).1
    · intro hγ
      by_cases hγT : γ ∈ T
      · obtain ⟨j, rfl⟩ : γ ∈ Set.range γ₁ := hγ₁ ▸ hγT
        exact ⟨Fin.castAdd l j, Fin.append_left _ _ _⟩
      · obtain ⟨j, rfl⟩ : γ ∈ Set.range γ₂ := hγ₂ ▸ ⟨hγ, hγT⟩
        exact ⟨Fin.natAdd k j, Fin.append_right _ _ _⟩
  obtain ⟨d, -, hd⟩ := (bijOn_prod_pinnedX K hT hTc γ₁ γ₁.injective hγ₁).surjOn hzT
  have hz' : z = (List.ofFn fun i =>
      pinnedX t.tag K (Fin.append γ₁ γ₂ i) (Fin.append d (0 : Fin l → K) i)).prod := by
    have e : (fun i => pinnedX t.tag K (Fin.append γ₁ γ₂ i) (Fin.append d (0 : Fin l → K) i)) =
        Fin.append (fun i => pinnedX t.tag K (γ₁ i) (d i)) fun _ => 1 := by
      funext i
      induction i using Fin.addCases with
      | left j => rw [Fin.append_left, Fin.append_left, Fin.append_left]
      | right j => rw [Fin.append_right, Fin.append_right, Fin.append_right, Pi.zero_apply,
          pinnedX_zero]
    rw [e, List.ofFn_fin_append, List.prod_append, List.ofFn_const, List.prod_replicate, one_pow,
      mul_one]
    exact hd.symm
  by_contra hαT
  obtain ⟨j, hj⟩ : α ∈ Set.range γ₂ := hγ₂ ▸ ⟨⟨hαr, hαp⟩, hαT⟩
  have hne := ((hcoord _ hβinj hβrange).2 _ hz' (Fin.natAdd k j)).2
    (by rw [Fin.append_right, hj]; exact t.self_mem_diagramOrbit α)
  exact hne (by rw [Fin.append_right, Pi.zero_apply])

theorem diagram_fixed_positive_root_coordinate_detection
    (t : TwistTag) (K : Type) [Field K]
    (σ : K →+* K) :
    (∀ O ∈ t.diagramRootOrbits, (∀ α ∈ O, 0 < height α) →
      ∃ z ∈ rootSpan t.tag K (O : Set (Fin t.tag.rank → ℤ)) ⊓ twistedFixedGroup t K σ,
        ∀ {m : ℕ} (β : Fin m → Fin t.tag.rank → ℤ), Function.Injective β →
          Set.range β = {α | IsRoot t.tag α ∧ 0 < height α} →
          (∃ c : Fin m → K, z = (List.ofFn fun i => pinnedX t.tag K (β i) (c i)).prod) ∧
          ∀ c : Fin m → K, z = (List.ofFn fun i => pinnedX t.tag K (β i) (c i)).prod →
            ∀ i, (c i ≠ 0 ↔ β i ∈ O)) ∧
    ∀ S T : Set (Fin t.tag.rank → ℤ),
      (∀ α ∈ S, IsRoot t.tag α ∧ 0 < height α) → (∀ α ∈ S, permLattice t.perm α ∈ S) →
      (∀ α ∈ S, ∀ β ∈ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot t.tag (a • α + b • β) →
        a • α + b • β ∈ S) →
      (∀ α ∈ T, IsRoot t.tag α ∧ 0 < height α) → (∀ α ∈ T, permLattice t.perm α ∈ T) →
      (∀ α ∈ T, ∀ β ∈ T, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot t.tag (a • α + b • β) →
        a • α + b • β ∈ T) →
      (rootSpan t.tag K S ⊓ twistedFixedGroup t K σ ≤
          rootSpan t.tag K T ⊓ twistedFixedGroup t K σ ↔ S ⊆ T) ∧
      (rootSpan t.tag K S ⊓ twistedFixedGroup t K σ =
          rootSpan t.tag K T ⊓ twistedFixedGroup t K σ ↔ S = T) := by
  refine ⟨fun O hO hpos => exists_orbit_coordinate_element σ hO hpos,
    fun S T hS hSρ hSc hT hTρ hTc => ?_⟩
  have key : rootSpan t.tag K S ⊓ twistedFixedGroup t K σ ≤
      rootSpan t.tag K T ⊓ twistedFixedGroup t K σ ↔ S ⊆ T :=
    ⟨subset_of_rootSpan_inf_le σ hS hSρ hT hTc, fun h => inf_le_inf_right _ (rootSpan_mono h)⟩
  refine ⟨key, ⟨fun h => Set.Subset.antisymm (key.1 h.le)
    (subset_of_rootSpan_inf_le σ hT hTρ hS hSc h.ge), fun h => by rw [h]⟩⟩

end CFSG.LieType.Chevalley
