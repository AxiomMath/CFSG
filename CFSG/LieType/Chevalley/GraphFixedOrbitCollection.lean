module

public import CFSG.LieType.Chevalley.GraphFixedCoordinateDetection
public import CFSG.LieType.Chevalley.GraphFixedRootMonomialQuotient

public noncomputable section

namespace CFSG.Blueprint.Chevalley.TwistTag

open CFSG.LieType.Chevalley Matrix

variable (t : TwistTag)

theorem diagramOrbit_eq_of_mem
    {α β : Fin t.tag.rank → ℤ} (h : β ∈ t.diagramOrbit α) :
    t.diagramOrbit β = t.diagramOrbit α := by
  obtain ⟨g, hg, rfl⟩ := (t.mem_diagramOrbit).1 h
  ext γ
  rw [t.mem_diagramOrbit, t.mem_diagramOrbit]
  constructor
  · rintro ⟨g', hg', rfl⟩
    exact ⟨g' * g, mul_mem hg' hg, rfl⟩
  · rintro ⟨g', hg', rfl⟩
    exact ⟨g' * g⁻¹, mul_mem hg' (inv_mem hg),
      congrArg (permLattice g') (permLattice_symm_permLattice g α)⟩

theorem disjoint_diagramOrbit
    {α β : Fin t.tag.rank → ℤ}
    (h : t.diagramOrbit α ≠ t.diagramOrbit β) : Disjoint (t.diagramOrbit α) (t.diagramOrbit β) :=
  Finset.disjoint_left.2 fun _ hα hβ =>
    h ((t.diagramOrbit_eq_of_mem hα).symm.trans (t.diagramOrbit_eq_of_mem hβ))

theorem permLattice_mem_diagramOrbit {α β : Fin t.tag.rank → ℤ} (h : β ∈ t.diagramOrbit α) :
    permLattice t.perm β ∈ t.diagramOrbit α := by
  obtain ⟨g, hg, rfl⟩ := (t.mem_diagramOrbit).1 h
  exact (t.mem_diagramOrbit).2 ⟨t.perm * g, mul_mem (Subgroup.mem_zpowers _) hg, rfl⟩

theorem not_isRoot_nsmul_add_nsmul_of_mem_diagramOrbit
    {α β γ : Fin t.tag.rank → ℤ}
    (hα : IsRoot t.tag α) (hβ : β ∈ t.diagramOrbit α) (hγ : γ ∈ t.diagramOrbit α) {a b : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) : ¬IsRoot t.tag (a • β + b • γ) := by
  intro hr
  by_cases hβγ : β = γ
  · subst hβγ
    rw [← add_smul, ← natCast_zsmul] at hr
    rcases hr.eq_one_or_neg_one_of_eq_smul rfl with h | h <;> omega
  · have hββ := rootForm_self t.isSimplyLaced (t.isRoot_of_mem_diagramOrbit hα hβ)
    have hγγ := rootForm_self t.isSimplyLaced (t.isRoot_of_mem_diagramOrbit hα hγ)
    have h0 := (diagram_root_orbit_reduction t).2.2.1 α hα β hβ γ hγ hβγ
    have h0' := (diagram_root_orbit_reduction t).2.2.1 α hα γ hγ β hβ (Ne.symm hβγ)
    have hrr := rootForm_self t.isSimplyLaced hr
    rw [← Nat.cast_smul_eq_nsmul ℤ a β, ← Nat.cast_smul_eq_nsmul ℤ b γ] at hrr
    simp only [add_dotProduct, dotProduct_add, mulVec_add, mulVec_smul, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, hββ, hγγ, h0, h0'] at hrr
    have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
    have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
    nlinarith

end CFSG.Blueprint.Chevalley.TwistTag

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley

section Collection

variable {τ : Tag}

theorem permLattice_mul (g h : Equiv.Perm (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    permLattice (g * h) v = permLattice g (permLattice h v) :=
  rfl

theorem rootSpan_le_adjointGroup
    (K : Type) [Field K] (S : Set (Fin τ.rank → ℤ)) :
    rootSpan τ K S ≤ adjointGroup τ K :=
  iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α

theorem exists_list_prod_pinnedX_eq
    (R : Type) [CommRing R] {S : Set (Fin τ.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot τ α ∧ 0 < height α)
    (hclosed : ∀ α ∈ S, ∀ β ∈ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • α + b • β) →
      a • α + b • β ∈ S)
    {l : List (Fin τ.rank → ℤ)} (hl : l.Nodup) (hmem : ∀ α, α ∈ l ↔ α ∈ S)
    {g : (Module.End R (RootModule τ R))ˣ} (hg : g ∈ rootSpan τ R S) :
    ∃ c : (Fin τ.rank → ℤ) → R, (l.map fun α => pinnedX τ R α (c α)).prod = g := by
  have hget : Function.Injective l.get := List.nodup_iff_injective_get.1 hl
  have hrange : Set.range l.get = S := by
    ext α
    rw [Set.mem_range, ← hmem]
    exact List.mem_iff_get.symm
  obtain ⟨c, -, hc⟩ := (bijOn_prod_pinnedX R hS hclosed l.get hget hrange).surjOn hg
  refine ⟨Function.extend l.get c 0, ?_⟩
  rw [← hc]
  have e : ∀ f : (Fin τ.rank → ℤ) → (Module.End R (RootModule τ R))ˣ,
      l.map f = List.ofFn (f ∘ l.get) := fun f => by rw [← List.map_ofFn, List.ofFn_get]
  rw [e]
  congr 2
  funext i
  simp only [Function.comp_apply, hget.extend_apply]

theorem prod_map_flatten_ofFn {G ι : Type*} [Monoid G] {k : ℕ} (L : Fin k → List ι)
    (f : ι → G) :
    (((List.ofFn L).flatten).map f).prod = (List.ofFn fun j => ((L j).map f).prod).prod := by
  simp [List.map_flatten, List.prod_flatten, List.map_ofFn, Function.comp_def]

variable (R : Type) [CommRing R] {k : ℕ} (O : Fin k → Finset (Fin τ.rank → ℤ))

theorem nodup_flatten_toList (hdisj : ∀ i j, i ≠ j → Disjoint (O i) (O j)) :
    ((List.ofFn fun j => (O j).toList).flatten).Nodup := by
  refine List.nodup_flatten.2 ⟨fun l hl => ?_, List.pairwise_ofFn.2 fun i j hij => ?_⟩
  · obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hl
    exact Finset.nodup_toList _
  · intro α hi hj
    exact Finset.disjoint_left.1 (hdisj i j hij.ne) (Finset.mem_toList.1 hi)
      (Finset.mem_toList.1 hj)

theorem mem_flatten_toList {α : Fin τ.rank → ℤ} :
    α ∈ (List.ofFn fun j => (O j).toList).flatten ↔ ∃ j, α ∈ O j := by
  simp [List.mem_flatten, List.mem_ofFn]

variable {R O}
variable (hdisj : ∀ i j, i ≠ j → Disjoint (O i) (O j))
  (hpos : ∀ j, ∀ α ∈ O j, IsRoot τ α ∧ 0 < height α)
  (hcl : ∀ j, ∀ α ∈ O j, ∀ β ∈ O j, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → ¬IsRoot τ (a • α + b • β))
include hdisj hpos hcl

theorem exists_common_parameters
    (u : Fin k → (Module.End R (RootModule τ R))ˣ)
    (hu : ∀ j, u j ∈ rootSpan τ R (O j : Set (Fin τ.rank → ℤ))) :
    ∃ c : (Fin τ.rank → ℤ) → R,
      ∀ j, ((O j).toList.map fun α => pinnedX τ R α (c α)).prod = u j := by
  classical
  have hc := fun j => exists_list_prod_pinnedX_eq R (S := (O j : Set (Fin τ.rank → ℤ)))
    (fun α hα => hpos j α hα) (fun α hα β hβ a b ha hb hr => absurd hr (hcl j α hα β hβ a b ha hb))
    (Finset.nodup_toList _) (fun α => Finset.mem_toList) (hu j)
  choose c hc using hc
  refine ⟨fun α => ∑ j, if α ∈ O j then c j α else 0, fun j => ?_⟩
  rw [← hc j]
  refine congrArg List.prod (List.map_congr_left fun α hα => ?_)
  have hα' := Finset.mem_toList.1 hα
  dsimp only
  rw [Finset.sum_eq_single j (fun i _ hij => ite_eq_right_iff.2 fun hi =>
    absurd hα' (Finset.disjoint_left.1 (hdisj i j hij) hi)) (by simp), ite_eq_left_iff.2
    fun h => absurd hα' h]

theorem eq_of_prod_rootSpan_eq
    {u u' : Fin k → (Module.End R (RootModule τ R))ˣ}
    (hu : ∀ j, u j ∈ rootSpan τ R (O j : Set (Fin τ.rank → ℤ)))
    (hu' : ∀ j, u' j ∈ rootSpan τ R (O j : Set (Fin τ.rank → ℤ)))
    (h : (List.ofFn u).prod = (List.ofFn u').prod) : u = u' := by
  obtain ⟨c, hc⟩ := exists_common_parameters hdisj hpos hcl u hu
  obtain ⟨c', hc'⟩ := exists_common_parameters hdisj hpos hcl u' hu'
  have hL : ∀ α ∈ (List.ofFn fun j => (O j).toList).flatten, IsRoot τ α ∧ 0 < height α :=
    fun α hα => by
      obtain ⟨j, hj⟩ := (mem_flatten_toList O).1 hα
      exact hpos j α hj
  have heq := pinnedX_list_prod_injective _ (nodup_flatten_toList O hdisj) hL c c' (by
    rw [prod_map_flatten_ofFn, prod_map_flatten_ofFn]
    simp only [hc, hc']
    exact h)
  funext j
  rw [← hc j, ← hc' j]
  exact congrArg List.prod (List.map_congr_left fun α hα => by
    rw [heq α ((mem_flatten_toList O).2 ⟨j, Finset.mem_toList.1 hα⟩)])

omit hpos hcl in
theorem exists_prod_rootSpan_eq
    {S : Set (Fin τ.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot τ α ∧ 0 < height α)
    (hclosed : ∀ α ∈ S, ∀ β ∈ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • α + b • β) →
      a • α + b • β ∈ S)
    (hSO : ∀ α, α ∈ S ↔ ∃ j, α ∈ O j) {g : (Module.End R (RootModule τ R))ˣ}
    (hg : g ∈ rootSpan τ R S) :
    ∃ u : Fin k → (Module.End R (RootModule τ R))ˣ,
      (∀ j, u j ∈ rootSpan τ R (O j : Set (Fin τ.rank → ℤ))) ∧ (List.ofFn u).prod = g := by
  obtain ⟨c, hc⟩ := exists_list_prod_pinnedX_eq R hS hclosed (nodup_flatten_toList O hdisj)
    (fun α => (mem_flatten_toList O).trans (hSO α).symm) hg
  refine ⟨fun j => ((O j).toList.map fun α => pinnedX τ R α (c α)).prod, fun j => ?_, ?_⟩
  · refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨α, hα, rfl⟩ := List.mem_map.1 hx
    exact Subgroup.mem_iSup_of_mem α (Subgroup.mem_iSup_of_mem (Finset.mem_toList.1 hα)
      (Subgroup.subset_closure ⟨c α, rfl⟩))
  · rw [← hc, prod_map_flatten_ofFn]

end Collection

variable {t : TwistTag} {K : Type} [Field K]

theorem bijOn_prod_graphFixed
    {σ : K →+* K} (hσ : Function.Surjective σ)
    {S : Set (Fin t.tag.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot t.tag α ∧ 0 < height α)
    (hSρ : ∀ α ∈ S, permLattice t.perm α ∈ S)
    (hclosed : ∀ α ∈ S, ∀ β ∈ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot t.tag (a • α + b • β) →
      a • α + b • β ∈ S)
    {k : ℕ} (O : Fin k → Finset (Fin t.tag.rank → ℤ)) (hO : Function.Injective O)
    (hrange : Set.range O =
      {O' | O' ∈ t.diagramRootOrbits ∧ (O' : Set (Fin t.tag.rank → ℤ)) ⊆ S}) :
    Set.BijOn (fun u : (j : Fin k) → ↥(rootSpan t.tag K (O j : Set (Fin t.tag.rank → ℤ)) ⊓
        twistedFixedGroup t K σ) => (List.ofFn fun j => (u j : ModGL t.tag K)).prod)
      Set.univ (rootSpan t.tag K S ⊓ twistedFixedGroup t K σ) := by
  have hOj : ∀ j, O j ∈ t.diagramRootOrbits ∧ (O j : Set (Fin t.tag.rank → ℤ)) ⊆ S := fun j => by
    have h : O j ∈ Set.range O := Set.mem_range_self j
    rw [hrange] at h
    exact h
  have hdisj : ∀ i j, i ≠ j → Disjoint (O i) (O j) := fun i j hij => by
    obtain ⟨⟨α, -, hα⟩, -⟩ := hOj i
    obtain ⟨⟨β, -, hβ⟩, -⟩ := hOj j
    rw [← hα, ← hβ]
    exact t.disjoint_diagramOrbit (by rw [hα, hβ]; exact hO.ne hij)
  have hpos : ∀ j, ∀ α ∈ O j, IsRoot t.tag α ∧ 0 < height α := fun j α hα =>
    hS α ((hOj j).2 hα)
  have hcl : ∀ j, ∀ α ∈ O j, ∀ β ∈ O j, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      ¬IsRoot t.tag (a • α + b • β) := fun j α hα β hβ a b ha hb => by
    obtain ⟨⟨γ, hγ, hγO⟩, -⟩ := hOj j
    rw [← hγO] at hα hβ
    exact t.not_isRoot_nsmul_add_nsmul_of_mem_diagramOrbit hγ hα hβ ha hb
  have hSO : ∀ α, α ∈ S ↔ ∃ j, α ∈ O j := fun α => by
    refine ⟨fun hα => ?_, fun ⟨j, hj⟩ => (hOj j).2 hj⟩
    have h : t.diagramOrbit α ∈ Set.range O := by
      rw [hrange]
      exact ⟨⟨α, (hS α hα).1, rfl⟩, diagramOrbit_subset hSρ hα⟩
    obtain ⟨j, hj⟩ := h
    exact ⟨j, hj ▸ t.self_mem_diagramOrbit α⟩
  have hF : ∀ j, ∀ g ∈ rootSpan t.tag K (O j : Set (Fin t.tag.rank → ℤ)),
      twistHom t K σ g ∈ rootSpan t.tag K (O j : Set (Fin t.tag.rank → ℤ)) := fun j g hg => by
    have h := Subgroup.mem_map_of_mem (twistHom t K σ) hg
    rw [map_twistHom_rootSpan t K hσ fun α hα => (hpos j α hα).1] at h
    refine rootSpan_mono ?_ h
    rintro _ ⟨β, hβ, rfl⟩
    obtain ⟨⟨γ, -, hγ⟩, -⟩ := hOj j
    rw [← hγ] at hβ ⊢
    exact t.permLattice_mem_diagramOrbit hβ
  refine ⟨fun u _ => Subgroup.mem_inf.2 ⟨Subgroup.list_prod_mem _ fun x hx => ?_,
    Subgroup.list_prod_mem _ fun x hx => ?_⟩, fun u _ u' _ h => ?_, fun g hg => ?_⟩
  · obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
    exact rootSpan_mono (hOj j).2 (Subgroup.mem_inf.1 (u j).2).1
  · obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
    exact (Subgroup.mem_inf.1 (u j).2).2
  · have h' := eq_of_prod_rootSpan_eq hdisj hpos hcl (u := fun j => (u j : ModGL t.tag K))
      (u' := fun j => (u' j : ModGL t.tag K)) (fun j => (Subgroup.mem_inf.1 (u j).2).1)
      (fun j => (Subgroup.mem_inf.1 (u' j).2).1) h
    funext j
    exact Subtype.ext (congrFun h' j)
  · obtain ⟨hgS, hgΓ⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨v, hv, rfl⟩ := exists_prod_rootSpan_eq hdisj hS hclosed hSO hgS
    have hfix : twistHom t K σ (List.ofFn v).prod = (List.ofFn v).prod :=
      ((mem_twistedFixedGroup_iff_twistHom t K σ).1 hgΓ).2
    have hFv : (fun j => twistHom t K σ (v j)) = v := by
      refine eq_of_prod_rootSpan_eq hdisj hpos hcl (fun j => hF j _ (hv j)) hv ?_
      rw [← hfix, map_list_prod, List.map_ofFn]
      rfl
    have hvΓ : ∀ j, v j ∈ twistedFixedGroup t K σ := fun j =>
      (mem_twistedFixedGroup_iff_twistHom t K σ).2
        ⟨rootSpan_le_adjointGroup K _ (hv j), congrFun hFv j⟩
    exact ⟨fun j => ⟨v j, Subgroup.mem_inf.2 ⟨hv j, hvΓ j⟩⟩, Set.mem_univ _, rfl⟩

theorem image_smul_posRoots_of_reversesSigns
    {τ : Tag} {w₀ : WeylGroup τ} (h₀ : ReversesSigns w₀) :
    (fun α => w₀ • α) '' {α | IsRoot τ α ∧ 0 < height α} = {α | IsRoot τ α ∧ height α < 0} := by
  ext γ
  constructor
  · rintro ⟨β, ⟨hβ, hβp⟩, rfl⟩
    exact ⟨IsRoot.smul hβ w₀, h₀ β hβ hβp⟩
  · rintro ⟨hγ, hγn⟩
    refine ⟨w₀⁻¹ • γ, ⟨IsRoot.smul hγ w₀⁻¹, ?_⟩, smul_inv_smul w₀ γ⟩
    rcases IsRoot.height_pos_or_neg (IsRoot.smul hγ w₀⁻¹) with h | h
    · exact h
    · have h' := h₀ _ (IsRoot.neg (IsRoot.smul hγ w₀⁻¹)) (by rw [height_neg]; omega)
      rw [smul_neg, smul_inv_smul, height_neg] at h'
      omega

theorem exists_ordering_posOrbits (t : TwistTag) :
    ∃ (k : ℕ) (O : Fin k → Finset (Fin t.tag.rank → ℤ)), Function.Injective O ∧
      Set.range O = {O' | O' ∈ t.diagramRootOrbits ∧
        (O' : Set (Fin t.tag.rank → ℤ)) ⊆ {α | IsRoot t.tag α ∧ 0 < height α}} := by
  have hfin : {O' | O' ∈ t.diagramRootOrbits ∧
      (O' : Set (Fin t.tag.rank → ℤ)) ⊆ {α | IsRoot t.tag α ∧ 0 < height α}}.Finite :=
    ((finite_setOf_isRoot t.tag).image t.diagramOrbit).subset fun O' ⟨⟨α, hα, hαO⟩, _⟩ =>
      ⟨α, hα, hαO⟩
  obtain ⟨k, O, hO⟩ := hfin.fin_embedding
  exact ⟨k, O, O.injective, hO⟩

variable (σ : K →+* K)

theorem exists_eq_canonicalRep_conj_orbitX
    {O : Finset (Fin t.tag.rank → ℤ)}
    (hO : O ∈ t.diagramRootOrbits) {u : ModGL t.tag K}
    (hu : u ∈ rootSpan t.tag K (O : Set (Fin t.tag.rank → ℤ)) ⊓ twistedFixedGroup t K σ) :
    ∃ w ∈ relWeylTwist t, ∃ a, ∃ c : orbitField t K σ a,
      u = canonicalRep (coxeterSystem t.tag) K w * orbitX t K σ a c *
        (canonicalRep (coxeterSystem t.tag) K w)⁻¹ := by
  obtain ⟨α, hα, rfl⟩ := hO
  obtain ⟨w, hw, a, h⟩ := t.exists_diagramOrbit_eq hα
  rw [h, Finset.coe_image] at hu
  obtain ⟨c, hc⟩ := (orbitConjHom_bijective t σ a hw).2 ⟨u, hu⟩
  exact ⟨w, hw, a, c.toAdd, (congrArg Subtype.val hc).symm⟩

theorem graphFixedRootGroup_eq_closure
    (hσ : Function.Surjective σ) :
    graphFixedRootGroup t K σ = Subgroup.closure {g | ∃ w ∈ relWeylTwist t, ∃ a,
      ∃ c : orbitField t K σ a, g = canonicalRep (coxeterSystem t.tag) K w *
        orbitX t K σ a c * (canonicalRep (coxeterSystem t.tag) K w)⁻¹} := by
  set G := Subgroup.closure {g | ∃ w ∈ relWeylTwist t, ∃ a,
    ∃ c : orbitField t K σ a, g = canonicalRep (coxeterSystem t.tag) K w *
      orbitX t K σ a c * (canonicalRep (coxeterSystem t.tag) K w)⁻¹}
  have hOG : ∀ O ∈ t.diagramRootOrbits, ∀ u ∈ rootSpan t.tag K (O : Set (Fin t.tag.rank → ℤ)) ⊓
      twistedFixedGroup t K σ, u ∈ G := fun O hO u hu =>
    Subgroup.subset_closure (exists_eq_canonicalRep_conj_orbitX σ hO hu)
  obtain ⟨k, O, hO, hrange⟩ := exists_ordering_posOrbits t
  have hposS : ∀ α ∈ {α | IsRoot t.tag α ∧ 0 < height α}, IsRoot t.tag α ∧ 0 < height α :=
    fun α hα => hα
  have hposρ : ∀ α ∈ {α | IsRoot t.tag α ∧ 0 < height α},
      permLattice t.perm α ∈ {α | IsRoot t.tag α ∧ 0 < height α} := fun α hα => by
    rw [← image_permLattice_posRoots t]
    exact ⟨α, hα, rfl⟩
  have hposcl : ∀ α ∈ {α | IsRoot t.tag α ∧ 0 < height α},
      ∀ β ∈ {α | IsRoot t.tag α ∧ 0 < height α}, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
        IsRoot t.tag (a • α + b • β) → a • α + b • β ∈ {α | IsRoot t.tag α ∧ 0 < height α} :=
    fun α hα β hβ a b ha hb hr => by
      refine ⟨hr, ?_⟩
      rw [height_nsmul_add_nsmul]
      have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
      have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
      nlinarith [hα.2, hβ.2]
  have hbij := bijOn_prod_graphFixed (K := K) hσ hposS hposρ hposcl O hO hrange
  have hOj : ∀ j, O j ∈ t.diagramRootOrbits := fun j => by
    have h : O j ∈ Set.range O := Set.mem_range_self j
    rw [hrange] at h
    exact h.1
  have hplus : graphFixedPosUnipotent t K σ ≤ G := fun g hg => by
    obtain ⟨u, -, rfl⟩ := hbij.surjOn hg
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
    exact hOG _ (hOj j) _ (u j).2
  refine le_antisymm (sup_le hplus fun g hg => ?_) ((Subgroup.closure_le _).2 ?_)
  ·
    obtain ⟨w₀, hw₀, h₀⟩ := t.exists_reversesSigns_mem_relWeylTwist
    set n := canonicalRep (coxeterSystem t.tag) K w₀
    have hn : n ∈ twistedFixedGroup t K σ :=
      canonicalRep_mem_twistedFixedGroup t K σ ((mem_relWeylTwist t).1 hw₀)
    obtain ⟨hgU, hgΓ⟩ := Subgroup.mem_inf.1 hg
    have hmap := (canonical_weyl_root_transport t.tag K).1 w₀ {α | IsRoot t.tag α ∧ 0 < height α}
      fun α hα => hα.1
    rw [image_smul_posRoots_of_reversesSigns h₀] at hmap
    have hgU' : g ∈ rootSpan t.tag K {α | IsRoot t.tag α ∧ height α < 0} := hgU
    rw [← hmap] at hgU'
    obtain ⟨g', hg', rfl⟩ := hgU'
    have hg'Γ : g' ∈ twistedFixedGroup t K σ := by
      have e : g' = n⁻¹ * (MulAut.conj n).toMonoidHom g' * n := by simp [mul_assoc]
      rw [e]
      exact mul_mem (mul_mem (inv_mem hn) hgΓ) hn
    obtain ⟨u, -, rfl⟩ := hbij.surjOn (Subgroup.mem_inf.2 ⟨hg', hg'Γ⟩)
    rw [map_list_prod]
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hy
    obtain ⟨α, hα, hαO⟩ := hOj j
    have hroots : ∀ β ∈ (O j : Set (Fin t.tag.rank → ℤ)), IsRoot t.tag β := fun β hβ => by
      rw [← hαO] at hβ
      exact t.isRoot_of_mem_diagramOrbit hα hβ
    have hconj := (canonical_weyl_root_transport t.tag K).1 w₀ _ hroots
    have hmem : (MulAut.conj n).toMonoidHom (u j : ModGL t.tag K) ∈
        rootSpan t.tag K ((fun β => w₀ • β) '' (O j : Set (Fin t.tag.rank → ℤ))) := by
      rw [← hconj]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_inf.1 (u j).2).1
    refine hOG (t.diagramOrbit (w₀ • α)) ⟨_, IsRoot.smul hα w₀, rfl⟩ _
      (Subgroup.mem_inf.2 ⟨?_, ?_⟩)
    · rw [t.diagramOrbit_smul hw₀, Finset.coe_image, hαO]
      exact hmem
    · exact mul_mem (mul_mem hn (Subgroup.mem_inf.1 (u j).2).2) (inv_mem hn)
  · rintro _ ⟨w, hw, a, c, rfl⟩
    have hnC := canonicalRep_mem_graphFixedRootGroup (K := K) (σ := σ) hw
    exact mul_mem (mul_mem hnC (graphFixedPosUnipotent_le_graphFixedRootGroup t K σ
      (orbitX_mem_graphFixedPosUnipotent t σ a c))) (inv_mem hnC)

theorem fixed_positive_orbit_collection
    (t : TwistTag) (K : Type) [Field K] (σ : K ≃+* K) :
    (∀ S : Set (Fin t.tag.rank → ℤ), (∀ α ∈ S, IsRoot t.tag α ∧ 0 < height α) →
      (∀ α ∈ S, permLattice t.perm α ∈ S) →
      (∀ α ∈ S, ∀ β ∈ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot t.tag (a • α + b • β) →
        a • α + b • β ∈ S) →
      ∀ {k : ℕ} (O : Fin k → Finset (Fin t.tag.rank → ℤ)), Function.Injective O →
        Set.range O =
          {O' | O' ∈ t.diagramRootOrbits ∧ (O' : Set (Fin t.tag.rank → ℤ)) ⊆ S} →
        Set.BijOn (fun u : (j : Fin k) → ↥(rootSpan t.tag K (O j : Set (Fin t.tag.rank → ℤ)) ⊓
            twistedFixedGroup t K σ.toRingHom) => (List.ofFn fun j => (u j : ModGL t.tag K)).prod)
          Set.univ (rootSpan t.tag K S ⊓ twistedFixedGroup t K σ.toRingHom)) ∧
    graphFixedRootGroup t K σ.toRingHom = Subgroup.closure {g | ∃ w ∈ relWeylTwist t, ∃ a,
      ∃ c : orbitField t K σ.toRingHom a, g = canonicalRep (coxeterSystem t.tag) K w *
        orbitX t K σ.toRingHom a c * (canonicalRep (coxeterSystem t.tag) K w)⁻¹} :=
  ⟨fun _ hS hSρ hclosed _ O hO hrange =>
    bijOn_prod_graphFixed σ.surjective hS hSρ hclosed O hO hrange,
    graphFixedRootGroup_eq_closure σ.toRingHom σ.surjective⟩

end CFSG.LieType.Chevalley
