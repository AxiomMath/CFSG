module

public import CFSG.LieType.Chevalley.ProductInjectivity
public import CFSG.LieType.Chevalley.RootIdealNormality
public import CFSG.LieType.Steinberg.HeightCollection

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

variable {τ : Tag}

theorem rootSubgroup_mul_comm
    (R : Type*) [CommRing R] {β : Fin τ.rank → ℤ}
    {x y : (Module.End R (RootModule τ R))ˣ} (hx : x ∈ rootSubgroup τ R β)
    (hy : y ∈ rootSubgroup τ R β) : x * y = y * x := by
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
  obtain ⟨d, rfl⟩ := mem_rootSubgroup.1 hy
  rw [← pinnedX_add, ← pinnedX_add, add_comm]

theorem commutator_rootSubgroup_le
    (R : Type) [CommRing R] {α β : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (hβ : IsRoot τ β) (hαp : 0 < height α) (hβp : 0 < height β)
    (hne : α ≠ β) :
    ⁅rootSubgroup τ R α, rootSubgroup τ R β⁆ ≤
      ⨆ (γ : Fin τ.rank → ℤ) (_ : IsRoot τ γ ∧ ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ γ = a • α + b • β),
        rootSubgroup τ R γ := by
  have hc := ringCommContained_pos R ⟨α, hα⟩ ⟨β, hβ⟩ hαp hβp
    (fun h => hne (congrArg Subtype.val h))
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [rootSubgroup_eq_ringRootSubgroup R hα] at hx
  rw [rootSubgroup_eq_ringRootSubgroup R hβ] at hy
  rw [commutatorElement_def]
  have hle : (⨆ (γ : Root τ) (_ : ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ γ.1 = a • α + b • β),
      (rootOperatorFamily τ).ringRootSubgroup R γ) ≤
      ⨆ (γ : Fin τ.rank → ℤ) (_ : IsRoot τ γ ∧ ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ γ = a • α + b • β),
        rootSubgroup τ R γ := by
    refine iSup₂_le fun γ hγ => ?_
    obtain ⟨a, b, ha, hb, hγe⟩ := hγ
    rw [← rootSubgroup_eq_ringRootSubgroup R γ.2]
    exact le_iSup₂_of_le γ.1 ⟨γ.2, a, b, ha, hb, hγe⟩ le_rfl
  exact hle (hc x hx y hy)

theorem height_nsmul_add_nsmul (a b : ℕ) (α β : Fin τ.rank → ℤ) :
    height (a • α + b • β) = a * height α + b * height β := by
  simp [height, Finset.sum_add_distrib, Finset.mul_sum]

theorem bijOn_prod_pinnedX
    (R : Type) [CommRing R] {S : Set (Fin τ.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot τ α ∧ 0 < height α)
    (hclosed : ∀ α ∈ S, ∀ β ∈ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • α + b • β) →
      a • α + b • β ∈ S)
    {m : ℕ} (α : Fin m → Fin τ.rank → ℤ) (hα : Function.Injective α) (hrange : Set.range α = S) :
    Set.BijOn (fun c : Fin m → R => (List.ofFn fun i => pinnedX τ R (α i) (c i)).prod)
      Set.univ (rootSpan τ R S) := by
  classical
  have hαS : ∀ i, α i ∈ S := fun i => hrange ▸ Set.mem_range_self i
  have hUX : ∀ β ∈ S, rootSubgroup τ R β ≤ rootSpan τ R S := fun β hβ =>
    le_iSup₂_of_le β hβ le_rfl
  refine ⟨fun c _ => ?_, fun c _ c' _ h =>
    (positive_root_product_injectivity τ R α hα fun i => hS _ (hαS i)).2 h, fun g hg => ?_⟩
  · refine list_prod_mem fun x hx => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    exact hUX _ (hαS i) (Subgroup.subset_closure ⟨c i, rfl⟩)
  set X := rootSpan τ R S
  have : Fintype S :=
    ((finite_setOf_isRoot τ).subset fun a ha => (hS a ha).1).fintype
  let A : S → Subgroup X := fun β => (rootSubgroup τ R β.1).subgroupOf X
  have hmapA : ∀ β : S, (A β).map X.subtype = rootSubgroup τ R β.1 := fun β => by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 (hUX β.1 β.2)]
  have hab : ∀ β, IsMulCommutative (A β) := fun β =>
    ⟨⟨fun x y => Subtype.ext (Subtype.ext (rootSubgroup_mul_comm R
      (Subgroup.mem_subgroupOf.1 x.2) (Subgroup.mem_subgroupOf.1 y.2)))⟩⟩
  have hgen : ⨆ β, A β = ⊤ := by
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    simp only [hmapA]
    exact (iSup_subtype' (p := (· ∈ S)) (f := fun β _ => rootSubgroup τ R β)).symm
  have hc : ∀ i j : S, i ≠ j →
      ⁅A i, A j⁆ ≤ ⨆ (k : S) (_ : max (height i.1) (height j.1) < height k.1), A k := by
    intro i j hij
    rw [← Subgroup.map_le_map_iff_of_injective X.subtype_injective, Subgroup.map_commutator,
      hmapA, hmapA]
    simp only [Subgroup.map_iSup, hmapA]
    obtain ⟨hir, hip⟩ := hS _ i.2
    obtain ⟨hjr, hjp⟩ := hS _ j.2
    refine (commutator_rootSubgroup_le R hir hjr hip hjp
      (fun h => hij (Subtype.ext h))).trans (iSup₂_le fun γ hγ => ?_)
    obtain ⟨hγr, a, b, ha, hb, rfl⟩ := hγ
    have hγS : a • i.1 + b • j.1 ∈ S := hclosed _ i.2 _ j.2 a b ha hb hγr
    refine le_iSup₂_of_le (⟨a • i.1 + b • j.1, hγS⟩ : S) ?_ le_rfl
    rw [height_nsmul_add_nsmul]
    have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
    have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
    refine max_lt ?_ ?_ <;> nlinarith
  let L : List S := List.ofFn fun i => (⟨α i, hαS i⟩ : S)
  have hnd : L.Nodup := List.nodup_ofFn.2 fun i j h => hα (congrArg Subtype.val h)
  have hall : ∀ β : S, β ∈ L := fun β => by
    obtain ⟨i, hi⟩ : β.1 ∈ Set.range α := hrange ▸ β.2
    exact List.mem_ofFn.2 ⟨i, Subtype.ext hi⟩
  obtain ⟨f, hf, hgf⟩ := CFSG.LieType.Steinberg.height_commutator_collection
    (fun β : S => height β.1) A hab hgen hc L hnd hall ⟨g, hg⟩
  have hc' : ∀ β : S,
      ∃ c : R, pinnedX τ R β.1 c = ((f β : X) : (Module.End R (RootModule τ R))ˣ) :=
    fun β => mem_rootSubgroup.1 (Subgroup.mem_subgroupOf.1 (hf β))
  choose c hc using hc'
  refine ⟨fun i => c ⟨α i, hαS i⟩, Set.mem_univ _, ?_⟩
  have hg' : g = (L.map fun β => ((f β : X) : (Module.End R (RootModule τ R))ˣ)).prod := by
    have h1 := congrArg Subtype.val hgf
    rwa [Subgroup.val_list_prod, List.map_map] at h1
  rw [hg', List.map_ofFn]
  show (List.ofFn fun i => pinnedX τ R (α i) (c ⟨α i, hαS i⟩)).prod = _
  congr 1
  exact List.ofFn_inj.2 (funext fun i => hc ⟨α i, hαS i⟩)

theorem positive_root_collection
    (τ : Tag) (R : Type) [CommRing R] :
    (∀ S : Set (Fin τ.rank → ℤ), (∀ α ∈ S, IsRoot τ α ∧ 0 < height α) →
      (∀ α ∈ S, ∀ β ∈ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • α + b • β) →
        a • α + b • β ∈ S) →
      ∀ {m : ℕ} (α : Fin m → Fin τ.rank → ℤ), Function.Injective α → Set.range α = S →
        Set.BijOn (fun c : Fin m → R => (List.ofFn fun i => pinnedX τ R (α i) (c i)).prod)
          Set.univ (rootSpan τ R S)) ∧
    ∀ {m : ℕ} (α : Fin m → Fin τ.rank → ℤ), Function.Injective α →
      Set.range α = {β | IsRoot τ β ∧ 0 < height β} →
      Set.BijOn (fun c : Fin m → R => (List.ofFn fun i => pinnedX τ R (α i) (c i)).prod)
        Set.univ (posUnipotent τ R) := by
  refine ⟨fun S hS hclosed m α hα hrange => bijOn_prod_pinnedX R hS hclosed α hα hrange,
    fun α hα hrange => bijOn_prod_pinnedX R (fun β hβ => hβ) (fun β hβ γ hγ a b ha hb hr => ?_)
      α hα hrange⟩
  refine ⟨hr, ?_⟩
  rw [height_nsmul_add_nsmul]
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  nlinarith [hβ.2, hγ.2]

end CFSG.LieType.Chevalley
