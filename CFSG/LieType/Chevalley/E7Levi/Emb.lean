module

public import CFSG.Blueprint.ChevalleyRootArtifact
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhatDefs

public noncomputable section

namespace CFSG.LieType.Chevalley.E7Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

class E7Sub (τ : Tag) : Prop where
  rank_ge : Tag.E7.rank ≤ τ.rank
  cartan_eq : ∀ k l : Fin Tag.E7.rank,
    τ.cartan (Fin.castLE rank_ge k) (Fin.castLE rank_ge l) = Tag.E7.cartan k l
  roots_up : ∀ l ∈ Tag.E7.artifactRoots, l ++ List.replicate (τ.rank - Tag.E7.rank) 0 ∈
    τ.artifactRoots
  roots_down : ∀ l ∈ τ.artifactRoots, l.drop Tag.E7.rank = List.replicate (τ.rank - Tag.E7.rank) 0 →
    l.take Tag.E7.rank ∈ Tag.E7.artifactRoots

instance : E7Sub .E7 :=
  have h : Tag.E7.rank ≤ Tag.E7.rank := by decide
  ⟨h, fun k l => sub_eq_zero.1 ((by decide +revert : ∀ (h : Tag.E7.rank ≤ Tag.E7.rank)
    (k l : Fin Tag.E7.rank), Tag.E7.cartan (Fin.castLE h k) (Fin.castLE h l) -
      Tag.E7.cartan k l = 0) h k l), by decide +kernel, by decide +kernel⟩

instance : E7Sub .E8 :=
  have h : Tag.E7.rank ≤ Tag.E8.rank := by decide
  ⟨h, fun k l => sub_eq_zero.1 ((by decide +revert : ∀ (h : Tag.E7.rank ≤ Tag.E8.rank)
    (k l : Fin Tag.E7.rank), Tag.E8.cartan (Fin.castLE h k) (Fin.castLE h l) -
      Tag.E7.cartan k l = 0) h k l), by decide +kernel, by decide +kernel⟩

@[expose] def e7Lat (τ : Tag) (β : Fin Tag.E7.rank → ℤ) : Fin τ.rank → ℤ :=
  fun i => if h : i.val < Tag.E7.rank then β ⟨i.val, h⟩ else 0

section Lattice

variable {τ : Tag}

theorem e7Lat_apply_of_le {β : Fin Tag.E7.rank → ℤ} {i : Fin τ.rank} (h : Tag.E7.rank ≤ i.val) :
    e7Lat τ β i = 0 := by
  simp [e7Lat, not_lt.2 h]

theorem e7Lat_add (β γ : Fin Tag.E7.rank → ℤ) : e7Lat τ (β + γ) = e7Lat τ β + e7Lat τ γ := by
  funext i
  by_cases h : i.val < Tag.E7.rank <;> simp [e7Lat, h]

theorem e7Lat_neg (β : Fin Tag.E7.rank → ℤ) : e7Lat τ (-β) = -e7Lat τ β := by
  funext i
  by_cases h : i.val < Tag.E7.rank <;> simp [e7Lat, h]

theorem e7Lat_sub (β γ : Fin Tag.E7.rank → ℤ) : e7Lat τ (β - γ) = e7Lat τ β - e7Lat τ γ := by
  funext i
  by_cases h : i.val < Tag.E7.rank <;> simp [e7Lat, h]

theorem e7Lat_smul (n : ℤ) (β : Fin Tag.E7.rank → ℤ) : e7Lat τ (n • β) = n • e7Lat τ β := by
  funext i
  by_cases h : i.val < Tag.E7.rank <;> simp [e7Lat, h]

end Lattice

section Index

variable {τ : Tag} [hτ : E7Sub τ]

@[expose] def e7Idx (k : Fin Tag.E7.rank) : Fin τ.rank := Fin.castLE hτ.rank_ge k

theorem e7Idx_injective : Function.Injective (e7Idx (τ := τ)) :=
  Fin.castLE_injective hτ.rank_ge

theorem e7Lat_apply_e7Idx (β : Fin Tag.E7.rank → ℤ) (k : Fin Tag.E7.rank) :
    e7Lat τ β (e7Idx k) = β k := by
  simp [e7Lat, e7Idx]

theorem exists_e7Idx_eq {i : Fin τ.rank} (h : i.val < Tag.E7.rank) : ∃ k, e7Idx (τ := τ) k = i :=
  ⟨⟨i.val, h⟩, Fin.ext rfl⟩

theorem e7Lat_single (k : Fin Tag.E7.rank) :
    e7Lat τ (Pi.single k 1) = Pi.single (e7Idx k) 1 := by
  funext i
  by_cases h : i.val < Tag.E7.rank
  · obtain ⟨l, rfl⟩ := exists_e7Idx_eq (τ := τ) h
    simp only [e7Lat_apply_e7Idx, Pi.single_apply, e7Idx_injective.eq_iff]
  · rw [e7Lat_apply_of_le (not_lt.1 h), Pi.single_apply, eq_comm, ite_eq_right_iff]
    intro hi
    exact absurd (by rw [hi]; exact k.2) h

theorem e7Lat_injective : Function.Injective (e7Lat τ) := by
  intro β γ h
  funext k
  rw [← e7Lat_apply_e7Idx (τ := τ) β k, ← e7Lat_apply_e7Idx (τ := τ) γ k, h]

theorem e7Lat_comp_e7Idx {γ : Fin τ.rank → ℤ}
    (h : ∀ i : Fin τ.rank, Tag.E7.rank ≤ i.val → γ i = 0) :
    e7Lat τ (fun k => γ (e7Idx k)) = γ := by
  funext i
  by_cases hi : i.val < Tag.E7.rank
  · obtain ⟨l, rfl⟩ := exists_e7Idx_eq (τ := τ) hi
    rw [e7Lat_apply_e7Idx]
  · rw [e7Lat_apply_of_le (not_lt.1 hi), h i (not_lt.1 hi)]

theorem cartan_e7Idx (k l : Fin Tag.E7.rank) :
    τ.cartan (e7Idx k) (e7Idx l) = Tag.E7.cartan k l :=
  hτ.cartan_eq k l

theorem sum_eq_sum_e7Idx (f : Fin τ.rank → ℤ)
    (hf : ∀ i : Fin τ.rank, Tag.E7.rank ≤ i.val → f i = 0) :
    ∑ j, f j = ∑ k : Fin Tag.E7.rank, f (e7Idx k) := by
  rw [← Finset.sum_image (f := f) (g := e7Idx (τ := τ)) (fun a _ b _ h => e7Idx_injective h)]
  refine (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => hf j ?_).symm
  by_contra hlt
  exact hj (Finset.mem_image.2 ⟨⟨j.val, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)

theorem sum_cartan_e7Lat (k : Fin Tag.E7.rank) (β : Fin Tag.E7.rank → ℤ) :
    ∑ j, τ.cartan (e7Idx k) j * e7Lat τ β j = ∑ j, Tag.E7.cartan k j * β j := by
  rw [sum_eq_sum_e7Idx _ (fun i hi => by rw [e7Lat_apply_of_le hi, mul_zero])]
  exact Finset.sum_congr rfl fun l _ => by rw [cartan_e7Idx, e7Lat_apply_e7Idx]

theorem e7Lat_reflect (k : Fin Tag.E7.rank) (β : Fin Tag.E7.rank → ℤ) :
    e7Lat τ (reflect Tag.E7 k β) = reflect τ (e7Idx k) (e7Lat τ β) := by
  rw [reflect, reflect, e7Lat_sub, e7Lat_smul, e7Lat_single, sum_cartan_e7Lat]

theorem ofFn_e7Lat (β : Fin Tag.E7.rank → ℤ) :
    List.ofFn (e7Lat τ β) = List.ofFn β ++ List.replicate (τ.rank - Tag.E7.rank) 0 := by
  have hge := hτ.rank_ge
  refine List.ext_getElem (by simp; omega) fun n h1 h2 => ?_
  simp only [List.length_ofFn] at h1
  simp only [List.getElem_ofFn, List.getElem_append, List.length_ofFn, List.getElem_replicate]
  by_cases hn : n < Tag.E7.rank
  · simp [e7Lat, hn]
  · simp [e7Lat, hn]

theorem e7Lat_add_smul_single (β : Fin Tag.E7.rank → ℤ) (k : Fin Tag.E7.rank) (n : ℤ) :
    e7Lat τ (β + n • Pi.single k 1) = e7Lat τ β + n • Pi.single (e7Idx k) 1 := by
  rw [e7Lat_add, e7Lat_smul, e7Lat_single]

theorem e7Lat_sub_smul_single (β : Fin Tag.E7.rank → ℤ) (k : Fin Tag.E7.rank) (n : ℤ) :
    e7Lat τ (β - n • Pi.single k 1) = e7Lat τ β - n • Pi.single (e7Idx k) 1 := by
  rw [sub_eq_add_neg, ← neg_smul, e7Lat_add_smul_single, neg_smul, ← sub_eq_add_neg]

theorem e7Lat_eq_single_iff {α : Fin Tag.E7.rank → ℤ} {k : Fin Tag.E7.rank} :
    e7Lat τ α = Pi.single (e7Idx k) 1 ↔ α = Pi.single k 1 := by
  rw [← e7Lat_single]
  exact e7Lat_injective.eq_iff

theorem e7Lat_eq_neg_single_iff {α : Fin Tag.E7.rank → ℤ} {k : Fin Tag.E7.rank} :
    e7Lat τ α = -Pi.single (e7Idx k) 1 ↔ α = -Pi.single k 1 := by
  rw [← e7Lat_single, ← e7Lat_neg]
  exact e7Lat_injective.eq_iff

end Index

section Roots

variable {τ : Tag} [hτ : E7Sub τ]

theorem isRoot_e7Lat_iff {β : Fin Tag.E7.rank → ℤ} : IsRoot τ (e7Lat τ β) ↔ IsRoot Tag.E7 β := by
  rw [isRoot_iff_mem_artifactRoots, isRoot_iff_mem_artifactRoots, ofFn_e7Lat]
  refine ⟨fun h => ?_, hτ.roots_up _⟩
  have h' := hτ.roots_down _ h (by rw [List.drop_left' (by simp)])
  rwa [List.take_left' (by simp)] at h'

theorem stringUp_e7Lat (k : Fin Tag.E7.rank) (β : Fin Tag.E7.rank → ℤ) :
    stringUp τ (e7Idx k) (e7Lat τ β) = stringUp Tag.E7 k β := by
  simp only [stringUp, ← e7Lat_add_smul_single, isRoot_e7Lat_iff]

theorem stringDown_e7Lat (k : Fin Tag.E7.rank) (β : Fin Tag.E7.rank → ℤ) :
    stringDown τ (e7Idx k) (e7Lat τ β) = stringDown Tag.E7 k β := by
  simp only [stringDown, ← e7Lat_sub_smul_single, isRoot_e7Lat_iff]

@[expose] def e7Label : Label Tag.E7 → Label τ
  | .inl k => .inl (e7Idx k)
  | .inr β => .inr ⟨e7Lat τ β.1, isRoot_e7Lat_iff.2 β.2⟩

theorem e7Label_injective : Function.Injective (e7Label (τ := τ)) := by
  rintro (k | β) (l | γ) h
  · exact congrArg Sum.inl (e7Idx_injective (Sum.inl_injective h))
  · exact absurd h Sum.inl_ne_inr
  · exact absurd h Sum.inr_ne_inl
  · exact congrArg Sum.inr
      (Subtype.ext (e7Lat_injective (congrArg Subtype.val (Sum.inr_injective h))))

variable (τ) (K : Type) [Field K]

@[expose] def e7Emb : RootModule Tag.E7 K →ₗ[K] RootModule τ K :=
  Finsupp.lmapDomain K K (e7Label (τ := τ))

variable {τ} {K}

theorem e7Emb_single (b : Label Tag.E7) (c : K) :
    e7Emb τ K (Finsupp.single b c) = Finsupp.single (e7Label b) c :=
  Finsupp.mapDomain_single

theorem e7Emb_injective : Function.Injective (e7Emb τ K) :=
  Finsupp.mapDomain_injective e7Label_injective

theorem e7Emb_hVec (k : Fin Tag.E7.rank) :
    e7Emb τ K (hVec Tag.E7 K k) = hVec τ K (e7Idx k) :=
  e7Emb_single _ 1

theorem e7Emb_rootVec (β : Fin Tag.E7.rank → ℤ) :
    e7Emb τ K (rootVec Tag.E7 K β) = rootVec τ K (e7Lat τ β) := by
  by_cases hβ : IsRoot Tag.E7 β
  · rw [rootVec_eq_single_of_isRoot hβ, rootVec_eq_single_of_isRoot (isRoot_e7Lat_iff.2 hβ),
      e7Emb_single]
    rfl
  · rw [rootVec, dite_eq_right hβ, rootVec, dite_eq_right (mt isRoot_e7Lat_iff.1 hβ), map_zero]

theorem xOp_comp_e7Emb (k : Fin Tag.E7.rank) (c : K) :
    xOp τ K (e7Idx k) c ∘ₗ e7Emb τ K = e7Emb τ K ∘ₗ xOp Tag.E7 K k c := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, e7Emb_single, xOp,
    Finsupp.linearCombination_single, one_smul]
  rcases b with j | ⟨α, hα⟩
  · simp only [e7Label]
    rw [map_add, map_smul, e7Emb_hVec, e7Emb_rootVec, e7Lat_single, cartan_e7Idx]
  · simp only [e7Label, e7Lat_eq_single_iff, e7Lat_eq_neg_single_iff]
    split_ifs with h1 h2
    · rw [e7Emb_single]
      rfl
    · rw [map_add, map_add, map_smul, map_smul, e7Emb_single, e7Emb_hVec, e7Emb_rootVec,
        e7Lat_single]
      rfl
    · rw [map_sum, stringUp_e7Lat, stringDown_e7Lat]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [map_smul, e7Emb_rootVec, e7Lat_add_smul_single]

theorem yOp_comp_e7Emb (k : Fin Tag.E7.rank) (c : K) :
    yOp τ K (e7Idx k) c ∘ₗ e7Emb τ K = e7Emb τ K ∘ₗ yOp Tag.E7 K k c := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, e7Emb_single, yOp,
    Finsupp.linearCombination_single, one_smul]
  rcases b with j | ⟨α, hα⟩
  · simp only [e7Label]
    rw [map_add, map_smul, e7Emb_hVec, e7Emb_rootVec, e7Lat_neg, e7Lat_single, cartan_e7Idx]
  · simp only [e7Label, e7Lat_eq_single_iff, e7Lat_eq_neg_single_iff]
    split_ifs with h1 h2
    · rw [e7Emb_single]
      rfl
    · rw [map_add, map_add, map_smul, map_smul, e7Emb_single, e7Emb_hVec, e7Emb_rootVec,
        e7Lat_neg, e7Lat_single]
      rfl
    · rw [map_sum, stringUp_e7Lat, stringDown_e7Lat]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [map_smul, e7Emb_rootVec, e7Lat_sub_smul_single]

theorem e7Emb_comp_injective {f f' : Module.End K (RootModule Tag.E7 K)}
    (h : e7Emb τ K ∘ₗ f = e7Emb τ K ∘ₗ f') : f = f' :=
  LinearMap.ext fun v => e7Emb_injective (LinearMap.congr_fun h v)

theorem one_comp_e7Emb : ((1 : ModGL τ K) : Module.End K (RootModule τ K)) ∘ₗ e7Emb τ K =
    e7Emb τ K ∘ₗ ((1 : ModGL Tag.E7 K) : Module.End K (RootModule Tag.E7 K)) := by
  rw [Units.val_one, Units.val_one, Module.End.one_eq_id, Module.End.one_eq_id,
    LinearMap.id_comp, LinearMap.comp_id]

theorem mul_comp_e7Emb {g h : ModGL τ K} {g' h' : ModGL Tag.E7 K}
    (hg : (g : Module.End K (RootModule τ K)) ∘ₗ e7Emb τ K =
      e7Emb τ K ∘ₗ (g' : Module.End K (RootModule Tag.E7 K)))
    (hh : (h : Module.End K (RootModule τ K)) ∘ₗ e7Emb τ K =
      e7Emb τ K ∘ₗ (h' : Module.End K (RootModule Tag.E7 K))) :
    ((g * h : ModGL τ K) : Module.End K (RootModule τ K)) ∘ₗ e7Emb τ K =
      e7Emb τ K ∘ₗ ((g' * h' : ModGL Tag.E7 K) : Module.End K (RootModule Tag.E7 K)) := by
  rw [Units.val_mul, Units.val_mul, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
    LinearMap.comp_assoc, hh, ← LinearMap.comp_assoc, hg, LinearMap.comp_assoc]

theorem inv_comp_e7Emb {g : ModGL τ K} {g' : ModGL Tag.E7 K}
    (hg : (g : Module.End K (RootModule τ K)) ∘ₗ e7Emb τ K =
      e7Emb τ K ∘ₗ (g' : Module.End K (RootModule Tag.E7 K))) :
    ((g⁻¹ : ModGL τ K) : Module.End K (RootModule τ K)) ∘ₗ e7Emb τ K =
      e7Emb τ K ∘ₗ ((g'⁻¹ : ModGL Tag.E7 K) : Module.End K (RootModule Tag.E7 K)) := by
  have e : ∀ v, (g : Module.End K (RootModule τ K))
      (((g⁻¹ : ModGL τ K) : Module.End K (RootModule τ K)) (e7Emb τ K v)) =
      (g : Module.End K (RootModule τ K)) (e7Emb τ K
        (((g'⁻¹ : ModGL Tag.E7 K) : Module.End K (RootModule Tag.E7 K)) v)) := by
    intro v
    have h1 := LinearMap.congr_fun hg (((g'⁻¹ : ModGL Tag.E7 K) : Module.End K _) v)
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at h1
    rw [h1, ← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Module.End.one_apply, ← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Module.End.one_apply]
  refine LinearMap.ext fun v => ?_
  have hinj : Function.Injective (g : Module.End K (RootModule τ K)) := fun x y hxy => by
    have := congrArg ((g⁻¹ : ModGL τ K) : Module.End K (RootModule τ K)) hxy
    rwa [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Module.End.one_apply, ← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Module.End.one_apply] at this
  exact hinj (e v)

variable (τ K) in
@[expose] def e7Preserving : Subgroup (ModGL τ K) where
  carrier := {g | ∃ g' : ModGL Tag.E7 K,
    (g : Module.End K (RootModule τ K)) ∘ₗ e7Emb τ K =
      e7Emb τ K ∘ₗ (g' : Module.End K (RootModule Tag.E7 K))}
  mul_mem' := by
    rintro g h ⟨g', hg⟩ ⟨h', hh⟩
    exact ⟨g' * h', mul_comp_e7Emb hg hh⟩
  one_mem' := ⟨1, one_comp_e7Emb⟩
  inv_mem' := by
    rintro g ⟨g', hg⟩
    exact ⟨g'⁻¹, inv_comp_e7Emb hg⟩

theorem e7Preserving_partner_unique {g : ModGL τ K} {g' g'' : ModGL Tag.E7 K}
    (h' : (g : Module.End K (RootModule τ K)) ∘ₗ e7Emb τ K =
      e7Emb τ K ∘ₗ (g' : Module.End K (RootModule Tag.E7 K)))
    (h'' : (g : Module.End K (RootModule τ K)) ∘ₗ e7Emb τ K =
      e7Emb τ K ∘ₗ (g'' : Module.End K (RootModule Tag.E7 K))) : g' = g'' :=
  Units.ext (e7Emb_comp_injective (h'.symm.trans h''))

variable (τ K) in
@[expose] def e7PreservingRes : e7Preserving τ K →* ModGL Tag.E7 K where
  toFun g := g.2.choose
  map_one' := e7Preserving_partner_unique (1 : e7Preserving τ K).2.choose_spec one_comp_e7Emb
  map_mul' g h := e7Preserving_partner_unique (g * h).2.choose_spec
    (mul_comp_e7Emb g.2.choose_spec h.2.choose_spec)

theorem e7PreservingRes_spec (g : e7Preserving τ K) :
    ((g : ModGL τ K) : Module.End K (RootModule τ K)) ∘ₗ e7Emb τ K =
      e7Emb τ K ∘ₗ (e7PreservingRes τ K g : Module.End K (RootModule Tag.E7 K)) :=
  g.2.choose_spec

theorem e7PreservingRes_eq {g : e7Preserving τ K} {g' : ModGL Tag.E7 K}
    (h : ((g : ModGL τ K) : Module.End K (RootModule τ K)) ∘ₗ e7Emb τ K =
      e7Emb τ K ∘ₗ (g' : Module.End K (RootModule Tag.E7 K))) : e7PreservingRes τ K g = g' :=
  e7Preserving_partner_unique (e7PreservingRes_spec g) h

end Roots

section Units

variable {τ : Tag} [hτ : E7Sub τ]
  {K : Type} [Field K]

theorem xUnit_mem_e7Preserving (k : Fin Tag.E7.rank) (c : K) :
    xUnit τ K (e7Idx k) c ∈ e7Preserving τ K :=
  ⟨xUnit Tag.E7 K k c, xOp_comp_e7Emb k c⟩

theorem yUnit_mem_e7Preserving (k : Fin Tag.E7.rank) (c : K) :
    yUnit τ K (e7Idx k) c ∈ e7Preserving τ K :=
  ⟨yUnit Tag.E7 K k c, yOp_comp_e7Emb k c⟩

theorem subsystemGroup_le_e7Preserving {A : Set (Fin τ.rank)}
    (hA : ∀ i ∈ A, i.val < Tag.E7.rank) : subsystemGroup τ K A ≤ e7Preserving τ K := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨i, hi, c, rfl | rfl⟩
  · obtain ⟨k, rfl⟩ := exists_e7Idx_eq (τ := τ) (hA i hi)
    exact xUnit_mem_e7Preserving k c
  · obtain ⟨k, rfl⟩ := exists_e7Idx_eq (τ := τ) (hA i hi)
    exact yUnit_mem_e7Preserving k c

variable (K) in
@[expose] def e7Res {A : Set (Fin τ.rank)} (hA : ∀ i ∈ A, i.val < Tag.E7.rank) :
    subsystemGroup τ K A →* ModGL Tag.E7 K :=
  (e7PreservingRes τ K).comp (Subgroup.inclusion (subsystemGroup_le_e7Preserving hA))

theorem e7Res_apply {A : Set (Fin τ.rank)} (hA : ∀ i ∈ A, i.val < Tag.E7.rank)
    (g : subsystemGroup τ K A) (v : RootModule Tag.E7 K) :
    ((g : ModGL τ K) : Module.End K (RootModule τ K)) (e7Emb τ K v) =
      e7Emb τ K ((e7Res K hA g : Module.End K (RootModule Tag.E7 K)) v) :=
  LinearMap.congr_fun (e7PreservingRes_spec (Subgroup.inclusion
    (subsystemGroup_le_e7Preserving hA) g)) v

theorem e7Res_eq {A : Set (Fin τ.rank)} (hA : ∀ i ∈ A, i.val < Tag.E7.rank)
    {g : subsystemGroup τ K A} {g' : ModGL Tag.E7 K}
    (h : ∀ v, ((g : ModGL τ K) : Module.End K (RootModule τ K)) (e7Emb τ K v) =
      e7Emb τ K ((g' : Module.End K (RootModule Tag.E7 K)) v)) : e7Res K hA g = g' :=
  e7PreservingRes_eq (LinearMap.ext h)

theorem e7Res_xUnit {A : Set (Fin τ.rank)} (hA : ∀ i ∈ A, i.val < Tag.E7.rank)
    (k : Fin Tag.E7.rank) (hk : e7Idx (τ := τ) k ∈ A) (c : K) :
    e7Res K hA ⟨xUnit τ K (e7Idx k) c, xUnit_mem_subsystemGroup hk c⟩ = xUnit Tag.E7 K k c :=
  e7Res_eq hA fun v => LinearMap.congr_fun (xOp_comp_e7Emb k c) v

theorem e7Res_yUnit {A : Set (Fin τ.rank)} (hA : ∀ i ∈ A, i.val < Tag.E7.rank)
    (k : Fin Tag.E7.rank) (hk : e7Idx (τ := τ) k ∈ A) (c : K) :
    e7Res K hA ⟨yUnit τ K (e7Idx k) c, yUnit_mem_subsystemGroup hk c⟩ = yUnit Tag.E7 K k c :=
  e7Res_eq hA fun v => LinearMap.congr_fun (yOp_comp_e7Emb k c) v

end Units

end CFSG.LieType.Chevalley.E7Levi
