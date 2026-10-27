module

public import CFSG.LieType.Ree.LargeReeBlockData
public import CFSG.LieType.Ree.BorelSelfNormalizers

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Collection

variable {τ : Tag} {K : Type} [Field K]

theorem posRoots_nsmul_add_nsmul_mem :
    ∀ α ∈ {β : Fin τ.rank → ℤ | IsRoot τ β ∧ 0 < height β},
      ∀ β ∈ {β : Fin τ.rank → ℤ | IsRoot τ β ∧ 0 < height β}, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
        IsRoot τ (a • α + b • β) →
          a • α + b • β ∈ {β : Fin τ.rank → ℤ | IsRoot τ β ∧ 0 < height β} := by
  intro α hα β hβ a b ha hb hr
  refine ⟨hr, ?_⟩
  rw [height_nsmul_add_nsmul]
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  nlinarith [hα.2, hβ.2]

theorem list_prod_pinnedX_bijective
    {S : Set (Fin τ.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot τ α ∧ 0 < height α)
    (hclosed : ∀ α ∈ S, ∀ β ∈ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • α + b • β) →
      a • α + b • β ∈ S)
    {L : List (Fin τ.rank → ℤ)} (hL : L.Nodup) (hLS : {x | x ∈ L} = S) :
    (∀ c : (Fin τ.rank → ℤ) → K, (L.map fun α => pinnedX τ K α (c α)).prod ∈ rootSpan τ K S) ∧
    (∀ g ∈ rootSpan τ K S, ∃ c : (Fin τ.rank → ℤ) → K,
      (L.map fun α => pinnedX τ K α (c α)).prod = g) ∧
    ∀ c c' : (Fin τ.rank → ℤ) → K, (L.map fun α => pinnedX τ K α (c α)).prod =
      (L.map fun α => pinnedX τ K α (c' α)).prod → ∀ α ∈ L, c α = c' α := by
  have hinj : Function.Injective L.get := List.nodup_iff_injective_get.1 hL
  have hB := bijOn_prod_pinnedX K hS hclosed L.get hinj (by rw [Set.range_list_get, hLS])
  have key : ∀ c : (Fin τ.rank → ℤ) → K, (L.map fun α => pinnedX τ K α (c α)) =
      List.ofFn fun i => pinnedX τ K (L.get i) (c (L.get i)) := by
    intro c
    conv_lhs => rw [← List.ofFn_get L]
    rw [List.map_ofFn]
    rfl
  refine ⟨fun c => ?_, fun g hg => ?_, fun c c' h α hα => ?_⟩
  · rw [key]
    exact hB.1 (Set.mem_univ fun i => c (L.get i))
  · obtain ⟨d, -, hd⟩ := hB.2.2 hg
    refine ⟨Function.extend L.get d 0, ?_⟩
    rw [key, ← hd]
    simp only [hinj.extend_apply]
  · rw [key, key] at h
    have h' := hB.2.1 (Set.mem_univ fun i => c (L.get i)) (Set.mem_univ fun i => c' (L.get i)) h
    obtain ⟨i, rfl⟩ : α ∈ Set.range L.get := by
      rw [Set.range_list_get]
      exact hα
    exact congrFun h' i

theorem prod_map_flatten_ofFn {G : Type*} [Monoid G] {n : ℕ}
    (L : Fin n → List (Fin τ.rank → ℤ)) (f : (Fin τ.rank → ℤ) → G) :
    (((List.ofFn L).flatten).map f).prod = (List.ofFn fun k => ((L k).map f).prod).prod := by
  rw [List.map_flatten, List.prod_flatten, List.map_ofFn, List.map_ofFn]
  rfl

theorem bijOn_list_prod_rootSpan
    {n : ℕ} {Q : Fin n → Set (Fin τ.rank → ℤ)}
    {L : Fin n → List (Fin τ.rank → ℤ)} (hQ : ∀ k, ∀ α ∈ Q k, IsRoot τ α ∧ 0 < height α)
    (hcl : ∀ k, ∀ α ∈ Q k, ∀ β ∈ Q k, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • α + b • β) →
      a • α + b • β ∈ Q k)
    (hL : ∀ k, (L k).Nodup) (hLQ : ∀ k, {x | x ∈ L k} = Q k)
    (hdisj : ∀ k k', k ≠ k' → Disjoint (Q k) (Q k'))
    (hcover : ∀ α, IsRoot τ α → 0 < height α → ∃ k, α ∈ Q k) :
    Set.BijOn (fun u : Fin n → ModGL τ K => (List.ofFn u).prod)
      (Set.univ.pi fun k => (rootSpan τ K (Q k) : Set (ModGL τ K)))
      (posUnipotent τ K : Set (ModGL τ K)) := by
  classical
  have hmemQ : ∀ k x, x ∈ L k ↔ x ∈ Q k := fun k x => by
    rw [← hLQ k]
    rfl
  have hmemL : ∀ x, x ∈ (List.ofFn L).flatten ↔ ∃ k, x ∈ L k := by
    intro x
    rw [List.mem_flatten]
    constructor
    · rintro ⟨l, hl, hx⟩
      obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hl
      exact ⟨k, hx⟩
    · rintro ⟨k, hx⟩
      exact ⟨L k, List.mem_ofFn.2 ⟨k, rfl⟩, hx⟩
  have huniq : ∀ k k' x, x ∈ L k → x ∈ L k' → k = k' := by
    intro k k' x h h'
    by_contra hne
    exact Set.disjoint_left.1 (hdisj k k' hne) ((hmemQ k x).1 h) ((hmemQ k' x).1 h')
  have hnd : ((List.ofFn L).flatten).Nodup := by
    refine List.nodup_flatten.2 ⟨fun l hl => ?_, List.pairwise_ofFn.2 fun k k' hkk' => ?_⟩
    · obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hl
      exact hL k
    · exact fun x h h' => (ne_of_lt hkk') (huniq k k' x h h')
  have hset : {x | x ∈ (List.ofFn L).flatten} =
      {β : Fin τ.rank → ℤ | IsRoot τ β ∧ 0 < height β} := by
    ext x
    change x ∈ (List.ofFn L).flatten ↔ IsRoot τ x ∧ 0 < height x
    rw [hmemL]
    constructor
    · rintro ⟨k, hx⟩
      exact hQ k x ((hmemQ k x).1 hx)
    · rintro ⟨hr, hp⟩
      obtain ⟨k, hk⟩ := hcover x hr hp
      exact ⟨k, (hmemQ k x).2 hk⟩
  have hT := list_prod_pinnedX_bijective (K := K) (fun α hα => hα) posRoots_nsmul_add_nsmul_mem
    hnd hset
  have hB := fun k => list_prod_pinnedX_bijective (K := K) (hQ k) (hcl k) (hL k) (hLQ k)
  let glue : ((k : Fin n) → (Fin τ.rank → ℤ) → K) → (Fin τ.rank → ℤ) → K := fun c x =>
    if hx : ∃ k, x ∈ L k then c hx.choose x else 0
  have hglue : ∀ c k, ∀ x ∈ L k, glue c x = c k x := by
    intro c k x hx
    have hex : ∃ k, x ∈ L k := ⟨k, hx⟩
    change (if hx : ∃ k, x ∈ L k then c hx.choose x else 0) = c k x
    rw [dite_eq_left hex, huniq _ _ x hex.choose_spec hx]
  have hsplit : ∀ c : (Fin τ.rank → ℤ) → K,
      (((List.ofFn L).flatten).map fun α => pinnedX τ K α (c α)).prod =
        (List.ofFn fun k => ((L k).map fun α => pinnedX τ K α (c α)).prod).prod :=
    fun c => prod_map_flatten_ofFn L _
  have hblock : ∀ (c : (k : Fin n) → (Fin τ.rank → ℤ) → K) k,
      ((L k).map fun α => pinnedX τ K α (glue c α)).prod =
        ((L k).map fun α => pinnedX τ K α (c k α)).prod := fun c k => by
    rw [List.map_congr_left fun x hx => by rw [hglue c k x hx]]
  refine ⟨fun u hu => ?_, fun u hu v hv h => ?_, fun g hg => ?_⟩
  · refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
    exact rootSpan_le_posUnipotent (hQ k) (hu k (Set.mem_univ k))
  · choose cu hcu using fun k => (hB k).2.1 (u k) (hu k (Set.mem_univ k))
    choose cv hcv using fun k => (hB k).2.1 (v k) (hv k (Set.mem_univ k))
    have hu' : (List.ofFn u).prod =
        (((List.ofFn L).flatten).map fun α => pinnedX τ K α (glue cu α)).prod := by
      rw [hsplit]
      exact congrArg List.prod (List.ofFn_inj.2 (funext fun k => by rw [hblock, hcu]))
    have hv' : (List.ofFn v).prod =
        (((List.ofFn L).flatten).map fun α => pinnedX τ K α (glue cv α)).prod := by
      rw [hsplit]
      exact congrArg List.prod (List.ofFn_inj.2 (funext fun k => by rw [hblock, hcv]))
    have heq := hT.2.2 _ _ (hu'.symm.trans (h.trans hv'))
    funext k
    rw [← hcu k, ← hcv k]
    refine congrArg List.prod (List.map_congr_left fun x hx => ?_)
    have hx' := heq x ((hmemL x).2 ⟨k, hx⟩)
    rw [hglue cu k x hx, hglue cv k x hx] at hx'
    rw [hx']
  · obtain ⟨c, rfl⟩ := hT.2.1 g hg
    exact ⟨fun k => ((L k).map fun α => pinnedX τ K α (c α)).prod, fun k _ => (hB k).1 c,
      (hsplit c).symm⟩

end Collection

namespace ReeTag

@[expose] def largeReeBlocks :
    Set (Set (Fin F4.tag.rank → ℤ)) :=
  {Q | ∃ w ∈ F4.relWeylRee, ∃ j, Q = (w • ·) '' F4.fixedOrbitRoots j}

@[expose] def largeReePosBlocks :
    Set (Set (Fin F4.tag.rank → ℤ)) :=
  {Q | Q ∈ largeReeBlocks ∧ Q ⊆ {α | IsRoot F4.tag α ∧ 0 < height α}}

@[expose] def largeReeBlockGroup
    (K : Type) [Field K] [Finite K] [CharP K F4.prime] (a : ℕ)
    (Q : Set (Fin F4.tag.rank → ℤ)) : Subgroup (ModGL F4.tag K) :=
  rootSpan F4.tag K Q ⊓ F4.reeGamma K a

theorem setOf_mem_eq_of_subset {α : Type*} {l l' : List α} (h : l ⊆ l') (h' : l' ⊆ l) :
    {x | x ∈ l} = {x | x ∈ l'} :=
  Set.ext fun _ => ⟨fun hx => h hx, fun hx => h' hx⟩

theorem image_fixedRelElt_fixedOrbitRoots
    (k : Fin F4.fixedWeylOrder)
    (j : Fin F4.fixedOrbitCount) :
    (F4.fixedRelElt k • ·) '' F4.fixedOrbitRoots j = {x | x ∈ largeReeBlockImage k j} := by
  rw [fixedRelElt, list_prod_map_fixedOrbitElement, fixedOrbitRoots_eq_list]
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq, largeReeBlockImage, List.mem_map,
    CFSG.LieType.Ree.wordProd_smul]

theorem largeReeBlocks_eq_range :
    largeReeBlocks = Set.range fun i : Fin 16 => {x | x ∈ largeReeBlockTable i} := by
  ext Q
  constructor
  · rintro ⟨w, hw, j, rfl⟩
    obtain ⟨k, rfl⟩ := exists_fixedRelElt_eq hw
    obtain ⟨i, h1, h2⟩ := largeReeBlockImage_check k j
    refine ⟨i, ?_⟩
    rw [image_fixedRelElt_fixedOrbitRoots]
    exact setOf_mem_eq_of_subset h2 h1
  · rintro ⟨i, rfl⟩
    obtain ⟨k, j, h1, h2⟩ := largeReeBlockTable_check i
    refine ⟨_, fixedRelElt_mem k, j, ?_⟩
    rw [image_fixedRelElt_fixedOrbitRoots]
    exact setOf_mem_eq_of_subset h1 h2

theorem largeReeBlockSet_mem
    (i : Fin 16) :
    {x | x ∈ largeReeBlockTable i} ∈ largeReeBlocks := by
  rw [largeReeBlocks_eq_range]
  exact ⟨i, rfl⟩

theorem largeReeBlockSet_injective :
    Function.Injective fun i : Fin 16 => {x | x ∈ largeReeBlockTable i} := by
  intro i i' h
  by_contra hne
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (largeReeBlockTable_ne_nil_nodup i).1
  exact largeReeBlockTable_disjoint i i' hne x hx ((Set.ext_iff.1 h x).1 hx)

theorem ncard_largeReeBlockSet (i : Fin 16) :
    {x | x ∈ largeReeBlockTable i}.ncard = (largeReeBlockTable i).length := by
  rw [← List.coe_toFinset, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup (largeReeBlockTable_ne_nil_nodup i).2]

theorem isRoot_of_mem_largeReeBlocks
    {Q : Set (Fin F4.tag.rank → ℤ)} (hQ : Q ∈ largeReeBlocks)
    {x : Fin F4.tag.rank → ℤ} (hx : x ∈ Q) : IsRoot F4.tag x := by
  obtain ⟨w, -, j, rfl⟩ := hQ
  obtain ⟨β, hβ, rfl⟩ := hx
  exact IsRoot.smul (mem_fixedOrbitRoots_iff.1 hβ).1 w

theorem ncard_largeReeBlocks :
    largeReeBlocks.ncard = 16 := by
  rw [largeReeBlocks_eq_range, Set.ncard_range_of_injective largeReeBlockSet_injective,
    Nat.card_eq_fintype_card, Fintype.card_fin]

theorem largeReeBlocks_disjoint
    {Q Q' : Set (Fin F4.tag.rank → ℤ)} (hQ : Q ∈ largeReeBlocks)
    (hQ' : Q' ∈ largeReeBlocks) (hne : Q ≠ Q') : Disjoint Q Q' := by
  rw [largeReeBlocks_eq_range] at hQ hQ'
  obtain ⟨i, rfl⟩ := hQ
  obtain ⟨i', rfl⟩ := hQ'
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  exact largeReeBlockTable_disjoint i i' (fun h => hne (by rw [h])) x hx hx'

theorem sUnion_largeReeBlocks :
    ⋃₀ largeReeBlocks = {α | IsRoot F4.tag α} := by
  refine Set.Subset.antisymm (fun x ⟨Q, hQ, hx⟩ => isRoot_of_mem_largeReeBlocks hQ hx)
    fun α hα => ?_
  have hα' : IsRoot F4.tag α := hα
  obtain ⟨m, hm, rfl⟩ := RootCertificate.exists_root_eq F4.tag.rootCertificate_check hα'
  obtain ⟨i, hi⟩ := largeReeBlockTable_cover m hm
  exact ⟨_, largeReeBlockSet_mem i, hi⟩

theorem ncard_largeReeBlocks_filter
    (P : Set (Fin F4.tag.rank → ℤ) → Prop) (p : Fin 16 → Prop)
    [DecidablePred p] (hP : ∀ i, P {x | x ∈ largeReeBlockTable i} ↔ p i) :
    {Q | Q ∈ largeReeBlocks ∧ P Q}.ncard = (Finset.univ.filter p).card := by
  have h : {Q | Q ∈ largeReeBlocks ∧ P Q} =
      (fun i : Fin 16 => {x | x ∈ largeReeBlockTable i}) '' ↑(Finset.univ.filter p) := by
    ext Q
    rw [largeReeBlocks_eq_range]
    constructor
    · rintro ⟨⟨i, rfl⟩, hQ⟩
      exact ⟨i, by simpa using (hP i).1 hQ, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, rfl⟩, (hP i).2 (by simpa using hi)⟩
  rw [h, Set.ncard_image_of_injective _ largeReeBlockSet_injective, Set.ncard_coe_finset]

theorem largeReeBlockSet_subset_iff
    (i : Fin 16) :
    {x | x ∈ largeReeBlockTable i} ⊆ {α | IsRoot F4.tag α ∧ 0 < height α} ↔
      ∀ x ∈ largeReeBlockTable i, 0 < height x :=
  ⟨fun h _ hx => (h hx).2,
    fun h x hx => ⟨isRoot_of_mem_largeReeBlocks (largeReeBlockSet_mem i) hx, h x hx⟩⟩

theorem ncard_largeReePosBlocks_filter
    (n : ℕ) :
    {Q | Q ∈ largeReePosBlocks ∧ Q.ncard = n}.ncard =
      (Finset.univ.filter fun i : Fin 16 =>
        (∀ x ∈ largeReeBlockTable i, 0 < height x) ∧ (largeReeBlockTable i).length = n).card := by
  have e : {Q | Q ∈ largeReePosBlocks ∧ Q.ncard = n} = {Q | Q ∈ largeReeBlocks ∧
      (Q ⊆ {α | IsRoot F4.tag α ∧ 0 < height α} ∧ Q.ncard = n)} := by
    ext Q
    exact and_assoc
  rw [e]
  exact ncard_largeReeBlocks_filter _ _ fun i => by
    rw [largeReeBlockSet_subset_iff, ncard_largeReeBlockSet]

theorem largeReeBlocks_sign
    {Q : Set (Fin F4.tag.rank → ℤ)} (hQ : Q ∈ largeReeBlocks) :
    (∀ α ∈ Q, 0 < height α) ∨ ∀ α ∈ Q, height α < 0 := by
  obtain ⟨w, hw, j, rfl⟩ := hQ
  rcases fixedOrbitRoots_sign hw j with h | h
  · left
    rintro _ ⟨β, hβ, rfl⟩
    exact h β hβ
  · right
    rintro _ ⟨β, hβ, rfl⟩
    exact h β hβ

theorem dualRoot_mem_fixedOrbitRoots_F4 {j : Fin F4.fixedOrbitCount}
    {α : Fin F4.tag.rank → ℤ} (hα : α ∈ F4.fixedOrbitRoots j) :
    F4.dualRoot α ∈ F4.fixedOrbitRoots j := by
  rw [fixedOrbitRoots_eq_list] at hα ⊢
  exact dualRoot_mem_fixedOrbitRootList_F4 j α hα

theorem dualRoot_mem_largeReeBlocks
    {Q : Set (Fin F4.tag.rank → ℤ)} (hQ : Q ∈ largeReeBlocks)
    {α : Fin F4.tag.rank → ℤ} (hα : α ∈ Q) : F4.dualRoot α ∈ Q := by
  obtain ⟨w, hw, j, rfl⟩ := hQ
  obtain ⟨β, hβ, rfl⟩ := hα
  have hδ : F4.weylPerm w = w := hw
  refine ⟨F4.dualRoot β, dualRoot_mem_fixedOrbitRoots_F4 hβ, ?_⟩
  change w • F4.dualRoot β = F4.dualRoot (w • β)
  rw [dualRoot_smul w (mem_fixedOrbitRoots_iff.1 hβ).1, hδ]

theorem height_list_sum {τ : Tag} (l : List (Fin τ.rank → ℤ)) :
    height l.sum = (l.map height).sum := by
  induction l with
  | nil => simp [height]
  | cons x l ih =>
    rw [List.sum_cons, List.map_cons, List.sum_cons, ← ih]
    simp [height, Finset.sum_add_distrib]

theorem list_sum_mem_fixedOrbitRoots {t : ReeTag} {j : Fin t.fixedOrbitCount}
    {l : List (Fin t.tag.rank → ℤ)} (hl : l ≠ []) (hmem : ∀ x ∈ l, x ∈ t.fixedOrbitRoots j)
    (hr : IsRoot t.tag l.sum) : l.sum ∈ t.fixedOrbitRoots j := by
  refine mem_fixedOrbitRoots_iff.2 ⟨hr, ?_, fun i hi => ?_⟩
  · rw [height_list_sum]
    refine List.sum_pos _ (fun h hh => ?_) (by simpa using hl)
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hh
    exact (mem_fixedOrbitRoots_iff.1 (hmem x hx)).2.1
  · rw [Pi.list_sum_apply]
    refine List.sum_eq_zero fun y hy => ?_
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    exact (mem_fixedOrbitRoots_iff.1 (hmem x hx)).2.2 i hi

theorem list_sum_mem_largeReeBlocks
    {Q : Set (Fin F4.tag.rank → ℤ)} (hQ : Q ∈ largeReeBlocks)
    {l : List (Fin F4.tag.rank → ℤ)} (hl : l ≠ []) (hmem : ∀ x ∈ l, x ∈ Q)
    (hr : IsRoot F4.tag l.sum) : l.sum ∈ Q := by
  obtain ⟨w, -, j, rfl⟩ := hQ
  have hll : (l.map (w⁻¹ • ·)).map (w • ·) = l := by
    simp [List.map_map, Function.comp_def]
  have hsum : l.sum = w • (l.map (w⁻¹ • ·)).sum := by
    rw [List.smul_sum, hll]
  have hmem' : ∀ x ∈ l.map (w⁻¹ • ·), x ∈ F4.fixedOrbitRoots j := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    obtain ⟨β, hβ, rfl⟩ := hmem y hy
    simpa using hβ
  have hr' : IsRoot F4.tag (l.map (w⁻¹ • ·)).sum := by
    rw [hsum] at hr
    exact (isRoot_smul_iff w).1 hr
  rw [hsum]
  exact ⟨_, list_sum_mem_fixedOrbitRoots (by simpa using hl) hmem' hr', rfl⟩

theorem nsmul_add_nsmul_mem_largeReeBlocks
    {Q : Set (Fin F4.tag.rank → ℤ)}
    (hQ : Q ∈ largeReeBlocks) {α β : Fin F4.tag.rank → ℤ} (hα : α ∈ Q) (hβ : β ∈ Q) {a b : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hr : IsRoot F4.tag (a • α + b • β)) : a • α + b • β ∈ Q := by
  have hs : (List.replicate a α ++ List.replicate b β).sum = a • α + b • β := by
    rw [List.sum_append, List.sum_replicate, List.sum_replicate]
  rw [← hs] at hr ⊢
  refine list_sum_mem_largeReeBlocks hQ ?_ (fun x hx => ?_) hr
  · intro h
    have := congrArg List.length h
    simp only [List.length_append, List.length_replicate, List.length_nil] at this
    omega
  · rcases List.mem_append.1 hx with hx | hx
    · rw [List.eq_of_mem_replicate hx]
      exact hα
    · rw [List.eq_of_mem_replicate hx]
      exact hβ

section Groups

variable (K : Type) [Field K] [Finite K] [CharP K F4.prime] (a : ℕ)

theorem largeReeBlockGroup_eq_map
    {w : WeylGroup F4.tag} (hw : w ∈ F4.relWeylRee)
    (j : Fin F4.fixedOrbitCount) :
    largeReeBlockGroup K a ((w • ·) '' F4.fixedOrbitRoots j) =
      (F4.reeFixedOrbitUnipotent K a j).map
        (MulAut.conj (canonicalRep (coxeterSystem F4.tag) K w)).toMonoidHom := by
  have hn : canonicalRep (coxeterSystem F4.tag) K w ∈ F4.reeGamma K a :=
    (canonicalRep_mem_reeFixedMonomial F4 K a hw).2
  rw [reeFixedOrbitUnipotent, Subgroup.map_inf_eq _ _ _ (MulAut.conj _).injective,
    (canonical_weyl_root_transport F4.tag K).1 w _ fun α hα => (mem_fixedOrbitRoots_iff.1 hα).1,
    map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hn)]
  rfl

theorem largeReeBlockGroup_ne_bot
    {w : WeylGroup F4.tag} (hw : w ∈ F4.relWeylRee)
    (j : Fin F4.fixedOrbitCount) :
    largeReeBlockGroup K a ((w • ·) '' F4.fixedOrbitRoots j) ≠ ⊥ := by
  rw [largeReeBlockGroup_eq_map K a hw j]
  obtain ⟨u, hu, hu1⟩ := exists_ne_one_mem_reeFixedOrbitUnipotent (t := F4) (K := K) (a := a) j
  intro h
  have hmem : MulAut.conj (canonicalRep (coxeterSystem F4.tag) K w) u ∈
      (F4.reeFixedOrbitUnipotent K a j).map
        (MulAut.conj (canonicalRep (coxeterSystem F4.tag) K w)).toMonoidHom := ⟨u, hu, rfl⟩
  rw [h, Subgroup.mem_bot, MulAut.conj_apply, mul_inv_eq_one, mul_eq_left] at hmem
  exact hu1 hmem

theorem bijOn_list_prod_largeReeBlockGroup
    (Q : Fin 8 → Set (Fin F4.tag.rank → ℤ))
    (hQinj : Function.Injective Q) (hQ : Set.range Q = largeReePosBlocks) :
    Set.BijOn (fun x : Fin 8 → ModGL F4.tag K => (List.ofFn x).prod)
      (Set.univ.pi fun k => (largeReeBlockGroup K a (Q k) : Set (ModGL F4.tag K)))
      (F4.reeFixedPosUnipotent K a : Set (ModGL F4.tag K)) := by
  classical
  have hQmem : ∀ k, Q k ∈ largeReePosBlocks := fun k => hQ ▸ Set.mem_range_self k
  have hQB : ∀ k, Q k ∈ largeReeBlocks := fun k => (hQmem k).1
  have hQpos : ∀ k, ∀ α ∈ Q k, IsRoot F4.tag α ∧ 0 < height α := fun k _ hα => (hQmem k).2 hα
  have hL : ∀ k, ∃ i : Fin 16, {x | x ∈ largeReeBlockTable i} = Q k := fun k => by
    have h := hQB k
    rw [largeReeBlocks_eq_range] at h
    exact h
  choose ι hι using hL
  have hdisj : ∀ k k', k ≠ k' → Disjoint (Q k) (Q k') := fun k k' h =>
    largeReeBlocks_disjoint (hQB k) (hQB k') (hQinj.ne h)
  have hcover : ∀ α, IsRoot F4.tag α → 0 < height α → ∃ k, α ∈ Q k := by
    intro α hr hp
    have hU : α ∈ ⋃₀ largeReeBlocks := by
      rw [sUnion_largeReeBlocks]
      exact hr
    obtain ⟨Q', hQ', hα⟩ := hU
    have hpos : Q' ∈ largeReePosBlocks := by
      refine ⟨hQ', fun β hβ => ⟨isRoot_of_mem_largeReeBlocks hQ' hβ, ?_⟩⟩
      rcases largeReeBlocks_sign hQ' with h | h
      · exact h β hβ
      · exact absurd (h α hα) (by omega)
    rw [← hQ] at hpos
    obtain ⟨k, rfl⟩ := hpos
    exact ⟨k, hα⟩
  have hBij := bijOn_list_prod_rootSpan (K := K) (Q := Q)
    (L := fun k => largeReeBlockTable (ι k)) hQpos
    (fun k _ hα _ hβ _ _ ha hb hr => nsmul_add_nsmul_mem_largeReeBlocks (hQB k) hα hβ ha hb hr)
    (fun k => (largeReeBlockTable_ne_nil_nodup (ι k)).2) hι hdisj hcover
  refine ⟨fun x hx => ?_, fun x hx y hy h => ?_, fun g hg => ?_⟩
  · refine Subgroup.mem_inf.2 ⟨hBij.1 fun k _ => (hx k (Set.mem_univ k)).1,
      Subgroup.list_prod_mem _ fun y hy => ?_⟩
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hy
    exact (hx k (Set.mem_univ k)).2
  · exact hBij.2.1 (fun k _ => (hx k (Set.mem_univ k)).1) (fun k _ => (hy k (Set.mem_univ k)).1) h
  · obtain ⟨u, hu, rfl⟩ := hBij.2.2 (Subgroup.mem_inf.1 hg).1
    have hga : ∀ k, u k ∈ adjointGroup F4.tag K := fun k =>
      rootSpan_le_adjointGroup _ (hu k (Set.mem_univ k))
    set ũ : Fin 8 → adjointGroup F4.tag K := fun k => ⟨u k, hga k⟩ with hũ
    set v : Fin 8 → ModGL F4.tag K :=
      fun k => ((F4.finiteReeAut K a (ũ k) : adjointGroup F4.tag K) : ModGL F4.tag K) with hv
    have hvQ : ∀ k, v k ∈ rootSpan F4.tag K (Q k) := fun k =>
      finiteReeAut_mem_of_map_le (map_finiteReeAut_rootSpan_le fun α hα =>
        ⟨(hQpos k α hα).1, dualRoot_mem_largeReeBlocks (hQB k) hα⟩) (hu k (Set.mem_univ k))
        (hga k)
    have hprod : (List.ofFn v).prod = (List.ofFn u).prod := by
      have hga' : (List.ofFn u).prod ∈ adjointGroup F4.tag K :=
        Subgroup.list_prod_mem _ fun y hy => by
          obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hy
          exact hga k
      have e : (⟨(List.ofFn u).prod, hga'⟩ : adjointGroup F4.tag K) = (List.ofFn ũ).prod := by
        refine Subtype.ext ?_
        rw [Subgroup.val_list_prod, List.map_ofFn]
        rfl
      have hF := finiteReeAut_eq_of_mem_reeGamma (Subgroup.mem_inf.1 hg).2 hga'
      rw [e, map_list_prod, List.map_ofFn, Subgroup.val_list_prod, List.map_ofFn] at hF
      exact hF
    have hvu : v = u := hBij.2.1 (fun k _ => hvQ k) hu hprod
    refine ⟨u, fun k _ => Subgroup.mem_inf.2 ⟨hu k (Set.mem_univ k),
      mem_reeGamma_of_fixed (hga k) (congrFun hvu k)⟩, rfl⟩

end Groups

theorem large_Ree_relative_block_collection
    (a : ℕ) (K : Type) [Field K] [Finite K]
    [CharP K F4.prime] :
    largeReeBlocks.ncard = 16 ∧
    (∀ Q ∈ largeReeBlocks, ∀ Q' ∈ largeReeBlocks, Q ≠ Q' → Disjoint Q Q') ∧
    ⋃₀ largeReeBlocks = {α | IsRoot F4.tag α} ∧
    {Q | Q ∈ largeReeBlocks ∧ Q.ncard = 2}.ncard = 8 ∧
    {Q | Q ∈ largeReeBlocks ∧ Q.ncard = 4}.ncard = 8 ∧
    (∀ Q ∈ largeReeBlocks, ((∀ α ∈ Q, 0 < height α) ∨ ∀ α ∈ Q, height α < 0) ∧
      (∀ α ∈ Q, F4.dualRoot α ∈ Q) ∧
      ∀ l : List (Fin F4.tag.rank → ℤ), l ≠ [] → (∀ α ∈ l, α ∈ Q) → IsRoot F4.tag l.sum →
        l.sum ∈ Q) ∧
    {Q | Q ∈ largeReePosBlocks ∧ Q.ncard = 2}.ncard = 4 ∧
    {Q | Q ∈ largeReePosBlocks ∧ Q.ncard = 4}.ncard = 4 ∧
    (∀ w ∈ F4.relWeylRee, ∀ j : Fin F4.fixedOrbitCount,
      largeReeBlockGroup K a ((w • ·) '' F4.fixedOrbitRoots j) =
        (F4.reeFixedOrbitUnipotent K a j).map
          (MulAut.conj (canonicalRep (coxeterSystem F4.tag) K w)).toMonoidHom ∧
      largeReeBlockGroup K a ((w • ·) '' F4.fixedOrbitRoots j) ≠ ⊥) ∧
    ∀ Q : Fin 8 → Set (Fin F4.tag.rank → ℤ), Function.Injective Q →
      Set.range Q = largeReePosBlocks →
      Set.BijOn (fun x : Fin 8 → ModGL F4.tag K => (List.ofFn x).prod)
        (Set.univ.pi fun k => (largeReeBlockGroup K a (Q k) : Set (ModGL F4.tag K)))
        (F4.reeFixedPosUnipotent K a : Set (ModGL F4.tag K)) := by
  obtain ⟨c2, c4, p2, p4⟩ := largeReeBlockTable_card
  refine ⟨ncard_largeReeBlocks, fun Q hQ Q' hQ' hne => largeReeBlocks_disjoint hQ hQ' hne,
    sUnion_largeReeBlocks, ?_, ?_,
    fun Q hQ => ⟨largeReeBlocks_sign hQ, fun α hα => dualRoot_mem_largeReeBlocks hQ hα,
      fun l hl hmem hr => list_sum_mem_largeReeBlocks hQ hl hmem hr⟩, ?_, ?_,
    fun w hw j => ⟨largeReeBlockGroup_eq_map K a hw j, largeReeBlockGroup_ne_bot K a hw j⟩,
    fun Q hQinj hQ => bijOn_list_prod_largeReeBlockGroup K a Q hQinj hQ⟩
  · exact (ncard_largeReeBlocks_filter (fun Q => Q.ncard = 2)
      (fun i => (largeReeBlockTable i).length = 2)
      fun i => by rw [ncard_largeReeBlockSet]).trans c2
  · exact (ncard_largeReeBlocks_filter (fun Q => Q.ncard = 4)
      (fun i => (largeReeBlockTable i).length = 4)
      fun i => by rw [ncard_largeReeBlockSet]).trans c4
  · exact (ncard_largeReePosBlocks_filter 2).trans p2
  · exact (ncard_largeReePosBlocks_filter 4).trans p4

end ReeTag

end CFSG.LieType.Ree
